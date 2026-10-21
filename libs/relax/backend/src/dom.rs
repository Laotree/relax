//! Dominators and block layout order on RIR, shared by the emitters and the optimiser.

use crate::regalloc::reachable;
use crate::rir::*;

/// `relayout`, returning the new order: per new block, the block it was.
pub fn relayout_order(f: &mut Func) -> Vec<u32> {
    let n = f.blocks.len();
    if n <= 1 {
        return (0..n as u32).collect();
    }
    let reach = reachable(f);
    // blocks only reachable through unwind edges (cleanup pads) are cold
    let mut normal = vec![false; n];
    let mut st = vec![0u32];
    while let Some(b) = st.pop() {
        if normal[b as usize] {
            continue;
        }
        normal[b as usize] = true;
        match f.blocks[b as usize].term {
            Term::Invoke(t, _) => st.push(t),
            ref t => st.extend(t.succs()),
        }
    }
    // Loops stay contiguous (LLVM MachineBlockPlacement builds a loop's chains before the code
    // around it): a chain does not leave the innermost loop of its block while that loop still
    // has blocks to place, and the next chain starts in the innermost loop of the last placed
    // block that has some. Without it, a loop whose body the source order splits around other
    // code was laid out in pieces: inflate's fast loop had its literal path at 0x566 and its
    // length/match path at 0x1393, 3.3 KB of the slow decoder between (14x rustc's i-cache misses,
    // 40% more taken branches).
    let nest = LoopNest::new(f, &reach);
    let mut left: Vec<u32> = nest.size.clone();
    // per loop: the next body index (bodies ascending) not known to be placed
    let mut cursor = vec![0usize; nest.body.len()];
    let mut placed = vec![false; n];
    let mut order: Vec<u32> = Vec::new();
    let mut cold: Vec<u32> = Vec::new();
    let mut next = 0u32;
    let mut unplaced = 0;
    loop {
        let mut b = next;
        let mut last = b;
        while !placed[b as usize] && reach[b as usize] {
            placed[b as usize] = true;
            last = b;
            let mut l = nest.inner[b as usize];
            while l != NO_LOOP {
                left[l as usize] -= 1;
                l = nest.parent[l as usize];
            }
            if (matches!(f.blocks[b as usize].term, Term::Unreachable | Term::Resume) || !normal[b as usize]) && b != 0 {
                cold.push(b);
            } else {
                order.push(b);
            }
            // the innermost loop of b with blocks still to place: the chain stays in it
            let mut l = nest.inner[b as usize];
            while l != NO_LOOP && left[l as usize] == 0 {
                l = nest.parent[l as usize];
            }
            let stays = |s: u32| l == NO_LOOP || nest.contains(l, s);
            b = match f.blocks[b as usize].term {
                Term::Jump(t) | Term::Invoke(t, _) => {
                    if !stays(t) {
                        break;
                    }
                    t
                }
                Term::Branch(_, t, e) => {
                    // fall through to the true successor (then-block, loop body) unless it is
                    // placed already, a panic path or out of the loop
                    let t_cold = matches!(f.blocks[t as usize].term, Term::Unreachable);
                    if !placed[t as usize] && !t_cold && stays(t) {
                        t
                    } else if stays(e) {
                        e
                    } else {
                        break;
                    }
                }
                _ => break,
            };
        }
        // the next chain: the first unplaced block of the innermost loop around the last one
        // that has any
        let mut seed = None;
        let mut l = nest.inner[last as usize];
        while l != NO_LOOP {
            if left[l as usize] > 0 {
                let body = &nest.body[l as usize];
                let c = &mut cursor[l as usize];
                while *c < body.len() && placed[body[*c] as usize] {
                    *c += 1;
                }
                if *c < body.len() {
                    seed = Some(body[*c]);
                    break;
                }
            }
            l = nest.parent[l as usize];
        }
        if let Some(s) = seed {
            next = s;
            continue;
        }
        // Placement is monotone: earlier blocks never need to be searched again.
        while unplaced < n && (placed[unplaced] || !reach[unplaced]) {
            unplaced += 1;
        }
        if unplaced == n {
            break;
        }
        next = unplaced as u32;
    }
    order.extend(cold);
    let mut map = vec![u32::MAX; n];
    for (i, b) in order.iter().enumerate() {
        map[*b as usize] = i as u32;
    }
    let old = std::mem::take(&mut f.blocks);
    let mut slots: Vec<Option<Block>> = Vec::with_capacity(n);
    for b in old {
        slots.push(Some(b));
    }
    for b in &order {
        let mut blk = slots[*b as usize].take().unwrap();
        blk.term.map_succs(|t| map[t as usize]);
        f.blocks.push(blk);
    }
    order
}

const NO_LOOP: u32 = u32::MAX;

/// Natural loops of the reachable blocks (a back edge's target dominates its source; the body is
/// what reaches the source without passing the header), nested by containment. Irreducible
/// cycles are no loops here.
struct LoopNest {
    /// per block: its innermost loop (NO_LOOP: none)
    inner: Vec<u32>,
    /// per loop: the loop around it
    parent: Vec<u32>,
    /// per loop: its blocks (nested loops' included), ascending
    body: Vec<Vec<u32>>,
    size: Vec<u32>,
}

impl LoopNest {
    fn new(f: &Func, reach: &[bool]) -> LoopNest {
        let n = f.blocks.len();
        let mut nest = LoopNest { inner: vec![NO_LOOP; n], parent: Vec::new(), body: Vec::new(), size: Vec::new() };
        let mut latches: Vec<(u32, u32)> = Vec::new();
        let idom = idoms(f);
        let (pre, post, _) = dom_numbers(&idom);
        let dominates = |a: u32, b: u32| pre[a as usize] != u32::MAX && pre[b as usize] != u32::MAX && pre[a as usize] <= pre[b as usize] && post[b as usize] <= post[a as usize];
        for b in 0..n as u32 {
            if !reach[b as usize] {
                continue;
            }
            for s in f.blocks[b as usize].term.succs() {
                if dominates(s, b) {
                    latches.push((s, b));
                }
            }
        }
        if latches.is_empty() {
            return nest;
        }
        let mut preds: Vec<Vec<u32>> = vec![Vec::new(); n];
        for b in 0..n as u32 {
            if reach[b as usize] {
                for s in f.blocks[b as usize].term.succs() {
                    preds[s as usize].push(b);
                }
            }
        }
        latches.sort_unstable();
        let mut mark = vec![u32::MAX; n];
        let mut heads: Vec<u32> = Vec::new();
        let mut st: Vec<u32> = Vec::new();
        let mut k = 0;
        while k < latches.len() {
            let h = latches[k].0;
            let id = heads.len() as u32;
            heads.push(h);
            mark[h as usize] = id;
            let mut body = vec![h];
            while k < latches.len() && latches[k].0 == h {
                st.push(latches[k].1);
                k += 1;
            }
            while let Some(b) = st.pop() {
                if mark[b as usize] == id {
                    continue;
                }
                mark[b as usize] = id;
                body.push(b);
                st.extend(preds[b as usize].iter().copied().filter(|&p| reach[p as usize]));
            }
            body.sort_unstable();
            nest.size.push(body.len() as u32);
            nest.body.push(body);
        }
        // innermost first: a block's first loop is its innermost, a header's next one its parent
        let mut by_size: Vec<u32> = (0..heads.len() as u32).collect();
        by_size.sort_by_key(|&l| nest.size[l as usize]);
        nest.parent = vec![NO_LOOP; heads.len()];
        let mut head_of = vec![NO_LOOP; n];
        for (l, &h) in heads.iter().enumerate() {
            head_of[h as usize] = l as u32;
        }
        for &l in &by_size {
            for &b in &nest.body[l as usize] {
                if nest.inner[b as usize] == NO_LOOP {
                    nest.inner[b as usize] = l;
                }
                let m = head_of[b as usize];
                if m != NO_LOOP && m != l && nest.parent[m as usize] == NO_LOOP {
                    nest.parent[m as usize] = l;
                }
            }
        }
        nest
    }

    /// block b is in loop l (or a loop inside it)
    fn contains(&self, l: u32, b: u32) -> bool {
        let mut m = self.inner[b as usize];
        while m != NO_LOOP {
            if m == l {
                return true;
            }
            m = self.parent[m as usize];
        }
        false
    }
}

/// Immediate dominators (Cooper/Harvey/Kennedy) over reachable blocks; entry's idom is itself.
pub fn idoms(f: &Func) -> Vec<u32> {
    let succs_of = |b: u32| f.blocks[b as usize].term.succs();
    let n = f.blocks.len();
    if n == 1 {
        return vec![0];
    }
    // reverse postorder
    let mut rpo: Vec<u32> = Vec::with_capacity(n);
    let mut seen = vec![false; n];
    let mut stack: Vec<(u32, u8)> = Vec::with_capacity(2 * n);
    stack.push((0, 0));
    while let Some((b, st)) = stack.pop() {
        if st == 0 {
            if seen[b as usize] {
                continue;
            }
            seen[b as usize] = true;
            stack.push((b, 1));
            // pushed in reverse: the first successor is visited first
            let succ: Vec<u32> = succs_of(b).collect();
            for t in succ.iter().rev() {
                stack.push((*t, 0));
            }
        } else {
            rpo.push(b);
        }
    }
    rpo.reverse();
    let mut order = vec![u32::MAX; n];
    for (i, b) in rpo.iter().enumerate() {
        order[*b as usize] = i as u32;
    }
    // predecessors in reverse postorder, flat (pred_off[b]..pred_off[b + 1])
    let mut pred_off = vec![0u32; n + 1];
    for &b in &rpo {
        for t in succs_of(b) {
            pred_off[t as usize + 1] += 1;
        }
    }
    for i in 0..n {
        pred_off[i + 1] += pred_off[i];
    }
    let mut fill = pred_off.clone();
    let mut preds = vec![0u32; pred_off[n] as usize];
    for &b in &rpo {
        for t in succs_of(b) {
            preds[fill[t as usize] as usize] = b;
            fill[t as usize] += 1;
        }
    }
    let mut idom = vec![u32::MAX; n];
    idom[0] = 0;
    let mut changed = true;
    while changed {
        changed = false;
        for &b in rpo.iter().skip(1) {
            let mut new = u32::MAX;
            for &p in &preds[pred_off[b as usize] as usize..pred_off[b as usize + 1] as usize] {
                if idom[p as usize] == u32::MAX {
                    continue;
                }
                if new == u32::MAX {
                    new = p;
                } else {
                    let (mut x, mut y) = (p, new);
                    while x != y {
                        while order[x as usize] > order[y as usize] {
                            x = idom[x as usize];
                        }
                        while order[y as usize] > order[x as usize] {
                            y = idom[y as usize];
                        }
                    }
                    new = x;
                }
            }
            if new != u32::MAX && idom[b as usize] != new {
                idom[b as usize] = new;
                changed = true;
            }
        }
    }
    idom
}

/// Dominator-tree pre/post numbers: `a` dominates `b` iff pre[a] <= pre[b] && post[b] <= post[a].
/// Dominator-tree children, flat: block b's children (ascending) are
/// `child[off[b]..off[b + 1]]`.
pub struct DomKids {
    off: Vec<u32>,
    child: Vec<u32>,
}

impl std::ops::Index<usize> for DomKids {
    type Output = [u32];
    #[inline]
    fn index(&self, b: usize) -> &[u32] {
        &self.child[self.off[b] as usize..self.off[b + 1] as usize]
    }
}

pub fn dom_numbers(idom: &[u32]) -> (Vec<u32>, Vec<u32>, DomKids) {
    let n = idom.len();
    let mut off = vec![0u32; n + 1];
    for b in 1..n {
        if idom[b] != u32::MAX && idom[b] as usize != b {
            off[idom[b] as usize + 1] += 1;
        }
    }
    for i in 0..n {
        off[i + 1] += off[i];
    }
    let mut fill = off.clone();
    let mut child = vec![0u32; off[n] as usize];
    for b in 1..n {
        if idom[b] != u32::MAX && idom[b] as usize != b {
            let p = idom[b] as usize;
            child[fill[p] as usize] = b as u32;
            fill[p] += 1;
        }
    }
    let children = DomKids { off, child };
    let mut pre = vec![u32::MAX; n];
    let mut post = vec![0u32; n];
    let mut clock = 0u32;
    let mut stack: Vec<(u32, bool)> = Vec::with_capacity(2 * n);
    stack.push((0, false));
    while let Some((b, done)) = stack.pop() {
        if done {
            post[b as usize] = clock;
            clock += 1;
            continue;
        }
        pre[b as usize] = clock;
        clock += 1;
        stack.push((b, true));
        for &c in children[b as usize].iter().rev() {
            stack.push((c, false));
        }
    }
    (pre, post, children)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A loop whose body is split around other code by block numbering is laid out in one piece:
    /// b0 -> b1 (header: body b2 or exit b8); b2 -> b3 (latch) or b6 -> b7 (latch); b4, b5 are
    /// after the loop (reached from the exit) but numbered between its parts.
    #[test]
    fn a_loop_body_stays_contiguous() {
        let mut f = Func::new("lp".to_string(), 0);
        let c = f.vreg(Cls::I);
        f.params.push(c);
        for _ in 0..9 {
            f.block();
        }
        f.blocks[0].term = Term::Jump(1);
        f.blocks[1].term = Term::Branch(c, 2, 8);
        f.blocks[2].term = Term::Branch(c, 3, 6);
        f.blocks[3].term = Term::Jump(1);
        f.blocks[4].term = Term::Jump(5);
        f.blocks[5].term = Term::Ret(vec![]);
        f.blocks[6].term = Term::Jump(7);
        f.blocks[7].term = Term::Jump(1);
        f.blocks[8].term = Term::Jump(4);
        let order = relayout_order(&mut f);
        let at = |b: u32| order.iter().position(|&x| x == b).unwrap();
        let mut lp: Vec<usize> = [1, 2, 3, 6, 7].iter().map(|&b| at(b)).collect();
        lp.sort();
        assert_eq!(lp[4] - lp[0], 4, "loop blocks not contiguous: {order:?}");
        assert_eq!(order[0], 0);
        f.verify().unwrap();
    }

    /// Nested loops: the inner loop's blocks stay together inside the outer one's.
    #[test]
    fn nested_loops_stay_contiguous() {
        let mut f = Func::new("nest".to_string(), 0);
        let c = f.vreg(Cls::I);
        f.params.push(c);
        for _ in 0..8 {
            f.block();
        }
        // b1 outer header (body b2, exit b7); b2 inner header (body b3, exit to b6);
        // b3 -> b4 (unrelated after-code numbered inside) is not in either; b3 -> b5 inner latch
        f.blocks[0].term = Term::Jump(1);
        f.blocks[1].term = Term::Branch(c, 2, 7);
        f.blocks[2].term = Term::Branch(c, 3, 6);
        f.blocks[3].term = Term::Branch(c, 4, 5);
        f.blocks[4].term = Term::Ret(vec![]);
        f.blocks[5].term = Term::Jump(2);
        f.blocks[6].term = Term::Jump(1);
        f.blocks[7].term = Term::Ret(vec![]);
        let order = relayout_order(&mut f);
        let at = |b: u32| order.iter().position(|&x| x == b).unwrap();
        let mut inner: Vec<usize> = [2, 3, 5].iter().map(|&b| at(b)).collect();
        inner.sort();
        assert_eq!(inner[2] - inner[0], 2, "inner loop split: {order:?}");
        let mut outer: Vec<usize> = [1, 2, 3, 5, 6].iter().map(|&b| at(b)).collect();
        outer.sort();
        assert_eq!(outer[4] - outer[0], 4, "outer loop split: {order:?}");
    }
}
