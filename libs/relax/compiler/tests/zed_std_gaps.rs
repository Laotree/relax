//! std items Zed's crates use (editor, multi_buffer, proto, rpc, project_panel), against rustc's std.
use std::any::Any;
use std::path::{Path, PathBuf};

#[test]
#[allow(deprecated)]
fn collections_bound_reexport() {
    // library/std/src/collections/mod.rs: `pub use crate::ops::Bound` (deprecated)
    let b: std::collections::Bound<usize> = std::ops::Bound::Included(3);
    assert_eq!(b, std::ops::Bound::Included(3));
}

#[test]
fn box_any_send_sync_downcast() {
    let ok: Box<dyn Any + Send + Sync> = Box::new(7u32);
    assert_eq!(*ok.downcast::<u32>().unwrap(), 7);
    let other: Box<dyn Any + Send + Sync> = Box::new("x");
    let back = other.downcast::<u32>().unwrap_err();
    assert_eq!(*back.downcast::<&str>().unwrap(), "x");
}

/// palette's `BitOps` (theme's `Hsla::from_color`): `bool` takes its bit operators' operands by
/// reference too.
#[test]
fn bool_bit_operators_by_reference() {
    fn all<T>(a: T, b: T) -> (T, T, T)
    where
        for<'a> T: std::ops::BitAnd<&'a T, Output = T> + std::ops::BitOr<&'a T, Output = T> + std::ops::BitXor<&'a T, Output = T> + Copy,
    {
        (a & &b, a | &b, a ^ &b)
    }
    assert_eq!(all(true, false), (false, true, true));
    let (t, f) = (&true, &false);
    assert_eq!((t & f, t | false, true ^ t), (false, true, false));
    let mut m = true;
    m &= &false;
    m |= &true;
    m ^= &true;
    assert!(!m);
}

/// What zed's run reaches in wasmtime (`expose_provenance`, `paca`), scc (`NonNull::align_offset`)
/// and wax (`Cow<str> + Cow<str>`).
#[test]
fn run_time_std_items_of_zeds_dependencies() {
    let mut x = 7u64;
    let p: *mut u64 = &mut x;
    assert_eq!(p.expose_provenance(), p as usize);
    assert_eq!((p as *const u64).expose_provenance(), p as usize);
    let nn = std::ptr::NonNull::new(p).unwrap();
    assert_eq!(nn.align_offset(8), 0);
    let joined = std::borrow::Cow::Borrowed("a") + std::borrow::Cow::Borrowed("b");
    assert_eq!(joined, "ab");
    let mut c = std::borrow::Cow::Borrowed("");
    c += "x";
    c += std::borrow::Cow::Owned("y".to_string());
    assert_eq!(c, "xy");
    #[cfg(target_arch = "aarch64")]
    {
        let _ = std::arch::is_aarch64_feature_detected!("paca");
        let _ = std::arch::is_aarch64_feature_detected!("sve2");
        assert!(std::arch::is_aarch64_feature_detected!("neon"));
    }
}

/// slotmap 1.0's `#[derive(Debug)]` SparseSecondaryMap drain holds a `hash_map::Drain`: both
/// drains print the entries still to come.
#[test]
fn hash_drains_print_what_is_left() {
    let mut m = std::collections::HashMap::new();
    m.insert(1u8, 2u8);
    let mut d = m.drain();
    assert_eq!(format!("{d:?}"), "[(1, 2)]");
    assert_eq!(d.next(), Some((1, 2)));
    assert_eq!(format!("{d:?}"), "[]");
    drop(d);
    let mut s = std::collections::HashSet::new();
    s.insert(3u8);
    assert_eq!(format!("{:?}", s.drain()), "[3]");
}

/// moxcms's NEON color conversion: unsigned float conversions, widening multiply-accumulate,
/// saturating narrowing, RDM rounding doubling multiply-accumulate (Arm's definitions; rustc runs
/// the instructions).
#[cfg(target_arch = "aarch64")]
#[test]
fn neon_color_conversion_lanes() {
    use std::arch::aarch64::*;
    unsafe {
        let f: float32x4_t = std::mem::transmute([1.9f32, -3.0, 4e9, f32::NAN]);
        let z: [u32; 4] = std::mem::transmute(vcvtq_u32_f32(f));
        assert_eq!(z, [1, 0, 4_000_000_000, 0]);
        let n: float32x4_t = std::mem::transmute([1.5f32, 2.5, -0.4, 5e10]);
        let a: [u32; 4] = std::mem::transmute(vcvtaq_u32_f32(n));
        assert_eq!(a, [2, 3, 0, u32::MAX]);
        let acc: [i32; 4] = std::mem::transmute(vmlal_s16(std::mem::transmute([1i32, 2, 3, 4]), std::mem::transmute([2i16, -3, 100, 32767]), std::mem::transmute([5i16, 7, -100, 32767])));
        assert_eq!(acc, [11, -19, -9997, 1_073_676_293]);
        let un: [u16; 4] = std::mem::transmute(vqmovun_s32(std::mem::transmute([-5i32, 70000, 300, 65535])));
        assert_eq!(un, [0, 65535, 300, 65535]);
        let (ra, rb, rc): (int16x4_t, int16x4_t, int16x4_t) = (std::mem::transmute([0i16, 0, 32767, -32768]), std::mem::transmute([16384i16, 16384, 32767, -32768]), std::mem::transmute([16384i16, -16384, 32767, -32768]));
        let ah: [i16; 4] = std::mem::transmute(vqrdmlah_s16(ra, rb, rc));
        assert_eq!(ah, [8192, -8192, 32767, 0]);
        let sh: [i16; 4] = std::mem::transmute(vqrdmlsh_s16(ra, rb, rc));
        assert_eq!(sh, [-8192, 8192, 1, -32768]);
        let ahq: [i16; 8] = std::mem::transmute(vqrdmlahq_s16(std::mem::transmute([ra, ra]), std::mem::transmute([rb, rb]), std::mem::transmute([rc, rc])));
        assert_eq!(ahq, [8192, -8192, 32767, 0, 8192, -8192, 32767, 0]);
        let shq: [i16; 8] = std::mem::transmute(vqrdmlshq_s16(std::mem::transmute([ra, ra]), std::mem::transmute([rb, rb]), std::mem::transmute([rc, rc])));
        assert_eq!(shq, [-8192, 8192, 1, -32768, -8192, 8192, 1, -32768]);
        let q32: [i32; 4] = std::mem::transmute(vqrdmlahq_s32(std::mem::transmute([0i32, 0, i32::MAX, 0]), std::mem::transmute([1i32 << 30, -(1 << 30), i32::MAX, 0]), std::mem::transmute([1i32 << 30, 1 << 30, i32::MAX, 0])));
        assert_eq!(q32, [536_870_912, -536_870_912, i32::MAX, 0]);
    }
}

/// What zed's dependencies name or call: `ToSocketAddrs`'s iterator types (tokio-socks),
/// `OsString` and `BinaryHeap` extended (rayon), a deque's `IntoIter` cloned (wax), btree set
/// iterators cloned and printed (wasmparser), listeners' `Incoming` printed (cap-std).
#[test]
fn std_iterator_types_and_impls_of_zed_dependencies() {
    use std::collections::{BTreeSet, BinaryHeap, VecDeque};
    use std::ffi::{OsStr, OsString};
    use std::net::{SocketAddr, ToSocketAddrs};
    let addr: SocketAddr = "127.0.0.1:80".parse().unwrap();
    let one: std::option::IntoIter<SocketAddr> = addr.to_socket_addrs().unwrap();
    assert_eq!(one.collect::<Vec<_>>(), [addr]);
    let list = [addr, addr];
    let many: std::iter::Cloned<std::slice::Iter<'_, SocketAddr>> = (&list[..]).to_socket_addrs().unwrap();
    assert_eq!(many.count(), 2);
    let mut os = OsString::from("a");
    os.extend([OsString::from("b")]);
    os.extend([OsStr::new("c")]);
    os.extend([std::borrow::Cow::Borrowed(OsStr::new("d"))]);
    assert_eq!(os, "abcd");
    let joined: OsString = [OsStr::new("x"), OsStr::new("y")].into_iter().collect();
    assert_eq!(joined, "xy");
    let mut heap: BinaryHeap<i32> = BinaryHeap::new();
    heap.extend(&[3, 1, 2]);
    assert_eq!(heap.into_sorted_vec(), [1, 2, 3]);
    let deque: VecDeque<u8> = [1, 2].into_iter().collect();
    let cycled: Vec<u8> = deque.into_iter().cycle().take(5).collect();
    assert_eq!(cycled, [1, 2, 1, 2, 1]);
    let (a, b): (BTreeSet<u8>, BTreeSet<u8>) = ([1, 2, 3].into(), [2, 3, 4].into());
    let union = a.union(&b);
    assert_eq!(union.clone().count(), 4);
    assert!(!format!("{:?}", a.intersection(&b).clone()).is_empty());
    assert!(!format!("{:?}", a.difference(&b)).is_empty() && !format!("{:?}", a.symmetric_difference(&b)).is_empty());
    assert!(format!("{:?}", a.clone().into_iter()).contains('1'));
    let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
    assert!(format!("{:?}", listener.incoming()).starts_with("Incoming"));
}

/// cap-std iterates a borrowed listener (`for s in &listener`).
#[cfg(unix)]
#[test]
fn a_borrowed_unix_listener_iterates_connections() {
    let path = std::env::temp_dir().join(format!("relax-listener-{}", std::process::id()));
    let _ = std::fs::remove_file(&path);
    let listener = std::os::unix::net::UnixListener::bind(&path).unwrap();
    let client = std::os::unix::net::UnixStream::connect(&path).unwrap();
    let mut incoming: std::os::unix::net::Incoming<'_> = (&listener).into_iter();
    assert!(incoming.next().unwrap().is_ok());
    drop(client);
    std::fs::remove_file(&path).unwrap();
}

/// system-interface's `Peek`: a chain of two buffered readers is one.
#[test]
fn chained_buffered_readers_are_buffered() {
    use std::io::{BufRead, Read};
    let mut chain = (&b"ab\ncd"[..]).chain(&b"e\nf"[..]);
    assert_eq!(chain.fill_buf().unwrap(), b"ab\ncd");
    let mut line = Vec::new();
    assert_eq!(chain.read_until(b'\n', &mut line).unwrap(), 3);
    line.clear();
    assert_eq!(chain.read_until(b'\n', &mut line).unwrap(), 4);
    assert_eq!(line, b"cde\n");
    chain.consume(0);
    let mut rest = String::new();
    chain.read_line(&mut rest).unwrap();
    assert_eq!(rest, "f");
}

/// vsimd's NEON paths (base64 and hex): pairwise min/max, two-register tables, unzips and zips.
#[cfg(target_arch = "aarch64")]
#[test]
fn neon_pairwise_tables_unzip_zip() {
    use std::arch::aarch64::*;
    unsafe {
        let a: uint8x8_t = std::mem::transmute([1u8, 2, 3, 4, 5, 6, 7, 8]);
        let b: uint8x8_t = std::mem::transmute([9u8, 10, 11, 12, 13, 14, 15, 16]);
        let at: [u8; 8] = std::mem::transmute(vpmin_u8(a, b));
        assert_eq!(at, [1, 3, 5, 7, 9, 11, 13, 15]);
        let m: [u32; 2] = std::mem::transmute(vpmax_u32(std::mem::transmute([3u32, 9]), std::mem::transmute([7u32, 2])));
        assert_eq!(m, [9, 7]);
        let u1: [u8; 8] = std::mem::transmute(vuzp1_u8(a, b));
        assert_eq!(u1, [1, 3, 5, 7, 9, 11, 13, 15]);
        let uz = vuzp_u8(a, b);
        let u2: [u8; 8] = std::mem::transmute(uz.1);
        assert_eq!(u2, [2, 4, 6, 8, 10, 12, 14, 16]);
        let t2: [u8; 8] = std::mem::transmute(vtbl2_u8(uint8x8x2_t(a, b), std::mem::transmute([0u8, 8, 15, 16, 7, 3, 255, 9])));
        assert_eq!(t2, [1, 9, 16, 0, 8, 4, 0, 10]);
        let q: uint8x16_t = std::mem::transmute(*b"0123456789abcdef");
        let r: uint8x16_t = std::mem::transmute(*b"ghijklmnopqrstuv");
        let tq: [u8; 16] = std::mem::transmute(vqtbl2q_u8(uint8x16x2_t(q, r), std::mem::transmute([0u8, 16, 31, 32, 15, 17, 200, 1, 2, 3, 4, 5, 6, 7, 8, 9])));
        assert_eq!(&tq, &[b'0', b'g', b'v', 0, b'f', b'h', 0, b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9']);
        let uq = vuzpq_u8(q, r);
        let (e, o): ([u8; 16], [u8; 16]) = (std::mem::transmute(uq.0), std::mem::transmute(uq.1));
        assert_eq!(&e, b"02468acegikmoqsu");
        assert_eq!(&o, b"13579bdfhjlnprtv");
        let e2: [u8; 16] = std::mem::transmute(vuzp1q_u8(q, r));
        let o2: [u8; 16] = std::mem::transmute(vuzp2q_u8(q, r));
        assert_eq!((e2, o2), (e, o));
        let z = vzipq_u8(q, r);
        let (lo, hi): ([u8; 16], [u8; 16]) = (std::mem::transmute(z.0), std::mem::transmute(z.1));
        assert_eq!(&lo, b"0g1h2i3j4k5l6m7n");
        assert_eq!(&hi, b"8o9paqbrcsdteufv");
        let z16 = vzipq_u16(std::mem::transmute([0u16, 1, 2, 3, 4, 5, 6, 7]), std::mem::transmute([10u16, 11, 12, 13, 14, 15, 16, 17]));
        let l16: [u16; 8] = std::mem::transmute(z16.0);
        let h16: [u16; 8] = std::mem::transmute(z16.1);
        assert_eq!((l16, h16), ([0, 10, 1, 11, 2, 12, 3, 13], [4, 14, 5, 15, 6, 16, 7, 17]));
        let z32 = vzipq_u32(std::mem::transmute([0u32, 1, 2, 3]), std::mem::transmute([10u32, 11, 12, 13]));
        let l32: [u32; 4] = std::mem::transmute(z32.0);
        let h32: [u32; 4] = std::mem::transmute(z32.1);
        assert_eq!((l32, h32), ([0, 10, 1, 11], [2, 12, 3, 13]));
    }
}

#[test]
fn components_and_iter_as_path() {
    let mut rest = Path::new("a/b/c").components();
    rest.next();
    let mut p = PathBuf::from("x");
    p.push(rest.clone());
    assert_eq!(p, Path::new("x/b/c"));
    let os: &std::ffi::OsStr = rest.as_ref();
    assert_eq!(os, "b/c");
    let mut iter = Path::new("a/b").iter();
    iter.next();
    let tail: &Path = iter.as_ref();
    assert_eq!(tail, Path::new("b"));
}

/// ordered-float's `Ord::cmp` is `self < other` on `&OrderedFloat`, and its `lt` is its own (not
/// `partial_cmp`'s, which is `cmp`): comparing references forwards every method, as core does,
/// or `cmp` recursed until the stack overflowed (zed's agent panel under `relax run`).
#[test]
fn reference_comparisons_keep_the_types_own_methods() {
    use std::cmp::Ordering;
    #[derive(Clone, Copy, PartialEq, Debug)]
    struct Ordered(f64);
    impl Eq for Ordered {}
    impl PartialOrd for Ordered {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
        fn lt(&self, other: &Self) -> bool {
            !self.ge(other)
        }
        fn le(&self, other: &Self) -> bool {
            other.ge(self)
        }
        fn gt(&self, other: &Self) -> bool {
            !other.ge(self)
        }
        fn ge(&self, other: &Self) -> bool {
            self.0.is_nan() | (self.0 >= other.0)
        }
    }
    impl Ord for Ordered {
        fn cmp(&self, other: &Self) -> Ordering {
            if self < other {
                Ordering::Less
            } else if self > other {
                Ordering::Greater
            } else {
                Ordering::Equal
            }
        }
    }
    let (a, b, nan) = (Ordered(1.0), Ordered(2.0), Ordered(f64::NAN));
    assert_eq!(a.cmp(&b), Ordering::Less);
    assert_eq!(nan.cmp(&b), Ordering::Greater);
    let mut v = vec![b, nan, a];
    v.sort();
    assert_eq!((v[0].0, v[1].0), (1.0, 2.0));
    assert!(v[2].0.is_nan());
    assert!(&mut a.clone() < &mut b.clone());

    struct Never;
    impl PartialEq for Never {
        fn eq(&self, _: &Self) -> bool {
            true
        }
        fn ne(&self, _: &Self) -> bool {
            true
        }
    }
    assert!(&Never != &Never, "a reference's `ne` is the type's own");
}

/// rustfft's NEON butterflies (zed's speech-to-text): the f64 transposes and the lane multiply.
#[cfg(target_arch = "aarch64")]
#[test]
fn neon_f64_transposes_and_lane_multiply() {
    use std::arch::aarch64::*;
    unsafe {
        let a = vld1q_f64([1.0f64, 2.0].as_ptr());
        let b = vld1q_f64([3.0f64, 4.0].as_ptr());
        let mut out = [0.0f64; 2];
        vst1q_f64(out.as_mut_ptr(), vtrn1q_f64(a, b));
        assert_eq!(out, [1.0, 3.0]);
        vst1q_f64(out.as_mut_ptr(), vtrn2q_f64(a, b));
        assert_eq!(out, [2.0, 4.0]);
        vst1q_f64(out.as_mut_ptr(), vmulq_laneq_f64::<1>(a, b));
        assert_eq!(out, [4.0, 8.0]);
    }
}

/// zeromq's tcp transport asserts `ip == resolved_addr.ip()` with `ip: Ipv4Addr` / `Ipv6Addr`:
/// core compares an address with an `IpAddr` both ways.
#[test]
fn ip_addresses_compare_with_ip_addr_both_ways() {
    use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    let v4 = Ipv4Addr::new(127, 0, 0, 1);
    let v6 = Ipv6Addr::LOCALHOST;
    let (any4, any6) = (IpAddr::V4(v4), IpAddr::V6(v6));
    assert!(v4 == any4 && any4 == v4 && v6 == any6 && any6 == v6);
    assert!(v4 != any6 && v6 != any4);
    assert!(v4 < any6 && any6 > v4 && v6 > any4 && any4 < v6);
    assert_eq!(v6.partial_cmp(&any6), Some(std::cmp::Ordering::Equal));
}
