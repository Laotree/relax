//! SipHash (rustc library/core/src/hash/sip.rs): `SipHasher` (2-4, deprecated since 1.13) and the
//! hidden SipHasher13 (1-3) that real std's DefaultHasher::new hashes with (fast.rs). Same
//! algorithm and byte stream as real core, so each hashes to real core's values for the same keys.

use super::Hasher;

#[derive(Debug, Clone, Copy)]
struct State {
    v0: u64,
    v2: u64,
    v1: u64,
    v3: u64,
}

fn compress(s: &mut State) {
    s.v0 = s.v0.wrapping_add(s.v1);
    s.v2 = s.v2.wrapping_add(s.v3);
    s.v1 = s.v1.rotate_left(13);
    s.v1 ^= s.v0;
    s.v3 = s.v3.rotate_left(16);
    s.v3 ^= s.v2;
    s.v0 = s.v0.rotate_left(32);

    s.v2 = s.v2.wrapping_add(s.v1);
    s.v0 = s.v0.wrapping_add(s.v3);
    s.v1 = s.v1.rotate_left(17);
    s.v1 ^= s.v2;
    s.v3 = s.v3.rotate_left(21);
    s.v3 ^= s.v0;
    s.v2 = s.v2.rotate_left(32);
}

/// Little-endian load of `len` (< 8) bytes of `buf` starting at `start`.
fn u8to64_le(buf: &[u8], start: usize, len: usize) -> u64 {
    let mut out = 0u64;
    let mut i = 0;
    while i < len {
        out |= (buf[start + i] as u64) << (i * 8);
        i += 1;
    }
    out
}

/// The state both variants share; `c` / `d`: the compression rounds per message word and at the end.
#[derive(Debug, Clone)]
struct Sip {
    length: usize, // how many bytes we've processed
    state: State,  // hash State
    tail: u64,     // unprocessed bytes le
    ntail: usize,  // how many bytes in tail are valid
}

impl Sip {
    const fn new_with_keys(key0: u64, key1: u64) -> Sip {
        Sip {
            length: 0,
            state: State {
                v0: key0 ^ 0x736f6d6570736575,
                v1: key1 ^ 0x646f72616e646f6d,
                v2: key0 ^ 0x6c7967656e657261,
                v3: key1 ^ 0x7465646279746573,
            },
            tail: 0,
            ntail: 0,
        }
    }

    #[inline]
    fn rounds(s: &mut State, n: usize) {
        let mut i = 0;
        while i < n {
            compress(s);
            i += 1;
        }
    }

    #[inline]
    fn write(&mut self, msg: &[u8], c: usize) {
        let length = msg.len();
        self.length += length;

        let mut needed = 0;

        if self.ntail != 0 {
            needed = 8 - self.ntail;
            let take = if length < needed { length } else { needed };
            self.tail |= u8to64_le(msg, 0, take) << (8 * self.ntail);
            if length < needed {
                self.ntail += length;
                return;
            } else {
                self.state.v3 ^= self.tail;
                Sip::rounds(&mut self.state, c);
                self.state.v0 ^= self.tail;
                self.ntail = 0;
            }
        }

        // Buffered tail is now flushed, process new input.
        let len = length - needed;
        let left = len & 0x7; // len % 8

        let mut i = needed;
        while i < len - left {
            let mi = u8to64_le(msg, i, 7) | ((msg[i + 7] as u64) << 56);

            self.state.v3 ^= mi;
            Sip::rounds(&mut self.state, c);
            self.state.v0 ^= mi;

            i += 8;
        }

        self.tail = u8to64_le(msg, i, left);
        self.ntail = left;
    }

    #[inline]
    fn finish(&self, c: usize, d: usize) -> u64 {
        let mut state = self.state;

        let b: u64 = ((self.length as u64 & 0xff) << 56) | self.tail;

        state.v3 ^= b;
        Sip::rounds(&mut state, c);
        state.v0 ^= b;

        state.v2 ^= 0xff;
        Sip::rounds(&mut state, d);

        state.v0 ^ state.v1 ^ state.v2 ^ state.v3
    }
}

/// SipHash-2-4.
#[derive(Debug, Clone)]
pub struct SipHasher(Sip);

impl SipHasher {
    #[deprecated(since = "1.13.0", note = "use `std::hash::DefaultHasher` instead")]
    #[must_use]
    pub fn new() -> SipHasher {
        SipHasher(Sip::new_with_keys(0, 0))
    }

    #[deprecated(since = "1.13.0", note = "use `std::hash::DefaultHasher` instead")]
    #[must_use]
    pub fn new_with_keys(key0: u64, key1: u64) -> SipHasher {
        SipHasher(Sip::new_with_keys(key0, key1))
    }
}

impl Default for SipHasher {
    fn default() -> SipHasher {
        SipHasher(Sip::new_with_keys(0, 0))
    }
}

impl Hasher for SipHasher {
    fn write(&mut self, msg: &[u8]) {
        self.0.write(msg, 2)
    }

    fn finish(&self) -> u64 {
        self.0.finish(2, 4)
    }
}

/// SipHash-1-3, real core's hidden SipHasher13: the hash of real std's `DefaultHasher::new()`. Its
/// writes are real core's: integers as their native-endian bytes (`write`), a str as its bytes and
/// 0xff (the Hasher defaults).
#[derive(Debug, Clone)]
pub(crate) struct SipHasher13(Sip);

impl SipHasher13 {
    pub(crate) const fn new_with_keys(key0: u64, key1: u64) -> SipHasher13 {
        SipHasher13(Sip::new_with_keys(key0, key1))
    }
}

impl Hasher for SipHasher13 {
    fn write(&mut self, msg: &[u8]) {
        self.0.write(msg, 1)
    }

    fn finish(&self) -> u64 {
        self.0.finish(1, 3)
    }
}
