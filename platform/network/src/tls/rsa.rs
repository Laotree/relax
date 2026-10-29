//! RSASSA-PKCS1-v1_5 signature verification with SHA-256 (RFC 8017 8.2.2),
//! for checking a certificate against its issuer's RSA key. Public-key
//! operations only: nothing here touches secret data, so plain (not
//! constant-time) arithmetic is fine.

use crate::digest::sha256_hash;

/// DigestInfo prefixes for SHA-256: with the NULL parameters (the standard
/// encoding) and without them (which verifiers must also accept).
const SHA256_DIGEST_INFO: [u8; 19] =
    [0x30, 0x31, 0x30, 0x0D, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20];
const SHA256_DIGEST_INFO_NO_NULL: [u8; 17] =
    [0x30, 0x2F, 0x30, 0x0B, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x04, 0x20];

fn strip_zeros(bytes: &[u8]) -> &[u8] {
    let first = bytes.iter().position(|b| *b != 0).unwrap_or(bytes.len());
    &bytes[first..]
}

/// Big-endian bytes into `len` little-endian 32-bit limbs.
fn limbs(be: &[u8], len: usize) -> Vec<u32> {
    let mut out = vec![0u32; len];
    for (i, b) in be.iter().rev().enumerate() {
        out[i / 4] |= (*b as u32) << (8 * (i % 4));
    }
    out
}

fn to_be(limbs: &[u32], len: usize) -> Vec<u8> {
    let mut out = vec![0u8; len];
    for i in 0..len {
        out[len - 1 - i] = (limbs[i / 4] >> (8 * (i % 4))) as u8;
    }
    out
}

fn geq(a: &[u32], b: &[u32]) -> bool {
    for i in (0..a.len()).rev() {
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    true
}

fn sub_in_place(a: &mut [u32], b: &[u32]) {
    let mut borrow = 0i64;
    for i in 0..a.len() {
        let d = a[i] as i64 - b[i] as i64 - borrow;
        borrow = (d < 0) as i64;
        a[i] = d as u32;
    }
}

/// Montgomery arithmetic modulo an odd `n` (R = 2^(32 * limbs)).
struct Mont {
    n: Vec<u32>,
    /// -n^-1 mod 2^32.
    n0: u32,
}

impl Mont {
    fn new(n: Vec<u32>) -> Self {
        let mut inv = n[0];
        for _ in 0..5 {
            inv = inv.wrapping_mul(2u32.wrapping_sub(n[0].wrapping_mul(inv)));
        }
        Self { n, n0: inv.wrapping_neg() }
    }

    /// a * b / R mod n (CIOS); a, b < n.
    fn mul(&self, a: &[u32], b: &[u32]) -> Vec<u32> {
        let s = self.n.len();
        let mut t = vec![0u32; s + 2];
        for i in 0..s {
            let mut carry = 0u64;
            for j in 0..s {
                let v = t[j] as u64 + a[j] as u64 * b[i] as u64 + carry;
                t[j] = v as u32;
                carry = v >> 32;
            }
            let v = t[s] as u64 + carry;
            t[s] = v as u32;
            t[s + 1] = (v >> 32) as u32;
            let m = t[0].wrapping_mul(self.n0);
            let mut carry = (t[0] as u64 + m as u64 * self.n[0] as u64) >> 32;
            for j in 1..s {
                let v = t[j] as u64 + m as u64 * self.n[j] as u64 + carry;
                t[j - 1] = v as u32;
                carry = v >> 32;
            }
            let v = t[s] as u64 + carry;
            t[s - 1] = v as u32;
            t[s] = t[s + 1] + (v >> 32) as u32;
        }
        let mut out = t[..s].to_vec();
        if t[s] != 0 || geq(&out, &self.n) {
            sub_in_place(&mut out, &self.n);
        }
        out
    }

    /// R^2 mod n, by doubling 1 (64 * limbs) times.
    fn r_squared(&self) -> Vec<u32> {
        let s = self.n.len();
        let mut r = vec![0u32; s];
        r[0] = 1;
        for _ in 0..64 * s {
            let top = r[s - 1] >> 31;
            for i in (1..s).rev() {
                r[i] = (r[i] << 1) | (r[i - 1] >> 31);
            }
            r[0] <<= 1;
            if top != 0 || geq(&r, &self.n) {
                sub_in_place(&mut r, &self.n);
            }
        }
        r
    }

    /// base^exp mod n; exp > 0.
    fn pow(&self, base: &[u32], exp: u64) -> Vec<u32> {
        let s = self.n.len();
        let base_m = self.mul(base, &self.r_squared());
        let mut x = base_m.clone();
        for bit in (0..63 - exp.leading_zeros()).rev() {
            x = self.mul(&x, &x);
            if exp >> bit & 1 == 1 {
                x = self.mul(&x, &base_m);
            }
        }
        let mut one = vec![0u32; s];
        one[0] = 1;
        self.mul(&x, &one)
    }
}

/// Whether `signature` is a valid RSASSA-PKCS1-v1_5 SHA-256 signature of
/// `message` under the public key (`modulus`, `exponent`, big-endian).
/// Keys of 2048 to 8192 bits.
pub fn verify_pkcs1_sha256(modulus: &[u8], exponent: &[u8], message: &[u8], signature: &[u8]) -> bool {
    let n = strip_zeros(modulus);
    let e = strip_zeros(exponent);
    let k = n.len();
    if !(256..=1024).contains(&k) || n[k - 1] & 1 == 0 || e.is_empty() || e.len() > 8 || signature.len() != k {
        return false;
    }
    let exp = e.iter().fold(0u64, |acc, b| (acc << 8) | *b as u64);
    if exp < 3 || exp & 1 == 0 {
        return false;
    }
    let s = k.div_ceil(4);
    let mont = Mont::new(limbs(n, s));
    let sig = limbs(signature, s);
    if geq(&sig, &mont.n) {
        return false;
    }
    let em = to_be(&mont.pow(&sig, exp), k);
    let hash = sha256_hash(message);
    [&SHA256_DIGEST_INFO[..], &SHA256_DIGEST_INFO_NO_NULL[..]].iter().any(|info| {
        let t_len = info.len() + hash.len();
        if k < t_len + 11 {
            return false;
        }
        let ps = k - t_len - 3;
        em[0] == 0
            && em[1] == 1
            && em[2..2 + ps].iter().all(|b| *b == 0xFF)
            && em[2 + ps] == 0
            && &em[3 + ps..3 + ps + info.len()] == *info
            && em[3 + ps + info.len()..] == hash
    })
}
