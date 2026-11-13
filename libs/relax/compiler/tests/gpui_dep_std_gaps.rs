//! std items and method lookups that GPUI's dependencies use (circular-buffer, indexmap,
//! allocator-api2, rustix, chrono, futures-util, async-process, zerovec), against rustc's std.
use std::fmt;
use std::num::NonZeroI32;
use std::ops::Bound;
use std::panic::AssertUnwindSafe;

#[test]
fn slice_split_off() {
    let mut s: &[i32] = &[1, 2, 3, 4, 5, 6];
    assert_eq!(s.split_off(..2), Some(&[1, 2][..]));
    assert_eq!(s.split_off(3..), Some(&[6][..]));
    assert_eq!(s.split_off(..=0), Some(&[3][..]));
    assert_eq!(s.split_off_first(), Some(&4));
    assert_eq!(s.split_off_last(), Some(&5));
    assert!(s.is_empty());
    assert_eq!(s.split_off(..1), None);
    assert_eq!(s.split_off_first(), None);
}

#[test]
fn slice_split_off_mut() {
    let mut a = [1, 2, 3, 4, 5];
    let mut s: &mut [i32] = &mut a;
    s.split_off_mut(..1).unwrap()[0] = 10;
    *s.split_off_first_mut().unwrap() = 20;
    *s.split_off_last_mut().unwrap() = 50;
    s.split_off_mut(1..).unwrap()[0] = 40;
    assert_eq!(s.len(), 1);
    assert!(s.split_off_mut(..9).is_none());
    assert_eq!(a, [10, 20, 3, 40, 50]);
}

fn by_bounds<T>(s: &[T], r: (Bound<usize>, Bound<usize>)) -> &[T] {
    &s[r]
}

#[test]
fn slice_index_by_bound_pair() {
    let mut v = [1, 2, 3, 4];
    assert_eq!(&v[(Bound::Excluded(0), Bound::Included(2))], &[2, 3]);
    assert_eq!(by_bounds(&v, (Bound::Unbounded, Bound::Excluded(1))), &[1]);
    v[(Bound::Included(3), Bound::Unbounded)][0] = 9;
    assert_eq!(v[3], 9);
    let s: &[i32] = &v;
    assert_eq!(&s[(Bound::Included(1), Bound::Excluded(3))], &[2, 3]);
    assert_eq!(v.get((Bound::Excluded(1), Bound::Unbounded)), Some(&[3, 9][..]));
}

#[test]
fn slice_as_mut_ptr_range() {
    let mut v = vec![1u8, 2, 3];
    let r = v.as_mut_ptr_range();
    assert_eq!(unsafe { r.end.offset_from(r.start) }, 3);
    unsafe { *r.start = 7 };
    assert_eq!(v[0], 7);
}

#[test]
fn integer_exponent_format() {
    assert_eq!(format!("{:e}", 1500u32), "1.5e3");
    assert_eq!(format!("{:E}", 1500i64), "1.5E3");
    assert_eq!(format!("{:e}", -1500i64), "-1.5e3");
    assert_eq!(format!("{:e}", 0u8), "0e0");
    assert_eq!(format!("{:e}", 7u8), "7e0");
    assert_eq!(format!("{:e}", u128::MAX), "3.40282366920938463463374607431768211455e38");
    assert_eq!(format!("{:e}", i8::MIN), "-1.28e2");
    assert_eq!(format!("{:.3e}", 15u32), "1.500e1");
    assert_eq!(format!("{:.0e}", 15u32), "2e1");
    assert_eq!(format!("{:.0e}", 25u32), "2e1");
    assert_eq!(format!("{:.1e}", 1250u32), "1.2e3");
    assert_eq!(format!("{:.1e}", 1350u32), "1.4e3");
    assert_eq!(format!("{:.1e}", 1251u32), "1.3e3");
    assert_eq!(format!("{:.1e}", 999u32), "1.0e3");
    assert_eq!(format!("{:+010.2e}", 15i32), "+0001.50e1");
    assert_eq!(format!("{:>8e}", 100usize), "     1e2");
}

#[test]
fn nonzero_radix_and_exponent_format() {
    let n = NonZeroI32::new(10).unwrap();
    assert_eq!(format!("{:b} {:o} {:x} {:X} {:e} {:E}", n, n, n, n, n, n), "1010 12 a A 1e1 1E1");
    assert_eq!(format!("{:#06x}", n), "0x000a");
}

// rustix's newtype formatting: the implemented trait is in scope inside its own impl
struct Pid(NonZeroI32);
impl fmt::Binary for Pid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
struct Uid(u32);
impl fmt::LowerExp for Uid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

#[test]
fn newtype_forwards_format() {
    assert_eq!(format!("{:b}", Pid(NonZeroI32::new(5).unwrap())), "101");
    assert_eq!(format!("{:e}", Uid(1500)), "1.5e3");
}

// chrono's `Date<Tz>: Display`: `Tz::Offset: Display` by a where-clause and `Debug` by the
// associated type's bound; only Display is in scope, so the call is not ambiguous
trait Offset: Clone + fmt::Debug {}
trait TimeZone {
    type Offset: Offset;
}
#[derive(Clone, Debug)]
struct FixedOffset;
impl Offset for FixedOffset {}
impl fmt::Display for FixedOffset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("+00:00")
    }
}
struct Utc;
impl TimeZone for Utc {
    type Offset = FixedOffset;
}
struct Date<Tz: TimeZone> {
    offset: Tz::Offset,
}
impl<Tz: TimeZone> fmt::Display for Date<Tz>
where
    Tz::Offset: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.offset.fmt(f)
    }
}

#[test]
fn projection_bound_method_is_not_ambiguous() {
    assert_eq!(Date::<Utc> { offset: FixedOffset }.to_string(), "+00:00");
}

fn as_debug<T: fmt::Debug>(x: &AssertUnwindSafe<T>) -> &dyn fmt::Debug {
    x
}

#[test]
fn assert_unwind_safe_debug() {
    assert_eq!(format!("{:?}", as_debug(&AssertUnwindSafe(5))), "AssertUnwindSafe(5)");
}

#[cfg(unix)]
#[test]
fn command_ext_uid_gid() {
    use std::os::unix::fs::MetadataExt;
    use std::os::unix::process::CommandExt;
    // this process's own user: setuid to it needs no privilege
    let dir = std::env::temp_dir().join(format!("relax-uid-{}", std::process::id()));
    std::fs::write(&dir, b"x").unwrap();
    let uid = std::fs::metadata(&dir).unwrap().uid();
    std::fs::remove_file(&dir).unwrap();
    let status = std::process::Command::new("true").uid(uid).status().unwrap();
    assert!(status.success());
    let mut with_group = std::process::Command::new("true");
    with_group.gid(0);
    let _ = &with_group;
}
