// `<*const T>::byte_offset_from` / `byte_offset_from_unsigned` and the `*mut T` forms (core const_ptr.rs,
// mut_ptr.rs): a byte distance between pointers to different pointee types, in a constant too.
// interprocess 2.4.7's `offset_of!` computes a field offset this way.
#[repr(C)] struct P { a: u8, b: u32, c: [u16; 3] }
const OFF: usize = { let d = std::mem::MaybeUninit::<P>::uninit(); let base = d.as_ptr(); let f = unsafe { std::ptr::addr_of!((*base).c) }; unsafe { f.cast::<()>().byte_offset_from(base.cast::<()>()) as usize } };
#[test] fn t() {
    assert_eq!(OFF, 8);
    let mut x = [0u32; 4];
    let p = x.as_mut_ptr();
    unsafe {
        assert_eq!(p.add(3).byte_offset_from(p), 12);
        assert_eq!(p.add(3).byte_offset_from_unsigned(p as *mut u8), 12);
        assert_eq!((p as *const u32).byte_offset_from(p.add(1)), -4);
    }
}
