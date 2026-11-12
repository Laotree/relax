// io::repeat / Repeat, Empty as a writer and seeker, &Sink, IoSlice / IoSliceMut (new, deref,
// advance, advance_slices), the default read_vectored / write_vectored, the adapters' derived
// Debug (Take, Chain, Bytes, Lines, Split) and Seek for Take (real std).
use std::io::{self, IoSlice, IoSliceMut, Read, Seek, SeekFrom, Write};

#[test]
fn a01_repeat_empty_sink() {
    let mut buf = [0u8; 5];
    let n = io::repeat(7).read(&mut buf).unwrap();
    println!("| repeat {} {:?}", n, buf);
    let mut taken = Vec::new();
    io::repeat(b'z').take(4).read_to_end(&mut taken).unwrap();
    println!("| take {:?}", String::from_utf8(taken).unwrap());
    let mut v = Vec::new();
    println!("| repeat read_to_end {:?}", io::repeat(1).read_to_end(&mut v).map_err(|e| e.kind()));
    let mut e = io::empty();
    println!("| empty write {:?} seek {:?} flush {:?}", e.write(b"abc").map_err(|e| e.kind()), e.seek(SeekFrom::End(5)).map_err(|e| e.kind()), e.flush().is_ok());
    let s = io::sink();
    let mut r = &s;
    println!("| &sink {:?} {:?}", r.write(b"xyz").map_err(|e| e.kind()), io::copy(&mut io::repeat(0).take(1000), &mut io::sink()).map_err(|e| e.kind()));
    println!("| debug {:?} {:?}", io::empty(), io::sink());
}

#[test]
fn a02_io_slices() {
    let a = [1u8, 2, 3];
    let b = [4u8, 5];
    let c = [6u8, 7, 8, 9];
    let mut slices = [IoSlice::new(&a), IoSlice::new(&b), IoSlice::new(&c)];
    println!("| deref {} {:?}", slices[0].len(), &*slices[1]);
    let mut bufs: &mut [IoSlice] = &mut slices;
    IoSlice::advance_slices(&mut bufs, 4);
    println!("| advanced {} first {:?}", bufs.len(), &*bufs[0]);
    let mut one = IoSlice::new(&c);
    one.advance(2);
    println!("| one {:?} dbg {:?}", &*one, one);
    let mut out = Vec::new();
    let n = out.write_vectored(&[IoSlice::new(&[]), IoSlice::new(&a), IoSlice::new(&b)]).unwrap();
    println!("| write_vectored {} {:?}", n, out);
    let mut x = [0u8; 2];
    let mut y = [0u8; 3];
    let mut src: &[u8] = &[9, 8, 7, 6, 5];
    let n = src.read_vectored(&mut [IoSliceMut::new(&mut x), IoSliceMut::new(&mut y)]).unwrap();
    println!("| read_vectored {} {:?} {:?}", n, x, y);
    let mut m1 = [1u8; 3];
    let mut m2 = [2u8; 3];
    let mut ms = [IoSliceMut::new(&mut m1), IoSliceMut::new(&mut m2)];
    let mut mb: &mut [IoSliceMut] = &mut ms;
    IoSliceMut::advance_slices(&mut mb, 5);
    mb[0][0] = 99;
    println!("| mut advanced {} {:?}", mb.len(), &*mb[0]);
}

#[test]
fn a03_adapters_debug() {
    use std::io::BufRead;
    // relax issue 99: a derived Debug over a `?Sized` reader's Take field (zip's ZipFileReader),
    // here for an unsized reader
    #[derive(Debug)]
    enum Reader<'a, R: Read + ?Sized> {
        Raw(io::Take<&'a mut R>),
        None,
    }
    trait DebugRead: Read + std::fmt::Debug {}
    impl<T: Read + std::fmt::Debug> DebugRead for T {}
    let mut b = [0u8; 2];
    let mut cur = io::Cursor::new(vec![1u8, 2, 3, 4, 5]);
    let r: &mut dyn DebugRead = &mut cur;
    let mut raw: Reader<'_, dyn DebugRead> = Reader::Raw(r.take(3));
    if let Reader::Raw(t) = &mut raw {
        t.read(&mut b).unwrap();
    }
    println!("| reader {:?} {:?}", raw, Reader::<dyn DebugRead>::None);
    // real std's derived Debug of the adapters: Take's len (the limit as set) and limit (left)
    let mut t = io::Cursor::new(vec![1u8, 2, 3, 4, 5]).take(3);
    println!("| take {:?}", t);
    t.read(&mut b).unwrap();
    println!("| take {:?}", t);
    t.set_limit(10);
    println!("| take {:?} {}", t, t.limit());
    let mut c = (&b"ab"[..]).chain(&b"cd"[..]);
    println!("| chain {:?}", c);
    let mut three = [0u8; 3];
    let n = c.read(&mut three).unwrap();
    println!("| chain {} {:?}", n, c);
    println!("| bytes {:?}", (&b"xy"[..]).bytes());
    println!("| lines {:?}", io::Cursor::new(&b"l1\nl2"[..]).lines());
    println!("| split {:?}", io::Cursor::new(&b"a,b"[..]).split(b','));
    println!("| pretty {}", format!("{:#?}", io::empty().take(7)).replace('\n', "/"));
}

#[test]
fn a04_take_seek() {
    // real std's Seek for Take: a position counts from where the Take began, within its len
    let show = |r: io::Result<u64>| format!("{:?}", r.map_err(|e| (e.kind(), e.to_string())));
    let mut inner = io::Cursor::new(vec![1u8, 2, 3, 4, 5, 6, 7]);
    inner.set_position(1);
    let mut t = inner.take(4);
    let mut b = [0u8; 1];
    t.read(&mut b).unwrap();
    println!("| at {:?} {:?}", t.stream_position(), t);
    for to in [SeekFrom::Current(1), SeekFrom::Start(0), SeekFrom::End(-1), SeekFrom::Current(9), SeekFrom::Current(-9), SeekFrom::End(1), SeekFrom::Start(4), SeekFrom::End(-4)] {
        let r = show(t.seek(to));
        let mut x = [0u8; 1];
        let n = t.read(&mut x).unwrap();
        println!("| seek {:?} {} read {} {:?} {:?}", to, r, n, x, t);
    }
    let rel = |t: &mut io::Take<io::Cursor<Vec<u8>>>, o: i64| format!("{:?}", t.seek_relative(o).map_err(|e| e.kind()));
    println!("| relative {} {} {} {:?}", rel(&mut t, 1), rel(&mut t, 9), rel(&mut t, -9), t);
    t.rewind().unwrap();
    println!("| rewound {:?} {:?}", t.stream_position(), t);
    t.set_limit(2);
    println!("| set {} {} {:?}", show(t.seek(SeekFrom::End(0))), show(t.seek(SeekFrom::Start(3))), t);
}
