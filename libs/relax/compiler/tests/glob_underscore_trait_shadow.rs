// A trait imported `as _` reaches a module through a glob that also has an item named like the
// trait. An underscore import has no name (rustc_resolve gives it a fresh one), so the item
// shadows nothing and the trait's methods stay in scope; a named glob binding is shadowed by
// the item of its own name. interprocess's uds_local_socket/stream.rs: `struct Stream` next to
// `use local_socket::prelude::*` (which holds `traits::Stream as _`).
#![allow(dead_code)]

mod lib {
    pub mod traits {
        pub trait Stream {
            fn timeout(&self, t: u32) -> u32;
        }
        pub trait Renamed {
            fn renamed(&self) -> u32 { 7 }
        }
    }
    pub mod prelude {
        pub use super::traits::Stream as _;
        // a named re-export under another name: only an item of that name shadows it
        pub use super::traits::Renamed as Ext;
    }
    pub mod imp {
        use super::{prelude::*, traits};
        use std::sync::Arc;
        pub struct Stream(pub u32);
        // the trait's own name, not its binding's: no shadowing
        pub struct Renamed;
        impl traits::Stream for Stream {
            fn timeout(&self, t: u32) -> u32 { self.0 + t }
        }
        impl traits::Renamed for Stream {}
        pub struct Half(pub Arc<Stream>);
        impl Half {
            pub fn through_arc(&self) -> u32 { self.0.timeout(1) }
        }
        pub fn by_ref(s: &Stream) -> u32 { s.timeout(2) + s.renamed() }
    }
}

#[test]
fn the_underscore_glob_trait_stays_in_scope() {
    let s = std::sync::Arc::new(lib::imp::Stream(40));
    assert_eq!(lib::imp::Half(s.clone()).through_arc(), 41);
    assert_eq!(lib::imp::by_ref(&s), 49);
}
