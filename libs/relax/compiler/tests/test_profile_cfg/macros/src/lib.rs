extern crate proc_macro;

#[proc_macro]
pub fn host_debug(_: proc_macro::TokenStream) -> proc_macro::TokenStream {
    format!("({}, {})", cfg!(debug_assertions), profile_dep::debug_enabled()).parse().unwrap()
}
