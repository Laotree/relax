use macro_dep::{value, Value};

pub fn value() -> Value {
    value!()
}

pub fn module() -> &'static str {
    module_path!()
}
