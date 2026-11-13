// rejects: a statement metavariable cannot expand in item position
// Even an item captured by `$s:stmt` is an NtStmt, not an NtItem.
macro_rules! as_item {
    ($s:stmt) => { $s };
}
as_item!(const VALUE: u32 = 7;);
