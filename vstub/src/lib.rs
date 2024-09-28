#![no_std]

#[macro_export]
macro_rules! verus {
    ($($rest:tt)*) => { $($rest)* };
}
