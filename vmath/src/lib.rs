#![no_std]
use vstd::prelude::*;

verus! {
    #[warn(unused_braces)]
    global size_of usize == 8;
}

pub mod bits;
