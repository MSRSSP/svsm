// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>

#![no_std]
#![allow(unused_braces)]
#![allow(unexpected_cfgs)]
use vstd::prelude::*;

pub mod bits;

verus! {

global size_of usize == 8;

#[verifier(external_body)]
pub const fn tracked_exec_arbirary<T>() -> Tracked<T>
{
    Tracked::assume_new()
}
}
