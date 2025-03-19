// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>

#![no_std]
#![allow(unused_braces)]
#![allow(unexpected_cfgs)]
use builtin_macros::*;

pub mod bits;
pub mod nonlinear;
pub mod set;
pub mod tseq;
pub mod frac_perm;
pub mod unique_ptr;

verus! {

global size_of usize == 8;

}
