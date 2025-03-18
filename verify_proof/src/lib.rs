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

verus! {

global size_of usize == 8;


#[cfg_attr(verus_keep_ghost, verifier::broadcast_use_by_default_when_this_crate_is_imported)]
pub broadcast group broadcast_lemmas {
    tseq::TrackedSeq::lemma_eq
}

}
