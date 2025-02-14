// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//
// This module defines specification helper functions to verify the correct use of memory.
//
// Trusted Assumptions:
// - hw_spec::SpecMemMapTr is correct
// Proofs:
// - FixedAddressMappingRange is viewed as LinearMap 
// - LinearMap satisfies all properties in hw_spec::SpecMemMapTr

use verify_external::convert::FromSpec;
use verify_external::hw_spec::SpecMemMapTr;

use crate::address::VADDR_RANGE_SIZE;

mod inner {
    use super::*;
    include!("address_space.inner.verus.rs");
}

pub use inner::LinearMap;

verus!{
impl FixedAddressMappingRange {
    pub closed spec fn view(&self) -> LinearMap {
        LinearMap::spec_new(self.virt_start, self.virt_end, self.phys_start)
    }
}
}