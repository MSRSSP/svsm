// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
use vstd::prelude::*;

verus! {

pub open spec fn from_spec<T1, T2>(v: T1) -> T2;

pub trait FromSpec<T>: Sized {
    spec fn from_spec(v: T) -> Self;
}

pub broadcast proof fn axiom_from_spec<T, U: FromSpec<T>>(v: T)
    ensures
        (#[trigger] from_spec::<T, U>(v)) === U::from_spec(v),
{
    admit();
}

#[verifier::external_trait_specification]
pub trait ExInto<T>: Sized {
    type ExternalTraitSpecificationFor: core::convert::Into<T>;

    fn into(self) -> (ret: T)
        ensures
            from_spec(self) === ret,
    ;
}

#[verifier::external_trait_specification]
pub trait ExFrom<T>: Sized {
    type ExternalTraitSpecificationFor: core::convert::From<T>;

    fn from(v: T) -> (ret: Self)
        ensures
            from_spec(v) === ret,
    ;
}

#[verifier::external_fn_specification]
pub fn ex_map<T, U, F: FnOnce(T) -> U>(a: Option<T>, f: F) -> (ret: Option<U>)
    requires
        a.is_some() ==> call_requires(f, (a.unwrap(),)),
    ensures
        ret.is_some() ==> a.is_some(),
        ret.is_some() ==> call_ensures(f, (a.unwrap(),), ret.unwrap()),
{
    a.map(f)
}

pub broadcast group group_convert_axioms {
    axiom_from_spec,
}

} // verus!
macro_rules! num_specs {
    ($uN:ty) => {
        verus! {
        pub open spec fn saturating_add(x: $uN, y: $uN) -> $uN {
            if x + y > <$uN>::MAX {
                <$uN>::MAX
            } else {
                (x + y) as $uN
            }
        }

        #[verifier::external_fn_specification]
        #[verifier::when_used_as_spec(saturating_add)]
        pub fn ex_saturating_add(x: $uN, y: $uN) -> (res: $uN)
            ensures res == saturating_add(x, y)
        {
            x.saturating_add(y)
        }
        }
    };
}

num_specs! {usize}
