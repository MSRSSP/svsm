use vstd::raw_ptr::PointsToRaw;
use vstd::simple_pptr::PointsTo;

pub type RawPerm = PointsToRaw;

pub type TypedPerm<T> = PointsTo<T>;
