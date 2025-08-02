use core::ops::RangeInclusive;
use open_enum_meta::Discriminant;
use open_enum_meta::Repr;

const REPR_RANGES: &'static [(Repr, RangeInclusive<i128>)] = &[
    (Repr::I8, (i8::MIN as i128)..=(i8::MAX as i128)),
    (Repr::U8, (u8::MIN as i128)..=(u8::MAX as i128)),
    (Repr::I16, (i16::MIN as i128)..=(i16::MAX as i128)),
    (Repr::U16, (u16::MIN as i128)..=(u16::MAX as i128)),
    (Repr::I32, (i32::MIN as i128)..=(i32::MAX as i128)),
    (Repr::U32, (u32::MIN as i128)..=(u32::MAX as i128)),
    (Repr::I64, (i64::MIN as i128)..=(i64::MAX as i128)),
    (Repr::U64, (u64::MIN as i128)..=(u64::MAX as i128)),
    (Repr::Isize, (isize::MIN as i128)..=(isize::MAX as i128)),
    (Repr::Usize, (usize::MIN as i128)..=(usize::MAX as i128)),
];

/// Finds the smallest repr that can fit this range, if any.
fn smallest_fitting_repr(range: RangeInclusive<i128>) -> Option<Repr> {
    // TODO: perhaps check this logic matches current rustc behavior?
    for (repr, repr_range) in REPR_RANGES {
        if range_contains(repr_range, &range) {
            return Some(*repr);
        }
    }
    None
}

fn range_contains(x: &RangeInclusive<i128>, y: &RangeInclusive<i128>) -> bool {
    x.contains(y.start()) && x.contains(y.end())
}

/// Figure out what the internal representation of the enum should be given its variants.
///
/// If we don't have sufficient info to auto-shrink the internal repr, fallback to isize.
pub fn autodetect_inner_repr<'a>(variants: impl Iterator<Item = &'a Discriminant>) -> Repr {
    let mut variants = variants.peekable();
    if variants.peek().is_none() {
        // TODO: maybe use the unit type for a fieldless open enum without a #[repr]?
        return Repr::Isize;
    }
    let mut min = i128::MAX;
    let mut max = i128::MIN;
    for value in variants {
        match value {
            &Discriminant::Literal(value) => {
                min = min.min(value);
                max = max.max(value);
            }
            Discriminant::Nonliteral { .. } => {
                // No way to do fancy sizing here, fall back to isize.
                return Repr::Isize;
            }
        }
    }
    smallest_fitting_repr(min..=max).unwrap_or(Repr::Isize)
}
