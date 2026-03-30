use core::ops::{Add, Div, Sub};

use hybrid_array::{
    ArraySize,
    sizes::{U1, U8, U64},
    typenum::{Diff, NonZero, Quot, Sum, Unsigned},
};

mod sealed_trait {
    pub trait AuthorizedWordBitsize {}
}

impl sealed_trait::AuthorizedWordBitsize for U8 {}
impl sealed_trait::AuthorizedWordBitsize for U64 {}

pub trait WordsizeFromBitsize<WordBitsize: sealed_trait::AuthorizedWordBitsize>: Unsigned {
    type Output: ArraySize + NonZero;
}

impl<Bitsize, WordBitsize: sealed_trait::AuthorizedWordBitsize> WordsizeFromBitsize<WordBitsize>
    for Bitsize
where
    Bitsize: Unsigned + Sub<U1>,
    Diff<Bitsize, U1>: Div<WordBitsize>,
    Quot<Diff<Bitsize, U1>, WordBitsize>: Add<U1>,
    Sum<Quot<Diff<Bitsize, U1>, WordBitsize>, U1>: ArraySize + NonZero,
{
    type Output = Sum<Quot<Diff<Bitsize, U1>, WordBitsize>, U1>;
}

pub(crate) type Bytesize<Bitsize> = <Bitsize as WordsizeFromBitsize<U8>>::Output;
pub(crate) type Octobytesize<Bitsize> = <Bitsize as WordsizeFromBitsize<U64>>::Output;
