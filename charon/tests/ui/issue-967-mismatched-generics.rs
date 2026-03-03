//@ charon-args=--preset=aeneas
//@ no-default-options
//@ known-failure

use std::marker::PhantomData;

pub trait NonZero {}
pub struct Eager {}

pub trait BufferKindUser: BlockSizeUser {
    type BufferKind;
}

pub trait IsLess<Rhs = Self> {
    type Output;
}

pub trait BlockSizeUser {
    type BlockSize;
}

pub trait ExtendableOutputCore: BlockSizeUser + BufferKindUser
where
    Self::BlockSize: IsLess<u128>,
    <<Self as BlockSizeUser>::BlockSize as IsLess<u128>>::Output: NonZero,
{
    type ReaderCore: BlockSizeUser;

    fn finalize_xof_core(
        &mut self,
        buffer: &mut BlockBuffer<
            <Self as BlockSizeUser>::BlockSize,
            <Self as BufferKindUser>::BufferKind,
        >,
    ) -> Self::ReaderCore;
}

pub struct XofReaderCoreWrapper<T>(PhantomData<(T, BlockBuffer<T::BlockSize, Eager>)>)
where
    T: BlockSizeUser,
    T::BlockSize: IsLess<u128>,
    <<T as BlockSizeUser>::BlockSize as IsLess<u128>>::Output: NonZero;

impl<T> ExtendableOutput for CoreWrapper<T>
where
    T: ExtendableOutputCore,
    T::BlockSize: IsLess<u128>,
    <<T as BlockSizeUser>::BlockSize as IsLess<u128>>::Output: NonZero,
    <T::ReaderCore as BlockSizeUser>::BlockSize: IsLess<u128>,
    <<T::ReaderCore as BlockSizeUser>::BlockSize as IsLess<u128>>::Output: NonZero,
{
    type Reader = XofReaderCoreWrapper<T::ReaderCore>;

    fn finalize_xof(self) -> Self::Reader {
        panic!()
    }
}


pub struct BlockBuffer<BlockSize, Kind>(PhantomData<(BlockSize, Kind)>)
where
    BlockSize: IsLess<u128>,
    <BlockSize as IsLess<u128>>::Output: NonZero;

pub trait ExtendableOutput: Sized {
    type Reader;

    fn finalize_xof(self) -> Self::Reader;
}

pub struct CoreWrapper<T>(PhantomData<(T, BlockBuffer<T::BlockSize, T::BufferKind>)>)
where
    T: BufferKindUser,
    T::BlockSize: IsLess<u128>,
    <<T as BlockSizeUser>::BlockSize as IsLess<u128>>::Output: NonZero;


impl<T> BlockSizeUser for CoreWrapper<T>
where
    T: BufferKindUser,
    T::BlockSize: IsLess<u128>,
    <<T as BlockSizeUser>::BlockSize as IsLess<u128>>::Output: NonZero,
{
    type BlockSize = T::BlockSize;
}
