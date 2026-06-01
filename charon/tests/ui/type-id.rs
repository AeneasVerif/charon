//@ charon-args=--extract-opaque-bodies

use std::any::TypeId;

fn type_id_u32() -> TypeId {
    TypeId::of::<u32>()
}

fn type_id_generic<T: 'static>() -> TypeId {
    TypeId::of::<T>()
}
