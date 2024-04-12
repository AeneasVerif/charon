pub mod generator;
pub mod map;
pub mod vector;

/// Generate an `Index` module which contains an index type and a generator
/// for fresh indices. We use it because we need manipulate
/// a lot of different indices (for various kinds of declarations, variables, blocks,
/// etc.).
/// For sanity purposes, we prevent any confusion between the different kinds
/// of indices by using different types. The following macro allows us to
/// easily derive those types, and the needed utilities (casts, vectors indexed
/// by those opaque indices, etc.).
///
/// The `ident` parameter should contain the name of the module to declare.
#[macro_export]
macro_rules! generate_index_type {
    ($name:ident) => {
        #[allow(non_snake_case)]
        pub mod $name {
            index_vec::define_index_type! {
                pub struct Id = usize;
                // Must fit in an u32 for serialization.
                MAX_INDEX = std::u32::MAX as usize;
            }

            pub type Vector<T> = crate::ids::vector::Vector<Id, T>;
            pub type Map<T> = crate::ids::map::Map<Id, T>;
            pub type Generator = crate::ids::generator::Generator<Id>;
            pub type MapGenerator<K> = crate::ids::generator::MapGenerator<K, Id>;

            impl Id {
                pub fn is_zero(&self) -> bool {
                    self.index() == 0
                }
            }

            pub static ZERO: Id = Id { _raw: 0 };

            impl std::fmt::Display for Id {
                fn fmt(
                    &self,
                    f: &mut std::fmt::Formatter<'_>,
                ) -> std::result::Result<(), std::fmt::Error> {
                    f.write_str(self.index().to_string().as_str())
                }
            }
        }
    };
}
