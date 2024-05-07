pub mod generator;
pub mod map;
pub mod vector;

pub use generator::{Generator, MapGenerator};
pub use map::Map;
pub use vector::Vector;

/// Generate an `Index` module which contains an index type and a generator
/// for fresh indices. We use it because we need manipulate
/// a lot of different indices (for various kinds of declarations, variables, blocks,
/// etc.).
/// For sanity purposes, we prevent any confusion between the different kinds
/// of indices by using different types. The following macro allows us to
/// easily derive those types, and the needed utilities (casts, vectors indexed
/// by those opaque indices, etc.).
///
/// The `name` parameter should contain the name of the module to declare. The `pretty_name`
/// parameter is used to implement `Id::to_pretty_string`; if not provided, it defaults to `name`.
#[macro_export]
macro_rules! generate_index_type {
    ($name:ident) => {
        $crate::generate_index_type!($name, stringify!($name));
    };
    ($name:ident, $pretty_name:expr) => {
        #[allow(non_snake_case)]
        pub mod $name {
            index_vec::define_index_type! {
                pub struct Id = usize;
                // Must fit in an u32 for serialization.
                MAX_INDEX = std::u32::MAX as usize;
            }

            impl Id {
                pub fn is_zero(&self) -> bool {
                    self.index() == 0
                }
                pub fn to_pretty_string(self) -> String {
                    format!("@{}{}", $pretty_name, self)
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
