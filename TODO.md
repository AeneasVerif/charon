* handle constants (rustc_hir::ItemKind::Const)
* handle external, public enumerations (extract their definitions, because
  we need their variants)
* handle arrays, slices
* im_ast::FunSig: change the type of `inputs`
* Update the reordering of definitions which was not thought for crates with
  several modules and external dependencies. We might want to group the
  definitions into modules (or not, because of potentially mutually recursive
  definitions).
* better support for external dependencies
* use `pub(crate)` more (instead of `pub`)
