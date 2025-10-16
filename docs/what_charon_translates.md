# What Charon Translates

Charon has a flexible system to determine which items get translated. This documents attempts to
describe how the system works.

- An "item" means a module, function, type decl, static, const, trait decl or trait impl. A crate is
  considered a module;
- Each item has an opacity, calculated from its name (TODO: document names); this can be tuned with
  `--include`, `--opaque`, `--exclude` and the `#[charon::opaque]` attribute. The default is
  `--opaque * --include crate`, which makes items in the current crate transparent and items in
  foreign crates opaque. The `--extract-opaque-bodies` flag is an alias for `--include *`.
- Charon first processes the items specified with `--start-from`. If `--start-from` is not used,
  that's equivalent to `--start-from=crate`, where `crate` stands for the current crate;
- To process a transparent module, we enqueue the items directly inside it for translation;
- To process any other module, we do nothing;
- To process a transparent non-module item, we translate it in its entirety.
- To process a opaque non-module item, we translate the item without its "body". For
  functions/consts/statics that's the literal function body, for types that's the contents of the
  type definition, for traits that's the optional methods.
- To process an invisible item (those selected with `--exclude`), we do nothing;
- Whenever in the process above we encounter a reference to a new item, we enqueue that item for
  processing.

This results in a dependency resolution algorithm that pulls the needed items. The default settings
translate the whole current crate as well as the signatures of all the foreign items mentioned in
the crate.
