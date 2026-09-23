# Charon translation

Running `charon` is split into two phases: *translation* calls into rustc APIs and constructs
Charon's representation for the crate and its contents,
and [*transformations*](./charon-transformations.md) then transforms the pure-Charon AST 
into its final shape.

The main loop of translation is that we have a queue of items to translate, and we translate them
one by one, enqueuing any new items we discover references to. Importantly translating each item is
rather independent of another, and is done lazily; we must be careful when looking into
`self.translated_crate` during translation, as it will likely be incomplete.

The main logic of translation is that each [`hax`](./hax.md) item gives rise to one or more Charon items.
That's for two reasons:
1. Monomorphization, where a given item is generated anew for each set of generic arguments it is
   used with;
2. Making implicit items concrete, for example a closure gives rise to a struct definition, up to
   three `impl FnFoo for closure` along with their methods and vtables, and finally a `Destruct`
   impl and method that carry the drop glue for the type.

`TransItemSource` identifies a unique Charon item. The `RustcItem` part distinguishes poly from mono
items, and the `TransItemSourceKind` part distinguishes which Charon item we're generating from
a same hax item.

Beyond that, most of the translation logic is straightforward. The remaining complexity is in the
handling of [generics](./translating-generics.md).
