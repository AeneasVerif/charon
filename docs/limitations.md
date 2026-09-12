# Current limitations of Charon

Charon is beta software. It works well but it is currently poorly documented, doesn't support all the
Rust features we'd like, and has several breaking changes planned in the near future.

## Planned breaking changes

- https://github.com/AeneasVerif/charon/issues/287
- https://github.com/AeneasVerif/charon/issues?q=sort%3Aupdated-desc%20is%3Aissue%20state%3Aopen%20label%3AS-representation
- Name matcher behavior likely to change in subtle ways
  (https://github.com/AeneasVerif/charon/issues/319).

## Known unsoundnesses

- https://github.com/AeneasVerif/charon/issues/583

## Unsupported Rust features

Tracked here: https://github.com/AeneasVerif/charon/issues/142

## Missing information in the translated output

- Lifetime information about captured closure variables
  https://github.com/AeneasVerif/charon/issues/1040;
- Precise lifetimes for higher-ranked trait predicates
  https://github.com/AeneasVerif/charon/issues/1143;
- Lifetime information inside function bodies (not planned).

## By-design limitations

- Charon's output contains little syntactic information. Stuff like scopes, or distinguishing
  between `loop`, `while` and `for`, is not kept; only semantic information is kept. This can impede
  lints. We do keep good spans for error reporting however.
- It's not possible to do trait solving on the output of Charon. Charon simply does not have all the
  type system logic needed to do that, nor would I want to try and reimplement that.
