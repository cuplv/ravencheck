# `ravencheck`

`ravencheck` is a tool for symbolic verification of Rust code, using guaranteed-decidable SMT queries for predictable results.

## Usage

To use `ravencheck`, clone this repository and then add it as a
dependency to your own package's Cargo.toml file:

```
# Cargo.toml
...
[dependencies]
ravencheck = { path = "path/to/cloned/repo" }
...
```

You will then use the `#[ravencheck::check_module]` macro on modules
in which you want to use verification. See
[examples/sets.rs](./examples/sets.rs) for an example.

## About

"Raven" is an acronym for *relationally-abstracted verification
encoding*, the technique that is used to reduce verification
conditions to a decidable fragment of first-order logic (specifically,
the Extended EPR fragment).
