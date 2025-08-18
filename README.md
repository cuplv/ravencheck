# `ravencheck`

`ravencheck` is a tool for symbolic verification of Rust code, using guaranteed-decidable SMT queries for predictable results.

## Usage

First, make sure you have the [CVC5](https://cvc5.github.io/) SMT
solver available. You should be able to run `cvc5 --version` in your
dev environment.

Then, you can add `ravencheck` as a dependency in your Cargo.toml
file, in three different ways:

### Depend on crates.io package (v0.1.0)

Add the following to your Cargo.toml:

```
[dependencies]
ravencheck = "0.1.0"
```

This gives you the latest published version (v0.1.0).

### Depend on the GitHub repo's latest commit

Add the following to your Cargo.toml:

```
[dependencies]
ravencheck = { git = "https://github.com/cuplv/ravencheck" }
```

This gives you the latest commit to `main`.

### Depend on local copy of the repo

Alternatively, you can clone the repo and use its path on your
filesystem as the dependency:

```
# Cargo.toml
...
[dependencies]
ravencheck = { path = "path/to/cloned/repo" }
...
```

This allows you to choose which commit in the repo to use.

### Verifying a module

You use `ravencheck` by adding the `#[ravencheck::check_module]` macro
attribute at the top of modules in which you want to use
verification. See [examples/sets.rs](./examples/sets.rs) for an
example.

## About

"Raven" is an acronym for *relationally-abstracted verification
encoding*, the technique that is used to reduce verification
conditions to a decidable fragment of first-order logic (specifically,
the Extended EPR fragment).
