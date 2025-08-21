To perform a release to crates.io, do the following:

1. update the version numbers found in the following files:

```
* lang/Cargo.toml
* macros/Cargo.toml
* Cargo.toml
* README.md
```

2. Create a release commit.

3. Run the following commands, looking for any errors:

```
$ cargo package -p ravenlang --list
...
# (check to see that the list doesn't 
# include anything unintended)
$ cargo package -p ravenlang
...
$ cargo publish -p ravenlang
...

# (repeat the cargo package+publish steps above
# for the 'ravencheck-macros' package)

# (finally, repeat the cargo package+publish steps 
# a third time for the 'ravencheck' package)
```
