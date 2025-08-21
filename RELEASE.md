To perform a release to crates.io, do the following:

1. update the version numbers found in the following files:

```
* lang/Cargo.toml
* macros/Cargo.toml
* Cargo.toml
* Makefile
```

2. Create a release commit.

3. Run the following commands, looking for any errors:

```
$ make prep-release
...
$ cd lang
$ cargo package --list
...
# (check to see that the list doesn't 
# include anything unintended)
$ cargo package
...
$ cargo publish
...
$ cd -

$ cd macros
# (repeat the cargo package+publish steps above
# for the macros package)
$ cd -

# (finally, repeat the cargo package+publish steps 
# a third time for the top-level ravencheck package)
```

4. Use git to clean up the files and changes created by step #3.
