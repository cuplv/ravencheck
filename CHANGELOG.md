# 2025-09-29: v0.4.1

* Fix annotate_multi for relations, using recursion guards.
* Add the #[total] option for #[declare] and #[define].

# 2025-09-28: v0.4.0

* Added enum definitions and pattern-matching
* Added the #[annotate_multi] recursive verification command

# 2025-09-24: v0.3.0

* simplified annotation syntax: see doc/migration.md
* added the #[falsify] command
* added #[import] to import declarations and definitions from other
  modules
* allowed #[assert] items to have multiple type arguments
* add #[phantom] annotation for verification-only items

# 2025-09-08: v0.2.0

* declared zero-arg functions are treated as constants in encoding,
  and do not generate quantifier edges
* added const declarations to macro interface
* added polymorphic types and operations
* added inductive verification for recursive function definitions
