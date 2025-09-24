The change from v0.2.0 to v0.3.0 includes some syntax changes to macro attributes. Here is what you should change in your code:

# Recursive definition

Old recursive definition looked like this:

```
#[define_rec]
fn add(..) -> {
    ..
}
```

Update to this:

```
#[define]
#[recursive]
fn add(..) -> {
    ..
}
```

# Annotations and AssumeFor

Old function-axiom looked like this:

```
#[assume_for(union)]
fn union_def() -> bool {
    |a: MySet, b: MySet|
    |c: MySet|
    forall(|e: u32| {
        member(e,c) == (member(e,a) || member(e,b))
}
```

Update to this:

```
#[assume(union(a, b) => c)]
fn union_def() -> bool {
    forall(|e: u32| {
        member(e,c) == (member(e,a) || member(e,b))
}
```

Old annotation looked like this:

```
#[annotate(union)]
fn union_def() -> bool {
    |a: MySet, b: MySet|
    |c: MySet|
    forall(|e: u32| {
        member(e,c) == (member(e,a) || member(e,b))
}
```

Update to this:

```
#[annotate(union(a, b) => c)]
fn union_def() -> bool {
    forall(|e: u32| {
        member(e,c) == (member(e,a) || member(e,b))
}
```

# Polymorphism

Old polymorphic assume looks like this:

```
#[assume((HashSet<E>, E))]
fn empty_no_member<E: Eq + Hash>() -> bool {
    forall(|e: E| !member_poly::<E>(e, empty_poly::<E>()))
}
```

Update to this:

```
#[assume]
#[for_type(HashSet<E> => <E>)]
fn empty_no_member<E: Eq + Hash>() -> bool {
    forall(|e: E| !member_poly::<E>(e, empty_poly::<E>()))
}
```

You can use multiple `for_type` lines.
