# Types

The HOL type language.  Types form the simply-typed layer that classifies
every term in the system.

**Depends on:** `foundation` (for `Subst`)

## The Type Enum

```mbt nocheck
///|
enum Type {
  TyVar(String) // type variable: enables polymorphism
  TyApp(String, Array[Type]) // type constructor applied to arguments
}
```

- `TyVar("'a")` is a **type variable** -- polymorphic constants like
  equality are parameterized over these.
- `TyApp("bool", [])` is the **Boolean type** (propositions).
- `TyApp("fun", [A, B])` is the **function type** `A -> B`.
- `TyApp("list", [A])` would be `A list` (once registered with `new_type`).

## Type Registry

The set of valid type constructors and their arities lives in a mutable
registry (`type_table`).  Initially it contains two primitives:

| Constructor | Arity | Meaning |
|-------------|-------|---------|
| `bool` | 0 | propositions |
| `ind` | 0 | individuals (needed for the axiom of infinity) |

The function type constructor `fun` is built-in (hardcoded arity 2) and
does not appear in the registry.

`mk_type` enforces arities: you cannot write `TyApp("bool", [x])` because
`bool` was registered with arity 0.

```mbt check
///|
test "types: basic construction and pretty-printing" {
  @types.Type::reset_table()
  let bool_ty = @types.bool_ty()
  let a = @types.mk_var("'a")
  let b = @types.mk_var("'b")
  assert_eq(@types.Type::pprint(bool_ty), "bool")
  assert_eq(@types.Type::pprint(a), "'a")
  assert_true(a.is_var())
  assert_false(bool_ty.is_var())

  // Function types: 'a -> 'b
  let fun_ty = @types.mk_fun(a, b)
  assert_eq(@types.Type::pprint(fun_ty), "'a --> 'b")
  assert_true(fun_ty.is_fun())
  let (dom, rng) = fun_ty.dest_fun()
  assert_true(dom == a)
  assert_true(rng == b)
}
```

### Registering New Type Constructors

`new_type(name, arity)` extends the registry.  `checkpoint_defs` /
`reset_table` support snapshot/rollback for tests:

```mbt check
///|
test "types: registering a new type constructor" {
  @types.Type::reset_table()
  @types.Type::new_type("list", 1)
  let a = @types.mk_var("'a")
  let list_a = @types.Type::mk_type("list", [a])
  assert_eq(@types.Type::pprint(list_a), "'a list")
}
```

## Type Substitution

`ty.subst(sigma)` replaces type variables according to the
substitution `sigma`.  This is how polymorphic constants get specialized
(e.g., `= : 'a -> 'a -> bool` becomes `= : nat -> nat -> bool`).

```mbt check
///|
test "types: substitution replaces type variables" {
  @types.Type::reset_table()
  @types.Type::new_type("list", 1)
  let a = @types.mk_var("'a")
  let b = @types.mk_var("'b")
  let list_a = @types.Type::mk_type("list", [a])

  // Substitute 'a := bool
  let sigma : @types.TypeSubst = Subst(pairs=[(a, @types.bool_ty())])
  assert_eq(@types.Type::pprint(list_a.subst(sigma)), "bool list")

  // Substitute in a function type
  let sigma2 : @types.TypeSubst = Subst(pairs=[(a, @types.bool_ty()), (b, @types.ind_ty())])
  assert_eq(@types.Type::pprint(@types.mk_fun(a, b).subst(sigma2)), "bool --> ind")
}
```

## Type Matching

`Type::match_type(pattern, observation, state)` finds a substitution S
such that `subst(S, pattern) == observation`.  The state carries
`(S, ids)` where `ids` is the set of type variables bound to themselves
(identity bindings).

The algorithm walks the pattern and observation in lockstep:
- `TyVar` vs anything: bind or check consistency
- `TyApp(c, args)` vs `TyApp(c, args)`: recurse into children
- Mismatch: abort

```mbt check
///|
test "types: matching finds a substitution" {
  @types.Type::reset_table()
  let a = @types.mk_var("'a")
  let bool_ty = @types.bool_ty()

  let empty_state : @types.TypeMatchState = { subst: Subst(), tyvars: [] }

  // Match 'a against bool  =>  { 'a := bool }
  let s = a.match_type(bool_ty, empty_state).subst
  assert_true(s.lookup(a) == Some(bool_ty))

  // Match ('a -> 'a) against (bool -> bool)  =>  { 'a := bool }
  let s2 = @types.mk_fun(a, a).match_type(
      @types.mk_fun(bool_ty, bool_ty),
      empty_state,
    ).subst
  assert_true(s2.lookup(a) == Some(bool_ty))

  // Match ('a -> 'b) -> 'c against (bool -> bool) -> ind
  // Tests that the observation tail (rest_obs) is tracked independently of
  // the pattern tail (rest_pats) when recursing into nested App children.
  let b = @types.mk_var("'b")
  let c = @types.mk_var("'c")
  let ind_ty = @types.ind_ty()
  let pat = @types.mk_fun(@types.mk_fun(a, b), c)
  let ob = @types.mk_fun(@types.mk_fun(bool_ty, bool_ty), ind_ty)
  let s3 = pat.match_type(ob, empty_state).subst
  assert_true(s3.lookup(a) == Some(bool_ty))
  assert_true(s3.lookup(b) == Some(bool_ty))
  assert_true(s3.lookup(c) == Some(ind_ty))
}
```

## Collecting Type Variables

`Type::vars_in(ty)` returns all type variables occurring in `ty`,
sorted and deduplicated.  Used by `defineTypeOp` to determine how many
type parameters a new type operator needs.

```mbt check
///|
test "types: vars_in collects type variables" {
  @types.Type::reset_table()
  let a = @types.mk_var("'a")
  let b = @types.mk_var("'b")
  let fun_ty = @types.mk_fun(a, @types.mk_fun(b, a))
  let vars = @types.Type::vars_in(fun_ty)
  // Should contain exactly 'a and 'b (sorted, deduplicated)
  assert_eq(vars.length(), 2)
}
```

## Type Aliases

| Alias | Expands to |
|-------|-----------|
| `TypeSubst` | `Subst[Type, Type]` |
| `TypeMatchState` | `{ subst: TypeSubst, tyvars: Array[Type] }` |
