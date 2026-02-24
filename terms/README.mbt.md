# Terms

The HOL term language.  Terms form a simply-typed lambda calculus
*with constants*, represented using the **locally nameless** convention.

**Depends on:** `foundation` (for `Subst`),
`types` (for `Type`, `TypeSubst`)

## The Term Enum

```mbt nocheck
///|
enum Term {
  FVar(String, Type) // free (named) variable with its type
  BVar(Int) // bound variable (de Bruijn index)
  Const(String, Type) // declared constant (e.g., "=")
  App(Term, Term) // function application
  Abs(Term, Term) // lambda abstraction
}
```

### Why Locally Nameless?

Bound variables use **de Bruijn indices** (`BVar(0)` = innermost binder),
while free variables use **names** (`FVar("x", ty)`).  This means
alpha-equivalent terms have *identical* representations:

```mbt nocheck
// \x. x  and  \y. y  both become  Abs(_, BVar(0))
```

No alpha-conversion is needed during comparison -- structural equality
suffices.

## Constant Table

The global signature of constants is stored in a mutable table.  The
only primitive constant is **polymorphic equality**:

```mbt nocheck
= : 'a -> 'a -> bool
```

All other connectives (`==>`, `/\`, `forall`, etc.) are *defined* on
top of equality (see the `logic` package).  New constants are registered
via `@terms.Term::new_const` (which also returns the new constant term)
or `Kernel::defineConst`.

## Building Terms

```mbt check
///|
test "terms: free variables and constants" {
  @types.Type::reset_table()
  @terms.Term::reset_table()
  let bool_ty = @types.bool_ty()

  // Free variables carry a name and a type
  let p = @terms.mk_var("p", bool_ty)
  guard p is FVar(name, _) else { fail("expected FVar") }
  assert_eq(name, "p")

  // The primitive constant: = : 'a -> 'a -> bool
  let a = @types.mk_var("'a")
  let eq_ty = @types.mk_fun(a, @types.mk_fun(a, bool_ty))
  let eq_const = @terms.Term::mk_const("=", eq_ty)
  assert_true(eq_const is Const(_, _))
}
```

## Lambda Abstraction

`mk_abs(x, body)` replaces free occurrences of `x` in `body` with
`BVar(0)`, producing a locally nameless abstraction.  `dest_abs`
reverses the process, picking a fresh name to avoid capture:

```mbt check
///|
test "terms: abstraction roundtrip and type inference" {
  @types.Type::reset_table()
  @terms.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)

  // Build the identity: \x. x
  let id_fn = @terms.Term::mk_abs(x, x)
  assert_true(id_fn is Abs(_, _))
  assert_eq(@types.Type::pprint(id_fn.type_of()), "'a --> 'a")

  // Destruct it back
  let (bv, body) = id_fn.dest_abs()
  assert_eq(@terms.Term::pprint(body), @terms.Term::pprint(bv))
}
```

## Equations

`mk_eq(l, r)` builds the equation `l = r`, checking that both sides
have the same type.  Internally it instantiates the polymorphic `=`
constant:

```mbt check
///|
test "terms: equations" {
  @types.Type::reset_table()
  @terms.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)
  let y = @terms.mk_var("y", a)

  let eq = @terms.Term::mk_eq(x, y)
  assert_true(@terms.Term::is_eq(eq))
  let (lhs, rhs) = @terms.Term::dest_eq(eq)
  assert_true(lhs == x)
  assert_true(rhs == y)
}
```

## Alpha-Convertibility

Because bound variables are de Bruijn indices, alpha-equivalent terms
are structurally identical.  `aconv` checks this:

```mbt check
///|
test "terms: alpha-convertibility" {
  @types.Type::reset_table()
  @terms.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)
  let y = @terms.mk_var("y", a)

  // \x. x  and  \y. y  are alpha-convertible
  assert_true(@terms.Term::mk_abs(x, x).aconv(@terms.Term::mk_abs(y, y)))
  // But x and y (as free variables) are NOT
  assert_false(x.aconv(y))
}
```

## Substitution

There are three kinds of substitution:

| Operation | What it does |
|-----------|-------------|
| `tm.inst(sigma)` | Apply a *type* substitution to every type annotation in `tm` |
| `tm.subst(sigma)` | Replace free *term* variables according to `sigma` |
| `ty.subst(sigma)` | Replace type variables in a type (see `types` package) |

Type instantiation is how polymorphic constants get specialized:

```mbt check
///|
test "terms: type instantiation" {
  @types.Type::reset_table()
  @terms.Term::reset_table()
  let a = @types.mk_var("'a")
  let bool_ty = @types.bool_ty()
  let eq_ty = @types.mk_fun(a, @types.mk_fun(a, bool_ty))
  let eq = @terms.Term::mk_const("=", eq_ty)

  // Instantiate 'a := bool
  let sigma : @types.TypeSubst = Subst(pairs=[(a, bool_ty)])
  let eq_bool = eq.inst(sigma)
  let expected = @types.mk_fun(
    bool_ty,
    @types.mk_fun(bool_ty, bool_ty),
  )
  assert_true(eq_bool.type_of() == expected)
}
```

## Term Matching

`pattern.match_term(observation)` finds both a term substitution
and a type substitution such that applying them to `pattern` yields
`observation`.  Used by tactics and rewriting:

```mbt check
///|
test "terms: pattern matching" {
  @types.Type::reset_table()
  @terms.Term::reset_table()
  let a = @types.mk_var("'a")
  let bool_ty = @types.bool_ty()
  let x = @terms.mk_var("x", a)
  let p = @terms.mk_var("p", bool_ty)

  // Match x:'a against p:bool => { x := p } and { 'a := bool }
  let (tm_s, ty_s) = x.match_term(p)
  assert_eq([..tm_s].length(), 1)
  assert_eq([..ty_s].length(), 1)
}
```

## Type Aliases

| Alias | Expands to |
|-------|-----------|
| `TermSubst` | `Subst[Term, Term]` |
| `TermMatchResult` | `(TermSubst, TypeSubst)` |
