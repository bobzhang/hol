# A Comprehensive Introduction to HOL

This tutorial is a self-contained introduction to **Higher-Order Logic (HOL)**
as implemented in this MoonBit port of
[HOL Light](https://github.com/jrh13/hol-light).  Every code example is a
verified `mbt check` block -- compiled and tested by `moon test` -- so nothing
here is hand-waved.

---

## 1. What is HOL?

**Higher-Order Logic** is a formal logic powerful enough to express most of
mathematics.  "Higher-order" means that quantifiers range over functions and
predicates, not just individuals.  HOL sits at the sweet spot between
expressiveness and automation: it is strong enough to formalize real analysis,
probability theory, and hardware verification, yet simple enough that its
trusted kernel fits in a few hundred lines of code.

### The LCF Architecture

This implementation follows the **LCF (Logic for Computable Functions)**
architecture pioneered by Robin Milner in the 1970s:

1. There is an **abstract type `Thm`** (theorem).
2. Values of type `Thm` can **only** be created by a small set of
   **primitive inference rules** in the kernel.
3. Because MoonBit enforces module boundaries, no outside code can fabricate a
   `Thm` -- every theorem is the result of a valid chain of inferences.

This is the fundamental **soundness guarantee**: if the kernel is correct,
every `Thm` value represents a logically valid statement.  Derived rules,
tactics, and decision procedures can be arbitrarily complex without
compromising soundness, because they must ultimately bottom out in kernel
primitives.

### Lineage

This project ports **HOL Light**, John Harrison's minimalist HOL
implementation, to MoonBit.  HOL Light traces its lineage through HOL88
back to Mike Gordon's original HOL system.

### Project Structure

The implementation is organized into MoonBit packages, each building on
the previous:

| Package | Key files | Description |
|---------|-----------|-------------|
| `foundation/` | `lib.mbt`, `subst.mbt` | Mergesort with deduplication; substitution infrastructure |
| `types/` | `type.mbt`, `match.mbt`, `env.mbt` | HOL types (simply-typed lambda calculus) + type matching |
| `terms/` | `term.mbt`, `aconv.mbt`, `match.mbt`, `subst.mbt`, ... | HOL terms (locally nameless) + term matching |
| `logic/` | `kernel.mbt`, `bool_syntax.mbt`, `equal.mbt` | LCF kernel, connectives defined from equality, derived rules |

We will walk through each package from the bottom up.

---

## 2. Types: The Type Language

HOL is a **simply-typed** lambda calculus.  Every term has a type, and types
are built from two constructors:

```mbt nocheck
///|
enum Type {
  TyVar(String) // type variable: enables polymorphism
  TyApp(String, Array[Type]) // type constructor applied to arguments
}
```

- `TyVar("'a")` is a **type variable** -- polymorphic constants like equality
  are parameterized over type variables.
- `TyApp("bool", [])` is the **Boolean type** (propositions).
- `TyApp("fun", [A, B])` is the **function type** `A -> B`.
- `TyApp("list", [A])` would be `A list` (once `list` is registered).

### Type Registry

The set of valid type constructors and their arities is tracked in a mutable
registry (`type_table`).  Initially it contains just two primitives:

- `bool` (arity 0) -- the type of propositions
- `ind` (arity 0) -- the type of individuals (needed for the axiom of infinity)

The function type constructor `fun` is built-in (hardcoded arity 2) and does
not appear in the registry.  `mk_type` enforces that you use the correct
number of arguments:

```mbt check
///|
test "types: creating basic types" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  // Primitive types
  let bool_ty = @types.bool_ty() // TyApp("bool", [])
  let ind_ty = @types.ind_ty() // TyApp("ind", [])
  assert_eq(@hol.Type::pprint(bool_ty), "bool")
  assert_eq(@hol.Type::pprint(ind_ty), "ind")

  // Type variables
  let a = @types.mk_var("'a")
  let b = @types.mk_var("'b")
  assert_eq(@hol.Type::pprint(a), "'a")
  assert_true(a.is_var())
  assert_false(b.is_type())

  // Function types: 'a -> 'b
  let fun_ty = @types.mk_fun(a, b)
  assert_eq(@hol.Type::pprint(fun_ty), "'a --> 'b")
  assert_true(fun_ty.is_fun())
  let (dom, rng) = fun_ty.dest_fun()
  assert_eq(@hol.Type::pprint(dom), "'a")
  assert_eq(@hol.Type::pprint(rng), "'b")
}
```

### Registering New Type Constructors

You can extend the type universe with `new_type`.  For example, registering
a unary `list` constructor:

```mbt check
///|
test "types: registering list and building list types" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  @hol.Type::new_type("list", 1)

  let a = @types.mk_var("'a")
  let list_a = @hol.Type::mk_type("list", [a])
  assert_eq(@hol.Type::pprint(list_a), "'a list")

  // Nested: ('a -> bool) list
  let pred_list = @hol.Type::mk_type("list", [@types.mk_fun(a, @types.bool_ty())])
  assert_eq(@hol.Type::pprint(pred_list), "'a --> bool list")
}
```

### Type Substitution

Type substitution replaces type variables with concrete types.  This is how
polymorphic constants get specialized:

```mbt check
///|
test "types: substitution" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  @hol.Type::new_type("list", 1)

  let a = @types.mk_var("'a")
  let b = @types.mk_var("'b")
  let list_a = @hol.Type::mk_type("list", [a])

  // Substitute 'a := bool
  let sigma : @hol.TypeSubst = Subst(pairs=[(a, @types.bool_ty())])
  let result = list_a.subst(sigma)
  assert_eq(@hol.Type::pprint(result), "bool list")

  // Substitute in a function type: ('a -> 'b) becomes (bool -> ind)
  let fun_ab = @types.mk_fun(a, b)
  let sigma2 : @hol.TypeSubst = Subst(pairs=[
    (a, @types.bool_ty()),
    (b, @types.ind_ty()),
  ])
  let result2 = fun_ab.subst(sigma2)
  assert_eq(@hol.Type::pprint(result2), "bool --> ind")
}
```

### Type Matching

Type matching finds a substitution S such that `subst(S, pattern) == target`.
This is used internally by the kernel to check that polymorphic constants are
instantiated consistently:

```mbt check
///|
test "types: matching" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()

  let a = @types.mk_var("'a")
  let bool_ty = @types.bool_ty()

  let empty_state : @hol.TypeMatchState = { subst: Subst(), tyvars: [] }

  // Match 'a against bool => { 'a := bool }
  let s = a.match_type(bool_ty, empty_state).subst
  let bound = s.lookup(a)
  assert_true(bound == Some(bool_ty))

  // Match ('a -> 'a) against (bool -> bool) => { 'a := bool }
  let fun_aa = @types.mk_fun(a, a)
  let fun_bb = @types.mk_fun(bool_ty, bool_ty)
  let s2 = fun_aa.match_type(fun_bb, empty_state).subst
  assert_true(s2.lookup(a) == Some(bool_ty))
}
```

---

## 3. Terms: The Term Language

HOL terms form a simply-typed lambda calculus with constants.  This
implementation uses a **locally nameless** representation:

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

The key insight: **bound variables** use de Bruijn indices (`BVar(0)` = the
innermost binder, `BVar(1)` = the next one out, etc.), while **free
variables** use names (`FVar("x", ty)`).  This means alpha-equivalent terms
have *identical* representations:

```mbt nocheck
// \x. x  and  \y. y  both become  Abs(_, BVar(0))
```

No need for alpha-conversion during comparison -- structural equality
suffices.

### Building Terms

```mbt check
///|
test "terms: free variables and constants" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let bool_ty = @types.bool_ty()

  // Free variables carry a name and a type
  let p = @terms.mk_var("p", bool_ty)
  guard p is FVar(name, ty) else { fail("expected FVar") }
  assert_eq(name, "p")
  assert_true(ty == bool_ty)

  // The only primitive constant: polymorphic equality  = : 'a -> 'a -> bool
  let a = @types.mk_var("'a")
  let eq_ty = @types.mk_fun(a, @types.mk_fun(a, bool_ty))
  let eq_const = @hol.Term::mk_const("=", eq_ty)
  assert_true(eq_const is Const(_, _))
  guard eq_const is Const(cname, _) else { fail("expected constant") }
  assert_eq(cname, "=")
}
```

### Lambda Abstraction: mk_abs and dest_abs

`mk_abs(x, body)` replaces free occurrences of `x` in `body` with `BVar(0)`,
producing a locally nameless abstraction.  `dest_abs` reverses the process,
picking a fresh name to avoid capture:

```mbt check
///|
test "terms: abstraction roundtrip" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)

  // Build the identity function: \x. x
  let id_fn = @hol.Term::mk_abs(x, x)
  assert_true(id_fn is Abs(_, _))

  // Destruct it back
  let (bv, body) = id_fn.dest_abs()
  // The binder variable and body should pretty-print the same (identity)
  assert_eq(@hol.Term::pprint(body), @hol.Term::pprint(bv))

  // The type of \x. x  is  'a -> 'a
  let id_ty = id_fn.type_of()
  assert_eq(@hol.Type::pprint(id_ty), "'a --> 'a")
}
```

### Application and Type Inference

```mbt check
///|
test "terms: application and type_of" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)
  let y = @terms.mk_var("y", a)

  // Build the application (\x. x) y
  let id_fn = @hol.Term::mk_abs(x, x)
  let app = @terms.mk_app(id_fn, y)
  assert_true(app is App(_, _))

  // The type of (\x. x) y  should be 'a
  let app_ty = app.type_of()
  assert_true(app_ty == a)

  // Build an equation: x = y
  let eq = @hol.Term::mk_eq(x, y)
  assert_true(@hol.Term::is_eq(eq))
  let (lhs, rhs) = @hol.Term::dest_eq(eq)
  assert_true(lhs == x)
  assert_true(rhs == y)
}
```

### Alpha-Convertibility

Because bound variables are de Bruijn indices, alpha-equivalent terms are
structurally identical.  The `aconv` function checks this:

```mbt check
///|
test "terms: alpha-convertibility" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)
  let y = @terms.mk_var("y", a)

  // \x. x  and  \y. y  are alpha-convertible
  let abs_x = @hol.Term::mk_abs(x, x)
  let abs_y = @hol.Term::mk_abs(y, y)
  assert_true(abs_x.aconv(abs_y))

  // But x and y (as free variables) are NOT alpha-convertible
  assert_false(x.aconv(y))
}
```

### Pretty-Printing

```mbt check
///|
test "terms: pretty-printing" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let bool_ty = @types.bool_ty()
  let p = @terms.mk_var("p", bool_ty)
  let q = @terms.mk_var("q", bool_ty)

  // A simple equation: p = q
  let eq = @hol.Term::mk_eq(p, q)
  assert_eq(@hol.Term::pprint(eq), "= p q :: bool")

  // The identity on booleans: (\p. p)
  let id_bool = @hol.Term::mk_abs(p, p)
  assert_eq(@hol.Term::pprint(id_bool), "(\\p. p) :: bool --> bool")
}
```

---

## 4. Substitution and Matching

Substitution is central to HOL.  There are three kinds:

1. **Type substitution** (`Type::subst`) -- replaces type variables in types
2. **Type instantiation** (`Term::inst`) -- applies a type substitution to
   every type annotation in a term
3. **Term substitution** (`Term::subst`) -- replaces free term variables

### Type Instantiation on Terms

This is how polymorphic constants get specialized.  For example, the equality
constant `= : 'a -> 'a -> bool` can be instantiated to
`= : bool -> bool -> bool`:

```mbt check
///|
test "subst: type instantiation on terms" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let bool_ty = @types.bool_ty()

  // Build polymorphic equality: = : 'a -> 'a -> bool
  let eq_ty = @types.mk_fun(a, @types.mk_fun(a, bool_ty))
  let eq_poly = @hol.Term::mk_const("=", eq_ty)

  // Instantiate 'a := bool
  let sigma : @hol.TypeSubst = Subst(pairs=[(a, bool_ty)])
  let eq_bool = eq_poly.inst(sigma)

  // The resulting type should be bool -> bool -> bool
  let result_ty = eq_bool.type_of()
  let expected = @types.mk_fun(bool_ty, @types.mk_fun(bool_ty, bool_ty))
  assert_true(result_ty == expected)
}
```

### Term Substitution

Term substitution replaces free variables in a term:

```mbt check
///|
test "subst: term substitution" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let bool_ty = @types.bool_ty()
  let p = @terms.mk_var("p", bool_ty)
  let q = @terms.mk_var("q", bool_ty)

  // Build p = p, then substitute p := q to get q = q
  let eq_pp = @hol.Term::mk_eq(p, p)
  let sigma : @hol.TermSubst = Subst(pairs=[(p, q)])
  let eq_qq = eq_pp.subst(sigma)

  let (lhs, rhs) = @hol.Term::dest_eq(eq_qq)
  assert_true(lhs == q)
  assert_true(rhs == q)
}
```

### Term Matching

Pattern matching finds substitutions (both term-level and type-level) such
that applying them to a pattern yields the observation.  This is used by
tactics and rewriting:

```mbt check
///|
test "subst: term matching" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let bool_ty = @types.bool_ty()

  // Pattern: variable x of type 'a
  let x = @terms.mk_var("x", a)
  // Observation: variable p of type bool
  let p = @terms.mk_var("p", bool_ty)

  // match x against p => { x := p } and { 'a := bool }
  let (tm_s, ty_s) = x.match_term(p)
  assert_eq([..tm_s].length(), 1)
  assert_eq([..ty_s].length(), 1)
}
```

---

## 5. Boolean Syntax: Connectives from Equality

One of HOL Light's most elegant design decisions: **all** logical connectives
and quantifiers are defined in terms of the single primitive constant
`= : 'a -> 'a -> bool`.  The definitions are:

```mbt nocheck
T     := (\p. p) = (\p. p)
/\    := \p q. (\f. f p q) = (\f. f T T)
==>   := \p q. (p /\ q) = p
forall:= \P. P = (\x. T)
exist := \P. forall q. (forall x. P x ==> q) ==> q
\/    := \p q. forall r. (p ==> r) ==> (q ==> r) ==> r
F     := forall p. p
~     := \p. p ==> F
?!    := \P. exist P /\ forall x y. P x /\ P y ==> x = y
```

Each connective has a uniform API of three functions:
- **`mk_*`** (constructor) -- builds the formula
- **`dest_*`** (destructor) -- takes it apart
- **`is_*`** (predicate) -- tests whether a term has that form

### Implication and Negation

```mbt check
///|
test "bool_syntax: implication and negation" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let bool_ty = @types.bool_ty()
  let p = @terms.mk_var("p", bool_ty)
  let q = @terms.mk_var("q", bool_ty)

  // Build p ==> q
  let imp = @hol.BoolSyntax::mk_imp(p, q)
  assert_true(@hol.BoolSyntax::is_imp(imp))
  let (ant, conseq) = @hol.BoolSyntax::dest_imp(imp)
  assert_true(ant == p)
  assert_true(conseq == q)

  // Build ~p
  let neg = @hol.BoolSyntax::mk_neg(p)
  assert_true(@hol.BoolSyntax::is_neg(neg))
  // dest_neg returns the inner term (not the whole negation)
  let inner = @hol.BoolSyntax::dest_neg(neg)
  assert_true(inner == p)
}
```

### Quantifiers

Quantifiers are applied to abstractions.  `forall x. P x` is encoded as
`(forall) (\x. P x)` -- the universal constant applied to a lambda:

```mbt check
///|
test "bool_syntax: quantifiers" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let bool_ty = @types.bool_ty()
  let x = @terms.mk_var("x", bool_ty)
  let p = @terms.mk_var("p", bool_ty)

  // Build: forall x. x ==> p
  // Internally this is  App(forall_inst, Abs(x, x ==> p))
  let body = @hol.BoolSyntax::mk_imp(x, p)
  let fa = @hol.BoolSyntax::mk_forall(x, body)
  assert_true(fa is App(_, _))
  // The type of a quantified formula is bool
  assert_true(fa.type_of() == bool_ty)

  // Build: exist x. x ==> p
  let ex = @hol.BoolSyntax::mk_exists(x, body)
  assert_true(ex is App(_, _))
  assert_true(ex.type_of() == bool_ty)
}
```

### Conjunction and Disjunction

```mbt check
///|
test "bool_syntax: conjunction and disjunction" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let bool_ty = @types.bool_ty()
  let p = @terms.mk_var("p", bool_ty)
  let q = @terms.mk_var("q", bool_ty)

  // Build p /\ q
  let conj = @hol.BoolSyntax::mk_conj(p, q)
  assert_true(@hol.BoolSyntax::is_conj(conj))
  let (cl, cr) = @hol.BoolSyntax::dest_conj(conj)
  assert_true(cl == p)
  assert_true(cr == q)

  // Build p \/ q
  let disj = @hol.BoolSyntax::mk_disj(p, q)
  assert_true(@hol.BoolSyntax::is_disj(disj))
  let (dl, dr) = @hol.BoolSyntax::dest_disj(disj)
  assert_true(dl == p)
  assert_true(dr == q)
}
```

---

## 6. The Kernel: Primitive Inference Rules

The kernel is the trusted core of HOL.  It provides the abstract type `Thm`
and exactly 10 primitive inference rules.  A theorem `{ hyps, concl }` asserts
that under hypotheses `hyps`, the conclusion `concl` holds.

### The Rules at a Glance

```mbt nocheck
refl t                                      |- t = t
assume phi                             phi |- phi
eqMp   (A1 |- phi = psi) (A2 |- phi)  A1 U A2 |- psi
absThm v (A |- t = u)                  A |- (\v. t) = (\v. u)
appThm (A1 |- f = g) (A2 |- x = y)    A1 U A2 |- f x = g y
deductAntisym (A1 |- phi) (A2 |- psi)  (A1\{psi}) U (A2\{phi}) |- phi = psi
termSubst sigma (A |- phi)             A[sigma] |- phi[sigma]
typeSubst sigma (A |- phi)             A[sigma] |- phi[sigma]
betaConv (\v. t) u                          |- (\v. t) u = t[u/v]
defineConst c t                             |- c = t
```

Let's work through each one with live examples.

### refl: Reflexivity of Equality

`refl(t)` produces `|- t = t` with no hypotheses:

```mbt check
///|
test "kernel: refl" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)

  // |- x = x
  let th = @hol.Kernel::refl(x)
  assert_eq(th.hyps.length(), 0) // no hypotheses
  let (lhs, rhs) = @hol.Term::dest_eq(th.concl)
  assert_true(lhs == x)
  assert_true(rhs == x)
}
```

### assume: Assumption Introduction

`assume(phi)` produces `phi |- phi` -- the formula assumed as both hypothesis
and conclusion:

```mbt check
///|
test "kernel: assume" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let p = @terms.mk_var("p", @types.bool_ty())

  // p |- p
  let th = @hol.Kernel::assume(p)
  assert_eq(th.hyps.length(), 1)
  assert_true(th.hyps[0] == p)
  assert_true(th.concl == p)
}
```

### eqMp: Modus Ponens for Equality

Given `A1 |- phi = psi` and `A2 |- phi`, conclude `A1 U A2 |- psi`.  This
is the workhorse rule -- it lets you "rewrite" the truth of `phi` into the
truth of `psi` via an equation:

```mbt check
///|
test "kernel: eqMp" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let p = @terms.mk_var("p", @types.bool_ty())

  //  |- p = p  (from refl)  and  p |- p  (from assume)
  let th_eq = @hol.Kernel::refl(p) // |- p = p
  let th_p = @hol.Kernel::assume(p) // p |- p

  // p |- p  (by eqMp with trivial equation)
  let th = @hol.Kernel::eqMp(th_eq, th_p)
  assert_true(th.concl == p)
  assert_eq(th.hyps.length(), 1)
}
```

### appThm: Congruence for Application

Given `A1 |- f = g` and `A2 |- x = y`, conclude `A1 U A2 |- f x = g y`.
If equal functions are applied to equal arguments, the results are equal:

```mbt check
///|
test "kernel: appThm" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)
  let f = @terms.mk_var("f", @types.mk_fun(a, a))

  // |- f = f  and  |- x = x
  let th_f = @hol.Kernel::refl(f)
  let th_x = @hol.Kernel::refl(x)

  // |- f x = f x
  let th = @hol.Kernel::appThm(th_f, th_x)
  let (lhs, rhs) = @hol.Term::dest_eq(th.concl)
  assert_true(lhs.aconv(rhs))
}
```

### absThm: Congruence Under Abstraction

Given `A |- t = u` and a variable `v` not free in the hypotheses, conclude
`A |- (\v. t) = (\v. u)`:

```mbt check
///|
test "kernel: absThm" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)

  // |- x = x
  let th = @hol.Kernel::refl(x)

  // |- (\x. x) = (\x. x)
  let abs_th = @hol.Kernel::absThm(x, th)
  let (lhs, rhs) = @hol.Term::dest_eq(abs_th.concl)
  assert_true(lhs is Abs(_, _))
  assert_true(lhs.aconv(rhs))
}
```

### deductAntisym: The Deduction Theorem

Given `A1 |- phi` and `A2 |- psi`, conclude
`(A1 \ {psi}) U (A2 \ {phi}) |- phi = psi`.  This is how you prove two
formulas equal by assuming each and deriving the other:

```mbt check
///|
test "kernel: deductAntisym" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let p = @terms.mk_var("p", @types.bool_ty())
  let q = @terms.mk_var("q", @types.bool_ty())

  // p |- p  and  q |- q
  let th_p = @hol.Kernel::assume(p)
  let th_q = @hol.Kernel::assume(q)

  // {p}\{q} U {q}\{p} |- p = q  =>  {p, q} |- p = q
  let th = @hol.Kernel::deductAntisym(th_p, th_q)
  let (lhs, rhs) = @hol.Term::dest_eq(th.concl)
  assert_true(lhs == p)
  assert_true(rhs == q)
  // Both p and q remain as hypotheses (since p != q)
  assert_eq(th.hyps.length(), 2)
}
```

### betaConv: Beta Reduction

`betaConv((\v. t), u)` produces `|- (\v. t) u = t[u/v]`:

```mbt check
///|
test "kernel: betaConv" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)
  let y = @terms.mk_var("y", a)

  // (\x. x) applied to y  =>  |- (\x. x) y = y
  let id_fn = @hol.Term::mk_abs(x, x)
  let th = @hol.Kernel::betaConv(id_fn, y)
  let (_, rhs) = @hol.Term::dest_eq(th.concl)
  assert_true(rhs == y)

  // More interesting: (\x. x = x) applied to y  =>  |- (\x. x = x) y = (y = y)
  let eq_self = @hol.Term::mk_eq(x, x)
  let pred = @hol.Term::mk_abs(x, eq_self)
  let th2 = @hol.Kernel::betaConv(pred, y)
  let (_, rhs2) = @hol.Term::dest_eq(th2.concl)
  // rhs2 should be y = y
  let (eq_l, eq_r) = @hol.Term::dest_eq(rhs2)
  assert_true(eq_l == y)
  assert_true(eq_r == y)
}
```

### defineConst: Definitional Extension

`defineConst("c", t)` registers a new constant `c` with the type of `t` and
returns `|- c = t`.  This is how the logical vocabulary grows while
maintaining conservativity:

```mbt check
///|
test "kernel: defineConst" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)

  // Define id := \x. x
  let id_body = @hol.Term::mk_abs(x, x)
  let th = @hol.Kernel::defineConst("tutorial_id", id_body)

  // The theorem is  |- tutorial_id = (\x. x)
  assert_eq(th.hyps.length(), 0)
  let (lhs, rhs) = @hol.Term::dest_eq(th.concl)
  assert_true(lhs is Const(_, _))
  assert_true(rhs.aconv(id_body))
}
```

### termSubst and typeSubst: Substitution Rules

These rules apply substitutions to both hypotheses and conclusion:

```mbt check
///|
test "kernel: termSubst and typeSubst" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let bool_ty = @types.bool_ty()
  let x = @terms.mk_var("x", a)
  let y = @terms.mk_var("y", a)

  // |- x = x  (via refl)
  let th = @hol.Kernel::refl(x)

  // termSubst {x := y} gives |- y = y
  let s : @hol.TermSubst = Subst(pairs=[(x, y)])
  let th2 = @hol.Kernel::termSubst(s, th)
  let (lhs, rhs) = @hol.Term::dest_eq(th2.concl)
  assert_true(lhs == y)
  assert_true(rhs == y)

  // typeSubst {'a := bool} on |- x = x  gives  |- x:bool = x:bool
  let ts : @hol.TypeSubst = Subst(pairs=[(a, bool_ty)])
  let th3 = @hol.Kernel::typeSubst(ts, th)
  let result_ty = th3.concl.type_of()
  assert_true(result_ty == bool_ty)
}
```

---

## 7. Derived Rules: Building on the Kernel

`logic/equal.mbt` builds **derived** inference rules using only kernel
primitives.  Because they compose only sound primitives, they are sound by
construction -- no additional trust is needed.

### sym: Symmetry of Equality

Given `A |- s = t`, derive `A |- t = s`:

```mbt check
///|
test "derived: sym" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)
  let y = @terms.mk_var("y", a)

  // x = y |- x = y
  let eq_xy = @hol.Term::mk_eq(x, y)
  let th = @hol.Kernel::assume(eq_xy)

  // x = y |- y = x
  let sym_th = @hol.Equal::sym(th)
  let (lhs, rhs) = @hol.Term::dest_eq(sym_th.concl)
  assert_true(lhs == y)
  assert_true(rhs == x)
}
```

### How does sym work internally?

The derivation is surprisingly clever.  Here is the sketch:

```mbt nocheck
// Given: A |- s = t
//
// 1. refl(s)          gives  |- s = s
// 2. apTerm((= s), th) gives  A |- (= s s) = (= s t)
//    i.e.,  A |- (s = s) = (s = t)
// 3. eqMp with the |- s = s from step 1 yields  A |- t = s
//
// The actual code uses appThm and the partially-applied equality operator
// to achieve this in a compact way.
```

### trans: Transitivity of Equality

Given `A1 |- s = t` and `A2 |- t = u`, derive `A1 U A2 |- s = u`:

```mbt check
///|
test "derived: trans" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)
  let y = @terms.mk_var("y", a)
  let z = @terms.mk_var("z", a)

  // x = y |- x = y  and  y = z |- y = z
  let th1 = @hol.Kernel::assume(@hol.Term::mk_eq(x, y))
  let th2 = @hol.Kernel::assume(@hol.Term::mk_eq(y, z))

  // {x = y, y = z} |- x = z
  let th = @hol.Equal::trans(th1, th2)
  let (lhs, rhs) = @hol.Term::dest_eq(th.concl)
  assert_true(lhs == x)
  assert_true(rhs == z)
}
```

### apTerm and apThm: Congruence Helpers

- `apTerm(f, A |- x = y)` derives `A |- f x = f y` (apply the same function
  to both sides)
- `apThm(x, A |- f = g)` derives `A |- f x = g x` (apply equal functions to
  the same argument)

```mbt check
///|
test "derived: apTerm and apThm" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)
  let y = @terms.mk_var("y", a)
  let f = @terms.mk_var("f", @types.mk_fun(a, a))
  let g = @terms.mk_var("g", @types.mk_fun(a, a))

  // x = y |- x = y
  let th_xy = @hol.Kernel::assume(@hol.Term::mk_eq(x, y))

  // apTerm f (x = y |- x = y)  =>  x = y |- f x = f y
  let th1 = @hol.Equal::apTerm(f, th_xy)
  let (lhs1, rhs1) = @hol.Term::dest_eq(th1.concl)
  assert_true(lhs1 is App(_, _))
  assert_true(rhs1 is App(_, _))

  // f = g |- f = g
  let th_fg = @hol.Kernel::assume(@hol.Term::mk_eq(f, g))

  // apThm x (f = g |- f = g)  =>  f = g |- f x = g x
  let th2 = @hol.Equal::apThm(x, th_fg)
  let (lhs2, rhs2) = @hol.Term::dest_eq(th2.concl)
  assert_true(lhs2 is App(_, _))
  assert_true(rhs2 is App(_, _))
}
```

### mkBinop: Binary Operator Congruence

`mkBinop(op, lth, rth)` combines two equalities under a binary operator:
given `A1 |- l1 = l2` and `A2 |- r1 = r2`, derive
`A1 U A2 |- op l1 r1 = op l2 r2`:

```mbt check
///|
test "derived: mkBinop" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let bool_ty = @types.bool_ty()
  let p1 = @terms.mk_var("p1", bool_ty)
  let p2 = @terms.mk_var("p2", bool_ty)
  let q1 = @terms.mk_var("q1", bool_ty)
  let q2 = @terms.mk_var("q2", bool_ty)

  // p1 = p2 |- p1 = p2  and  q1 = q2 |- q1 = q2
  let lth = @hol.Kernel::assume(@hol.Term::mk_eq(p1, p2))
  let rth = @hol.Kernel::assume(@hol.Term::mk_eq(q1, q2))

  // Use the implication connective as the binary operator
  let op = @hol.BoolSyntax::implication()
  let th = @hol.Equal::mkBinop(op, lth, rth)

  // Result: |- (==> p1 q1) = (==> p2 q2)
  let (lhs, rhs) = @hol.Term::dest_eq(th.concl)
  assert_true(@hol.BoolSyntax::is_imp(lhs))
  assert_true(@hol.BoolSyntax::is_imp(rhs))
}
```

### alpha: Alpha-Equivalence as a Theorem

`alpha(t1, t2)` produces `|- t1 = t2` when `t1` and `t2` are
alpha-convertible:

```mbt check
///|
test "derived: alpha" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)
  let y = @terms.mk_var("y", a)

  // \x. x  and  \y. y  are alpha-equivalent
  let t1 = @hol.Term::mk_abs(x, x)
  let t2 = @hol.Term::mk_abs(y, y)

  // |- (\x. x) = (\y. y)
  let th = @hol.Equal::alpha(t1, t2)
  assert_eq(th.hyps.length(), 0)
  assert_true(@hol.Term::is_eq(th.concl))
}
```

---

## 8. Putting It All Together

Let's work a complete example that exercises multiple packages.  We will:

1. Build some types and terms
2. Define a constant
3. Prove a small theorem using kernel rules
4. Apply derived rules to transform it

```mbt check
///|
test "worked example: combining packages" {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  let bool_ty = @types.bool_ty()
  let a = @types.mk_var("'a")

  // --- Types ---
  // We work with bool and 'a -> bool (predicates)
  let pred_ty = @types.mk_fun(a, bool_ty)
  assert_eq(@hol.Type::pprint(pred_ty), "'a --> bool")

  // --- Terms ---
  // Build the identity on booleans: \p. p
  let p = @terms.mk_var("p", bool_ty)
  let id_bool = @hol.Term::mk_abs(p, p)

  // --- Boolean syntax ---
  // Build: p ==> p
  let imp_pp = @hol.BoolSyntax::mk_imp(p, p)
  assert_true(@hol.BoolSyntax::is_imp(imp_pp))

  // --- Kernel ---
  // Prove |- id_bool = id_bool  (reflexivity)
  let refl_id = @hol.Kernel::refl(id_bool)
  assert_eq(refl_id.hyps.length(), 0)

  // Prove p |- p  (assumption)
  let assume_p = @hol.Kernel::assume(p)
  assert_eq(assume_p.hyps.length(), 1)

  // Prove |- (\p. p) p = p  (beta reduction)
  let beta_th = @hol.Kernel::betaConv(id_bool, p)
  let (_, beta_rhs) = @hol.Term::dest_eq(beta_th.concl)
  assert_true(beta_rhs == p)

  // --- Derived rules ---
  // Symmetry: |- p = (\p. p) p
  let sym_beta = @hol.Equal::sym(beta_th)
  let (sym_l, sym_r) = @hol.Term::dest_eq(sym_beta.concl)
  assert_true(sym_l == p)
  assert_true(sym_r is App(_, _))
}
```

### Summary

This tutorial has covered the complete HOL construction from first principles:

| Package | What it provides | Key insight |
|---------|-----------------|-------------|
| **Types** | `TyVar`, `TyApp`, `mk_fun`, `bool_ty` | Simply-typed lambda calculus with a registry |
| **Terms** | `FVar`, `BVar`, `Const`, `App`, `Abs` | Locally nameless: alpha-equivalence for free |
| **Substitution** | Type subst, term subst, matching | How polymorphism and rewriting work |
| **Bool syntax** | All connectives from `=` alone | Definitional minimalism |
| **Kernel** | 10 primitive rules, abstract `Thm` | LCF architecture = soundness guarantee |
| **Derived rules** | `sym`, `trans`, `apTerm`, etc. | Sound by construction |

The LCF architecture means you can trust the system as long as you trust the
kernel (~250 lines).  Everything else -- derived rules, tactics, decision
procedures -- is just convenience built on that foundation.

## Further Reading

- John Harrison's [HOL Light](https://github.com/jrh13/hol-light) -- the
  original system this project is based on
- John Harrison's [HOL Light Tutorial](https://www.cl.cam.ac.uk/~jrh13/hol-light/tutorial.pdf)
  for a comprehensive guide to the OCaml implementation
- Robin Milner's *Logic for Computable Functions* for the LCF architecture
