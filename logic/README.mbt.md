# Logic

The logical core of HOL: the trusted kernel, Boolean connectives, and
derived equality rules.

**Depends on:** `foundation` (for `Subst`), `types` (for `Type`,
`TypeSubst`), `terms` (for `Term`, `TermSubst`)

## Architecture

This package contains three layers:

| Namespace | File | Role |
|-----------|------|------|
| `Kernel` | `kernel.mbt` | LCF kernel: abstract `Thm` type + 10 primitive inference rules |
| `BoolSyntax` | `bool_syntax.mbt` | Connectives and quantifiers defined from equality |
| `Equal` | `equal.mbt` | Derived equality rules (`sym`, `trans`, `apTerm`, ...) |

## Kernel (LCF Architecture)

The kernel implements the **LCF (Logic for Computable Functions)**
architecture: the type `Thm` can only be constructed through the
inference rules below.  Because MoonBit enforces module boundaries, no
outside code can fabricate a `Thm` value -- every theorem is the result
of a valid chain of inferences.

```mbt nocheck
///|
struct Thm {
  hyps : Array[Term] // hypotheses (assumptions)
  concl : Term // conclusion
}
```

A theorem `{ hyps: [h1, ..., hn], concl: phi }` asserts:
*under hypotheses h1, ..., hn, the conclusion phi holds*.

### Primitive Inference Rules

```
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

Plus `defineTypeOp` (type definition principle) and `new_axiom`
(adds an axiom -- use sparingly!).

### Examples

```mbt check
///|
test "kernel: refl, assume, eqMp" {
  @types.Type::reset_table()
  @terms.Term::reset_table()
  let p = @terms.mk_var("p", @types.bool_ty())

  // |- p = p
  let th_eq = @logic.Kernel::refl(p)
  assert_eq(th_eq.hyps.length(), 0)

  // p |- p
  let th_p = @logic.Kernel::assume(p)
  assert_eq(th_p.hyps.length(), 1)

  // eqMp (|- p = p) (p |- p) => p |- p
  let th = @logic.Kernel::eqMp(th_eq, th_p)
  assert_true(th.concl == p)
}
```

```mbt check
///|
test "kernel: betaConv reduces a lambda application" {
  @types.Type::reset_table()
  @terms.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)
  let y = @terms.mk_var("y", a)

  // |- (\x. x) y = y
  let th = @logic.Kernel::betaConv(@terms.Term::mk_abs(x, x), y)
  let (_, rhs) = @terms.Term::dest_eq(th.concl)
  assert_true(rhs == y)
}
```

```mbt check
///|
test "kernel: defineConst registers a constant" {
  @types.Type::reset_table()
  @terms.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)
  let body = @terms.Term::mk_abs(x, x)

  // |- my_id = (\x. x)
  let th = @logic.Kernel::defineConst("my_id", body)
  assert_eq(th.hyps.length(), 0)
  let (lhs, rhs) = @terms.Term::dest_eq(th.concl)
  assert_true(lhs is Const(_, _))
  assert_true(rhs.aconv(body))
}
```

## BoolSyntax (Connectives and Quantifiers)

In the HOL Light approach, **all** connectives and quantifiers are
defined in terms of the single primitive `= : 'a -> 'a -> bool`:

| Connective | Definition |
|------------|-----------|
| `T` | `(\p. p) = (\p. p)` |
| `/\` | `\p q. (\f. f p q) = (\f. f T T)` |
| `==>` | `\p q. (p /\ q) = p` |
| `forall` | `\P. P = (\x. T)` |
| `exist` | `\P. forall q. (forall x. P x ==> q) ==> q` |
| `\/` | `\p q. forall r. (p ==> r) ==> (q ==> r) ==> r` |
| `F` | `forall p. p` |
| `~` | `\p. p ==> F` |

Each connective has a uniform triple of functions:

- **`mk_*`** -- builds the formula
- **`dest_*`** -- takes it apart
- **`is_*`** -- tests whether a term has that form

```mbt check
///|
test "BoolSyntax: implication and negation" {
  @types.Type::reset_table()
  @terms.Term::reset_table()
  let p = @terms.mk_var("p", @types.bool_ty())
  let q = @terms.mk_var("q", @types.bool_ty())

  // Build p ==> q
  let imp = @logic.BoolSyntax::mk_imp(p, q)
  assert_true(@logic.BoolSyntax::is_imp(imp))
  let (ant, conseq) = @logic.BoolSyntax::dest_imp(imp)
  assert_true(ant == p)
  assert_true(conseq == q)

  // Build ~p, then dest_neg returns the inner term
  let neg = @logic.BoolSyntax::mk_neg(p)
  assert_true(@logic.BoolSyntax::is_neg(neg))
  assert_true(@logic.BoolSyntax::dest_neg(neg) == p)
}
```

```mbt check
///|
test "BoolSyntax: quantifiers are applied to abstractions" {
  @types.Type::reset_table()
  @terms.Term::reset_table()
  let bool_ty = @types.bool_ty()
  let x = @terms.mk_var("x", bool_ty)
  let p = @terms.mk_var("p", bool_ty)

  // forall x. x ==> p  is  App(forall_inst, Abs(x, x ==> p))
  let body = @logic.BoolSyntax::mk_imp(x, p)
  let fa = @logic.BoolSyntax::mk_forall(x, body)
  assert_true(fa is App(_, _))
  assert_true(fa.type_of() == bool_ty)

  // exist x. x ==> p
  let ex = @logic.BoolSyntax::mk_exists(x, body)
  assert_true(ex is App(_, _))
}
```

## Equal (Derived Equality Rules)

Derived inference rules built entirely from kernel primitives.  Because
they compose only sound primitives, they are **sound by construction**
-- no additional trust is needed beyond the kernel.

| Rule | Given | Conclusion |
|------|-------|-----------|
| `sym` | `A \|- s = t` | `A \|- t = s` |
| `trans` | `A1 \|- s = t`, `A2 \|- t = u` | `A1 U A2 \|- s = u` |
| `apTerm` | `f`, `A \|- x = y` | `A \|- f x = f y` |
| `apThm` | `x`, `A \|- f = g` | `A \|- f x = g x` |
| `mkBinop` | `op`, `A1 \|- l1 = l2`, `A2 \|- r1 = r2` | `A1 U A2 \|- op l1 r1 = op l2 r2` |
| `alpha` | `t1`, `t2` (alpha-convertible) | `\|- t1 = t2` |

```mbt check
///|
test "Equal: sym and trans" {
  @types.Type::reset_table()
  @terms.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)
  let y = @terms.mk_var("y", a)
  let z = @terms.mk_var("z", a)

  // x = y |- x = y
  let th_xy = @logic.Kernel::assume(@terms.Term::mk_eq(x, y))

  // sym: x = y |- y = x
  let sym_th = @logic.Equal::sym(th_xy)
  let (lhs, rhs) = @terms.Term::dest_eq(sym_th.concl)
  assert_true(lhs == y)
  assert_true(rhs == x)

  // trans: {x = y, y = z} |- x = z
  let th_yz = @logic.Kernel::assume(@terms.Term::mk_eq(y, z))
  let trans_th = @logic.Equal::trans(th_xy, th_yz)
  let (tl, tr) = @terms.Term::dest_eq(trans_th.concl)
  assert_true(tl == x)
  assert_true(tr == z)
}
```

```mbt check
///|
test "Equal: alpha produces a theorem from alpha-convertible terms" {
  @types.Type::reset_table()
  @terms.Term::reset_table()
  let a = @types.mk_var("'a")
  let x = @terms.mk_var("x", a)
  let y = @terms.mk_var("y", a)

  // \x. x  and  \y. y  are alpha-equivalent
  let t1 = @terms.Term::mk_abs(x, x)
  let t2 = @terms.Term::mk_abs(y, y)

  // |- (\x. x) = (\y. y)
  let th = @logic.Equal::alpha(t1, t2)
  assert_eq(th.hyps.length(), 0)
  assert_true(@terms.Term::is_eq(th.concl))
}
```
