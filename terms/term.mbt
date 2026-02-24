// Step 3: Terms
//
// HOL terms form a simply-typed lambda calculus *with constants*.  This file
// uses a **locally nameless** representation (see Jesper Cocx's
// "1001 Representations of Syntax with Binding"):
//
//   Term ::= FVar(name, ty)   -- free (named) variable
//          | BVar(index)      -- bound variable (de Bruijn index)
//          | Const(name, ty)  -- declared constant (e.g., "=")
//          | App(f, x)        -- application
//          | Abs(binder, body)-- lambda abstraction
//
// The key advantage: bound variables are nameless indices, so alpha-equivalent
// terms have identical representations (modulo the binder annotation kept for
// pretty-printing).  `mk_abs(x, body)` converts free occurrences of `x` into
// BVar(0); `dest_abs` reverses the process with a fresh name.

///|
/// HOL term in locally nameless representation: free variables are named, bound variables use de Bruijn indices, and constants carry their (possibly polymorphic) type.
pub enum Term {
  // Named free variable with its type
  FVar(String, @types.Type)
  // De Bruijn index for a bound variable (0 = innermost binder)
  BVar(Int)
  // Declared constant (e.g., "=" with polymorphic type)
  Const(String, @types.Type)
  // Function application
  App(Term, Term)
  // Lambda abstraction; the first field is a binder annotation (FVar) kept
  // for name/type information, while the body uses BVar for references
  Abs(Term, Term)
} derive(Eq, Compare, Show, Debug)

///|
/// A substitution mapping terms to terms, used to replace free variables in a term.
pub type TermSubst = @foundation.Subst[Term, Term]

///|
/// Register a new constant with the given name and type in the global signature,
/// aborting if the name is already in use. Returns the constructed constant term.
pub fn Term::new_const(name : String, ty : @types.Type) -> Term {
  if const_table.val.contains(name) {
    abort("new_const: already used \{name}")
  }
  const_table.val = const_table.val.add(name, ty)
  Const(name, ty)
}

///|
/// Construct a free (named) variable with the given name and type.
pub fn mk_var(name : String, ty : @types.Type) -> Term {
  FVar(name, ty)
}

///|
/// Construct a constant term without checking the global signature.
/// Intended for the logic layer, which builds connective and type-operator heads
/// before they are formally registered.  Prefer `mk_const` for user-facing code.
pub fn const_(name : String, ty : @types.Type) -> Term {
  Const(name, ty)
}

///|
/// Construct a constant term, checking that the name is registered in the global signature and that the requested type is a valid instance of the declared polymorphic type.
pub fn Term::mk_const(name : String, ty : @types.Type) -> Term raise {
  match const_table.val.get(name) {
    None => abort("mk_const: unregistered constant \{name}")
    Some(declared_ty) => {
      // Allow polymorphic constants by matching the declared type schema
      // against the requested instance type.
      ignore(declared_ty.match_type(ty, { subst: Subst(), tyvars: [] }))
      Const(name, ty)
    }
  }
}

///|
/// Construct a function application term.
pub fn mk_app(m : Term, n : Term) -> Term {
  App(m, n)
}

///|
/// Construct the abstraction `\x. m` in locally nameless encoding.
///
/// `x` must be a free variable (`FVar`).  Every free occurrence of `x` inside
/// `m` is replaced by `BVar(0)`, and `x` itself is kept as a binder annotation
/// so that `dest_abs` can recover a human-readable name.  Under nested
/// abstractions the de Bruijn index is shifted so that each `BVar` always
/// points to its correct binder.
///
/// If `x` does not occur free in `m`, the body is left unchanged (a vacuous
/// abstraction).  If `x` is shadowed by an inner `Abs` with the same binder,
/// occurrences below that inner binder are *not* captured.
///
/// Aborts if `x` is not a free variable.
pub fn Term::mk_abs(x : Term, m : Term) -> Term {
  // Locally-nameless encoding: convert free occurrences of `x` into BVar(idx).
  // Under each nested Abs, the index increments so that BVar always refers to
  // the correct binder level.
  fn abs_iter(idx : Int, x : Term, m : Term) -> Term {
    match m {
      FVar(_, _) as y => if x == y { BVar(idx) } else { y }
      BVar(_) => m
      Const(_, _) => m
      App(p, q) => App(abs_iter(idx, x, p), abs_iter(idx, x, q))
      Abs(y, n) => if x == y { m } else { Abs(y, abs_iter(idx + 1, x, n)) }
    }
  }
  match x {
    FVar(_, _) => Abs(x, abs_iter(0, x, m))
    _ => abort("mk_abs: first arg must be a free variable")
  }
}

///|
/// Decompose an abstraction `Abs(x, body)` back into `(x', body')` where
/// `x'` is a fresh free variable and `body'` has every `BVar(0)` (and any
/// residual free occurrence of `x`) replaced by `x'`.
///
/// Because the locally nameless encoding erases the original binder name,
/// `dest_abs` must invent a fresh name that does not clash with any variable
/// already present in the body.  Starting from the annotation name it appends
/// primes (`'`) until the name is unused, guaranteeing that round-tripping
/// `mk_abs` / `dest_abs` never accidentally captures a free variable.
///
/// This is the inverse of `mk_abs`: for any free variable `x` and term `m`,
/// `mk_abs(x, m).dest_abs()` yields a pair `(x', m')` that is
/// alpha-equivalent to `(x, m)`.
///
/// Aborts if the term is not an abstraction.
pub fn Term::dest_abs(self : Term) -> (Term, Term) {
  // Collect every variable (free or binder annotation) in a term.
  fn all_vars(t : Term) -> Array[Term] {
    match t {
      FVar(_, _) => [t]
      BVar(_) => []
      Const(_, _) => []
      App(p, q) => [..all_vars(p), ..all_vars(q)]
      Abs(x, n) => [x, ..all_vars(n)]
    }
  }
  // Return a name not used by any free variable in `vars`, appending primes
  // until a fresh name is found.
  fn fresh_name(x : String, vars : Array[Term]) -> String {
    let taken = fn(name) { vars.any(fn(v) { v is FVar(y, _) && y == name }) }
    for name = x; taken(name); {
      continue name + "'"
    } nobreak {
      name
    }
  }
  // Return a variant of free variable `v` whose name does not clash with
  // any variable in term `m`.
  fn fresh_for(v : Term, m : Term) -> Term {
    match v {
      FVar(x, ty) => {
        let vars = @foundation.dedup_sort(all_vars(m))
        let x2 = fresh_name(x, vars)
        if x2 == x {
          v
        } else {
          FVar(x2, ty)
        }
      }
      _ => abort("fresh_for: expected free variable")
    }
  }
  // Replace both free occurrences of `old` and `BVar(idx)` with `new`,
  // incrementing the index under each nested Abs.
  fn replace_with(old : Term, new : Term, idx : Int, m : Term) -> Term {
    match old {
      FVar(_, _) =>
        match m {
          FVar(_, _) => if old == m { new } else { m }
          BVar(i) => if i == idx { new } else { m }
          Const(_, _) => m
          App(p, q) =>
            App(replace_with(old, new, idx, p), replace_with(old, new, idx, q))
          Abs(y, n) => Abs(y, replace_with(old, new, idx + 1, n))
        }
      _ => abort("replace_with: expected free variable")
    }
  }
  match self {
    Abs(x, m) => {
      let x2 = fresh_for(x, m)
      (x2, replace_with(x, x2, 0, m))
    }
    _ => abort("dest_abs: expected abstraction")
  }
}

///|
test "Term: mk_abs / dest_abs roundtrip" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let abs = Term::mk_abs(x, x)
  assert_true(abs is Abs(_, _))
  // dest_abs recovers a fresh binder and the body as a free variable
  let (bv, body) = abs.dest_abs()
  guard bv is FVar(bname, bty) else { fail("expected FVar") }
  debug_inspect(
    (bname, bty, body),
    content=(
      #|("x", TyApp("bool", []), FVar("x", TyApp("bool", [])))
    ),
  )
  // type of \x:bool. x  is  bool -> bool
  inspect(
    abs.type_of().pprint(),
    content=(
      #|bool --> bool
    ),
  )
  debug_inspect(
    abs,
    content=(
      #|Abs(FVar("x", TyApp("bool", [])), BVar(0))
    ),
  )
}

///|
test "Term: dest_abs renames binder to avoid capture" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let y = mk_var("y", bool_ty)
  // \x. y — no clash, binder stays "x"
  let (bv1, body1) = Term::mk_abs(x, y).dest_abs()
  guard bv1 is FVar(n1, _) else { fail("expected FVar") }
  assert_eq(n1, "x")
  assert_true(body1 == y)
  // \x. x — binder annotation "x" doesn't clash with BVar(0), stays "x"
  let (bv2, body2) = Term::mk_abs(x, x).dest_abs()
  guard bv2 is FVar(n2, _) else { fail("expected FVar") }
  assert_eq(n2, "x")
  // body is the recovered free variable
  assert_true(body2 == bv2)
}

///|
test "Term: dest_abs freshens when binder name clashes with body" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let y = mk_var("y", bool_ty)
  // Build \y. (x y) — body contains free x; binder "y" doesn't clash
  let abs1 = Term::mk_abs(y, App(x, y))
  let (bv1, _) = abs1.dest_abs()
  guard bv1 is FVar(n1, _) else { fail("expected FVar") }
  assert_eq(n1, "y")
  // Build Abs(x_annotation, FVar("x", bool)) directly so the body contains
  // a free "x" that clashes with the binder annotation "x".
  // This simulates a term where the binder name collides with a free var.
  let clashing = Abs(x, FVar("x", bool_ty))
  let (bv2, _) = clashing.dest_abs()
  guard bv2 is FVar(n2, _) else { fail("expected FVar") }
  // binder must be renamed to avoid capturing the free "x" in the body
  assert_eq(n2, "x'")
}

///|
test "Term: dest_abs handles nested abstractions" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let y = mk_var("y", bool_ty)
  // \x. \y. x  — dest_abs the outer layer, get (x, \y. x)
  let nested = Term::mk_abs(x, Term::mk_abs(y, x))
  let (bv, inner) = nested.dest_abs()
  guard bv is FVar(name, _) else { fail("expected FVar") }
  assert_eq(name, "x")
  // inner should still be an abstraction
  assert_true(inner is Abs(_, _))
  // dest_abs the inner layer
  let (bv2, body) = inner.dest_abs()
  guard bv2 is FVar(name2, _) else { fail("expected FVar") }
  assert_eq(name2, "y")
  // body should be the free variable matching the outer binder
  assert_true(body == bv)
}

///|
test "Term: mk_abs binds the variable in the body" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let y = mk_var("y", bool_ty)
  // \x. x  =>  Abs(x, BVar(0))
  debug_inspect(
    Term::mk_abs(x, x),
    content=(
      #|Abs(FVar("x", TyApp("bool", [])), BVar(0))
    ),
  )
  // \x. y  =>  vacuous abstraction, y is unchanged
  debug_inspect(
    Term::mk_abs(x, y),
    content=(
      #|Abs(FVar("x", TyApp("bool", [])), FVar("y", TyApp("bool", [])))
    ),
  )
  // \x. (x x)  =>  both occurrences become BVar(0)
  debug_inspect(
    Term::mk_abs(x, App(x, x)),
    content=(
      #|Abs(FVar("x", TyApp("bool", [])), App(BVar(0), BVar(0)))
    ),
  )
}

///|
test "Term: mk_abs nested abstractions and shadowing" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let y = mk_var("y", bool_ty)
  // \x. \y. x  =>  outer x becomes BVar(1) under the inner binder
  let inner = Term::mk_abs(y, x)
  let outer = Term::mk_abs(x, inner)
  debug_inspect(
    outer,
    content=(
      #|Abs(
      #|  FVar("x", TyApp("bool", [])),
      #|  Abs(FVar("y", TyApp("bool", [])), BVar(1)),
      #|)
    ),
  )
  // Shadowing: \x. \x. x  =>  the inner \x. x already bound x to BVar(0),
  // so the outer mk_abs sees no free x and the body is unchanged
  let shadow = Term::mk_abs(x, Term::mk_abs(x, x))
  debug_inspect(
    shadow,
    content=(
      #|Abs(
      #|  FVar("x", TyApp("bool", [])),
      #|  Abs(FVar("x", TyApp("bool", [])), BVar(0)),
      #|)
    ),
  )
}

///|
test "Term: mk_abs leaves constants and bound vars untouched" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let c = const_("c", bool_ty)
  // \x. c  =>  constant is not affected
  debug_inspect(
    Term::mk_abs(x, c),
    content=(
      #|Abs(FVar("x", TyApp("bool", [])), Const("c", TyApp("bool", [])))
    ),
  )
}

///|
test "Term: construction and predicates" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  debug_inspect(
    x,
    content=(
      #|FVar("x", TyApp("bool", []))
    ),
  )
  // pattern match on FVar
  guard x is FVar(name, ty) else { fail("expected FVar") }
  assert_eq(name, "x")
  assert_true(ty == bool_ty)
  // type_of and is_bool
  assert_true(x.type_of() == bool_ty)
  assert_true(x.is_bool())
}
