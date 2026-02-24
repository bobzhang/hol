///|
/// Apply a type substitution to every type annotation in the term, specializing polymorphic constants and variables to concrete types.
pub fn Term::inst(self : Term, sigma : @types.TypeSubst) -> Term {
  match self {
    FVar(x, ty) => FVar(x, ty.subst(sigma))
    BVar(_) => self
    Const(c, ty) => Const(c, ty.subst(sigma))
    App(p, q) => App(p.inst(sigma), q.inst(sigma))
    Abs(x, n) => Abs(x.inst(sigma), n.inst(sigma))
  }
}

///|
test "Term: inst" {
  let a = @types.mk_var("'a")
  let bool_ty = @types.bool_ty()
  // a variable of type 'a becomes bool after instantiation
  let v = mk_var("v", a)
  let tau : @types.TypeSubst = Subst(pairs=[(a, bool_ty)])
  assert_true(v.inst(tau).type_of() == bool_ty)
}

///|
/// Apply a term-level substitution simultaneously, replacing free variables
/// according to the given mapping in a single pass.
///
/// Unlike sequential application (which would let the range of one pair be
/// rewritten by later pairs), this looks up each free variable in the original
/// term independently, matching standard HOL semantics.
pub fn Term::subst(self : Term, s : TermSubst) -> Term {
  if s.is_empty() {
    return self
  }
  fn go(tm : Term) -> Term {
    match tm {
      FVar(_, _) =>
        match s.lookup(tm) {
          Some(rep) => rep
          None => tm
        }
      BVar(_) => tm
      Const(_, _) => tm
      App(p, q) => App(go(p), go(q))
      Abs(x, n) => Abs(x, go(n))
    }
  }
  go(self)
}

///|
test "Term: subst" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let y = mk_var("y", bool_ty)
  // x[y/x] = y
  let sigma : TermSubst = Subst(pairs=[(x, y)])
  assert_true(x.subst(sigma) == y)
  // substitution inside application: (x x)[y/x] = (y y)
  let app = mk_app(x, x)
  assert_true(app.subst(sigma) == mk_app(y, y))
}

///|
test "Term: subst is simultaneous, not sequential" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let y = mk_var("y", bool_ty)
  // {x→y, y→x} should swap x and y, not collapse both to x
  let swap : TermSubst = Subst(pairs=[(x, y), (y, x)])
  // On a single variable:
  assert_true(x.subst(swap) == y)
  assert_true(y.subst(swap) == x)
  // On an application with both variables: (x y) becomes (y x)
  let app = mk_app(x, y)
  assert_true(app.subst(swap) == mk_app(y, x))
}

///|
test "Term: subst avoids range-domain interference" {
  // Regression: {n→m, m→k} should substitute n and m independently
  // in the original term, not let n→m feed into m→k.
  let bool_ty = @types.bool_ty()
  let n = mk_var("n", bool_ty)
  let m = mk_var("m", bool_ty)
  let k = mk_var("k", bool_ty)
  let sigma : TermSubst = Subst(pairs=[(n, m), (m, k)])
  // n becomes m (not k)
  assert_true(n.subst(sigma) == m)
  // m becomes k
  assert_true(m.subst(sigma) == k)
  // (n m) becomes (m k), not (k k)
  let app = mk_app(n, m)
  assert_true(app.subst(sigma) == mk_app(m, k))
}

///|
/// Collect all free variables in the term, returning them sorted and deduplicated.
fn Term::free_vars(self : Term) -> Array[Term] {
  fn iter(acc : Array[Term], t : Term) -> Array[Term] {
    match t {
      FVar(_, _) as x => [x, ..acc]
      BVar(_) => acc
      Const(_, _) => acc
      App(p, q) => iter(iter(acc, p), q)
      Abs(_, n) => iter(acc, n)
    }
  }
  @foundation.dedup_sort(iter([], self))
}

///|
test "Term: free_vars" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let y = mk_var("y", bool_ty)
  // abstraction binds x, so only y is free in (\x. y)
  let fvs = Term::mk_abs(x, y).free_vars()
  assert_eq(fvs.length(), 1)
  assert_true(fvs[0] == y)
  // application collects free vars of both sides
  assert_eq(mk_app(x, y).free_vars().length(), 2)
}
