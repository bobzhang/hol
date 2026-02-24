///|
/// Test alpha-equivalence: two terms are alpha-convertible if they are
/// identical up to renaming of bound variables.  Free variables and constants
/// must match exactly.
pub fn Term::aconv(self : Term, rhs : Term) -> Bool {
  match (self, rhs) {
    (FVar(_, _), FVar(_, _)) => self == rhs
    (Const(_, _), Const(_, _)) => self == rhs
    (BVar(i), BVar(j)) => i == j
    (App(m, n), App(p, q)) => m.aconv(p) && n.aconv(q)
    (Abs(FVar(_, ty1), m), Abs(FVar(_, ty2), n)) => ty1 == ty2 && m.aconv(n)
    _ => false
  }
}

///|
test "Term: aconv" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let y = mk_var("y", bool_ty)
  // (\x. x) and (\y. y) differ only in bound variable name: alpha-equivalent
  assert_true(Term::mk_abs(x, x).aconv(Term::mk_abs(y, y)))
  // (\x. x) and (\x. y): bodies differ, not alpha-equivalent
  assert_false(Term::mk_abs(x, x).aconv(Term::mk_abs(x, y)))
}
