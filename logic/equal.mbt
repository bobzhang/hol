// Step 7: Derived Equality Rules
//
// These are **derived** inference rules built entirely from the kernel
// primitives (refl, eqMp, appThm, absThm, ...).  Because they compose
// only sound primitives, they are sound by construction -- no additional
// trust is needed beyond the kernel.
//
// This corresponds to HOL Light's `equal.ml`.

///|
/// Namespace for derived equality rules built from kernel primitives.
pub enum Equal {}

///|
fn equal_rator(tm : @terms.Term) -> @terms.Term {
  match tm {
    App(l, _) => l
    _ => abort("equal_rator: expected application")
  }
}

///|
/// Apply a term to both sides: from `A |- x = y`, derive `A |- f x = f y`.
pub fn Equal::apTerm(tm : @terms.Term, th : Thm) -> Thm raise {
  let rth = Kernel::refl(tm)
  Kernel::appThm(rth, th)
}

///|
/// Transitivity (fast version): from `A1 |- s = t` and `A2 |- t = u`, derive `A1 U A2 |- s = u`.
pub fn Equal::trans_fast(th1 : Thm, th2 : Thm) -> Thm raise {
  let (s, _) = th1.concl.dest_eq()
  let f = s.curry_eq()
  let th3 = Equal::apTerm(f, th2)
  Kernel::eqMp(th3, th1)
}

///|
/// Symmetry: from `A |- s = t`, derive `A |- t = s`.
pub fn Equal::sym(th : Thm) -> Thm raise {
  let tm = th.concl
  let (l, _r) = tm.dest_eq()
  let lth = Kernel::refl(l)
  Kernel::eqMp(
    Kernel::appThm(Equal::apTerm(equal_rator(equal_rator(tm)), th), lth),
    lth,
  )
}

///|
test "Equal::sym" {
  // sym(|- x = x)  gives  |- x = x  (same for refl, but sides are swapped)
  let x = @terms.mk_var("x", @types.bool_ty())
  let th = Kernel::refl(x)
  let th_sym = Equal::sym(th)
  let (lhs, rhs) = th_sym.concl.dest_eq()
  // For refl x=x, sym gives x=x (both sides same)
  assert_true(lhs == x && rhs == x)
  // symmetry is an involution: sym(sym(th)) ≡ th
  let th_sym2 = Equal::sym(th_sym)
  assert_true(th_sym2.concl == th.concl)
}

///|
/// Apply an argument to both sides: from `A |- f = g`, derive `A |- f x = g x`.
pub fn Equal::apThm(tm : @terms.Term, th : Thm) -> Thm raise {
  Kernel::appThm(th, Kernel::refl(tm))
}

///|
/// Transitivity (hypothesis-preserving variant): from `A1 |- s = t` and `A2 |- t = u`, derive `A1 U A2 |- s = u`.
fn Equal::trans_preserve_hyps(th1 : Thm, th2 : Thm) -> Thm raise {
  let (_, u) = th2.concl.dest_eq()
  let f = u.curry_eq()
  let th3 = Equal::sym(Equal::apTerm(f, th1))
  let th2p = Equal::sym(th2)
  let th4 = Kernel::eqMp(th3, th2p)
  Equal::sym(th4)
}

///|
/// Transitivity: from `A1 |- s = t` and `A2 |- t = u`, derive `A1 U A2 |- s = u`.
pub fn Equal::trans(th1 : Thm, th2 : Thm) -> Thm raise {
  Equal::trans_preserve_hyps(th1, th2)
}

///|
test "Equal::trans" {
  // trans(|- x = x, |- x = x)  gives  |- x = x
  let x = @terms.mk_var("x", @types.bool_ty())
  let th = Kernel::refl(x)
  let th_trans = Equal::trans(th, th)
  let (lhs, rhs) = th_trans.concl.dest_eq()
  assert_true(lhs == x && rhs == x)
  assert_eq(th_trans.hyps.length(), 0)
}

///|
/// Alpha-conversion: derive `|- t1 = t2` when `t1` and `t2` are alpha-convertible.
pub fn Equal::alpha(t1 : @terms.Term, t2 : @terms.Term) -> Thm raise {
  Equal::trans(Kernel::refl(t1), Kernel::refl(t2))
}

///|
/// Binary operator congruence: from `A1 |- l1 = l2` and `A2 |- r1 = r2`, derive `A1 U A2 |- b l1 r1 = b l2 r2`.
pub fn Equal::mkBinop(binop : @terms.Term, lth : Thm, rth : Thm) -> Thm raise {
  Kernel::appThm(Equal::apTerm(binop, lth), rth)
}
