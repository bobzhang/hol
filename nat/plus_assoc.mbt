// Proof of associativity of plus: |- plus(plus(n,m),k) = plus(n,plus(m,k))
//
// This demonstrates the HOL kernel's equational reasoning capabilities.
// The proof proceeds by induction on k:
//
//   Base case:  plus(plus(n,m), 0) = plus(n, plus(m, 0))
//     Both sides reduce to plus(n,m) using PLUS_0.
//
//   Inductive step: assuming plus(plus(n,m), k) = plus(n, plus(m, k)),
//     show plus(plus(n,m), SUC(k)) = plus(n, plus(m, SUC(k)))
//     by unfolding PLUS_SUC on both sides and applying the IH under SUC.
//
// Every equational step uses real kernel primitives (termSubst, appThm,
// trans, sym).  Only the induction principle itself is axiomatized.

///|
/// Specialize free variables in a theorem via termSubst.
fn specialize(
  th : @hol.Thm,
  pairs : Array[(@hol.Term, @hol.Term)]
) -> @hol.Thm {
  @hol.Kernel::termSubst(Subst(pairs=pairs[:]), th)
}

///|
/// Prove associativity of plus:
///   `|- plus(plus(n,m), k) = plus(n, plus(m, k))`
/// with `n`, `m`, `k` free (= universally quantified).
pub fn Nat::plus_assoc() -> @hol.Thm raise {
  let (plus_0, plus_suc, _, _) = Nat::setup()
  // Free variables (also serve as substitution redexes since the axioms
  // use the same variable names n, m)
  let n = @hol.mk_var("n", nat_ty())
  let m = @hol.mk_var("m", nat_ty())
  let k = @hol.mk_var("k", nat_ty())
  // The property to prove: plus(plus(n,m),k) = plus(n,plus(m,k))
  let assoc_prop = @hol.Term::mk_eq(
    mk_plus(mk_plus(n, m), k),
    mk_plus(n, mk_plus(m, k)),
  )

  // ================================================================
  // BASE CASE: |- plus(plus(n,m), 0) = plus(n, plus(m, 0))
  // ================================================================

  // Step 1: plus(plus(n,m), 0) = plus(n,m)
  //   from PLUS_0 with n := plus(n,m)
  let b1 = specialize(plus_0, [(n, mk_plus(n, m))])

  // Step 2: plus(m, 0) = m
  //   from PLUS_0 with n := m
  let b2 = specialize(plus_0, [(n, m)])

  // Step 3: plus(n, plus(m, 0)) = plus(n, m)
  //   from b2 by congruence: apTerm(plus(n), plus(m,0) = m)
  let b3 = @hol.Equal::apTerm(@hol.mk_app(plus(), n), b2)

  // Step 4: plus(plus(n,m), 0) = plus(n, plus(m, 0))
  //   trans(b1, sym(b3))
  let base = @hol.Equal::trans(b1, @hol.Equal::sym(b3))

  // ================================================================
  // INDUCTIVE STEP
  // IH: plus(plus(n,m), k) = plus(n, plus(m, k))
  // Goal: plus(plus(n,m), SUC(k)) = plus(n, plus(m, SUC(k)))
  // ================================================================

  // The induction hypothesis formula
  let ih_formula = assoc_prop

  // Step 1: plus(plus(n,m), SUC(k)) = SUC(plus(plus(n,m), k))
  //   from PLUS_SUC with n := plus(n,m), m := k
  let s1 = specialize(plus_suc, [(n, mk_plus(n, m)), (m, k)])

  // Step 2: SUC(plus(plus(n,m), k)) = SUC(plus(n, plus(m, k)))
  //   from IH by congruence under SUC: apTerm(SUC, IH)
  let ih = @hol.Kernel::assume(ih_formula)
  let s2 = @hol.Equal::apTerm(suc(), ih)

  // Step 3: plus(m, SUC(k)) = SUC(plus(m, k))
  //   from PLUS_SUC with n := m, m := k
  let s3 = specialize(plus_suc, [(n, m), (m, k)])

  // Step 4: plus(n, plus(m, SUC(k))) = plus(n, SUC(plus(m, k)))
  //   congruence: apTerm(plus(n), s3)
  let s4 = @hol.Equal::apTerm(@hol.mk_app(plus(), n), s3)

  // Step 5: plus(n, SUC(plus(m, k))) = SUC(plus(n, plus(m, k)))
  //   from PLUS_SUC with n := n, m := plus(m,k)
  let s5 = specialize(plus_suc, [(n, n), (m, mk_plus(m, k))])

  // Step 6: Chain everything:
  //   plus(plus(n,m), SUC(k))
  //     = SUC(plus(plus(n,m), k))       [s1]
  //     = SUC(plus(n, plus(m, k)))      [s2]
  //     = plus(n, SUC(plus(m, k)))      [sym(s5)]
  //     = plus(n, plus(m, SUC(k)))      [sym(s4)]
  let step_result = @hol.Equal::trans(
    s1,
    @hol.Equal::trans(
      s2,
      @hol.Equal::trans(@hol.Equal::sym(s5), @hol.Equal::sym(s4)),
    ),
  )

  // ================================================================
  // APPLY INDUCTION
  // ================================================================
  Nat::induction(base~, step=step_result, v=k, prop=assoc_prop)
}

///|
test "plus_assoc: plus(plus(n,m),k) = plus(n,plus(m,k))" {
  let th = Nat::plus_assoc()
  // No hypotheses — this is a theorem, not a conditional result
  assert_eq(th.hyps.length(), 0)
  // Conclusion is an equation
  assert_true(@hol.Term::is_eq(th.concl))
  let (lhs, rhs) = @hol.Term::dest_eq(th.concl)
  // LHS = plus(plus(n,m),k)
  let n = @hol.mk_var("n", nat_ty())
  let m = @hol.mk_var("m", nat_ty())
  let k = @hol.mk_var("k", nat_ty())
  assert_eq(lhs, mk_plus(mk_plus(n, m), k))
  // RHS = plus(n,plus(m,k))
  assert_eq(rhs, mk_plus(n, mk_plus(m, k)))
}

///|
test "setup: nat type and constants registered" {
  let (plus_0, plus_suc, _, _) = Nat::setup()
  // Both axioms have no hypotheses
  assert_eq(plus_0.hyps.length(), 0)
  assert_eq(plus_suc.hyps.length(), 0)
  // PLUS_0 conclusion is an equation
  assert_true(@hol.Term::is_eq(plus_0.concl))
  // PLUS_SUC conclusion is an equation
  assert_true(@hol.Term::is_eq(plus_suc.concl))
}
