// Proof of distributivity of multiplication over addition:
//   |- mult(a, plus(b, c)) = plus(mult(a, b), mult(a, c))
//
// This proof requires an auxiliary lemma about plus (associativity)
// and proceeds by induction on c.
//
// Lemma proved:
//   plus_assoc_lemma: |- plus(plus(a, b), c) = plus(a, plus(b, c))
//
// Main theorem:
//   mult_dist:        |- mult(a, plus(b, c)) = plus(mult(a, b), mult(a, c))

///|
/// Lemma: `|- plus(plus(a, b), c) = plus(a, plus(b, c))` by induction on c.
/// (Reproved here for use in mult_dist, independent of plus_assoc.mbt.)
fn plus_assoc_lemma(
  plus_0 : @hol.Thm,
  plus_suc : @hol.Thm
) -> @hol.Thm raise {
  let a = @hol.mk_var("a", nat_ty())
  let b = @hol.mk_var("b", nat_ty())
  let c = @hol.mk_var("c", nat_ty())
  let n = @hol.mk_var("n", nat_ty())
  let m = @hol.mk_var("m", nat_ty())
  // Property: plus(plus(a, b), c) = plus(a, plus(b, c))
  let prop = @hol.Term::mk_eq(
    mk_plus(mk_plus(a, b), c),
    mk_plus(a, mk_plus(b, c)),
  )

  // BASE: plus(plus(a, b), 0) = plus(a, plus(b, 0))
  //   plus(plus(a, b), 0) = plus(a, b)   from PLUS_0 with n := plus(a, b)
  let b1 = specialize(plus_0, [(n, mk_plus(a, b))])
  //   plus(b, 0) = b   from PLUS_0 with n := b
  let b2 = specialize(plus_0, [(n, b)])
  //   plus(a, plus(b, 0)) = plus(a, b)   from b2 by congruence
  let b3 = @hol.Equal::apTerm(@hol.mk_app(plus(), a), b2)
  //   plus(plus(a, b), 0) = plus(a, plus(b, 0))
  let base = @hol.Equal::trans(b1, @hol.Equal::sym(b3))

  // STEP: assuming plus(plus(a,b), c) = plus(a, plus(b, c)),
  //   show plus(plus(a,b), SUC(c)) = plus(a, plus(b, SUC(c)))
  //
  //   plus(plus(a,b), SUC(c)) = SUC(plus(plus(a,b), c))
  let s1 = specialize(plus_suc, [(n, mk_plus(a, b)), (m, c)])
  //   IH
  let ih = @hol.Kernel::assume(prop)
  //   SUC(plus(plus(a,b), c)) = SUC(plus(a, plus(b, c)))
  let s2 = @hol.Equal::apTerm(suc(), ih)
  //   plus(b, SUC(c)) = SUC(plus(b, c))
  let s3 = specialize(plus_suc, [(n, b), (m, c)])
  //   plus(a, plus(b, SUC(c))) = plus(a, SUC(plus(b, c)))
  let s4 = @hol.Equal::apTerm(@hol.mk_app(plus(), a), s3)
  //   plus(a, SUC(plus(b, c))) = SUC(plus(a, plus(b, c)))
  let s5 = specialize(plus_suc, [(n, a), (m, mk_plus(b, c))])
  //   Chain: plus(plus(a,b), SUC(c))
  //     = SUC(plus(plus(a,b), c))       [s1]
  //     = SUC(plus(a, plus(b, c)))      [s2]
  //     = plus(a, SUC(plus(b, c)))      [sym(s5)]
  //     = plus(a, plus(b, SUC(c)))      [sym(s4)]
  let step = @hol.Equal::trans(
    s1,
    @hol.Equal::trans(
      s2,
      @hol.Equal::trans(@hol.Equal::sym(s5), @hol.Equal::sym(s4)),
    ),
  )

  Nat::induction(base~, step~, v=c, prop~)
}

///|
/// Prove distributivity of multiplication over addition:
///   `|- mult(a, plus(b, c)) = plus(mult(a, b), mult(a, c))`
/// with `a`, `b`, `c` free (= universally quantified).
pub fn Nat::mult_dist() -> @hol.Thm raise {
  let (plus_0, plus_suc, mult_0, mult_suc) = Nat::setup()
  let a = @hol.mk_var("a", nat_ty())
  let b = @hol.mk_var("b", nat_ty())
  let c = @hol.mk_var("c", nat_ty())
  let n = @hol.mk_var("n", nat_ty())
  let m = @hol.mk_var("m", nat_ty())
  // The property to prove: mult(a, plus(b, c)) = plus(mult(a, b), mult(a, c))
  let dist_prop = @hol.Term::mk_eq(
    mk_mult(a, mk_plus(b, c)),
    mk_plus(mk_mult(a, b), mk_mult(a, c)),
  )

  // Get auxiliary lemma
  let passoc = plus_assoc_lemma(plus_0, plus_suc)

  // ================================================================
  // BASE CASE: mult(a, plus(b, 0)) = plus(mult(a, b), mult(a, 0))
  // ================================================================

  // LHS: mult(a, plus(b, 0)) = mult(a, b)
  //   plus(b, 0) = b   from PLUS_0 with n := b
  let lb1 = specialize(plus_0, [(n, b)])
  //   mult(a, plus(b, 0)) = mult(a, b)   congruence under mult(a, -)
  let lb2 = @hol.Equal::apTerm(@hol.mk_app(mult(), a), lb1)

  // RHS: plus(mult(a, b), mult(a, 0)) = mult(a, b)
  //   mult(a, 0) = 0   from MULT_0 with n := a
  let rb1 = specialize(mult_0, [(n, a)])
  //   plus(mult(a, b), mult(a, 0)) = plus(mult(a, b), 0)   congruence
  let rb2 = @hol.Equal::apTerm(
    @hol.mk_app(plus(), mk_mult(a, b)),
    rb1,
  )
  //   plus(mult(a, b), 0) = mult(a, b)   from PLUS_0 with n := mult(a, b)
  let rb3 = specialize(plus_0, [(n, mk_mult(a, b))])
  //   plus(mult(a, b), mult(a, 0)) = mult(a, b)
  let rb4 = @hol.Equal::trans(rb2, rb3)

  // BASE: mult(a, plus(b, 0)) = plus(mult(a, b), mult(a, 0))
  //   trans(lb2, sym(rb4))
  let base = @hol.Equal::trans(lb2, @hol.Equal::sym(rb4))

  // ================================================================
  // INDUCTIVE STEP
  // IH: mult(a, plus(b, c)) = plus(mult(a, b), mult(a, c))
  // Goal: mult(a, plus(b, SUC(c))) = plus(mult(a, b), mult(a, SUC(c)))
  // ================================================================

  let ih = @hol.Kernel::assume(dist_prop)

  // LHS chain: mult(a, plus(b, SUC(c)))
  //   Step 1: plus(b, SUC(c)) = SUC(plus(b, c))   from PLUS_SUC with n := b, m := c
  let l1 = specialize(plus_suc, [(n, b), (m, c)])
  //   mult(a, plus(b, SUC(c))) = mult(a, SUC(plus(b, c)))
  let l2 = @hol.Equal::apTerm(@hol.mk_app(mult(), a), l1)
  //   Step 2: mult(a, SUC(plus(b, c))) = plus(mult(a, plus(b, c)), a)
  //   from MULT_SUC with n := a, m := plus(b, c)
  let l3 = specialize(mult_suc, [(n, a), (m, mk_plus(b, c))])
  //   mult(a, plus(b, SUC(c))) = plus(mult(a, plus(b, c)), a)
  let l4 = @hol.Equal::trans(l2, l3)
  //   Step 3: Apply IH: mult(a, plus(b, c)) = plus(mult(a, b), mult(a, c))
  //   Use mkBinop: from IH and refl(a),
  //   get plus(mult(a,plus(b,c)), a) = plus(plus(mult(a,b),mult(a,c)), a)
  let l5 = @hol.Equal::mkBinop(plus(), ih, @hol.Kernel::refl(a))
  //   mult(a, plus(b, SUC(c))) = plus(plus(mult(a, b), mult(a, c)), a)
  let l6 = @hol.Equal::trans(l4, l5)

  // RHS chain: plus(mult(a, b), mult(a, SUC(c)))
  //   mult(a, SUC(c)) = plus(mult(a, c), a)   from MULT_SUC with n := a, m := c
  let r1 = specialize(mult_suc, [(n, a), (m, c)])
  //   plus(mult(a, b), mult(a, SUC(c))) = plus(mult(a, b), plus(mult(a, c), a))
  let r2 = @hol.Equal::apTerm(
    @hol.mk_app(plus(), mk_mult(a, b)),
    r1,
  )

  // Now we need:
  //   LHS = plus(plus(mult(a,b), mult(a,c)), a)
  //   RHS = plus(mult(a,b), plus(mult(a,c), a))
  // These are equal by plus_assoc with a := mult(a,b), b := mult(a,c), c := a
  // plus_assoc_lemma: |- plus(plus(a, b), c) = plus(a, plus(b, c))
  // Specialize with a := mult(a,b), b := mult(a,c), c := a
  let assoc_inst = specialize(
    passoc,
    [(a, mk_mult(a, b)), (b, mk_mult(a, c)), (c, a)],
  )
  // assoc_inst: plus(plus(mult(a,b), mult(a,c)), a) = plus(mult(a,b), plus(mult(a,c), a))

  // Chain: mult(a, plus(b, SUC(c)))
  //   = plus(plus(mult(a,b), mult(a,c)), a)   [l6]
  //   = plus(mult(a,b), plus(mult(a,c), a))   [assoc_inst]
  //   = plus(mult(a,b), mult(a, SUC(c)))      [sym(r2)]
  let step = @hol.Equal::trans(
    l6,
    @hol.Equal::trans(assoc_inst, @hol.Equal::sym(r2)),
  )

  // ================================================================
  // APPLY INDUCTION
  // ================================================================
  Nat::induction(base~, step~, v=c, prop=dist_prop)
}

///|
test "mult_dist: mult(a, plus(b, c)) = plus(mult(a, b), mult(a, c))" {
  let th = Nat::mult_dist()
  // No hypotheses — this is a theorem, not a conditional result
  assert_eq(th.hyps.length(), 0)
  // Conclusion is an equation
  assert_true(@hol.Term::is_eq(th.concl))
  let (lhs, rhs) = @hol.Term::dest_eq(th.concl)
  // LHS = mult(a, plus(b, c))
  let a = @hol.mk_var("a", nat_ty())
  let b = @hol.mk_var("b", nat_ty())
  let c = @hol.mk_var("c", nat_ty())
  assert_eq(lhs, mk_mult(a, mk_plus(b, c)))
  // RHS = plus(mult(a, b), mult(a, c))
  assert_eq(rhs, mk_plus(mk_mult(a, b), mk_mult(a, c)))
}
