///|
fn setup_hol_tables() -> Unit {
  @types.Type::reset_table()
  @types.Type::new_type("list", 1)
  @terms.Term::reset_table()
}

///|
test "type: constructors and subst" {
  setup_hol_tables()
  let a = @types.mk_var("a")
  let b = @types.mk_var("b")
  let list_a = @types.Type::mk_type("list", [a])
  let got = list_a.subst(Subst(pairs=[(a, b)]))
  assert_eq(got.pprint(), "b list")
}

///|
test "type: match" {
  setup_hol_tables()
  let a = @types.mk_var("a")
  let bool_t = @types.bool_ty()
  let state = a.match_type(bool_t, { subst: Subst(), tyvars: [] })
  assert_true(state.subst.contains(a))
}

///|
test "term: abs and dest_abs" {
  setup_hol_tables()
  let a = @types.mk_var("a")
  let x = @terms.mk_var("x", a)
  let tm = @terms.Term::mk_abs(x, x)
  let (bv, body) = @terms.Term::dest_abs(tm)
  assert_true(bv is FVar(_, _))
  assert_eq(@terms.Term::pprint(body), @terms.Term::pprint(bv))
}

///|
test "term: match_term" {
  setup_hol_tables()
  let a = @types.mk_var("a")
  ignore(@terms.Term::new_const("c_match", a))
  let pat = @terms.mk_var("x", a)
  let ob = @terms.Term::mk_const("c_match", a)
  let (tm_s, _ty_s) = pat.match_term(ob)
  assert_eq([..tm_s].length(), 1)
}

///|
test "boolsyntax: mk_imp" {
  setup_hol_tables()
  let p = @terms.mk_var("p", @types.bool_ty())
  let imp = @logic.BoolSyntax::mk_imp(p, p)
  let neg = @logic.BoolSyntax::mk_neg(p)
  assert_true(@logic.BoolSyntax::is_imp(imp))
  let (lhs, rhs) = @logic.BoolSyntax::dest_imp(imp)
  assert_true(lhs == p)
  assert_true(rhs == p)
  // dest_neg(~ p) should return p (the inner term), not ~ p.
  assert_true(@logic.BoolSyntax::dest_neg(neg) == p)
}

///|
// Regression test: dest_neg must return the inner term, not the whole negation.
// See step5 for the full rationale.
test "boolsyntax: dest_neg returns inner term (roundtrip)" {
  setup_hol_tables()
  let p = @terms.mk_var("p", @types.bool_ty())
  let neg = @logic.BoolSyntax::mk_neg(p)
  let inner = @logic.BoolSyntax::dest_neg(neg)
  // Roundtrip: dest_neg(mk_neg(p)) == p
  assert_true(inner == p)
  // The result should NOT be the negation itself
  assert_false(inner == neg)
  // Double negation: dest_neg(mk_neg(mk_neg(p))) == mk_neg(p)
  let double_neg = @logic.BoolSyntax::mk_neg(neg)
  assert_true(@logic.BoolSyntax::dest_neg(double_neg) == neg)
}

///|
test "kernel: refl/assume/eqMp" {
  setup_hol_tables()
  let p = @terms.mk_var("p", @types.bool_ty())
  let th_eq = @logic.Kernel::refl(p)
  let th_p = @logic.Kernel::assume(p)
  let th = @logic.Kernel::eqMp(th_eq, th_p)
  assert_true(th.concl == p)
}

///|
test "kernel: betaConv" {
  setup_hol_tables()
  let a = @types.mk_var("a")
  let x = @terms.mk_var("x", a)
  let y = @terms.mk_var("y", a)
  let abs = @terms.Term::mk_abs(x, x)
  let th = @logic.Kernel::betaConv(abs, y)
  let (_lhs, rhs) = @terms.Term::dest_eq(th.concl)
  assert_true(rhs == y)
}

///|
test "kernel: defineConst" {
  setup_hol_tables()
  let a = @types.mk_var("a")
  let x = @terms.mk_var("x", a)
  let rhs = @terms.Term::mk_abs(x, x)
  let th = @logic.Kernel::defineConst("id_const", rhs)
  let (_lhs, got_rhs) = @terms.Term::dest_eq(th.concl)
  assert_true(got_rhs.aconv(rhs))
}

///|
test "equal: sym and trans" {
  setup_hol_tables()
  let a = @types.mk_var("a")
  let x = @terms.mk_var("x", a)
  let th = @logic.Kernel::refl(x)
  let sym = @logic.Equal::sym(th)
  let trans = @logic.Equal::trans(th, th)
  assert_true(@terms.Term::is_eq(sym.concl))
  assert_true(@terms.Term::is_eq(trans.concl))
}
