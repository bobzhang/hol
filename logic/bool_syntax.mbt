// Step 5 / Step 8: Boolean Syntax (Connectives and Quantifiers)
//
// In the HOL Light approach, **all** connectives and quantifiers are defined
// in terms of polymorphic equality `= : 'a -> 'a -> bool`:
//
//   T     := (\p. p) = (\p. p)
//   /\    := \p q. (\f. f p q) = (\f. f T T)
//   ==>   := \p q. (p /\ q) = p
//   forall:= \P. P = (\x. T)
//   exist := \P. forall q. (forall x. P x ==> q) ==> q
//   \/    := \p q. forall r. (p ==> r) ==> (q ==> r) ==> r
//   F     := forall p. p
//   ~     := \p. p ==> F
//   ?!    := \P. exist P /\ forall x y. P x /\ P y ==> x = y
//
// This file provides uniform constructors (`mk_*`), destructors (`dest_*`),
// and predicates (`is_*`) for each connective/quantifier.

///|
/// Namespace for Boolean connective and quantifier operations in HOL.
pub enum BoolSyntax {}

///|
fn boolsyntax_a() -> @types.Type {
  @types.mk_var("'a")
}

///|
/// Test whether a term has the individual type `ind`.
pub fn BoolSyntax::is_ind(tm : @terms.Term) -> Bool {
  @types.ind_ty() == tm.type_of()
}

///|
// Common type schemas used for constant declarations.
fn equality_ty() -> @types.Type {
  let a = boolsyntax_a()
  @types.mk_fun(a, @types.mk_fun(a, @types.bool_ty()))
}

///|
fn connective_ty() -> @types.Type {
  @types.mk_fun(
    @types.bool_ty(),
    @types.mk_fun(@types.bool_ty(), @types.bool_ty()),
  )
}

///|
fn quant_ty() -> @types.Type {
  let a = boolsyntax_a()
  @types.mk_fun(@types.mk_fun(a, @types.bool_ty()), @types.bool_ty())
}

///|
/// Return the polymorphic equality constant `= : 'a -> 'a -> bool`.
pub fn BoolSyntax::equality() -> @terms.Term {
  @terms.const_("=", equality_ty())
}

///|
/// Return the implication constant `==> : bool -> bool -> bool`.
pub fn BoolSyntax::implication() -> @terms.Term {
  @terms.const_("==>", connective_ty())
}

///|
/// Return the truth constant `T : bool`.
pub fn BoolSyntax::verum() -> @terms.Term {
  @terms.const_("T", @types.bool_ty())
}

///|
/// Return the falsity constant `F : bool`.
pub fn BoolSyntax::falsum() -> @terms.Term {
  @terms.const_("F", @types.bool_ty())
}

///|
/// Return the universal quantifier constant `forall : ('a -> bool) -> bool`.
pub fn BoolSyntax::universal() -> @terms.Term {
  @terms.const_("forall", quant_ty())
}

///|
/// Return the existential quantifier constant `exist : ('a -> bool) -> bool`.
pub fn BoolSyntax::existential() -> @terms.Term {
  @terms.const_("exist", quant_ty())
}

///|
/// Return the unique existence constant `?! : ('a -> bool) -> bool`.
pub fn BoolSyntax::ex_unique() -> @terms.Term {
  @terms.const_("ex_unique", quant_ty())
}

///|
/// Return the conjunction constant `/\ : bool -> bool -> bool`.
pub fn BoolSyntax::conjunction() -> @terms.Term {
  @terms.const_("/\\", connective_ty())
}

///|
/// Return the disjunction constant `\/ : bool -> bool -> bool`.
pub fn BoolSyntax::disjunction() -> @terms.Term {
  @terms.const_("\\/", connective_ty())
}

///|
/// Return the negation constant `~ : bool -> bool`.
pub fn BoolSyntax::negation() -> @terms.Term {
  @terms.const_("~", @types.mk_fun(@types.bool_ty(), @types.bool_ty()))
}

///|
/// Construct an implication `p ==> q`, checking that both arguments have Boolean type.
pub fn BoolSyntax::mk_imp(ant : @terms.Term, conseq : @terms.Term) -> @terms.Term {
  if !ant.is_bool() {
    abort("mk_imp: antecedent is not bool")
  }
  if !conseq.is_bool() {
    abort("mk_imp: consequent is not bool")
  }
  @terms.mk_app(@terms.mk_app(BoolSyntax::implication(), ant), conseq)
}

///|
test "BoolSyntax: implication" {
  let bool_ty = @types.bool_ty()
  let p = @terms.mk_var("p", bool_ty)
  let q = @terms.mk_var("q", bool_ty)
  let imp = BoolSyntax::mk_imp(p, q)
  assert_true(BoolSyntax::is_imp(imp) && imp.is_bool())
  let (ant, con) = BoolSyntax::dest_imp(imp)
  assert_true(ant == p && con == q)
}

///|
// `mk_binder` pattern: quantifiers (forall, exist, ?!) are all applied to
// abstractions.  E.g., `forall x. P x` is `(forall) (\x. P x)`.  We
// instantiate the polymorphic quantifier constant to the bound variable's
// type before applying it.
fn boolsyntax_mk_binder(ctor : @terms.Term, bv : @terms.Term, body : @terms.Term) -> @terms.Term {
  let a = boolsyntax_a()
  let sigma : @types.TypeSubst = Subst(pairs=[(a, bv.type_of())])
  @terms.mk_app(ctor.inst(sigma), @terms.Term::mk_abs(bv, body))
}

///|
/// Construct a universal quantification `forall x. body`.
pub fn BoolSyntax::mk_forall(bv : @terms.Term, body : @terms.Term) -> @terms.Term {
  boolsyntax_mk_binder(BoolSyntax::universal(), bv, body)
}

///|
/// Construct an existential quantification `exist x. body`.
pub fn BoolSyntax::mk_exists(bv : @terms.Term, body : @terms.Term) -> @terms.Term {
  boolsyntax_mk_binder(BoolSyntax::existential(), bv, body)
}

///|
/// Construct a unique existence quantification `?! x. body`.
pub fn BoolSyntax::mk_ex_unique(bv : @terms.Term, body : @terms.Term) -> @terms.Term {
  boolsyntax_mk_binder(BoolSyntax::ex_unique(), bv, body)
}

///|
/// Construct a conjunction `p /\ q`, checking that both arguments have Boolean type.
pub fn BoolSyntax::mk_conj(c1 : @terms.Term, c2 : @terms.Term) -> @terms.Term {
  if !c1.is_bool() || !c2.is_bool() {
    abort("mk_conj: expected bool terms")
  }
  @terms.mk_app(@terms.mk_app(BoolSyntax::conjunction(), c1), c2)
}

///|
test "BoolSyntax: conjunction" {
  let bool_ty = @types.bool_ty()
  let p = @terms.mk_var("p", bool_ty)
  let q = @terms.mk_var("q", bool_ty)
  let conj = BoolSyntax::mk_conj(p, q)
  assert_true(BoolSyntax::is_conj(conj) && conj.is_bool())
  let (l, r) = BoolSyntax::dest_conj(conj)
  assert_true(l == p && r == q)
}

///|
/// Construct a disjunction `p \/ q`, checking that both arguments have Boolean type.
pub fn BoolSyntax::mk_disj(d1 : @terms.Term, d2 : @terms.Term) -> @terms.Term {
  if !d1.is_bool() || !d2.is_bool() {
    abort("mk_disj: expected bool terms")
  }
  @terms.mk_app(@terms.mk_app(BoolSyntax::disjunction(), d1), d2)
}

///|
/// Construct a negation `~ p`, checking that the argument has Boolean type.
pub fn BoolSyntax::mk_neg(fm : @terms.Term) -> @terms.Term {
  if !fm.is_bool() {
    abort("mk_neg: expected bool term")
  }
  @terms.mk_app(BoolSyntax::negation(), fm)
}

///|
// `dest_binop` pattern: for a binary connective `op l r` (encoded as
// `App(App(op, l), r)`), check that the head matches the expected constant
// and return (l, r).  Used by dest_eq, dest_imp, dest_conj, dest_disj.
fn boolsyntax_dest_binop(
  msg : String,
  op_const : @terms.Term,
  fm : @terms.Term,
) -> (@terms.Term, @terms.Term) {
  match fm {
    App(App(op, lhs), rhs) if op_const == op => (lhs, rhs)
    _ => abort(msg)
  }
}

///|
/// Decompose an equation `l = r` into its left and right sides.
pub fn BoolSyntax::dest_eq(fm : @terms.Term) -> (@terms.Term, @terms.Term) {
  boolsyntax_dest_binop("dest_eq", BoolSyntax::equality(), fm)
}

///|
/// Decompose an implication `p ==> q` into its antecedent and consequent.
pub fn BoolSyntax::dest_imp(fm : @terms.Term) -> (@terms.Term, @terms.Term) {
  boolsyntax_dest_binop("dest_imp", BoolSyntax::implication(), fm)
}

///|
/// Decompose a universal quantification `forall x. body` into the bound variable and body.
pub fn BoolSyntax::dest_forall(fm : @terms.Term) -> (@terms.Term, @terms.Term) {
  boolsyntax_dest_binop("dest_forall", BoolSyntax::universal(), fm)
}

///|
/// Decompose an existential quantification `exist x. body` into the bound variable and body.
pub fn BoolSyntax::dest_exists(fm : @terms.Term) -> (@terms.Term, @terms.Term) {
  boolsyntax_dest_binop("dest_exists", BoolSyntax::existential(), fm)
}

///|
/// Decompose a unique existence `?! x. body` into the bound variable and body.
pub fn BoolSyntax::dest_ex_unique(fm : @terms.Term) -> (@terms.Term, @terms.Term) {
  boolsyntax_dest_binop("dest_ex_unique", BoolSyntax::ex_unique(), fm)
}

///|
/// Decompose a conjunction `p /\ q` into its two conjuncts.
pub fn BoolSyntax::dest_conj(fm : @terms.Term) -> (@terms.Term, @terms.Term) {
  boolsyntax_dest_binop("dest_conj", BoolSyntax::conjunction(), fm)
}

///|
/// Decompose a disjunction `p \/ q` into its two disjuncts.
pub fn BoolSyntax::dest_disj(fm : @terms.Term) -> (@terms.Term, @terms.Term) {
  boolsyntax_dest_binop("dest_disj", BoolSyntax::disjunction(), fm)
}

///|
/// BUG FIX: The SML original returns `fm` (the whole negation `~ p`) here,
/// but that is inconsistent with every other destructor in this file:
///   dest_eq(= l r)   returns (l, r)  -- the inner operands
///   dest_imp(==> p q) returns (p, q) -- the inner operands
///   dest_conj(/\ p q) returns (p, q) -- the inner operands
/// By analogy, dest_neg(~ p) should return p (the inner term), not `~ p`.
/// The mk/dest roundtrip property also requires dest_neg(mk_neg(p)) == p.
/// Decompose a negation `~ p`, returning the inner term `p`.
pub fn BoolSyntax::dest_neg(fm : @terms.Term) -> @terms.Term {
  match fm {
    App(op, inner) if BoolSyntax::negation() == op => inner
    _ => abort("dest_neg")
  }
}

///|
test "BoolSyntax: negation" {
  let bool_ty = @types.bool_ty()
  let p = @terms.mk_var("p", bool_ty)
  let neg = BoolSyntax::mk_neg(p)
  assert_true(BoolSyntax::is_neg(neg) && neg.is_bool())
  let inner = BoolSyntax::dest_neg(neg)
  assert_true(inner == p)
}

///|
// `is_binop` / `is_app_match` pattern: predicates check whether a term's
// head constant matches the expected connective without destructing.
fn boolsyntax_is_app_match(c : @terms.Term, tm : @terms.Term) -> Bool {
  match tm {
    App(h, _) => c == h
    _ => false
  }
}

///|
fn boolsyntax_is_binop(op_const : @terms.Term, fm : @terms.Term) -> Bool {
  match fm {
    App(h, _) => boolsyntax_is_app_match(op_const, h)
    _ => false
  }
}

///|
/// Test whether a term is an equation `l = r`.
pub fn BoolSyntax::is_eq(fm : @terms.Term) -> Bool {
  boolsyntax_is_binop(BoolSyntax::equality(), fm)
}

///|
/// Test whether a term is an implication `p ==> q`.
pub fn BoolSyntax::is_imp(fm : @terms.Term) -> Bool {
  boolsyntax_is_binop(BoolSyntax::implication(), fm)
}

///|
/// Test whether a term is a universal quantification `forall x. body`.
pub fn BoolSyntax::is_forall(fm : @terms.Term) -> Bool {
  boolsyntax_is_binop(BoolSyntax::universal(), fm)
}

///|
/// Test whether a term is an existential quantification `exist x. body`.
pub fn BoolSyntax::is_exists(fm : @terms.Term) -> Bool {
  boolsyntax_is_binop(BoolSyntax::existential(), fm)
}

///|
/// Test whether a term is a unique existence quantification `?! x. body`.
pub fn BoolSyntax::is_ex_unique(fm : @terms.Term) -> Bool {
  boolsyntax_is_binop(BoolSyntax::ex_unique(), fm)
}

///|
/// Test whether a term is a conjunction `p /\ q`.
pub fn BoolSyntax::is_conj(fm : @terms.Term) -> Bool {
  boolsyntax_is_binop(BoolSyntax::conjunction(), fm)
}

///|
/// Test whether a term is a disjunction `p \/ q`.
pub fn BoolSyntax::is_disj(fm : @terms.Term) -> Bool {
  boolsyntax_is_binop(BoolSyntax::disjunction(), fm)
}

///|
/// Test whether a term is a negation `~ p`.
pub fn BoolSyntax::is_neg(fm : @terms.Term) -> Bool {
  boolsyntax_is_app_match(BoolSyntax::negation(), fm)
}
