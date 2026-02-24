// Natural numbers for HOL: type, constants, and axioms.
//
// This module registers the `nat` type constructor (arity 0) and four
// constants — `0 : nat`, `SUC : nat -> nat`, `plus : nat -> nat -> nat`,
// `mult : nat -> nat -> nat` — then postulates defining equations as axioms:
//
//   PLUS_0:    |- plus n 0 = n
//   PLUS_SUC:  |- plus n (SUC m) = SUC (plus n m)
//   MULT_0:    |- mult n 0 = 0
//   MULT_SUC:  |- mult n (SUC m) = plus (mult n m) n
//
// NOTE: A full HOL implementation would derive natural numbers via
// `defineTypeOp` and the axiom of infinity, then prove these equations
// as theorems.  Here we axiomatize them to keep the example focused on
// equational reasoning with the kernel primitives.

///|
/// Namespace for natural-number setup and proofs.
pub enum Nat {}

///|
/// The `nat` type.
fn nat_ty() -> @hol.Type {
  @hol.Type::mk_type("nat", [])
}

///|
/// The constant `0 : nat`.
fn zero() -> @hol.Term {
  @hol.const_("0", nat_ty())
}

///|
/// The constant `SUC : nat -> nat`.
fn suc() -> @hol.Term {
  @hol.const_("SUC", @hol.mk_fun(nat_ty(), nat_ty()))
}

///|
/// The constant `plus : nat -> nat -> nat`.
fn plus() -> @hol.Term {
  @hol.const_(
    "plus",
    @hol.mk_fun(nat_ty(), @hol.mk_fun(nat_ty(), nat_ty())),
  )
}

///|
/// The constant `mult : nat -> nat -> nat`.
fn mult() -> @hol.Term {
  @hol.const_(
    "mult",
    @hol.mk_fun(nat_ty(), @hol.mk_fun(nat_ty(), nat_ty())),
  )
}

///|
/// Build `SUC(t)`.
fn mk_suc(t : @hol.Term) -> @hol.Term {
  @hol.mk_app(suc(), t)
}

///|
/// Build `plus(a, b)`.
fn mk_plus(a : @hol.Term, b : @hol.Term) -> @hol.Term {
  @hol.mk_app(@hol.mk_app(plus(), a), b)
}

///|
/// Build `mult(a, b)`.
fn mk_mult(a : @hol.Term, b : @hol.Term) -> @hol.Term {
  @hol.mk_app(@hol.mk_app(mult(), a), b)
}

///|
/// Register `nat`, `0`, `SUC`, `plus`, `mult` and return the four axioms.
///
/// Resets type/term/axiom tables first to ensure a clean slate, then:
/// - registers type constructor `nat` (arity 0)
/// - registers constants `0`, `SUC`, `plus`, `mult`
/// - axiomatizes `plus n 0 = n` and `plus n (SUC m) = SUC (plus n m)`
/// - axiomatizes `mult n 0 = 0` and `mult n (SUC m) = plus (mult n m) n`
///
/// Returns `(PLUS_0, PLUS_SUC, MULT_0, MULT_SUC)`.
pub fn Nat::setup() -> (@hol.Thm, @hol.Thm, @hol.Thm, @hol.Thm) {
  @hol.Type::reset_table()
  @hol.Term::reset_table()
  @hol.Kernel::reset_axioms()
  // Register nat type
  @hol.Type::new_type("nat", 0)
  // Register constants
  ignore(@hol.Term::new_const("0", nat_ty()))
  ignore(@hol.Term::new_const("SUC", @hol.mk_fun(nat_ty(), nat_ty())))
  ignore(@hol.Term::new_const(
    "plus",
    @hol.mk_fun(nat_ty(), @hol.mk_fun(nat_ty(), nat_ty())),
  ))
  ignore(@hol.Term::new_const(
    "mult",
    @hol.mk_fun(nat_ty(), @hol.mk_fun(nat_ty(), nat_ty())),
  ))
  // Free variables for axioms
  let n = @hol.mk_var("n", nat_ty())
  let m = @hol.mk_var("m", nat_ty())
  // PLUS_0: |- plus n 0 = n
  let plus_0 = @hol.Kernel::new_axiom(@hol.Term::mk_eq(mk_plus(n, zero()), n))
  // PLUS_SUC: |- plus n (SUC m) = SUC (plus n m)
  let plus_suc = @hol.Kernel::new_axiom(
    @hol.Term::mk_eq(mk_plus(n, mk_suc(m)), mk_suc(mk_plus(n, m))),
  )
  // MULT_0: |- mult n 0 = 0
  let mult_0 = @hol.Kernel::new_axiom(
    @hol.Term::mk_eq(mk_mult(n, zero()), zero()),
  )
  // MULT_SUC: |- mult n (SUC m) = plus (mult n m) n
  let mult_suc = @hol.Kernel::new_axiom(
    @hol.Term::mk_eq(mk_mult(n, mk_suc(m)), mk_plus(mk_mult(n, m), n)),
  )
  (plus_0, plus_suc, mult_0, mult_suc)
}
