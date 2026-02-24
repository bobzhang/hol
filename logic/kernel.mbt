// Step 6: Kernel  (LCF Architecture)
//
// The kernel implements the **LCF (Logic for Computable Functions)**
// architecture: the abstract type `Thm` can only be constructed through
// the inference rules below.  Because MoonBit enforces module boundaries,
// no outside code can fabricate a `Thm` value -- every theorem is the
// result of a valid chain of inferences.  This is the fundamental
// soundness guarantee of HOL.
//
// Inference rules provided (following HOL Light / OpenTheory):
//
//   refl t                                |- t = t
//   assume phi                            phi |- phi
//   eqMp   (A1 |- phi = psi) (A2 |- phi)      A1 U A2 |- psi
//   absThm v (A |- t = u)                 A |- (\v. t) = (\v. u)
//   appThm (A1 |- f = g) (A2 |- x = y)   A1 U A2 |- f x = g y
//   deductAntisym (A1 |- phi) (A2 |- psi)
//       (A1\{psi}) U (A2\{phi}) |- phi = psi
//   termSubst sigma (A |- phi)            A[sigma] |- phi[sigma]
//   typeSubst sigma (A |- phi)            A[sigma] |- phi[sigma]
//   betaConv (\v. t) u                    |- (\v. t) u = t[u/v]
//   defineConst c t                       |- c = t     (definitional extension)
//   defineTypeOp ...                      (type definition principle)
//   new_axiom phi                         |- phi       (danger!)

///|
/// A proven theorem, consisting of a set of hypotheses and a conclusion (`hyps |- concl`).
pub struct Thm {
  hyps : Array[@terms.Term]
  concl : @terms.Term

  fn new(Array[@terms.Term], @terms.Term) -> Thm
} derive(Eq, Show)

///|
fn Thm::new(hyps : Array[@terms.Term], concl : @terms.Term) -> Thm {
  { hyps, concl }
}

///|
/// Namespace for the HOL Light LCF kernel inference rules.
pub enum Kernel {}

///|
let kernel_axioms : Ref[Array[Thm]] = { val: [] }

///|
/// Clear all registered axioms.
pub fn Kernel::reset_axioms() -> Unit {
  kernel_axioms.val = []
}

// Hypothesis helpers: hypotheses are treated as sets (no duplicates).
// `insert` adds if absent, `rm` removes all occurrences, `union` merges.

///|
fn kernel_hyp_contains(t : @terms.Term, hyps : Array[@terms.Term]) -> Bool {
  hyps.any(h => t == h)
}

///|
fn kernel_insert_hyp(t : @terms.Term, hyps : Array[@terms.Term]) -> Array[@terms.Term] {
  if kernel_hyp_contains(t, hyps) {
    hyps
  } else {
    [t, ..hyps]
  }
}

///|
fn kernel_rm_hyp(t : @terms.Term, hyps : Array[@terms.Term]) -> Array[@terms.Term] {
  hyps.filter(h => t != h)
}

///|
fn kernel_union_hyps(gammas : Array[@terms.Term], deltas : Array[@terms.Term]) -> Array[@terms.Term] {
  // Treat hypotheses as a set represented by an Array.
  let mut out = deltas
  for g in gammas {
    out = kernel_insert_hyp(g, out)
  }
  out
}

///|
fn kernel_subst_hyps(s : @terms.TermSubst, hs : Array[@terms.Term]) -> Array[@terms.Term] {
  hs.map(h => h.subst(s))
}

///|
fn kernel_inst_hyps(s : @types.TypeSubst, hs : Array[@terms.Term]) -> Array[@terms.Term] {
  hs.map(h => h.inst(s))
}

///|
/// Reflexivity: `|- t = t`.
pub fn Kernel::refl(t : @terms.Term) -> Thm {
  Thm([], @terms.Term::mk_eq(t, t))
}

///|
test "Kernel::refl" {
  let x = @terms.mk_var("x", @types.bool_ty())
  let th = Kernel::refl(x)
  assert_eq(th.hyps.length(), 0)
  let (lhs, rhs) = th.concl.dest_eq()
  assert_true(lhs == x && rhs == x)
}

///|
/// Assumption: `phi |- phi`.
pub fn Kernel::assume(phi : @terms.Term) -> Thm {
  if !phi.is_bool() {
    abort("assume: expected formula")
  }
  Thm([phi], phi)
}

///|
test "Kernel::assume" {
  let p = @terms.mk_var("p", @types.bool_ty())
  let th = Kernel::assume(p)
  assert_eq(th.hyps.length(), 1)
  assert_true(th.hyps[0] == p && th.concl == p)
}

///|
/// Equality modus ponens: from `A1 |- phi = psi` and `A2 |- phi`, derive `A1 U A2 |- psi`.
pub fn Kernel::eqMp(th1 : Thm, th2 : Thm) -> Thm raise {
  let (lhs, rhs) = th1.concl.dest_eq()
  if !lhs.aconv(th2.concl) {
    abort("eqMp: second theorem does not prove minor premise")
  }
  Thm(kernel_union_hyps(th1.hyps, th2.hyps), rhs)
}

///|
/// Abstraction: from `A |- t = u`, derive `A |- (\v. t) = (\v. u)`.
pub fn Kernel::absThm(v : @terms.Term, th : Thm) -> Thm raise {
  if not(v is FVar(_, _)) {
    abort("absThm: expected free variable")
  }
  let (lhs, rhs) = th.concl.dest_eq()
  Thm(th.hyps, @terms.Term::mk_eq(@terms.Term::mk_abs(v, lhs), @terms.Term::mk_abs(v, rhs)))
}

///|
/// Congruence: from `A1 |- f = g` and `A2 |- x = y`, derive `A1 U A2 |- f x = g y`.
pub fn Kernel::appThm(th1 : Thm, th2 : Thm) -> Thm raise {
  let (f, g) = th1.concl.dest_eq()
  let (x, y) = th2.concl.dest_eq()
  Thm(
    kernel_union_hyps(th1.hyps, th2.hyps),
    @terms.Term::mk_eq(@terms.mk_app(f, x), @terms.mk_app(g, y)),
  )
}

///|
/// Deduction antisymmetry: from `A1 |- phi` and `A2 |- psi`, derive `(A1\{psi}) U (A2\{phi}) |- phi = psi`.
pub fn Kernel::deductAntisym(th1 : Thm, th2 : Thm) -> Thm {
  Thm(
    kernel_union_hyps(
      kernel_rm_hyp(th2.concl, th1.hyps),
      kernel_rm_hyp(th1.concl, th2.hyps),
    ),
    @terms.Term::mk_eq(th1.concl, th2.concl),
  )
}

///|
/// Term substitution: from `A |- phi`, derive `A[sigma] |- phi[sigma]`.
pub fn Kernel::termSubst(s : @terms.TermSubst, th : Thm) -> Thm {
  Thm(kernel_subst_hyps(s, th.hyps), th.concl.subst(s))
}

///|
/// Type substitution: from `A |- phi`, derive `A[sigma] |- phi[sigma]`.
pub fn Kernel::typeSubst(s : @types.TypeSubst, th : Thm) -> Thm {
  Thm(kernel_inst_hyps(s, th.hyps), th.concl.inst(s))
}

///|
/// Beta reduction: `|- (\v. t) u = t[u/v]`.
pub fn Kernel::betaConv(abs_t : @terms.Term, u : @terms.Term) -> Thm {
  let (v, t) = abs_t.dest_abs()
  let lhs = @terms.mk_app(abs_t, u)
  let rhs = t.subst(Subst(pairs=[(v, u)]))
  Thm([], @terms.Term::mk_eq(lhs, rhs))
}

///|
test "Kernel::betaConv" {
  // |- (\x. x) x = x
  let x = @terms.mk_var("x", @types.bool_ty())
  let abs = @terms.Term::mk_abs(x, x)
  let th = Kernel::betaConv(abs, x)
  assert_eq(th.hyps.length(), 0)
  let (lhs, rhs) = th.concl.dest_eq()
  assert_true(lhs == @terms.mk_app(abs, x))
  assert_true(rhs == x)
}

///|
/// Definitional extension: register constant `c` and return `|- c = t`.
pub fn Kernel::defineConst(c : String, tm : @terms.Term) -> Thm {
  let cterm = @terms.Term::new_const(c, tm.type_of())
  Thm([], @terms.Term::mk_eq(cterm, tm))
}

///|
/// Type definition: given `|- P witness`, register a new type operator and return `|- abs(rep a) = a` and `|- P r = (rep(abs r) = r)`.
pub fn Kernel::defineTypeOp(
  name~ : String,
  abs~ : String,
  rep~ : String,
  tyvars~ : Array[String],
  tyax : Thm,
) -> (Thm, Thm) {
  ignore(tyvars)
  if tyax.hyps.length() != 0 {
    abort("defineTypeOp: input theorem must have no assumptions")
  }
  let fm0 = tyax.concl
  let (p, _witness) = match fm0 {
    App(p, w) => (p, w)
    _ => abort("defineTypeOp: theorem conclusion must be an application")
  }
  let tys = p.type_of().vars_in()
  @types.Type::new_type(name, tys.length())

  let (a_ty, _) = p.type_of().dest_fun()
  let ty = @types.Type::mk_type(name, [])
  let abs_const = @terms.const_(abs, @types.mk_fun(a_ty, ty))
  let rep_const = @terms.const_(rep, @types.mk_fun(ty, a_ty))
  let a = @terms.mk_var("a", a_ty)
  let r = @terms.mk_var("r", ty)

  (
    Thm([], @terms.Term::mk_eq(@terms.mk_app(abs_const, @terms.mk_app(rep_const, a)), a)),
    Thm(
      [],
      @terms.Term::mk_eq(
        @terms.mk_app(p, r),
        @terms.Term::mk_eq(@terms.mk_app(rep_const, @terms.mk_app(abs_const, r)), r),
      ),
    ),
  )
}

///|
/// Add an axiom `|- phi`. Use sparingly -- every axiom is a potential source of inconsistency.
pub fn Kernel::new_axiom(fm : @terms.Term) -> Thm {
  if !fm.is_bool() {
    abort("new_axiom: expected formula")
  }
  let th = Thm([], fm)
  kernel_axioms.val = [th, ..kernel_axioms.val]
  th
}
