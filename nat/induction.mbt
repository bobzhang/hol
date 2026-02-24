// Structural induction on natural numbers.
//
// This is a trusted helper that validates the structure of a base case and
// inductive step, then returns the universally quantified property via
// `new_axiom`.
//
// NOTE: A full HOL implementation would derive the induction principle from
// `defineTypeOp` and the axiom of infinity.  Here we axiomatize it to keep
// the example focused on equational reasoning.

///|
/// Structural induction on natural numbers.
///
/// Given:
///   - `base`: `|- P[0/v]`           (base case, no hypotheses)
///   - `step`: `{P[v/v]} |- P[SUC(v)/v]`  (inductive step, IH as hypothesis)
///   - `v`: the induction variable (must have type `nat`)
///   - `prop`: the property `P` (with `v` free)
///
/// Returns: `|- P[v/v]`  (i.e. `|- P`, with `v` free = universally quantified)
///
/// Validates:
///   1. `base` has no hypotheses
///   2. `base.concl` equals `prop[0/v]`
///   3. `step` has exactly one hypothesis equal to `prop`
///   4. `step.concl` equals `prop[SUC(v)/v]`
pub fn Nat::induction(
  base~ : @hol.Thm,
  step~ : @hol.Thm,
  v~ : @hol.Term,
  prop~ : @hol.Term
) -> @hol.Thm {
  // Validate induction variable type
  guard v is FVar(_, ty) else {
    abort("induction: v must be a free variable")
  }
  if ty != nat_ty() {
    abort("induction: v must have type nat")
  }
  // 1. base has no hypotheses
  if base.hyps.length() != 0 {
    abort("induction: base case must have no hypotheses")
  }
  // 2. base.concl = prop[0/v]
  let base_expected = prop.subst(Subst(pairs=[(v, zero())]))
  if base.concl != base_expected {
    abort(
      "induction: base case conclusion does not match prop[0/v]\n  expected: \{base_expected}\n  got:      \{base.concl}",
    )
  }
  // 3. step has exactly one hypothesis equal to prop
  if step.hyps.length() != 1 {
    abort("induction: step must have exactly one hypothesis (the IH)")
  }
  if step.hyps[0] != prop {
    abort("induction: step hypothesis does not match prop")
  }
  // 4. step.concl = prop[SUC(v)/v]
  let step_expected = prop.subst(Subst(pairs=[(v, mk_suc(v))]))
  if step.concl != step_expected {
    abort(
      "induction: step conclusion does not match prop[SUC(v)/v]\n  expected: \{step_expected}\n  got:      \{step.concl}",
    )
  }
  // All checks pass — return the property as an axiom
  @hol.Kernel::new_axiom(prop)
}
