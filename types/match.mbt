///|
/// The state carried during type matching: a pair of the current substitution 
/// and the list of identity-bound type variables.
pub(all) struct TypeMatchState {
  subst : TypeSubst
  tyvars : Array[Type]
}

///|
fn type_match_lookup(x : Type, state : TypeMatchState) -> Type? {
  match state.subst.lookup(x) {
    Some(v) => Some(v)
    None => if state.tyvars.contains(x) { Some(x) } else { None }
  }
}

///|
/// Step 4 algorithm: walk pattern and observation in lockstep while carrying
/// (current substitution, fixed identities).
fn type_match_impl(
  pats : ArrayView[Type],
  obs : ArrayView[Type],
  state : TypeMatchState,
) -> TypeMatchState raise {
  match (pats, obs) {
    ([], []) => state
    ([], _) | (_, []) => fail("match: different constructors")
    ([pat, .. rest_pats], [ob, .. rest_obs]) =>
      match (pat, ob) {
        (TyVar(_) as v, ty) => {
          let next_state = match type_match_lookup(v, state) {
            None =>
              if v == ty {
                { ..state, tyvars: [v, ..state.tyvars] }
              } else {
                { ..state, subst: state.subst.add(v, ty) }
              }
            Some(bound) =>
              if bound == ty {
                state
              } else {
                fail("match: double bind on type variable")
              }
          }
          type_match_impl(rest_pats, rest_obs, next_state)
        }
        (TyApp(c1, a1), TyApp(c2, a2)) => {
          if c1 != c2 {
            fail("match: attempt to match different type operators")
          }
          type_match_impl([..a1, ..rest_pats], [..a2, ..rest_obs], state)
        }
        _ => fail("match: different constructors")
      }
  }
}

///|
/// Match `self` as a pattern against `ob`, extending `state` with bindings so that applying the resulting substitution to the pattern yields `ob`.
pub fn Type::match_type(
  self : Type,
  ob : Type,
  state : TypeMatchState, // FIXME(upstream): goto def does not work
) -> TypeMatchState raise {
  type_match_impl([self], [ob], state)
}
