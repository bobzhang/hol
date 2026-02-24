///|
/// The result of pattern matching a term: a pair of a term substitution and a type substitution that, when applied to the pattern, yield the observation.
pub type TermMatchResult = (TermSubst, @types.TypeSubst)

///|
fn term_lookup_match(x : Term, ids : Array[Term], s : TermSubst) -> Term? {
  match s.lookup(x) {
    Some(v) => Some(v)
    None => if ids.contains(x) { Some(x) } else { None }
  }
}

///|
fn term_free_under(m : Term, depth : Int) -> Bool {
  match m {
    BVar(i) => i < depth
    App(p, q) => term_free_under(p, depth) && term_free_under(q, depth)
    Abs(_, n) => term_free_under(n, depth + 1)
    _ => true
  }
}

///|
fn term_bound_by_scoped(scoped : Bool, m : Term) -> Bool {
  scoped && !term_free_under(m, 0)
}

///|
// FIXME(upstream): TermMatchResult goto-def does not work
fn term_raw_match_rec(
  pat : Term,
  ob : Term,
  scoped : Bool,
  tm_fixed : Array[Term],
  ty_fixed : Array[@types.Type],
  tm_s : TermSubst,
  ty_s : @types.TypeSubst,
) -> TermMatchResult raise {
  // Core Step 4 matcher: accumulate term/type substitutions while rejecting
  // bindings that would capture scoped bound variables.
  match (pat, ob) {
    (FVar(_, ty) as v, tm) => {
      if term_bound_by_scoped(scoped, tm) {
        abort("match_term: attempt to capture bound variable")
      }
      let next_tm_s = match term_lookup_match(v, tm_fixed, tm_s) {
        None => if v == tm { tm_s } else { tm_s.add(v, tm) }
        Some(tm2) =>
          if tm2.aconv(tm) {
            tm_s
          } else {
            abort("match_term: double bind on variable")
          }
      }
      let next_ty_state = ty.match_type(tm.type_of(), {
        subst: ty_s,
        tyvars: ty_fixed,
      })
      (next_tm_s, next_ty_state.subst)
    }
    (Const(c1, ty1), Const(c2, ty2)) => {
      if c1 != c2 {
        abort("match_term: different constants")
      }
      let next_ty_state = ty1.match_type(ty2, { subst: ty_s, tyvars: ty_fixed })
      (tm_s, next_ty_state.subst)
    }
    (Abs(FVar(_, ty1), m), Abs(FVar(_, ty2), n)) => {
      let next_ty_state = ty1.match_type(ty2, { subst: ty_s, tyvars: ty_fixed })
      term_raw_match_rec(
        m,
        n,
        true,
        tm_fixed,
        ty_fixed,
        tm_s,
        next_ty_state.subst,
      )
    }
    (App(m, n), App(p, q)) => {
      let (tm_s2, ty_s2) = term_raw_match_rec(
        m, p, scoped, tm_fixed, ty_fixed, tm_s, ty_s,
      )
      term_raw_match_rec(n, q, scoped, tm_fixed, ty_fixed, tm_s2, ty_s2)
    }
    (BVar(i), BVar(j)) =>
      if i == j {
        (tm_s, ty_s)
      } else {
        abort("match_term: bound variable mismatch")
      }
    _ => abort("match_term: different constructors")
  }
}

///|
/// Match a pattern term against an observation term, extending the given substitution state while keeping the specified type and term variables fixed.
fn Term::raw_match(
  ty_fixed : Array[@types.Type],
  tm_fixed : Array[Term],
  pat : Term,
  ob : Term,
  state : TermMatchResult,
) -> TermMatchResult raise {
  let (tm_s, ty_s) = state
  term_raw_match_rec(pat, ob, false, tm_fixed, ty_fixed, tm_s, ty_s)
}

///|
fn term_normalize_subst(res : TermMatchResult) -> TermMatchResult {
  let (tm_s, ty_s) = res
  let mut norm : TermSubst = Subst()
  for pair in tm_s {
    let (old, new) = pair
    let old2 = old.inst(ty_s)
    if old2 != new {
      norm = norm.add(old2, new)
    }
  }
  (norm, ty_s)
}

///|
/// Match a pattern against an observation with the given fixed variables, returning normalized term and type substitutions with identity bindings removed.
fn Term::matches(
  vars : Array[Term],
  tyvars : Array[@types.Type],
  pat : Term,
  ob : Term,
) -> TermMatchResult raise {
  term_normalize_subst(
    Term::raw_match(tyvars, vars, pat, ob, (Subst(), Subst())),
  )
}

///|
/// First-order pattern matching: find substitutions `(sigma, tau)` such that
/// `self.subst(sigma).inst(tau) == ob`.
///
/// `self` is the pattern and `ob` is the observation (concrete term).  Free
/// variables in the pattern act as match variables — each one is bound to the
/// corresponding sub-term of `ob`.  Constants must match exactly (name and
/// compatible type).  Bound variables (de Bruijn indices) must be identical.
///
/// Returns a `TermMatchResult = (TermSubst, TypeSubst)`:
/// - The term substitution maps pattern variables to their matched sub-terms.
/// - The type substitution maps type variables in the pattern to concrete types.
///   Identity bindings (variable mapped to itself) are removed.
///
/// Aborts if the pattern cannot match the observation (structural mismatch,
/// inconsistent variable binding, or type mismatch).
pub fn Term::match_term(self : Term, ob : Term) -> TermMatchResult raise {
  Term::matches([], [], self, ob)
}

///|
test "Term: match_term variable against constant" {
  let a = @types.mk_var("'a")
  let bool_ty = @types.bool_ty()
  ignore(Term::new_const("c_mt", a))
  let pat = mk_var("x", bool_ty)
  let ob = Term::mk_const("c_mt", bool_ty)
  // A variable pattern matches any term of compatible type
  let (tm_s, _ty_s) = pat.match_term(ob)
  assert_true(tm_s.lookup(pat) == Some(ob))
}

///|
test "Term: match_term application" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let y = mk_var("y", bool_ty)
  let p = mk_var("p", bool_ty)
  let q = mk_var("q", bool_ty)
  // Pattern: (x y), Observation: (p q)
  // Each pattern variable binds to the corresponding sub-term
  let pat = mk_app(x, y)
  let ob = mk_app(p, q)
  let (tm_s, _) = pat.match_term(ob)
  assert_true(tm_s.lookup(x) == Some(p))
  assert_true(tm_s.lookup(y) == Some(q))
}

///|
test "Term: match_term identical terms produce empty substitution" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  // When pattern and observation are the same variable, the binding is
  // an identity and gets normalized away
  let (tm_s, ty_s) = x.match_term(x)
  assert_eq([..tm_s].length(), 0)
  assert_eq([..ty_s].length(), 0)
}

///|
test "Term: match_term with polymorphic type instantiation" {
  let a = @types.mk_var("'a")
  let bool_ty = @types.bool_ty()
  // Pattern variable has polymorphic type 'a; observation has type bool
  // The type substitution should bind 'a := bool
  let pat = mk_var("x", a)
  let ob = mk_var("y", bool_ty)
  let (tm_s, ty_s) = pat.match_term(ob)
  assert_true(tm_s.lookup(pat.inst(ty_s)) == Some(ob))
  assert_true(ty_s.lookup(a) == Some(bool_ty))
}

///|
test "Term: match_term abstractions match structurally" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let y = mk_var("y", bool_ty)
  // (\x. x) matches (\y. y) — bound structure is identical (both BVar(0))
  let pat = Term::mk_abs(x, x)
  let ob = Term::mk_abs(y, y)
  let (tm_s, ty_s) = pat.match_term(ob)
  // No free variables to bind in either pattern or observation
  assert_eq([..tm_s].length(), 0)
  assert_eq([..ty_s].length(), 0)
}
