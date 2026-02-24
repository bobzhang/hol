///|
// Polymorphic equality `= : 'a -> 'a -> bool` is the single primitive
// constant in HOL Light's approach.  All other connectives and quantifiers
// are defined in terms of equality (see `bool_syntax.mbt`).
fn equality_term() -> Term {
  Const(
    "=",
    @types.mk_fun(
      @types.mk_var("'a"),
      @types.mk_fun(@types.mk_var("'a"), @types.bool_ty()),
    ),
  )
}

///|
/// Build the partially applied equality `(=) : ty -> ty -> bool` instantiated
/// at `self`'s type, then apply it to `self`, yielding a term of type
/// `ty -> bool`.  Used by derived equality rules.
pub fn Term::curry_eq(self : Term) -> Term {
  let a = @types.mk_var("'a")
  let t1 = self.type_of()
  let sigma : @types.TypeSubst = Subst(pairs=[(a, t1)])
  mk_app(equality_term().inst(sigma), self)
}

///|
/// Build the equation `lhs = rhs`, checking that both sides have the same type and instantiating the polymorphic equality constant accordingly.
pub fn Term::mk_eq(lhs : Term, rhs : Term) -> Term {
  let a = @types.mk_var("'a")
  let t1 = lhs.type_of()
  if t1 != rhs.type_of() {
    abort("mk_eq: lhs and rhs have different types")
  }
  let sigma : @types.TypeSubst = Subst(pairs=[(a, t1)])
  let head = mk_app(equality_term().inst(sigma), lhs)
  mk_app(head, rhs)
}

///|
/// Test whether the term is an equation of the form `l = r`.
pub fn Term::is_eq(tm : Term) -> Bool {
  match tm {
    App(App(Const(c, _), _), _) => c == "="
    _ => false
  }
}

///|
/// Decompose an equation into its left- and right-hand sides, aborting if the term is not an equation.
pub fn Term::dest_eq(tm : Term) -> (Term, Term) raise {
  match tm {
    App(App(c, lhs), rhs) => {
      ignore(
        equality_term()
        .type_of()
        .match_type(c.type_of(), { subst: Subst(), tyvars: [] }),
      )
      (lhs, rhs)
    }
    _ => abort("dest_eq: expected equation")
  }
}

///|
test "Term: mk_eq / is_eq / dest_eq" {
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let y = mk_var("y", bool_ty)
  let eq = Term::mk_eq(x, y)
  assert_true(Term::is_eq(eq) && eq.is_bool())
  assert_false(Term::is_eq(x))
  let (lhs, rhs) = eq.dest_eq()
  assert_true(lhs == x && rhs == y)
}
