///|
fn term_pp_lookup(i : Int, names : Array[String]) -> String {
  match names.get(i) {
    Some(x) => x
    None => abort("pprint: cannot find name for bound variable")
  }
}

///|
fn term_pprint_iter(m : Term, names : Array[String]) -> String {
  match m {
    FVar(x, _) => x
    BVar(i) => term_pp_lookup(i, names)
    Const(c, _) => c
    App(p, q) => "\{term_pprint_iter(p, names)} \{term_pprint_iter(q, names)}"
    Abs(FVar(x, _), body) => "(\\\{x}. \{term_pprint_iter(body, [x, ..names])})"
    Abs(x, body) =>
      "(\\\{term_pprint_iter(x, names)}. \{term_pprint_iter(body, names)})"
  }
}

///|
/// Pretty-print the term followed by its type annotation, rendering bound variables by name and omitting internal constructors.
pub fn Term::pprint(self : Term) -> String {
  "\{term_pprint_iter(self, [])} :: \{self.type_of().pprint()}"
}

///|
test "Term: pprint" {
  Term::reset_table()
  let bool_ty = @types.bool_ty()
  let x = mk_var("x", bool_ty)
  let y = mk_var("y", bool_ty)
  inspect(x.pprint(), content="x :: bool")
  inspect(
    Term::mk_abs(x, x).pprint(),
    content=(
      #|(\x. x) :: bool --> bool
    ),
  )
  inspect(Term::mk_eq(x, y).pprint(), content="= x y :: bool")
}
