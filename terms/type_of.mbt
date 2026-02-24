///|
fn term_lookup_bvar(i : Int, tys : Array[@types.Type]) -> @types.Type {
  match tys.get(i) {
    Some(ty) => ty
    None => abort("type_of: cannot find binder type")
  }
}

///|
/// Infer the type of a term by recursively traversing its structure.
pub fn Term::type_of(self : Term) -> @types.Type {
  fn go(m : Term, bvars : Array[@types.Type]) -> @types.Type {
    match m {
      FVar(_, ty) => ty
      Const(_, ty) => ty
      BVar(i) => term_lookup_bvar(i, bvars)
      App(rator, _) => go(rator, bvars).range()
      Abs(FVar(_, ty), body) => @types.mk_fun(ty, go(body, [ty, ..bvars]))
      _ => abort("type_of: malformed abstraction")
    }
  }

  go(self, [])
}

///|
/// Test whether the term has boolean type.
pub fn Term::is_bool(self : Term) -> Bool {
  @types.bool_ty() == self.type_of()
}
