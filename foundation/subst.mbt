// Step 1: Substitutions
//
// Substitutions are central to HOL: they are used for type instantiation
// (Type -> Type), term-variable replacement (Term -> Term), and matching
// (building a mapping from pattern variables to concrete terms/types).
//
// A substitution is represented as a list of (redex, residue) pairs.  The
// SML original uses `('a * 'b) list`; here we use `@list.List[(A, B)]`.
// New bindings are prepended (`add`), so lookup finds the most recently
// added mapping first, giving natural shadowing semantics.

///|
/// An immutable substitution mapping keys of type `A` to values of type `B`, represented as an association list with most-recent-first lookup.
pub struct Subst[A, B] {
  priv items : @list.List[(A, B)]

  fn[A, B] new(pairs? : ArrayView[(A, B)]) -> Subst[A, B]
} derive(Debug)

///|
fn[A, B] Subst::new(pairs? : ArrayView[(A, B)] = []) -> Subst[A, B] {
  { items: @list.from_array(pairs) }
}

///|
/// Test whether the substitution contains no bindings.
pub fn[A, B] Subst::is_empty(self : Subst[A, B]) -> Bool {
  self.items.is_empty()
}

///|
/// Test whether `x` appears as a redex in the substitution.
pub fn[A : Eq, B] Subst::contains(self : Subst[A, B], x : A) -> Bool {
  self.items.any(pair => {
    let (y, _) = pair
    x == y
  })
}

///|
/// Extend the substitution with a new (redex, residue) binding.
///
/// The new binding is prepended so that `lookup` finds the most recently
/// added mapping first, giving natural shadowing semantics.
pub fn[A, B] Subst::add(
  self : Subst[A, B],
  redex : A,
  residue : B,
) -> Subst[A, B] {
  // Prepend so lookup finds the most recently added mapping first.
  { items: @list.cons((redex, residue), self.items) }
}

///|
/// Iterate over the (redex, residue) bindings.
pub fn[A, B] Subst::iter(self : Subst[A, B]) -> Iter[(A, B)] {
  self.items.iter()
}

///|
/// Look up the residue bound to `x`, returning `None` if `x` is not in
/// the domain. Finds the most recently added binding due to prepend order.
pub fn[A : Eq, B] Subst::lookup(self : Subst[A, B], x : A) -> B? {
  for pair in self.items {
    let (k, v) = pair
    if k == x {
      return Some(v)
    }
  }
  None
}
