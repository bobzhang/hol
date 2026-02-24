///|
// Global signature of constants.  The only primitive constant is polymorphic
// equality `= : 'a -> 'a -> bool` (the HOL Light approach).  All other
// connectives (==>, /\, forall, etc.) are defined on top of equality.
let initial_const_table : @sorted_map.SortedMap[String, @types.Type] = @sorted_map.new().add(
  "=",
  @types.mk_fun(
    @types.mk_var("'a"),
    @types.mk_fun(@types.mk_var("'a"), @types.bool_ty()),
  ),
)

///|
let const_table : Ref[@sorted_map.SortedMap[String, @types.Type]] = {
  val: initial_const_table,
}

///|
// Checkpoints let steps/tests extend definitions and then roll back.
let checkpoint_const_table : Ref[@sorted_map.SortedMap[String, @types.Type]] = {
  val: initial_const_table,
}

///|
/// Reset the global constant table to the most recent checkpoint, discarding any constants registered since then.
pub fn Term::reset_table() -> Unit {
  const_table.val = checkpoint_const_table.val
}

