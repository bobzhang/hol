///|
/// Type-constructor environment mapping names to their arities.
pub type Env = @sorted_map.SortedMap[String, Int]

///|
// The initial registry contains two primitive types:
//
// - `bool` (arity 0): the type of propositions.
// - `ind`  (arity 0): the type of individuals, an axiomatically infinite type
//   required by the axiom of infinity so that natural numbers and other
//   infinite structures can be modelled within the logic.
let initial_type_table : Env = Env::from_array([("bool", 0), ("ind", 0)])

///|
// Checkpoint/restore for the type registry.  Checkpoints snapshot the
// current table so that `reset_table` can roll back extensions made
// during tests or exploratory definitions.
let checkpoint_type_table : Ref[Env] = { val: initial_type_table }

///|
let type_table : Ref[Env] = { val: initial_type_table }
