// Utility library.
//
// `mergesort` is used throughout the prover to sort and deduplicate
// free-variable lists and type-variable lists.  When `unique` is true,
// adjacent duplicates are removed after sorting, producing a canonical
// set representation as a sorted array.

///|
/// Sort an array, optionally removing duplicates.
///
/// When `unique` is true, adjacent duplicates are eliminated after sorting,
/// producing a canonical set representation as a sorted array. This is used
/// throughout the prover to normalize free-variable and type-variable lists.
pub fn[A : Compare] dedup_sort(xs : Array[A]) -> Array[A] {
  let ys = xs.copy()
  ys.sort()

  let out : Array[A] = []
  for x in ys {
    match out.last() {
      Some(prev) => if prev != x { out.push(x) }
      None => out.push(x)
    }
  }
  out
}
