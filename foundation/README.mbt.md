# Foundation

Shared data structures used throughout the HOL prover.  This is the
lowest layer -- it has no dependencies on any other HOL sub-package.

## Overview

| Type | Role |
|------|------|
| `Subst[A, B]` | Substitution as a list of (redex, residue) pairs |

## Subst

A substitution is a list of `(redex, residue)` pairs.  New bindings are
prepended (`add`), so `lookup` finds the most recently added mapping
first, giving natural shadowing semantics.

Substitutions are used for:
- **Type instantiation** -- `Subst[Type, Type]` maps type variables to types
- **Term replacement** -- `Subst[Term, Term]` maps term variables to terms
- **Matching** -- building mappings from pattern variables to concrete values

```mbt check
///|
test "Subst: add, lookup, and shadowing" {
  let s : @foundation.Subst[String, Int] = Subst()
  assert_true(s.is_empty())

  let s2 = s.add("x", 1).add("y", 2)
  assert_eq(s2.lookup("x"), Some(1))
  assert_eq(s2.lookup("y"), Some(2))
  assert_eq(s2.lookup("z"), None)
  assert_true(s2.contains("x"))

  // Shadowing: a later binding for "x" wins
  let s3 = s2.add("x", 99)
  assert_eq(s3.lookup("x"), Some(99))
}
```

## mergesort

Sorts an array and optionally removes adjacent duplicates.  When
`unique` is `true`, the result is a canonical sorted set represented
as an array.  Used throughout the prover for free-variable lists and
type-variable lists.

```mbt check
///|
test "mergesort with deduplication" {
  let xs = [3, 1, 2, 1, 3]

  let unique = @foundation.dedup_sort(xs)
  assert_eq(unique, [1, 2, 3])
}
```
