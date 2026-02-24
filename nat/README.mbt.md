# Natural Numbers and Associativity of Plus

A self-contained example proving `plus(plus(n,m),k) = plus(n,plus(m,k))` using
the HOL kernel primitives from `hol/`.

## What this demonstrates

The proof exercises the core equational reasoning engine:

| Kernel primitive | Role in the proof |
|---|---|
| `new_axiom` | Postulate PLUS_0, PLUS_SUC, and the induction principle |
| `termSubst` | Specialize axiom free variables to concrete terms |
| `assume` | Introduce the induction hypothesis |
| `appThm` (via `apTerm`) | Congruence: lift an equation under `SUC` or `plus(n,_)` |
| `refl` | Identity step inside `apTerm` and `trans` |
| `eqMp` | Core of `sym` and `trans` |

The derived rules `Equal::sym`, `Equal::trans`, and `Equal::apTerm` are
built entirely from these primitives, so the equational chain is sound
by construction.

## Approach: axioms vs full derivation

A full HOL Light implementation would:
1. Define `nat` via `defineTypeOp` + axiom of infinity (~200 lines)
2. Derive the recursion theorem to justify `plus` (~300 lines)
3. Derive the induction principle from the type definition (~100 lines)

Here we shortcut steps 1-3 with `new_axiom`, keeping the example focused
on equational reasoning.  The three axioms are:

- **PLUS_0**: `|- plus n 0 = n`
- **PLUS_SUC**: `|- plus n (SUC m) = SUC (plus n m)`
- **Induction**: validated structurally by `Nat::induction`, then
  discharged via `new_axiom`

## Proof structure

**Base case** (`k = 0`):
```
plus(plus(n,m), 0) = plus(n,m)             [PLUS_0]
plus(n, plus(m, 0)) = plus(n, m)           [PLUS_0 + congruence]
--------------------------------------------------------------
plus(plus(n,m), 0) = plus(n, plus(m, 0))   [trans + sym]
```

**Inductive step** (assuming IH for `k`, prove for `SUC(k)`):
```
plus(plus(n,m), SUC(k))
  = SUC(plus(plus(n,m), k))         [PLUS_SUC]
  = SUC(plus(n, plus(m, k)))        [IH under SUC]
  = plus(n, SUC(plus(m, k)))        [sym(PLUS_SUC)]
  = plus(n, plus(m, SUC(k)))        [sym(PLUS_SUC under plus(n,_))]
```

**Induction**: combines base and step to yield `|- plus(plus(n,m),k) = plus(n,plus(m,k))`
with `n`, `m`, `k` free (universally quantified).

## Files

| File | Purpose |
|---|---|
| `nat.mbt` | Register `nat` type, constants `0`/`SUC`/`plus`, axioms |
| `induction.mbt` | Structural induction helper (validates base/step, uses `new_axiom`) |
| `plus_assoc.mbt` | The associativity proof and tests |

