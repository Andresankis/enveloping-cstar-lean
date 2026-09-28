# Formalizing the Enveloping C*-Algebra in Lean 4

This repository contains a Lean 4 formalization of:

1. The GNS construction for a unital *-algebra over ℂ.
2. The C*-identity for the maximal seminorm on a *-algebra.
3. The enveloping C*-algebra `C*(A)` and its universal property.

## Main results

All results are in `Collatz/State_A.lean`:

- `AlgState.gns_cyclic_inner` — the fundamental identity of the GNS construction.
- `AlgState.maximalSeminorm_cstar` — the C*-identity for the maximal seminorm.
- `AlgState.CStarAlgebra (envelopingCStar A)` — the C*-algebra structure on the completion of `A`.
- `AlgState.envelopingCStar_universal` — the universal property of the enveloping C*-algebra.

## Requirements

- Lean 4: `v4.35.0-rc3`
- Mathlib: `v4.35.0-rc3`

## Build

```bash
lake exe cache get
lake build Collatz.State_A
