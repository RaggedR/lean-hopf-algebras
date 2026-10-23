/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import HopfAlgebras

/-!
# Certification

`#print axioms` on the headline results of the finite-operator-calculus
development. CI runs this file and fails if the output mentions `sorryAx` (a
`sorry` reached the result) or if any report is missing (a name that failed to
resolve — a vacuous "proof"). A clean report lists only Lean's foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`).

**Scope — honest PARTIAL.** The library root (`HopfAlgebras.lean`) builds seven
modules — `Basic`, `Umbral`, `BinomialType`, `Duality`, `DeltaOperator`,
`LagrangeInversion`, `UmbralOperator` — and their dependency trees do **not** reach
`HopfAlgebras/Transfer.lean`, which still holds three *stated but unproven* results
(`IsBasicSequence.natDegree_eq`, `.expand_coeff_consistent`, `.expand_in_basis` —
each a `sorry`, pending a degree-drop lemma that is currently private in Mathlib).
So the theorems certified below are genuinely `sorry`-free; `Transfer` is explicitly
out of scope and described as stated-only in the README.
-/

-- The additive (𝔾ₐ) bialgebra structure on polynomials.
#print axioms Polynomial.additiveBialgebra

-- The derivative is a delta operator (shift-equivariant, lowers degree by one).
#print axioms Polynomial.derivative_isDeltaOperator

-- X^n and the descending Pochhammer are sequences of binomial type.
#print axioms Polynomial.X_pow_isBinomialType
#print axioms Polynomial.descPochhammer_isBinomialType

-- Compositional inverse of a delta formal power series (Lagrange inversion).
#print axioms PowerSeries.compInv_subst
