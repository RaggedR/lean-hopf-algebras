/-
Copyright (c) 2025 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import HopfAlgebras.DeltaOperator
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Rising factorials are of binomial type

The rising factorial (ascending Pochhammer) sequence `ascPochhammer R n` is
of binomial type, proved via Rota's classification: it is the basic sequence
of the backward difference operator `∇f(x) = f(x) - f(x-1)`.

## Proof strategy

1. Define the backward difference `backwardDiff = id - taylor(-1)`
2. Show it is a delta operator
3. Show `ascPochhammer R n` is its basic sequence (lowering + normalization)
4. Apply `IsBasicSequence.isBinomialType`

## Main results

* `Polynomial.backwardDiff_isDeltaOperator`
* `Polynomial.ascPochhammer_isBasicSequence_backwardDiff`
* `Polynomial.ascPochhammer_isBinomialType`

## References

* Langer, R., *Determinantal bases and the symmetric group*, arXiv:0907.3950, §1.2.2
-/

noncomputable section

open Polynomial Finset

namespace Polynomial

variable {R : Type*} [CommRing R]

/-! ### Backward difference operator -/

/-- The backward difference operator `∇ f(x) = f(x) - f(x-1)`. -/
def backwardDiff : R[X] →ₗ[R] R[X] := LinearMap.id - taylor (-1 : R)

@[simp]
theorem backwardDiff_apply (p : R[X]) :
    backwardDiff p = p - taylor (-1 : R) p := by
  simp [backwardDiff]

@[simp]
theorem backwardDiff_X : backwardDiff (X : R[X]) = (1 : R[X]) := by
  simp [taylor_X]

@[simp]
theorem backwardDiff_C (r : R) : backwardDiff (C r : R[X]) = 0 := by
  simp [taylor_C]

/-- The backward difference is shift-equivariant. -/
theorem backwardDiff_isShiftEquivariant :
    IsShiftEquivariant (backwardDiff : R[X] →ₗ[R] R[X]) := by
  intro a
  apply LinearMap.ext; intro f
  simp only [LinearMap.comp_apply, backwardDiff_apply]
  -- Need: taylor a f - taylor(-1)(taylor a f) = taylor a (f - taylor(-1) f)
  rw [map_sub]
  congr 1
  -- taylor(-1)(taylor a f) = taylor a (taylor(-1) f)
  -- because taylor r (taylor s f) = taylor(r+s) f
  rw [taylor_taylor, taylor_taylor]
  ring_nf

/-- The backward difference is a delta operator. -/
theorem backwardDiff_isDeltaOperator :
    IsDeltaOperator (backwardDiff : R[X] →ₗ[R] R[X]) where
  shift_equivariant := backwardDiff_isShiftEquivariant
  kills_constants := backwardDiff_C
  unit_leading := by simp [coeff_one]

/-! ### Rising factorials as the basic sequence of the backward difference -/

/-- `taylor(-1)(ascPochhammer R (n+1)) = ascPochhammer R n * (X - 1)`.
This is `(x-1)x(x+1)...(x+n-1) = asc(n) * (X-1)`. -/
private theorem taylor_neg_one_ascPochhammer_succ (n : ℕ) :
    taylor (-1 : R) (ascPochhammer R (n + 1)) =
      ascPochhammer R n * (X - 1) := by
  -- taylor r f = f.comp(X + C r), and succ_left: asc(n+1) = X * asc(n).comp(X+1)
  rw [ascPochhammer_succ_left, taylor_apply, mul_comp, X_comp]
  -- After: (X + C(-1)) * ((asc n).comp(X+1)).comp(X + C(-1)) = asc n * (X - 1)
  have h1 : ((ascPochhammer R n).comp ((X : R[X]) + 1)).comp (X + C (-1)) =
      ascPochhammer R n := by
    rw [comp_assoc]
    simp [add_comp, X_comp, comp_X]
  rw [h1]
  simp [C_neg, C_1]; ring

/-- The backward difference lowers ascending Pochhammer:
`∇(x⁽ⁿ⁺¹⁾) = (n+1) • x⁽ⁿ⁾`.

This is the telescoping identity:
`x(x+1)...(x+n) - (x-1)x...(x+n-1) = x(x+1)...(x+n-1) · [(x+n) - (x-1)] = (n+1) · x⁽ⁿ⁾` -/
theorem backwardDiff_ascPochhammer (n : ℕ) :
    backwardDiff (ascPochhammer R (n + 1)) = (n + 1) • ascPochhammer R n := by
  simp only [backwardDiff_apply]
  rw [taylor_neg_one_ascPochhammer_succ, ascPochhammer_succ_right]
  -- Goal: asc(n) * (X + n) - asc(n) * (X - 1) = (n+1) • asc(n)
  rw [← mul_sub, show (X : R[X]) + (↑n : R[X]) - (X - 1) = (↑(n + 1) : R[X]) from by
      push_cast; ring]
  rw [show (↑(n + 1) : R[X]) = C (↑(n + 1) : R) from by simp]
  rw [mul_comm, ← smul_eq_C_mul, Nat.cast_smul_eq_nsmul R]

/-- The ascending Pochhammer sequence is the basic sequence of the backward difference. -/
theorem ascPochhammer_isBasicSequence_backwardDiff :
    IsBasicSequence (backwardDiff : R[X] →ₗ[R] R[X])
      (fun n => ascPochhammer R n) where
  lowering := backwardDiff_ascPochhammer
  zero_one := ascPochhammer_zero R
  normalized n hn := by
    cases n with
    | zero => omega
    | succ n =>
      rw [ascPochhammer_succ_left]
      simp [eval_mul, eval_X]

variable [Algebra ℚ R]

/-- The ascending Pochhammer sequence is of binomial type.
Rota's classification: basic sequences of delta operators are binomial type. -/
theorem ascPochhammer_isBinomialType :
    IsBinomialType R (fun n => ascPochhammer R n) :=
  ascPochhammer_isBasicSequence_backwardDiff.isBinomialType backwardDiff_isDeltaOperator

end Polynomial

end
