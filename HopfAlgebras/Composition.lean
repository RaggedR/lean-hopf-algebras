/-
Copyright (c) 2025 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Module.Rat
import HopfAlgebras.Lah

/-!
# Compositional inverse relationship between exp and log

We prove that `exp` and `log` are compositional inverses as formal power series:

  `(log A).subst (exp A - 1) = X`

i.e., `log(exp(X)) = X`, and equivalently:

  `(exp A - 1).subst (log A) = X`

i.e., `exp(log(1+X)) - 1 = X`.

## Proof strategy

The first identity is proved by showing the composition has derivative 1 and constant
term 0, hence equals `X` by `derivative.ext`. The chain rule reduces the derivative
computation to the algebraic identity `(1 + X) * d⁄dX(log(1+X)) = 1`.

The second identity follows from the first via compositional inverse uniqueness
(`substInvOfIsUnit`).

## Main results

* `PowerSeries.log_subst_exp_sub_one`: `(log A).subst (exp A - 1) = X`
* `PowerSeries.exp_sub_one_subst_log`: `(exp A - 1).subst (log A) = X`
* `PowerSeries.exp_sub_one_subst_neg_evalNegHom_log`:
  `(exp A - 1).subst (-evalNegHom (log A)) = lahSeries A`
-/

noncomputable section

open PowerSeries Nat

namespace PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-! ### Derivative of log times (1 + X) -/

/-- `evalNegHom (mk 1) = d⁄dX A (log A)`: the image of the geometric series under
`X ↦ -X` equals the derivative of log. -/
private theorem evalNegHom_mk_one_eq_derivative_log :
    evalNegHom (mk 1 : A⟦X⟧) = d⁄dX A (log A) := by
  ext n
  simp [evalNegHom, coeff_rescale, coeff_mk, deriv_log, map_pow, map_neg, map_one]

/-- `(1 + X) * d⁄dX(log(1+X)) = 1`. This expresses `d⁄dX log(1+X) = 1/(1+X)`. -/
theorem one_add_X_mul_derivative_log :
    (1 + X : A⟦X⟧) * d⁄dX A (log A) = 1 := by
  rw [← evalNegHom_mk_one_eq_derivative_log]
  have hmk : (mk 1 : A⟦X⟧) * (1 - X) = 1 := mk_one_mul_one_sub_eq_one A
  have h := congr_arg (evalNegHom (A := A)) hmk
  simp only [map_mul, map_one] at h
  have hev : evalNegHom (1 - X : A⟦X⟧) = 1 + X := by
    have : evalNegHom (X : A⟦X⟧) = -X := evalNegHom_X
    simp [map_sub, map_one, this]
  rw [hev, mul_comm] at h
  exact h

/-! ### The main composition identities -/

/-- **log ∘ exp = id**: `(log A).subst (exp A - 1) = X`.

This says `log(exp(X)) = X` as formal power series over a ℚ-algebra. -/
theorem log_subst_exp_sub_one :
    (log A).subst (exp A - 1 : A⟦X⟧) = (X : A⟦X⟧) := by
  haveI : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat (M := A)
  have hexp : HasSubst (exp A - 1 : A⟦X⟧) := HasSubst.exp_sub_one
  apply derivative.ext (R := A)
  · -- Show: derivative of (log A).subst(exp A - 1) = derivative X = 1
    have hchain : d⁄dX A ((log A).subst (exp A - 1 : A⟦X⟧)) =
        (d⁄dX A (log A)).subst (exp A - 1 : A⟦X⟧) * d⁄dX A (exp A - 1 : A⟦X⟧) :=
      derivative_subst A hexp
    rw [hchain, derivative_X]
    -- derivative (exp A - 1) = exp A
    have hd : d⁄dX A (exp A - 1 : A⟦X⟧) = exp A := by
      simp [map_sub, derivative_exp]
    rw [hd]
    -- Key: (1 + X) * d⁄dX(log) = 1, apply subst(exp - 1) to both sides
    have hkey := @one_add_X_mul_derivative_log A _ _
    have hsub : ((1 + X : A⟦X⟧) * d⁄dX A (log A)).subst (exp A - 1 : A⟦X⟧) =
        (1 : A⟦X⟧).subst (exp A - 1 : A⟦X⟧) :=
      congr_arg (subst (exp A - 1 : A⟦X⟧)) hkey
    rw [subst_mul hexp] at hsub
    -- (1+X).subst(exp-1) = 1 + (exp-1) = exp
    have hone_X : subst (exp A - 1 : A⟦X⟧) (1 + X : A⟦X⟧) = exp A := by
      rw [subst_add hexp, subst_X hexp, show (1 : A⟦X⟧) = C 1 from rfl, subst_C]
      simp
    -- 1.subst(exp-1) = 1
    have hone : subst (exp A - 1 : A⟦X⟧) (1 : A⟦X⟧) = (1 : A⟦X⟧) := by
      rw [show (1 : A⟦X⟧) = C 1 from rfl, subst_C]; simp
    rw [hone_X, hone] at hsub
    -- hsub : exp A * (d⁄dX A (log A)).subst (exp A - 1) = 1
    rw [mul_comm]
    exact hsub
  · -- Show: constantCoeff of (log A).subst(exp A - 1) = constantCoeff X = 0
    have hc := constantCoeff_subst_eq_zero
      (show (exp A - 1 : A⟦X⟧).constantCoeff = 0 from by simp [constantCoeff_exp])
      (log A) constantCoeff_log
    -- constantCoeff on PowerSeries = MvPowerSeries.constantCoeff definitionally
    change constantCoeff ((log A).subst (exp A - 1 : A⟦X⟧)) = constantCoeff (X : A⟦X⟧)
    rw [show constantCoeff (X : A⟦X⟧) = (0 : A) from constantCoeff_X]
    exact hc

/-- **exp ∘ log = id**: `(exp A - 1).subst (log A) = X`.

This says `exp(log(1+X)) - 1 = X` as formal power series over a ℚ-algebra.

Derived from `log_subst_exp_sub_one` using compositional inverse uniqueness. -/
theorem exp_sub_one_subst_log :
    (exp A - 1 : A⟦X⟧).subst (log A) = (X : A⟦X⟧) := by
  have hconst : (exp A - 1 : A⟦X⟧).constantCoeff = 0 := by simp [constantCoeff_exp]
  have hunit : IsUnit ((exp A - 1 : A⟦X⟧).coeff 1) := by
    have h : (exp A - 1 : A⟦X⟧).coeff 1 = 1 := by
      simp [coeff_exp, Nat.factorial]
    rw [h]; exact isUnit_one
  -- The compositional inverse of (exp A - 1) exists
  set Q := substInvOfIsUnit (exp A - 1 : A⟦X⟧) hunit
  have hQ_sub : HasSubst Q := HasSubst.substInvOfIsUnit (exp A - 1) hunit
  -- Q is a two-sided inverse
  have hQ_left : Q.subst (exp A - 1 : A⟦X⟧) = X :=
    subst_substInvOfIsUnit_left (exp A - 1) hconst hunit
  have hQ_right : (exp A - 1 : A⟦X⟧).subst Q = X :=
    subst_substInvOfIsUnit_right (exp A - 1) hconst hunit
  -- Show Q = log A using associativity of composition
  suffices hQ_log : Q = log A by rw [← hQ_log]; exact hQ_right
  -- From log_subst_exp_sub_one: (log A).subst (exp A - 1) = X
  have key := @log_subst_exp_sub_one A _ _
  -- Apply (subst Q) to both sides, use associativity
  have hlhs : subst Q ((log A).subst (exp A - 1 : A⟦X⟧)) = Q := by
    rw [key, subst_X hQ_sub]
  have hrhs : subst Q ((log A).subst (exp A - 1 : A⟦X⟧)) = log A := by
    rw [subst_comp_subst_apply HasSubst.exp_sub_one hQ_sub, hQ_right, X_subst]
  rw [← hlhs, hrhs]

/-! ### The bridge to lahSeries -/

/-- **Composition identity for lahSeries**:
`exp(-log(1-X)) - 1 = X/(1-X) = lahSeries`.

This bridges the finite Jabotinsky computation to an all-n proof.
The proof derives this from `exp_sub_one_subst_log` via:
1. Compose with evalNegHom: `exp(log(1-X)) - 1 = -X`, so `exp(log(1-X)) = 1-X`
2. From `exp(a)·exp(-a) = 1`: `exp(-log(1-X)) = (1-X)⁻¹ = mk 1`
3. Subtract 1: `mk 1 - 1 = X · mk 1 = lahSeries` -/
theorem exp_sub_one_subst_neg_evalNegHom_log :
    (exp A - 1).subst (-evalNegHom (log A) : A⟦X⟧) = lahSeries A := by
  -- Auxiliary: HasSubst facts
  have hNegX : HasSubst (-X : A⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  have hf : HasSubst (evalNegHom (log A) : A⟦X⟧) := HasSubst.of_constantCoeff_zero' (by
    rw [← coeff_zero_eq_constantCoeff, evalNegHom, coeff_rescale, pow_zero, one_mul,
        coeff_zero_eq_constantCoeff, constantCoeff_log])
  have hnf : HasSubst (-evalNegHom (log A) : A⟦X⟧) := HasSubst.of_constantCoeff_zero' (by
    rw [← coeff_zero_eq_constantCoeff, map_neg, neg_eq_zero, coeff_zero_eq_constantCoeff]
    rw [← coeff_zero_eq_constantCoeff, evalNegHom, coeff_rescale, pow_zero, one_mul,
        coeff_zero_eq_constantCoeff, constantCoeff_log])
  -- Auxiliary: evalNegHom f = f.subst(-X)
  have heval_eq (g : A⟦X⟧) : evalNegHom g = g.subst (-X : A⟦X⟧) := by
    rw [show (-X : A⟦X⟧) = (-1 : A) • X from by simp, ← rescale_eq_subst]; rfl
  -- Auxiliary: subst f (-X) = -f (for f = evalNegHom(log A))
  have hfX : (-X : A⟦X⟧).subst (evalNegHom (log A) : A⟦X⟧) = -evalNegHom (log A) := by
    have : (-X : A⟦X⟧) = (0 : A⟦X⟧) - X := by ring
    rw [this, subst_sub hf, subst_X hf, show (0 : A⟦X⟧) = C 0 from by simp, subst_C]
    simp
  -- Step 1: (exp-1).subst(evalNegHom(log)) = -X
  have h_step1 : (exp A - 1).subst (evalNegHom (log A) : A⟦X⟧) = -(X : A⟦X⟧) := by
    have hkey := @exp_sub_one_subst_log A _ _
    have h := congr_arg (subst (-X : A⟦X⟧)) hkey
    rw [subst_X hNegX] at h
    rw [subst_comp_subst_apply HasSubst.log hNegX] at h
    rwa [← heval_eq] at h
  -- Step 2: exp.subst(evalNegHom(log)) = 1 - X
  have h_step2 : (exp A).subst (evalNegHom (log A) : A⟦X⟧) = 1 - X := by
    -- exp = (exp - 1) + 1
    have hdecomp : (exp A : A⟦X⟧) = (exp A - 1) + 1 := by ring
    rw [hdecomp, subst_add hf, h_step1, show (1 : A⟦X⟧) = C 1 from rfl, subst_C]
    simp; ring
  -- Step 3: exp.subst(f) * exp.subst(-f) = 1
  have h_step3 : (exp A).subst (evalNegHom (log A) : A⟦X⟧) *
      (exp A).subst (-evalNegHom (log A) : A⟦X⟧) = 1 := by
    have hmul := @exp_mul_exp_neg_eq_one A _ _
    -- Substitute evalNegHom(log) for X in exp * evalNegHom(exp) = 1
    have hsub := congr_arg (subst (evalNegHom (log A) : A⟦X⟧)) hmul
    rw [subst_mul hf, show (1 : A⟦X⟧) = C 1 from rfl, subst_C] at hsub
    -- (evalNegHom(exp)).subst(f) = ((exp).subst(-X)).subst(f) = exp.subst(-f)
    have heval_sub : (evalNegHom (exp A)).subst (evalNegHom (log A) : A⟦X⟧) =
        (exp A).subst (-evalNegHom (log A) : A⟦X⟧) := by
      rw [heval_eq (exp A), subst_comp_subst_apply hNegX hf, hfX]
    rw [heval_sub] at hsub
    simpa using hsub
  -- Step 4: exp.subst(-f) = mk 1
  have h_step4 : (exp A).subst (-evalNegHom (log A) : A⟦X⟧) = (mk 1 : A⟦X⟧) := by
    have h : (1 - X : A⟦X⟧) * (exp A).subst (-evalNegHom (log A) : A⟦X⟧) = 1 := by
      rw [← h_step2]; exact h_step3
    have hmk := mk_one_mul_one_sub_eq_one (S := A)
    -- g = 1 * g = (mk 1 * (1-X)) * g = mk 1 * ((1-X) * g) = mk 1 * 1 = mk 1
    calc (exp A).subst (-evalNegHom (log A) : A⟦X⟧)
        = 1 * (exp A).subst (-evalNegHom (log A) : A⟦X⟧) := (one_mul _).symm
      _ = (mk 1 : A⟦X⟧) * (1 - X) * (exp A).subst (-evalNegHom (log A) : A⟦X⟧) := by
          rw [hmk]
      _ = (mk 1 : A⟦X⟧) * ((1 - X) * (exp A).subst (-evalNegHom (log A) : A⟦X⟧)) := by
          ring
      _ = (mk 1 : A⟦X⟧) * 1 := by rw [h]
      _ = mk 1 := mul_one _
  -- Step 5: (exp-1).subst(-f) = mk 1 - 1 = X * mk 1 = lahSeries
  have hdecomp : (exp A - 1 : A⟦X⟧) = (exp A : A⟦X⟧) + (-1) := by ring
  rw [hdecomp, subst_add hnf, h_step4, show (-1 : A⟦X⟧) = C (-1) from by simp, subst_C]
  simp only [map_neg, map_one]
  -- Goal: mk 1 + (-1) = lahSeries A = X * mk 1
  rw [lahSeries]
  -- mk 1 + (-1) = X * mk 1 (coefficient comparison)
  ext n
  simp only [map_add, map_neg, coeff_mk, Pi.one_apply, coeff_one]
  rw [show X * (mk 1 : A⟦X⟧) = X ^ 1 * mk 1 from by ring, coeff_X_pow_mul' (mk 1 : A⟦X⟧) 1 n]
  cases n with
  | zero => simp
  | succ n => simp

end PowerSeries

end
