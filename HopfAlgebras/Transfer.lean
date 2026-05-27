/-
Copyright (c) 2025 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import HopfAlgebras.DeltaOperator

/-!
# The Transfer Formula: expanding one basic sequence in another

Given two delta operators `Q` and `R` with basic sequences `{p_n}` and `{q_n}`,
the transfer formula expresses `p_n` as a linear combination of `{q_k}`:

  `p_n = Σ_{k=0}^n c(n,k) • q_k`

where `c(n,k) = (R^k (p_n)).eval 0 / k!`.

This is the general theorem that specializes to give:
- Rising factorials in terms of falling: `x^(n) = Σ L(n,k) (x)_k`
- And vice versa

## Strategy

1. Show basic sequences form a basis (degree k, unit leading coefficient)
2. Show the expansion coefficients are extracted by iterated R evaluation at 0
3. (Future) Connect to Jabotinsky matrices and power series composition

## Main results

* `IsBasicSequence.natDegree_eq`: `natDegree (p n) = n`
* `IsBasicSequence.expand_in_basis`: the expansion theorem
-/

noncomputable section

open Polynomial Finset

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-! ### Basic sequences have degree n -/

/-- A basic sequence has `natDegree (p n) = n`.

Lower bound: `Q^n(p_n)(0) = n! ≠ 0` (from `iter_eval_zero`), and Q drops
degree by at least 1 (kills constants), so `natDegree(p_n) ≥ n`.

Upper bound: requires showing Q drops degree by EXACTLY 1 on non-constants.
The relevant degree-drop lemma (`natDegree_delta_op_pow`) is private in
`DeltaOperator.lean` and would need to be re-derived or made public. -/
theorem IsBasicSequence.natDegree_eq {Q : R[X] →ₗ[R] R[X]} {p : ℕ → R[X]}
    (hQ : IsDeltaOperator Q) (hp : IsBasicSequence Q p) (n : ℕ) :
    (p n).natDegree = n := by
  -- Use iter_eval_zero: Q^n(p_n)(0) = n! ≠ 0, so p_n ≠ 0 and has degree ≥ n
  -- Combined with upper bound from Q dropping degree, get exactly n
  sorry

/-- Iterated application of a linear map. -/
def LinearMap.iterateₗ (f : R[X] →ₗ[R] R[X]) : ℕ → (R[X] →ₗ[R] R[X])
  | 0 => LinearMap.id
  | k + 1 => f.comp (LinearMap.iterateₗ f k)

/-- Commutativity of iteration: `Q(Q^k(f)) = Q^k(Q(f))`. -/
private theorem iterateₗ_comm (Q : R[X] →ₗ[R] R[X]) (k : ℕ) (f : R[X]) :
    Q ((LinearMap.iterateₗ Q k) f) = (LinearMap.iterateₗ Q k) (Q f) := by
  induction k with
  | zero => simp [LinearMap.iterateₗ]
  | succ k ih =>
    simp only [LinearMap.iterateₗ, LinearMap.comp_apply]
    rw [ih]

/-- `Q^k(q_m)(0) = m! / (m-k)! · δ_{m≥k} · q_{m-k}(0)`.
Combined with the normalization `q_j(0) = 0` for j > 0, this gives
`Q^k(q_m)(0) = k!` if m = k, and 0 otherwise. -/
theorem IsBasicSequence.iter_eval_zero {Q : R[X] →ₗ[R] R[X]} {q : ℕ → R[X]}
    (hQ : IsDeltaOperator Q) (hq : IsBasicSequence Q q) (k m : ℕ) :
    ((LinearMap.iterateₗ Q k) (q m)).eval 0 =
      if m = k then (Nat.factorial k : R) else 0 := by
  induction k generalizing m with
  | zero =>
    simp only [LinearMap.iterateₗ, LinearMap.id_apply, Nat.factorial_zero, Nat.cast_one]
    cases m with
    | zero => simp [hq.zero_one]
    | succ m => simp [hq.normalized (m + 1) (Nat.succ_pos m)]
  | succ k ih =>
    -- Q^{k+1}(q_m) = Q^k(Q(q_m)), rewrite using commutativity
    show eval 0 (Q ((LinearMap.iterateₗ Q k) (q m))) = _
    rw [iterateₗ_comm]
    cases m with
    | zero =>
      -- Q(q_0) = Q(1) = 0 (kills constants)
      have h0 : Q (q 0) = 0 := by rw [hq.zero_one]; exact hQ.kills_constants 1
      rw [h0, map_zero, eval_zero]
      simp
    | succ m =>
      -- Q(q_{m+1}) = (m+1) • q_m by lowering
      rw [hq.lowering m, map_nsmul]
      simp only [eval_smul, smul_eq_mul, ih m]
      by_cases hm : m = k
      · -- m = k: (m+1) * k! = (k+1)!
        subst hm; simp [Nat.factorial_succ]
      · -- m ≠ k: (m+1) * 0 = 0
        simp [hm, show m + 1 ≠ k + 1 from by omega]

/-- The expansion coefficients are consistent: applying `S^j` and evaluating at 0
gives back `j!` times the j-th coefficient. This follows directly from
`iter_eval_zero` (orthogonality). -/
theorem IsBasicSequence.expand_coeff_consistent
    {Q S : R[X] →ₗ[R] R[X]} {p q : ℕ → R[X]}
    (hQ : IsDeltaOperator Q) (hp : IsBasicSequence Q p)
    (hS : IsDeltaOperator S) (hq : IsBasicSequence S q) (n j : ℕ) (hj : j ≤ n) :
    ((LinearMap.iterateₗ S j) ((range (n + 1)).sum fun k =>
      C (algebraMap ℚ R ((Nat.factorial k : ℚ)⁻¹) *
        ((LinearMap.iterateₗ S k) (p n)).eval 0) • q k)).eval 0 =
    ((LinearMap.iterateₗ S j) (p n)).eval 0 := by
  simp only [map_sum, map_smul, LinearMap.map_smul_of_tower]
  simp only [eval_smul, smul_eq_mul, eval_C]
  -- Each term: S^j(C(c_k) • q_k)(0) = c_k • S^j(q_k)(0) = c_k • k! • δ_{k,j}
  sorry

/-- **The Transfer Formula**: every basic sequence expands uniquely in any other.

If `{p_n}` is basic for Q and `{q_n}` is basic for R, then:
  `p_n = Σ_{k=0}^n c(n,k) • q_k`
where `c(n,k) = eval 0 (R^k(p_n)) / k!`.

The division by `k!` is safe in a ℚ-algebra: we multiply by `algebraMap ℚ R (1/k!)`.

Proof sketch: both sides agree under `S^j(·)(0)` for all j (by orthogonality
`iter_eval_zero`), and basic sequences span (from `natDegree_eq`). -/
theorem IsBasicSequence.expand_in_basis
    {Q S : R[X] →ₗ[R] R[X]} {p q : ℕ → R[X]}
    (hQ : IsDeltaOperator Q) (hp : IsBasicSequence Q p)
    (hS : IsDeltaOperator S) (hq : IsBasicSequence S q) (n : ℕ) :
    p n = (range (n + 1)).sum fun k =>
      C (algebraMap ℚ R ((Nat.factorial k : ℚ)⁻¹) *
        ((LinearMap.iterateₗ S k) (p n)).eval 0) • q k := by
  -- The proof requires:
  -- 1. natDegree_eq: basic sequences form a graded basis
  -- 2. iter_eval_zero: S^j extracts the j-th coefficient
  -- 3. Both sides agree under all S^j(·)(0) extractions
  -- 4. Agreement of all "moments" implies equality (since {q_k} spans)
  sorry

end Polynomial

end
