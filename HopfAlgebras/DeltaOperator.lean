/-
Copyright (c) 2025 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import HopfAlgebras.BinomialType
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Delta operators and basic sequences

A **delta operator** is a shift-equivariant linear operator on `R[X]` that kills
constants and sends `X` to a polynomial with unit constant term. The derivative
and forward difference operator are the canonical examples.

Each delta operator `Q` has a unique **basic sequence** `{pₙ}` satisfying
`Q(pₙ₊₁) = (n+1) • pₙ` with `p₀ = 1` and `pₙ(0) = 0` for `n ≥ 1`.
The fundamental theorem of the umbral calculus (Rota's classification) states
that these are exactly the sequences of binomial type.

## Main definitions

* `Polynomial.IsShiftEquivariant`: `Q` commutes with the Taylor shift `taylor a`
* `Polynomial.IsDeltaOperator`: shift-equivariant, kills constants, unit leading term
* `Polynomial.forwardDiff`: the forward difference operator `E_a - I`
* `Polynomial.IsBasicSequence`: the basic sequence of a delta operator

## Main results

* `Polynomial.hasseDeriv_isShiftEquivariant`: all Hasse derivatives are shift-equivariant
* `Polynomial.derivative_isDeltaOperator`: the derivative is a delta operator
* `Polynomial.forwardDiff_isDeltaOperator`: the forward difference is a delta operator
* `Polynomial.X_pow_isBasicSequence`: `{Xⁿ}` is the basic sequence of the derivative
* `Polynomial.descPochhammer_isBasicSequence_forwardDiff`: falling factorials are
  the basic sequence of the forward difference

## References

* Langer, R., *Determinantal bases and the symmetric group*, arXiv:0907.3950, §1.2.2
* Roman, S., *The Umbral Calculus*, Academic Press, 1984
* Rota, G.-C., Kahaner, D., Odlyzko, A., *Finite Operator Calculus*, JMAA 42 (1973)
-/

noncomputable section

open Polynomial Finset

namespace Polynomial

/-! ### Shift-equivariant operators

An operator `Q : R[X] →ₗ[R] R[X]` is shift-equivariant if it commutes with the
Taylor shift operator `taylor a` for all `a : R`. Equivalently, `Q` commutes with
the translation `p(x) ↦ p(x + a)`.

The Hasse derivatives `hasseDeriv k` are the prototypical shift-equivariant operators.
The proof uses the composition law `hasseDeriv n ∘ hasseDeriv k = C(n+k,n) • hasseDeriv (n+k)`
together with the binomial symmetry `C(n+k,n) = C(n+k,k)`. -/

variable {R : Type*} [CommSemiring R]

/-- An operator `Q : R[X] →ₗ[R] R[X]` is shift-equivariant if it commutes with the
Taylor shift: `Q ∘ taylor a = taylor a ∘ Q` for all `a`. This means `Q` respects
the "addition of alphabets" structure underlying the coalgebra on `R[X]`. -/
def IsShiftEquivariant (Q : R[X] →ₗ[R] R[X]) : Prop :=
  ∀ (a : R), Q.comp (taylor a) = (taylor a).comp Q

/-- Every Hasse derivative `hasseDeriv k` is shift-equivariant. The proof is
coefficient-by-coefficient: both sides yield `↑C(n+k,k) * (hasseDeriv (n+k) p).eval a`,
using the composition law for Hasse derivatives and the symmetry of binomial coefficients. -/
theorem hasseDeriv_isShiftEquivariant (k : ℕ) :
    IsShiftEquivariant (hasseDeriv k : R[X] →ₗ[R] R[X]) := by
  intro a
  apply LinearMap.ext; intro p
  apply Polynomial.ext; intro n
  simp only [LinearMap.comp_apply, hasseDeriv_coeff, taylor_coeff]
  -- LHS: ↑(n + k).choose k * (hasseDeriv (n + k) p).eval a
  -- RHS: (hasseDeriv n (hasseDeriv k p)).eval a
  -- Rewrite RHS using hasseDeriv_comp
  rw [← LinearMap.comp_apply (hasseDeriv n) (hasseDeriv k), hasseDeriv_comp,
      LinearMap.smul_apply]
  -- RHS: ((n + k).choose n • hasseDeriv (n + k) p).eval a
  -- Push eval through nsmul and convert to Nat.cast multiplication
  rw [Polynomial.eval_smul, nsmul_eq_mul]
  -- Goal: ↑(n + k).choose k * ... = ↑(n + k).choose n * ...
  congr 1
  exact congrArg (Nat.cast (R := R))
    (Nat.choose_symm_of_eq_add (show n + k = k + n by omega))

/-- Composition of shift-equivariant operators is shift-equivariant. -/
theorem isShiftEquivariant_comp {Q₁ Q₂ : R[X] →ₗ[R] R[X]}
    (h₁ : IsShiftEquivariant Q₁) (h₂ : IsShiftEquivariant Q₂) :
    IsShiftEquivariant (Q₁.comp Q₂) := by
  intro a
  rw [LinearMap.comp_assoc, h₂ a, ← LinearMap.comp_assoc, h₁ a, LinearMap.comp_assoc]

/-- The sum of shift-equivariant operators is shift-equivariant. -/
theorem isShiftEquivariant_add {Q₁ Q₂ : R[X] →ₗ[R] R[X]}
    (h₁ : IsShiftEquivariant Q₁) (h₂ : IsShiftEquivariant Q₂) :
    IsShiftEquivariant (Q₁ + Q₂) := by
  intro a
  simp only [LinearMap.add_comp, LinearMap.comp_add, h₁ a, h₂ a]

/-! ### Delta operators

A delta operator is a shift-equivariant operator that kills constants and
whose image of `X` has a unit constant term. The derivative `D` and the
forward difference `Δₐ = E_a - I` are the canonical examples. -/

/-- A **delta operator** on `R[X]` is a shift-equivariant linear operator that
kills constants and sends `X` to a polynomial with unit constant term. -/
structure IsDeltaOperator (Q : R[X] →ₗ[R] R[X]) : Prop where
  shift_equivariant : IsShiftEquivariant Q
  kills_constants : ∀ (r : R), Q (C r) = 0
  unit_leading : IsUnit ((Q X).coeff 0)

/-- The derivative (`hasseDeriv 1`) is a delta operator:
`D(C r) = 0`, `D(X) = 1`, and `1` is a unit. -/
theorem derivative_isDeltaOperator :
    IsDeltaOperator (hasseDeriv 1 : R[X] →ₗ[R] R[X]) where
  shift_equivariant := hasseDeriv_isShiftEquivariant 1
  kills_constants r := by
    rw [hasseDeriv_one]; exact derivative_C
  unit_leading := by
    rw [hasseDeriv_one, derivative_X]
    simp [coeff_one]

end Polynomial

end -- end CommSemiring noncomputable section

/-! ### Forward difference operator (requires subtraction) -/

noncomputable section

open Polynomial Finset

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The forward difference operator `Δₐ = E_a - I`, where `E_a = taylor a`
is the shift operator. For `a = 1`, this sends `p(x) ↦ p(x + 1) - p(x)`. -/
def forwardDiff (a : R) : R[X] →ₗ[R] R[X] := taylor a - LinearMap.id

@[simp]
theorem forwardDiff_apply (a : R) (p : R[X]) :
    forwardDiff a p = taylor a p - p := by
  simp [forwardDiff]

@[simp]
theorem forwardDiff_X (a : R) : forwardDiff a (X : R[X]) = C a := by
  simp [forwardDiff, taylor_X]

@[simp]
theorem forwardDiff_C (a : R) (r : R) : forwardDiff a (C r) = 0 := by
  simp [forwardDiff, taylor_C]

/-- The forward difference operator `Δₐ` is shift-equivariant: translation
commutes with taking differences because `taylor` composes additively. -/
theorem forwardDiff_isShiftEquivariant (a : R) :
    IsShiftEquivariant (forwardDiff a) := by
  intro b
  apply LinearMap.ext; intro p
  simp only [LinearMap.comp_apply, forwardDiff_apply]
  rw [map_sub (taylor b)]
  congr 1
  rw [taylor_taylor, taylor_taylor, add_comm]

/-- The forward difference `Δₐ` is a delta operator when `a` is a unit.
The leading term `Δₐ(X) = C a` has constant coefficient `a`. -/
theorem forwardDiff_isDeltaOperator (a : R) (ha : IsUnit a) :
    IsDeltaOperator (forwardDiff a) where
  shift_equivariant := forwardDiff_isShiftEquivariant a
  kills_constants := forwardDiff_C a
  unit_leading := by simp [coeff_C_zero, ha]

/-! ### Basic sequences

The basic sequence of a delta operator `Q` is the unique polynomial sequence
`{pₙ}` satisfying the lowering property `Q(pₙ₊₁) = (n+1) • pₙ`, normalized
by `p₀ = 1` and `pₙ(0) = 0` for `n ≥ 1`.

The fundamental theorem of the umbral calculus states that basic sequences are
exactly the sequences of binomial type. -/

/-- A sequence `p : ℕ → R[X]` is a **basic sequence** for an operator `Q` if:
* `Q(pₙ₊₁) = (n+1) • pₙ` (lowering property)
* `p₀ = 1`
* `pₙ(0) = 0` for `n ≥ 1` (normalization) -/
structure IsBasicSequence (Q : R[X] →ₗ[R] R[X]) (p : ℕ → R[X]) : Prop where
  lowering : ∀ n, Q (p (n + 1)) = (n + 1) • p n
  zero_one : p 0 = 1
  normalized : ∀ n, 0 < n → (p n).eval 0 = 0

/-- The monomial sequence `{Xⁿ}` is the basic sequence of the derivative.
The lowering property is `D(Xⁿ⁺¹) = (n+1) • Xⁿ`, which is the power rule. -/
theorem X_pow_isBasicSequence :
    IsBasicSequence (hasseDeriv 1 : R[X] →ₗ[R] R[X]) (fun n => (X : R[X]) ^ n) where
  lowering n := by
    rw [hasseDeriv_one, derivative_pow_succ, derivative_X, mul_one]
    -- Goal: C (↑n + 1) * X ^ n = (n + 1) • X ^ n
    rw [nsmul_eq_mul, ← C_eq_natCast, Nat.cast_succ, map_add, map_one]
  zero_one := pow_zero X
  normalized n hn := by
    simp [eval_pow, eval_X, zero_pow (by omega : n ≠ 0)]

/-- Helper: `taylor 1` is multiplicative (it equals `taylorAlgHom 1` on the nose). -/
private theorem taylor_one_mul (f g : R[X]) :
    taylor 1 (f * g) = taylor 1 f * taylor 1 g := by
  change taylorAlgHom 1 (f * g) = taylorAlgHom 1 f * taylorAlgHom 1 g
  exact map_mul _ f g

/-- Helper: `taylor 1 (X - ↑(n+1)) = X - ↑n` in `R[X]`. -/
private theorem taylor_one_X_sub_natCast (n : ℕ) :
    taylor (1 : R) ((X : R[X]) - (↑(n + 1) : R[X])) = X - (↑n : R[X]) := by
  have : taylor (1 : R) (↑(n + 1) : R[X]) = (↑(n + 1) : R[X]) := by
    change taylorAlgHom 1 (↑(n + 1) : R[X]) = _; exact map_natCast _ _
  rw [map_sub, taylor_X, this, Nat.cast_succ, C_1]
  ring

/-- The lowering property for falling factorials: the forward difference satisfies
`Δ₁(descPochhammer (n+1)) = (n+1) • descPochhammer n`. -/
private theorem forwardDiff_one_descPochhammer (n : ℕ) :
    forwardDiff (1 : R) (descPochhammer R (n + 1)) =
      (n + 1) • descPochhammer R n := by
  induction n with
  | zero =>
    simp [descPochhammer_one, descPochhammer_zero, forwardDiff_apply,
          taylor_X, one_smul]
  | succ n ih =>
    -- dp (n+2) = dp (n+1) * (X - ↑(n+1)) by descPochhammer_succ_right
    rw [descPochhammer_succ_right, forwardDiff_apply,
        taylor_one_mul, taylor_one_X_sub_natCast]
    -- From IH: taylor 1 (dp (n+1)) = dp (n+1) + (n+1) • dp n
    have ih' : taylor (1 : R) (descPochhammer R (n + 1)) =
        descPochhammer R (n + 1) + (n + 1) • descPochhammer R n := by
      calc taylor (1 : R) (descPochhammer R (n + 1))
          = forwardDiff (1 : R) (descPochhammer R (n + 1)) +
              descPochhammer R (n + 1) := by simp [forwardDiff_apply]
        _ = (n + 1) • descPochhammer R n + descPochhammer R (n + 1) := by rw [ih]
        _ = descPochhammer R (n + 1) + (n + 1) • descPochhammer R n :=
              add_comm _ _
    rw [ih', add_mul, smul_mul_assoc, ← descPochhammer_succ_right]
    -- Goal reduces to polynomial algebra after converting nsmul to multiplication
    simp only [nsmul_eq_mul, Nat.cast_succ]
    ring

/-- The falling factorial sequence is the basic sequence of the forward difference `Δ₁`.
This connects the forward difference operator to the Vandermonde identity. -/
theorem descPochhammer_isBasicSequence_forwardDiff :
    IsBasicSequence (forwardDiff (1 : R)) (fun n => descPochhammer R n) where
  lowering := forwardDiff_one_descPochhammer
  zero_one := descPochhammer_zero R
  normalized n hn := by
    -- descPochhammer R n has X as a factor for n ≥ 1
    cases n with
    | zero => omega
    | succ n =>
      rw [descPochhammer_succ_left]
      simp [eval_mul, eval_X]

/-! ### Bridge to binomial type (deferred)

The fundamental theorem of the umbral calculus: the basic sequence of any delta
operator is a sequence of binomial type.

Two proof routes are available:
1. **Coderivation**: show shift-equivariance implies `(Q ⊗ id) ∘ Δ = Δ ∘ Q`,
   then construct the umbral operator as a `CoalgHom` and apply `of_coalgebraHom`.
2. **Direct**: induction using the lowering property and binomial recurrence.

Both require compositional inverse infrastructure or tensor product ext lemmas
not yet developed. See HANDOVER.md for the planned approach via Lagrange inversion. -/

/-- **Rota's classification theorem** (umbral calculus): the basic sequence of a delta
operator is of binomial type. This connects the operator-theoretic and coalgebraic
viewpoints. -/
theorem IsBasicSequence.isBinomialType {Q : R[X] →ₗ[R] R[X]} {p : ℕ → R[X]}
    (_hQ : IsDeltaOperator Q) (_hp : IsBasicSequence Q p) :
    IsBinomialType R p := by
  sorry

end Polynomial

end
