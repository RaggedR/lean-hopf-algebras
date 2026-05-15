/-
Copyright (c) 2025 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import HopfAlgebras.Umbral
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Duality between polynomials and power series

The polynomial ring `R[X]` (as a coalgebra) and the power series ring `R⟦X⟧`
(as an algebra) are connected by a natural duality pairing. This file develops
the coefficient-level bridge between these structures.

The key identity is `(hasseDeriv k p).eval 0 = p.coeff k`: the Hasse derivative
composed with evaluation at zero extracts polynomial coefficients. This is the
umbral calculus pairing `⟨y^k, p(x)⟩ = [x^k/k!] p(x)` from Langer
(arXiv:0907.3950, §1.2) expressed factorial-free via Hasse derivatives.

The Leibniz rule for Hasse derivatives, when evaluated at zero, gives exactly the
power series multiplication formula (`PowerSeries.coeff_mul`). This exhibits
multiplication in `R⟦X⟧` as the convolution dual to the coalgebra structure on `R[X]`.

## Main results

* `Polynomial.hasseDeriv_eval_zero`: `(hasseDeriv k p).eval 0 = p.coeff k`
* `Polynomial.hasseDeriv_mul_eval_zero`: the Leibniz-convolution correspondence

## References

* Langer, R., *Determinantal bases and the symmetric group*, arXiv:0907.3950, §1.2
-/

noncomputable section

open Polynomial Finset

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-! ### The Hasse-eval bridge

The fundamental identity connecting Hasse derivatives to coefficient extraction:
`(hasseDeriv k p).eval 0 = p.coeff k`. This follows from Taylor's theorem at `r = 0`.
-/

/-- The Hasse derivative composed with evaluation at zero extracts polynomial
coefficients: `(hasseDeriv k p).eval 0 = p.coeff k`. This is the duality
pairing `⟨y^k, p(x)⟩` from the umbral calculus, expressed factorial-free. -/
theorem hasseDeriv_eval_zero (k : ℕ) (p : R[X]) :
    (hasseDeriv k p).eval 0 = p.coeff k := by
  rw [← taylor_coeff, taylor_zero]

/-- Linear map version: `leval 0 ∘ₗ hasseDeriv k = lcoeff R k`. -/
theorem leval_zero_comp_hasseDeriv (k : ℕ) :
    (Polynomial.leval (0 : R)).comp (hasseDeriv k) = Polynomial.lcoeff R k := by
  apply LinearMap.ext; intro p
  simp only [LinearMap.comp_apply, leval_apply, lcoeff_apply]
  exact hasseDeriv_eval_zero k p

/-! ### The Leibniz-convolution correspondence

The Hasse derivative Leibniz rule (`hasseDeriv_mul`) evaluated at zero gives
exactly the convolution formula for power series multiplication. This is the
core duality theorem: multiplication in `R⟦X⟧` is the operation dual to the
coalgebra comultiplication on `R[X]`. -/

/-- The Hasse-Leibniz rule at zero: the `k`-th coefficient of a product equals
the antidiagonal convolution of coefficients. This is `PowerSeries.coeff_mul`
derived from the polynomial Leibniz rule. -/
theorem hasseDeriv_mul_eval_zero (f g : R[X]) (n : ℕ) :
    (hasseDeriv n (f * g)).eval 0 =
      ∑ ij ∈ Finset.antidiagonal n,
        (hasseDeriv ij.1 f).eval 0 * (hasseDeriv ij.2 g).eval 0 := by
  rw [hasseDeriv_mul]
  simp [eval_finset_sum, eval_mul]

/-- The Leibniz-convolution correspondence restated as a coefficient identity:
`coeff n (f * g) = Σ_{i+j=n} coeff i f * coeff j g`. This connects the
polynomial world (Hasse derivatives) to the power series world (`coeff_mul`). -/
theorem coeff_mul_eq_antidiagonal_sum (f g : R[X]) (n : ℕ) :
    (f * g).coeff n =
      ∑ ij ∈ Finset.antidiagonal n, f.coeff ij.1 * g.coeff ij.2 := by
  rw [← hasseDeriv_eval_zero, hasseDeriv_mul_eval_zero]
  congr 1; ext ij
  simp [hasseDeriv_eval_zero]

/-! ### Non-degeneracy of the pairing

The coefficient pairing is non-degenerate on the power series side:
a power series is determined by its pairing with all monomials. -/

/-- A power series is determined by its coefficients: this is the
non-degeneracy of the pairing on the power series side. -/
theorem PowerSeries.eq_of_coeff_eq {f g : PowerSeries R}
    (h : ∀ n, PowerSeries.coeff n f = PowerSeries.coeff n g) : f = g :=
  PowerSeries.ext h

end Polynomial

end
