/-
  HopfAlgebras/Basic.lean — First explorations of Hopf algebras in Lean 4 / Mathlib

  This file serves as a learning playground: importing Mathlib's Hopf algebra
  definitions, examining the API, and proving small results to build fluency.
-/
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Exploring Hopf algebras in Lean 4

## What is a Hopf algebra?

A Hopf algebra over a commutative ring R is simultaneously:
- an R-algebra (with multiplication m and unit η)
- an R-coalgebra (with comultiplication Δ and counit ε)
- a bialgebra (Δ and ε are algebra morphisms)
- equipped with an antipode S : A →ₗ[R] A satisfying:
    m ∘ (S ⊗ id) ∘ Δ = η ∘ ε    and    m ∘ (id ⊗ S) ∘ Δ = η ∘ ε

The classic example: for a group G, the group algebra k[G] is a Hopf algebra with
  Δ(g) = g ⊗ g,  ε(g) = 1,  S(g) = g⁻¹.
-/

open HopfAlgebra Coalgebra

-- Section 1: The group algebra as a Hopf algebra
-- Mathlib already provides the instance MonoidAlgebra.instHopfAlgebra.
-- Let's verify we can use it.

section GroupAlgebra

variable {R : Type*} [CommSemiring R]
variable {G : Type*} [Group G]

-- The antipode on the group algebra sends g to g⁻¹
-- (and extends linearly, composing with the base antipode on R)
example (g : G) : antipode R (MonoidAlgebra.single g (1 : R)) =
    MonoidAlgebra.single g⁻¹ (1 : R) := by
  simp

-- The counit sends every group element to 1
example (g : G) : counit (R := R) (MonoidAlgebra.single g (1 : R)) = 1 := by
  simp [MonoidAlgebra.counit_single]

end GroupAlgebra

-- Section 2: The antipode preserves the counit (already in Mathlib, but
-- let's see how to access it)

section AntipodeBasics

variable {R : Type*} [CommSemiring R]
variable {A : Type*} [Semiring A] [HopfAlgebra R A]

-- ε ∘ S = ε  (the counit is invariant under the antipode)
example (a : A) : counit (R := R) (antipode R a) = counit a :=
  counit_antipode a

-- S(1) = 1
example : antipode R (1 : A) = 1 :=
  antipode_one

end AntipodeBasics

-- Section 3: Laurent polynomials as a Hopf algebra
-- This models the coordinate ring of the multiplicative group scheme 𝔾ₘ.

section LaurentPoly

variable {R : Type*} [CommSemiring R]

-- The antipode sends T^n to T^(-n) — this is "inversion" on 𝔾ₘ
example (n : ℤ) : antipode R (LaurentPolynomial.T n : LaurentPolynomial R) =
    LaurentPolynomial.T (-n) :=
  LaurentPolynomial.antipode_T n

end LaurentPoly
