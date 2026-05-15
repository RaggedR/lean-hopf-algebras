/-
  HopfAlgebras/Umbral.lean — The coalgebra structure on Q[x] from the umbral calculus

  Following Langer (arXiv:0907.3950), §1.2:

  The polynomial ring Q[x] is a coalgebra with:
    Δ(p(x)) = p(x + x')     (comultiplication = "addition of alphabets")
    ε(p(x)) = p(0)           (counit = evaluation at zero)

  This makes x a *primitive element*: Δ(x) = x ⊗ 1 + 1 ⊗ x.

  The divided powers x^n/n! form the natural basis:
    Δ(x^n/n!) = Σ_k (x^k/k!) ⊗ (x^(n-k)/(n-k)!)

  This is the additive group scheme 𝔾_a — dual to the multiplicative group
  scheme 𝔾_m already formalized in Mathlib via Laurent polynomials.
-/
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

open Polynomial TensorProduct

open scoped Polynomial TensorProduct

/-!
## The coalgebra structure on R[X]

For any commutative semiring R, the polynomial ring R[X] is a coalgebra with:
- comultiplication: the algebra hom X ↦ X ⊗ 1 + 1 ⊗ X
- counit: evaluation at 0

This is the coordinate ring of the additive group scheme 𝔾_a.
-/

noncomputable section

variable (R : Type*) [CommSemiring R]

/-- The comultiplication on R[X]: the unique R-algebra homomorphism sending
    X ↦ X ⊗ 1 + 1 ⊗ X. As a linear map, this encodes Δ(p(x)) = p(x + x'). -/
def Polynomial.comulAdditive : R[X] →ₐ[R] R[X] ⊗[R] R[X] :=
  Polynomial.aeval ((X : R[X]) ⊗ₜ 1 + 1 ⊗ₜ (X : R[X]))

/-- The counit on R[X]: evaluation at 0. This is ε(p) = p(0). -/
def Polynomial.counitAdditive : R[X] →ₗ[R] R :=
  Polynomial.leval 0

-- Basic computations

@[simp]
theorem Polynomial.comulAdditive_X :
    Polynomial.comulAdditive R (X : R[X]) = (X : R[X]) ⊗ₜ 1 + 1 ⊗ₜ (X : R[X]) := by
  simp [Polynomial.comulAdditive]

@[simp]
theorem Polynomial.counitAdditive_X :
    Polynomial.counitAdditive R (X : R[X]) = 0 := by
  simp [Polynomial.counitAdditive, Polynomial.leval]

@[simp]
theorem Polynomial.comulAdditive_C (r : R) :
    Polynomial.comulAdditive R (C r) = (C r) ⊗ₜ 1 := by
  simp [Polynomial.comulAdditive]

@[simp]
theorem Polynomial.counitAdditive_C (r : R) :
    Polynomial.counitAdditive R (C r) = r := by
  simp [Polynomial.counitAdditive, Polynomial.leval]

/-!
## Coalgebra instance

The three coalgebra axioms (coassociativity, left counitality, right counitality)
all reduce to checking equality of R-algebra homomorphisms out of R[X], which by the
universal property of polynomials reduces to checking on the generator X.
-/

/-- The additive group coalgebra structure on R[X].

This is the 𝔾_a structure: Δ(X) = X ⊗ 1 + 1 ⊗ X, ε(X) = 0.
Coassociativity holds because both (Δ ⊗ id) ∘ Δ and (id ⊗ Δ) ∘ Δ send
X to X⊗1⊗1 + 1⊗X⊗1 + 1⊗1⊗X — the "three-slot addition" x + x' + x''. -/
instance Polynomial.additiveCoalgebraStruct : CoalgebraStruct R R[X] where
  comul := (Polynomial.comulAdditive R).toLinearMap
  counit := Polynomial.counitAdditive R

-- Auxiliary: the comultiplication as an algebra homomorphism, for use in proofs
-- where we need to exploit that Δ is a ring map (not just linear).
private theorem comul_eq_comulAdditive :
    (CoalgebraStruct.comul : R[X] →ₗ[R] _) = (Polynomial.comulAdditive R).toLinearMap := rfl

private theorem counit_eq_counitAdditive :
    (CoalgebraStruct.counit : R[X] →ₗ[R] _) = Polynomial.counitAdditive R := rfl

-- The key insight: both sides of each coalgebra axiom are algebra homomorphisms
-- out of R[X] (disguised as linear maps). Since R[X] is free on X, algebra hom
-- equality reduces to checking on X alone (algHom_ext). We exploit this by
-- constructing the algebra hom versions and converting.

/-- The counit as an algebra homomorphism: evaluation at 0.
This is the same as `counitAdditive` but retains the algebra hom structure. -/
private def Polynomial.counitAlgHom : R[X] →ₐ[R] R :=
  Polynomial.aeval (0 : R)

@[simp]
private theorem Polynomial.counitAlgHom_X :
    Polynomial.counitAlgHom R (X : R[X]) = 0 := by
  simp [Polynomial.counitAlgHom]

@[simp]
private theorem Polynomial.counitAlgHom_C (r : R) :
    Polynomial.counitAlgHom R (C r) = r := by
  simp [Polynomial.counitAlgHom]

private theorem Polynomial.counitAdditive_eq_counitAlgHom :
    Polynomial.counitAdditive R = (Polynomial.counitAlgHom R).toLinearMap := by
  ext n
  simp [Polynomial.counitAdditive, Polynomial.leval, Polynomial.counitAlgHom]

-- Glue lemma: rTensor of the linear counit = toLinearMap of the algebra hom version
private theorem rTensor_counit_eq_map :
    (Polynomial.counitAdditive R).rTensor R[X] =
    (Algebra.TensorProduct.map (Polynomial.counitAlgHom R)
     (AlgHom.id R R[X])).toLinearMap := by
  ext x y
  simp [LinearMap.rTensor_tmul, Polynomial.counitAdditive_eq_counitAlgHom]

-- Glue lemma: lTensor of the linear counit = toLinearMap of the algebra hom version
private theorem lTensor_counit_eq_map :
    (Polynomial.counitAdditive R).lTensor R[X] =
    (Algebra.TensorProduct.map (AlgHom.id R R[X])
     (Polynomial.counitAlgHom R)).toLinearMap := by
  ext x y
  simp [LinearMap.lTensor_tmul, Polynomial.counitAdditive_eq_counitAlgHom]

-- Glue lemma: mk 1 = includeRight.toLinearMap
private theorem mk_one_eq_includeRight :
    TensorProduct.mk R R R[X] 1 =
    (Algebra.TensorProduct.includeRight : R[X] →ₐ[R] R ⊗[R] R[X]).toLinearMap := by
  ext y
  simp [Algebra.TensorProduct.includeRight_apply]

-- Glue lemma: (mk).flip 1 = includeLeft.toLinearMap
private theorem mk_flip_one_eq_includeLeft :
    (TensorProduct.mk R R[X] R).flip 1 =
    (Algebra.TensorProduct.includeLeft : R[X] →ₐ[R] R[X] ⊗[R] R).toLinearMap := by
  ext y
  simp [Algebra.TensorProduct.includeLeft_apply, LinearMap.flip_apply]

-- Glue lemma: rTensor of comul = toLinearMap of the algebra hom version
private theorem rTensor_comul_eq_map :
    ((Polynomial.comulAdditive R).toLinearMap).rTensor R[X] =
    (Algebra.TensorProduct.map (Polynomial.comulAdditive R)
     (AlgHom.id R R[X])).toLinearMap := by
  ext x y
  simp [LinearMap.rTensor_tmul]

-- Glue lemma: lTensor of comul = toLinearMap of the algebra hom version
private theorem lTensor_comul_eq_map :
    ((Polynomial.comulAdditive R).toLinearMap).lTensor R[X] =
    (Algebra.TensorProduct.map (AlgHom.id R R[X])
     (Polynomial.comulAdditive R)).toLinearMap := by
  ext x y
  simp [LinearMap.lTensor_tmul]

instance Polynomial.additiveCoalgebra : Coalgebra R R[X] :=
  { Polynomial.additiveCoalgebraStruct R with
    rTensor_counit_comp_comul := by
      rw [counit_eq_counitAdditive, comul_eq_comulAdditive, rTensor_counit_eq_map,
          mk_one_eq_includeRight]
      -- Goal: (map counitAlgHom id).toLinearMap ∘ₗ comulAdditive.toLinearMap
      --     = includeRight.toLinearMap
      change ((Algebra.TensorProduct.map (Polynomial.counitAlgHom R)
               (AlgHom.id R R[X])).comp (Polynomial.comulAdditive R)).toLinearMap = _
      congr 1
      apply Polynomial.algHom_ext
      simp [Polynomial.comulAdditive, Polynomial.counitAlgHom,
            Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeRight_apply]
    lTensor_counit_comp_comul := by
      rw [counit_eq_counitAdditive, comul_eq_comulAdditive, lTensor_counit_eq_map,
          mk_flip_one_eq_includeLeft]
      change ((Algebra.TensorProduct.map (AlgHom.id R R[X])
               (Polynomial.counitAlgHom R)).comp (Polynomial.comulAdditive R)).toLinearMap = _
      congr 1
      apply Polynomial.algHom_ext
      simp [Polynomial.comulAdditive, Polynomial.counitAlgHom,
            Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeft_apply]
    coassoc := by
      -- Both sides are algebra hom compositions (disguised as linear maps).
      -- Both send X ↦ X⊗(1⊗1) + 1⊗(X⊗1 + 1⊗X) — the "three-slot addition" x+x'+x''.
      -- Strategy: rewrite to algebra hom form, then algHom_ext (check on X).
      --
      -- Key fact: TensorProduct.assoc R M N P = AlgebraTensorModule.assoc R R R M N P
      -- (by AlgebraTensorModule.assoc_eq, which is rfl), and the latter is the
      -- toLinearEquiv of Algebra.TensorProduct.assoc (by assoc_toLinearEquiv, also rfl).
      rw [comul_eq_comulAdditive, rTensor_comul_eq_map, lTensor_comul_eq_map]
      -- LHS: assoc ∘ₗ (map Δ id).toLinearMap ∘ₗ Δ.toLinearMap
      -- RHS: (map id Δ).toLinearMap ∘ₗ Δ.toLinearMap
      -- Convert to algebra hom equality:
      change ((Algebra.TensorProduct.assoc R R R R[X] R[X] R[X]).toAlgHom.comp
              ((Algebra.TensorProduct.map (Polynomial.comulAdditive R)
                (AlgHom.id R R[X])).comp
               (Polynomial.comulAdditive R))).toLinearMap =
             ((Algebra.TensorProduct.map (AlgHom.id R R[X])
               (Polynomial.comulAdditive R)).comp
              (Polynomial.comulAdditive R)).toLinearMap
      congr 1
      apply Polynomial.algHom_ext
      simp only [Polynomial.comulAdditive, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe,
            AlgHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, aeval_X,
            map_add, map_one, Algebra.TensorProduct.one_def,
            Algebra.TensorProduct.assoc_tmul,
            TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel }

/-!
## Bialgebra instance

The four bialgebra axioms (counit preserves 1 and *, comul preserves 1 and *)
hold because both `comulAdditive` and `counitAlgHom` are algebra homomorphisms.
-/

instance Polynomial.additiveBialgebra : Bialgebra R R[X] :=
  Bialgebra.mk' R R[X]
    (by -- counit_one: ε(1) = 1
      simp [counit_eq_counitAdditive, Polynomial.counitAdditive_eq_counitAlgHom])
    (by -- counit_mul: ε(a * b) = ε(a) * ε(b)
      intro a b
      simp [counit_eq_counitAdditive, Polynomial.counitAdditive_eq_counitAlgHom, map_mul])
    (by -- comul_one: Δ(1) = 1
      simp [comul_eq_comulAdditive])
    (by -- comul_mul: Δ(a * b) = Δ(a) * Δ(b)
      intro a b
      simp [comul_eq_comulAdditive, map_mul])

/-!
## Primitive elements

An element x of a coalgebra is *primitive* if Δ(x) = x ⊗ 1 + 1 ⊗ x.
In the polynomial coalgebra, X is the canonical primitive element.

This is the Lie algebra / infinitesimal version of the group-like condition.
Group-like: Δ(g) = g ⊗ g  (finite, "exponential")
Primitive:  Δ(x) = x⊗1 + 1⊗x  (infinitesimal, "logarithmic")

The relationship: if g = exp(tx) formally, then Δ(g) = g⊗g iff Δ(x) = x⊗1 + 1⊗x.
-/

/-- An element of a coalgebra (which is also a semiring) is primitive if
    Δ(x) = x ⊗ 1 + 1 ⊗ x. -/
def IsPrimitive {A : Type*} [CommSemiring R] [Semiring A] [Module R A]
    [CoalgebraStruct R A] (x : A) : Prop :=
  CoalgebraStruct.comul x = x ⊗ₜ[R] 1 + 1 ⊗ₜ x

/-- X is a primitive element of the polynomial coalgebra. -/
theorem Polynomial.X_isPrimitive : IsPrimitive R (X : R[X]) := by
  unfold IsPrimitive
  change (Polynomial.comulAdditive R).toLinearMap X = _
  simp [Polynomial.comulAdditive]

end -- end CommSemiring section

/-!
## Hopf algebra instance

The antipode is S(X) = -X, extended as an algebra homomorphism.
This requires R to be a commutative ring (for negation).
The antipode axiom m ∘ (S ⊗ id) ∘ Δ = η ∘ ε reduces to:
  S(X) · 1 + 1 · X = -X + X = 0 = C(ε(X)) = C(0) = 0   ✓
-/

noncomputable section

variable (R : Type*) [CommRing R]

/-- The antipode on R[X]: the unique R-algebra homomorphism sending X ↦ -X.
This is the "inversion" on 𝔾_a: if Δ encodes addition (x ↦ x + x'),
then S encodes negation (x ↦ -x). -/
def Polynomial.antipodeAdditive : R[X] →ₐ[R] R[X] :=
  Polynomial.aeval (-X : R[X])

@[simp]
theorem Polynomial.antipodeAdditive_X :
    Polynomial.antipodeAdditive R (X : R[X]) = -X := by
  simp [Polynomial.antipodeAdditive]

@[simp]
theorem Polynomial.antipodeAdditive_C (r : R) :
    Polynomial.antipodeAdditive R (C r) = C r := by
  simp [Polynomial.antipodeAdditive]

-- Glue: rTensor of antipode = toLinearMap of algebra hom map
private theorem rTensor_antipode_eq_map :
    (Polynomial.antipodeAdditive R).toLinearMap.rTensor R[X] =
    (Algebra.TensorProduct.map (Polynomial.antipodeAdditive R)
     (AlgHom.id R R[X])).toLinearMap := by
  ext x y; simp [LinearMap.rTensor_tmul]

-- Glue: lTensor of antipode = toLinearMap of algebra hom map
private theorem lTensor_antipode_eq_map :
    (Polynomial.antipodeAdditive R).toLinearMap.lTensor R[X] =
    (Algebra.TensorProduct.map (AlgHom.id R R[X])
     (Polynomial.antipodeAdditive R)).toLinearMap := by
  ext x y; simp [LinearMap.lTensor_tmul]

-- Glue: the RHS of the antipode axiom as an algebra hom
-- Algebra.linearMap ∘ counit = (aeval 0 : R[X] →ₐ R[X]).toLinearMap
private theorem antipode_rhs_eq :
    (Algebra.linearMap R R[X]) ∘ₗ (Polynomial.counitAdditive R) =
    (Polynomial.aeval (0 : R[X]) : R[X] →ₐ[R] R[X]).toLinearMap := by
  ext p
  simp [Algebra.linearMap_apply, Polynomial.counitAdditive, Polynomial.leval]

instance Polynomial.additiveHopfAlgebra : HopfAlgebra R R[X] where
  antipode := (Polynomial.antipodeAdditive R).toLinearMap
  mul_antipode_rTensor_comul := by
    -- Both sides are algebra hom compositions: check on X.
    -- LHS sends X ↦ S(X)·1 + 1·X = -X + X = 0
    -- RHS sends X ↦ algebraMap(ε(X)) = algebraMap(0) = 0
    rw [comul_eq_comulAdditive, counit_eq_counitAdditive,
        rTensor_antipode_eq_map, ← Algebra.TensorProduct.lmul'_toLinearMap,
        antipode_rhs_eq]
    change ((Algebra.TensorProduct.lmul' R : R[X] ⊗[R] R[X] →ₐ[R] R[X]).comp
            ((Algebra.TensorProduct.map (Polynomial.antipodeAdditive R)
              (AlgHom.id R R[X])).comp
             (Polynomial.comulAdditive R))).toLinearMap =
           (Polynomial.aeval (0 : R[X]) : R[X] →ₐ[R] R[X]).toLinearMap
    congr 1
    apply Polynomial.algHom_ext
    simp [Polynomial.comulAdditive, Polynomial.antipodeAdditive,
          Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
  mul_antipode_lTensor_comul := by
    rw [comul_eq_comulAdditive, counit_eq_counitAdditive,
        lTensor_antipode_eq_map, ← Algebra.TensorProduct.lmul'_toLinearMap,
        antipode_rhs_eq]
    change ((Algebra.TensorProduct.lmul' R : R[X] ⊗[R] R[X] →ₐ[R] R[X]).comp
            ((Algebra.TensorProduct.map (AlgHom.id R R[X])
              (Polynomial.antipodeAdditive R)).comp
             (Polynomial.comulAdditive R))).toLinearMap =
           (Polynomial.aeval (0 : R[X]) : R[X] →ₐ[R] R[X]).toLinearMap
    congr 1
    apply Polynomial.algHom_ext
    simp [Polynomial.comulAdditive, Polynomial.antipodeAdditive,
          Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul]

end
