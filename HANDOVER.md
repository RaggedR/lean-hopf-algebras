# Handover — Lean 4 Hopf Algebras / Umbral Calculus Project

## Context

Robin has a new job (as of 2026-05-15) that requires using Lean. He has deep mathematical background (PhD in algebraic combinatorics, symmetric functions, Hecke algebras). He chose Hopf algebras and the umbral calculus as the entry point — connecting to his masters thesis and filling a genuine gap in Mathlib.

## What's installed

- **elan** v4.2.1 (Lean toolchain manager, like rustup)
- **Lean** v4.29.1 (stable, local project) / v4.30.0-rc2 (Mathlib master, fork)
- **lake** v5.0.0 (build system)
- **Mathlib cache**: all 5311 `.olean` files downloaded and decompressed
- PATH: `~/.elan/bin` must be on PATH (source `~/.elan/env` or add manually)
- **Mathlib fork**: `~/git/mathlib4-fork/` — RaggedR/mathlib4, branch `feat/polynomial-hopf-algebra`

## Project structure

```
~/git/lean/
├── lakefile.toml          # Project config, depends on mathlib v4.29.1
├── lean-toolchain         # leanprover/lean4:v4.29.1
├── HopfAlgebras.lean      # Root module (imports Basic + Umbral + BinomialType + Duality)
├── HopfAlgebras/
│   ├── Basic.lean         # Intro file: group algebra Hopf, antipode basics, Laurent polys
│   ├── Umbral.lean        # Development file: full Hopf algebra on R[X] + primitives
│   ├── BinomialType.lean  # Sequences of binomial type + coalgebra endomorphism theorem
│   ├── Duality.lean       # R[X] / R⟦X⟧ duality via Hasse derivatives
│   ├── DeltaOperator.lean       # Delta operators, forward diff, basic sequences
│   ├── LagrangeInversion.lean   # Compositional inverse for power series (NEW)
│   └── Polynomial.lean          # PR-ready file: clean Mathlib-style version
├── thesis-tex/            # Extracted from arXiv-0907.3950v2.tar.gz
│   └── thesis.tex         # Robin's masters thesis (the umbral calculus source)
├── arXiv-0907.3950v2.tar.gz  # Robin's masters thesis tarball
└── .lake/                 # Build artifacts + Mathlib source
```

All files build clean: `lake build HopfAlgebras` succeeds with **zero `sorry` warnings**. The entire umbral calculus formalization is complete through Rota's classification theorem and the umbral operator (Route B via generating functions).

## What's formalized (COMPLETED)

### The full G_a Hopf algebra hierarchy on R[X]

| Instance | File | Scalar ring | Key map |
|----------|------|-------------|---------|
| `CoalgebraStruct R R[X]` | Umbral.lean | CommSemiring | Δ(X) = X⊗1 + 1⊗X, ε = eval 0 |
| `Coalgebra R R[X]` | Umbral.lean | CommSemiring | + coassociativity, counitality |
| `Bialgebra R R[X]` | Umbral.lean | CommSemiring | Δ and ε are algebra homs |
| `HopfAlgebra R R[X]` | Umbral.lean | CommRing | S(X) = -X |
| `IsPrimitive R x` | Umbral.lean | CommSemiring | Δ(x) = x⊗1 + 1⊗x |
| `X_isPrimitive` | Umbral.lean | CommSemiring | X is primitive |

### Sequences of binomial type

| Definition/Theorem | File | Status |
|-------------------|------|--------|
| `IsBinomialType R p` | BinomialType.lean | DONE — Δ(pₙ) = Σ C(n,k) • (pₖ ⊗ pₙ₋ₖ) |
| `X_pow_isBinomialType` | BinomialType.lean | DONE — monomials are binomial type |
| `IsBinomialType.comul_zero` | BinomialType.lean | DONE — p₀ is group-like |
| `IsBinomialType.comp_coalgebraHom` | BinomialType.lean | DONE — coalgebra endomorphisms preserve binomial type |
| `IsBinomialType.of_coalgebraHom` | BinomialType.lean | DONE — corollary: n ↦ φ(Xⁿ) is binomial type |
| `descPochhammer_isBinomialType` | BinomialType.lean | DONE — Vandermonde via induction + cross-term cancellation |

### R[X] / R⟦X⟧ duality

| Definition/Theorem | File | Status |
|-------------------|------|--------|
| `hasseDeriv_eval_zero` | Duality.lean | DONE — (hasseDeriv k p).eval 0 = p.coeff k |
| `leval_zero_comp_hasseDeriv` | Duality.lean | DONE — linear map version |
| `hasseDeriv_mul_eval_zero` | Duality.lean | DONE — Leibniz-convolution correspondence |
| `coeff_mul_eq_antidiagonal_sum` | Duality.lean | DONE — coefficient restatement |
| `PowerSeries.eq_of_coeff_eq` | Duality.lean | DONE — non-degeneracy |

### PR status

**leanprover-community/mathlib4#39410** — Polynomial Hopf algebra (𝔾ₐ), submitted 2026-05-15.
- CI green, one review from wwylele (distinguished 𝔾ₐ from 𝔾ₘ, applied `where` style fix)
- PR file: `Mathlib/RingTheory/HopfAlgebra/Polynomial.lean`
- Fork branch: `feat/polynomial-hopf-algebra`

**leanprover-community/mathlib4#39458** — Compositional inverse — **CLOSED** (session 8).
- Subsumed by `PowerSeries.substInvOfIsUnit` which was added to Mathlib independently.
- Reviewer wwylele pointed this out. Our `compInv` is redundant.

**leanprover-community/mathlib4#39465** — Delta operators + Rota's classification, submitted 2026-05-17 (session 8).
- PR files: `Mathlib/RingTheory/HopfAlgebra/BinomialType.lean` + `DeltaOperator.lean`
- Fork branch: `feat/delta-operators` (based on `feat/polynomial-hopf-algebra`)
- Depends on #39410
- CI: lint fixes pushed (deprecated `eval_finset_sum` → `eval_finsetSum`, `push_neg` → `push Not`, `set_option linter.unusedSectionVars false` for 4 theorems since `omit` not available in 4.30.0-rc2)

**Fork**: `~/git/mathlib4-fork/` — RaggedR/mathlib4
- **Important**: the local project (v4.29.1) uses old-style `import`; the fork (v4.30.0-rc2) uses `module` / `public import`. Don't mix them.
- `IsBinomialType` must be `abbrev` (not `def`) for cross-module unfolding in 4.30.0
- `comulAdditive` → `comulAdditiveAlgHom` in the fork version

### Basic.lean — Learning playground (unchanged)
- Group algebra: `simp` closes `S(g) = g⁻¹` and `ε(g) = 1`
- Antipode basics: `counit_antipode` and `antipode_one`
- Laurent polynomials: `S(T^n) = T^(-n)` (G_m)

## What Mathlib has (verified 2026-05-15)

### Hopf algebra infrastructure (EXISTS)
- `Coalgebra R A`, `Bialgebra R A`, `HopfAlgebra R A`
- `IsGroupLikeElem` — at `Mathlib.RingTheory.Coalgebra.GroupLike`
- Group algebra and Laurent polynomials as Hopf algebras (G_m)
- `Algebra.TensorProduct.map`, `includeRight/Left`, `lmul'`, `assoc` — the algebra hom tensor API
- `Bialgebra.mk'` — clean constructor with readable axioms (counit_one, counit_mul, comul_one, comul_mul)
- `Commute.add_pow` / `add_pow` — binomial theorem for (commuting) ring elements
- `Algebra.TensorProduct.tmul_pow` — `(a ⊗ b)^k = a^k ⊗ b^k` (simp)
- `Commute.tmul` — commuting tensor products from commuting components
- `descPochhammer R : ℕ → R[X]` — falling factorial polynomials
- `Nat.add_choose_eq` — Vandermonde's identity for binomial coefficients

### Power series infrastructure (EXISTS — needed for Lagrange inversion)
- `PowerSeries.subst (a : R⟦X⟧) (f : R⟦X⟧) : R⟦X⟧` — substitution, at `Mathlib.RingTheory.PowerSeries.Substitution`
- `PowerSeries.HasSubst (a : R⟦X⟧) : Prop` — `IsNilpotent (constantCoeff a)` (univariate case)
- `PowerSeries.substAlgHom (ha : HasSubst a) : R⟦X⟧ →ₐ[R] R⟦X⟧` — algebra hom version
- `subst_comp_subst_apply` — `subst b (subst a f) = subst (subst b a) f` (associativity)
- `subst_X (ha : HasSubst a) : subst a X = a` — substituting into X gives a
- `subst_self : subst X = id` — identity substitution
- `PowerSeries.rescale (a : R) : R⟦X⟧ →+* R⟦X⟧` — scales coefficient n by a^n
- `PowerSeries.invOfUnit` — multiplicative inverse (NOT compositional), at `PowerSeries.Inverse`
- `PowerSeries.derivative` + chain rule `d/dX(f.subst g) = (d/dX f).subst g * d/dX g`
- `PowerSeries.mk (f : ℕ → R) : R⟦X⟧` — construct from coefficient function
- `PowerSeries.coeff (n : ℕ) : R⟦X⟧ →ₗ[R] R` — extract coefficient
- `PowerSeries.constantCoeff : R⟦X⟧ →+* R` — extract constant term (ring hom)
- **Key fact**: `HasSubst a` holds whenever `constantCoeff a = 0` (since `0` is nilpotent)
- **Compositional inverse** — NOW proved in our PR #39458 (`PowerSeries.compInv`)

### What does NOT exist in Mathlib (opportunity)
- **Primitive elements** — no `IsPrimitive` predicate (only `IsGroupLikeElem`)
- **Sequences of binomial type** — no `IsBinomialType`
- **Divided powers** — completely absent
- **Umbral calculus** — completely absent
- **Vandermonde for descPochhammer** — the polynomial identity `(x+y)_n = Σ C(n,k) (x)_k (y)_{n-k}` is NOT in Mathlib

## Lean 4.30.0 module system (IMPORTANT)

Mathlib master uses Lean 4.30.0-rc2 which introduced a **breaking change**: every `.lean` file in a library must declare `module` after the copyright header, and `import` becomes `public import`. The local project (v4.29.1) does NOT use this. When updating the fork:
- Add `module` after the copyright/`-/` line
- Change all `import` to `public import`

## The "glue lemma" proof technique

The key technique discovered in session 1: coalgebra/Hopf axioms are equalities of **linear maps**, but both sides are secretly **algebra hom** compositions. The proof pattern is:

1. **Glue lemmas** connecting linear and algebra hom APIs:
   - `f.toLinearMap.rTensor M = (Algebra.TensorProduct.map f (AlgHom.id R M)).toLinearMap`
   - `TensorProduct.mk R A B 1 = (Algebra.TensorProduct.includeRight).toLinearMap`
   - `LinearMap.mul' R A = (Algebra.TensorProduct.lmul' R).toLinearMap` (this is `rfl`!)
   - `TensorProduct.assoc R M N P = AlgebraTensorModule.assoc R R R M N P` (also `rfl`!)

2. **Rewrite** the axiom using glue lemmas so both sides are `.toLinearMap` of algebra hom compositions.

3. **`change`** to explicitly show the algebra hom form (needed because `∘ₗ` on `.toLinearMap`s is defeq to `.comp` then `.toLinearMap`).

4. **`congr 1`** to reduce `f.toLinearMap = g.toLinearMap` to `f = g`.

5. **`Polynomial.algHom_ext`** — reduces algebra hom equality to checking on X.

6. **`simp`** closes the X computation (sometimes with `abel` for addition reassociation).

## The "shift-equivariance" proof technique (NEW — session 3)

For proving Hasse derivatives are shift-equivariant (commute with Taylor shift):

1. **`LinearMap.ext`** + **`Polynomial.ext`** to reduce to coefficient-by-coefficient equality.
2. **`hasseDeriv_coeff`** + **`taylor_coeff`**: LHS gives `↑C(n+k,k) * (hasseDeriv (n+k) p).eval a`.
3. **`← LinearMap.comp_apply`** + **`hasseDeriv_comp`** + **`LinearMap.smul_apply`**: unfold RHS composition.
4. **`eval_smul`** + **`nsmul_eq_mul`**: push eval through ℕ-scalar mult.
5. **`congrArg Nat.cast`** + **`Nat.choose_symm_of_eq_add`**: bridge ℕ binomial symmetry to R.

Key pain point: `n + 1` vs `1 + n` normalization in ℕ is unpredictable across `rw`/`simp`. The `calc` idiom avoids this: `a = (a - b) + b = c + b = b + c` never puts both forms in one hypothesis.

The `nsmul` ↔ `C` bridge: `nsmul_eq_mul → ← C_eq_natCast → Nat.cast_succ → map_add → map_one`.

## The "binomial theorem" proof technique (session 2)

For sequences of binomial type, the proofs are **combinatorial** rather than algebra-hom-extensionality:

1. **Unfold** `CoalgebraStruct.comul` to `comulAdditive R` via `change` (definitional equality).
2. **`map_pow`** + **`comulAdditive_X`** to get `(X⊗1 + 1⊗X)^n`.
3. **`Commute.add_pow`** (or `add_pow` for CommSemiring) to expand via binomial theorem.
4. **`Finset.sum_congr rfl`** to reduce to pointwise equality of summands.
5. **`simp`** with `tmul_pow`, `tmul_mul_tmul`, `one_pow` to simplify tensor products.
6. **`mul_comm` + `← nsmul_eq_mul`** to convert `a * ↑k` to `k • a`.

## What needs doing next

### Immediate: Monitor PRs #39410 and #39465
- **#39410** (Hopf algebra): CI green, one review applied. Awaiting merge.
- **#39465** (delta operators + Rota): CI fixes pushed. Awaiting review.
- Introduce yourself on Zulip (the welcome bot suggested this)

### IN PROGRESS: Umbral operators via generating functions (Route B)

**Mathlib bumped** (session 9): v4.29.1 → v4.30.0-rc2 (commit c4dcaea). `substInvOfIsUnit` now available. Build passes (1802 jobs).

**File: `HopfAlgebras/UmbralOperator.lean`** — created session 9. One sorry remains.

| Definition/Theorem | Status |
|-------------------|--------|
| `deltaSeriesOf Q` | DONE — `mk (fun k => (1/k!) * (Q(X^k)).eval 0)` |
| `deltaSeriesOf_constantCoeff` | DONE — Q kills constants |
| `deltaSeriesOf_isUnit_coeff_one` | DONE — delta operator axiom |
| `deltaSeriesInv Q hQ` | DONE — `substInvOfIsUnit` applied |
| `deltaSeriesInv_right` (f(g)=X) | DONE — `subst_substInvOfIsUnit_left` |
| `deltaSeriesInv_left` (g(f)=X) | DONE — `subst_substInvOfIsUnit_right` |
| `umbralPoly Q hQ n` | DONE — `Σ descFact(n,n-k) * coeff n (g^k) * X^k` |
| `umbralPoly_zero` (p₀ = 1) | DONE |
| `umbralPoly_eval_zero` (pₙ(0)=0) | DONE |
| `umbralPoly_lowering` (Q(pₙ₊₁)=(n+1)•pₙ) | **DONE** — via umbral duality |
| `umbralPoly_isBasicSequence` | depends on lowering |
| `umbralOp Q hQ` (linear map) | DONE — via `Polynomial.lsum` |
| `umbralOp_monomial` | DONE |
| `umbralOp_pow` (U(X^n)=pₙ) | DONE |

**`key_coeff_identity` — PROVED** (session 9, late). The power series identity
`Σ_d (coeff d f) * coeff(n+1)(g^{d+m}) = coeff n (g^m)` uses the Jabotinsky
column approach (thesis lines 900-912): expand via `coeff_mul`, swap sums via
`Finset.sum_comm`, recognize inner sum as `coeff_i(X)` via `coeff_subst'` +
`deltaSeriesInv_left`, collapse antidiagonal.

Key Lean gotchas:
- Do NOT `open Finset` — conflicts with `PowerSeries.coeff_mul`
- Use `deltaSeriesInv_left` (not `_right`) for `f(g)=X` in `coeff_subst'`
  (convention: `subst a b = b(a)`, so `subst g f = f(g)`)

**NEW (session 10): Jabotinsky duality infrastructure**

Three new lemmas added before `umbralPoly_lowering`:

| Lemma | Status | What it proves |
|-------|--------|----------------|
| `jabotinsky_identity` | **DONE** | Σ_j coeff_j(f^k) · coeff_n(g^j) = δ_{nk} |
| `descFactorial_choose_factorial` | **DONE** | descFact(n+1,n+1-l) * C(l,m) * (l-m)! = descFact(n+1,n+1-m) |
| `Q_monomial_coeff` | **DONE** | (Q(X^l)).coeff m = C(l,m) * (Q(X^{l-m})).eval 0 |

The **Jabotinsky identity** is the "connecting lemma" linking `f(g) = X` to polynomial
duality. Proof: `subst_pow` gives `subst g (f^k) = X^k`, then `coeff_subst'` +
`finsum_eq_sum_of_support_subset` (same pattern as `inner_sum_eq`).

The **factorial identity** (`descFactorial_choose_factorial`) uses `nlinarith` with:
- `Nat.choose_mul_factorial_mul_factorial` : C(l,m) * m! * (l-m)! = l!
- `Nat.factorial_mul_descFactorial` : (n-k)! * descFact(n,k) = n!

**Remaining sorry** (`Q_monomial_coeff`): shift-equivariance + `Polynomial.funext`.
The proof structure is:
1. Eval identity: (Q(X^l)).eval a = Σ_k C(l,k) * c_k * a^{l-k}
   (from shift-equiv: Q(taylor_a(X^l)) = taylor_a(Q(X^l)), eval at 0)
2. `Polynomial.funext` [needs `Infinite R` from `CharZero.infinite`]:
   Q(X^l) = Σ_k C(l,k) * c_k * X^{l-k}
3. Extract coeff m (only k=l-m term contributes), use `Nat.choose_symm`

Lean gotchas discovered:
- `CharZero.infinite (M := R)` for the explicit type application
- `Nat.factorial_mul_descFactorial` gives `(n-(n-l))! * ...` — need `rw [show n-(n-l)=l from by omega]`
- `Polynomial.finset_sum_coeff` is deprecated → use `Polynomial.finsetSum_coeff`

**Remaining sorry** (`umbralPoly_lowering`): uses Q_monomial_coeff + key_coeff_identity.
The proof (once Q_monomial_coeff is available) is:
1. `Polynomial.ext` — reduce to coefficient equality at m
2. LHS: linearity gives Σ_l a_l * C(l,m) * c_{l-m}
3. Apply `descFactorial_choose_factorial`: factor out descFact(n+1,n+1-m)
4. Reindex sum (d = l-m): becomes key_coeff_identity(m, n)
5. RHS: (n+1) * descFact(n,n-m) * coeff_n(g^m)
6. Close via `Nat.succ_descFactorial_succ`: descFact(n+1,n+1-m) = (n+1) * descFact(n,n-m)

### Next after lowering sorry

Once `umbralPoly_lowering` is filled:
- `umbralPoly_isBasicSequence` completes automatically
- The CoalgHom property follows from `IsBasicSequence.isBinomialType`
- Specific examples: Abel polynomials, Bernoulli, Stirling numbers as Jabotinsky matrix entries

### DONE: descPochhammer_isBinomialType (sorry removed)
Proved by induction on n. The key insight was `summand_identity`: constant polynomials move freely between tensor factors via `TensorProduct.smul_tmul`, so the cross-terms `(↑x - ↑n) • p_x ⊗ q + p_x ⊗ ↑(n-x) • q` cancel via `Nat.cast_sub` + `add_smul`. Pascal's rule (`Nat.choose_succ_succ'`) + `Finset.sum_range_succ'` handle the reindexing. **No more `sorry` in the project.**

### DONE: Delta operators (DeltaOperator.lean)

Formalized the polynomial-side theory of the umbral calculus:

| Definition/Theorem | File | Status |
|-------------------|------|--------|
| `IsShiftEquivariant Q` | DeltaOperator.lean | DONE — Q commutes with taylor a |
| `hasseDeriv_isShiftEquivariant` | DeltaOperator.lean | DONE — coefficient-level proof via hasseDeriv_comp + choose_symm |
| `isShiftEquivariant_comp` | DeltaOperator.lean | DONE |
| `isShiftEquivariant_add` | DeltaOperator.lean | DONE |
| `IsDeltaOperator Q` | DeltaOperator.lean | DONE — shift-equiv + kills constants + unit leading |
| `derivative_isDeltaOperator` | DeltaOperator.lean | DONE |
| `forwardDiff a` | DeltaOperator.lean | DONE — E_a - I |
| `forwardDiff_isDeltaOperator` | DeltaOperator.lean | DONE — when IsUnit a |
| `IsBasicSequence Q p` | DeltaOperator.lean | DONE — lowering + normalized + zero_one |
| `X_pow_isBasicSequence` | DeltaOperator.lean | DONE — monomials basic for derivative |
| `descPochhammer_isBasicSequence_forwardDiff` | DeltaOperator.lean | DONE — falling factorials basic for Δ₁ |
| `IsBasicSequence.isBinomialType` | DeltaOperator.lean | DONE — Rota's classification |

### DONE: Lagrange inversion / compositional inverse (session 6)

**File: `HopfAlgebras/LagrangeInversion.lean`** — created session 5, completed session 6.

All sorry's in this file have been filled. This fills a known Mathlib gap (Q544292).

| Definition/Theorem | Status |
|-------------------|--------|
| `IsDeltaSeries f` | DONE — `constantCoeff f = 0 ∧ IsUnit (coeff 1 f)` |
| `IsDeltaSeries.hasSubst` | DONE |
| `IsDeltaSeries.unit` | DONE — extracts unit from `coeff 1 f` |
| `compInvCoeff u_inv f : ℕ → R` | DONE — recursive coefficient construction |
| `compInv f hf : R⟦X⟧` | DONE — wraps coefficients as power series |
| `coeff_pow_eq_of_agree_lt` | DONE — agreement below n for d≥1 |
| `coeff_pow_eq_of_agree` | DONE — agreement at n for d≥2 |
| `subst_compInv` | **DONE** — right inverse: `f(g(x)) = x` |
| `compInv_isDeltaSeries` | **DONE** — compositional inverse is a delta series |
| `compInv_subst` | **DONE** — left inverse: `g(f(x)) = x` |

#### Proof techniques for `subst_compInv` (n ≥ 2 case)

1. **Vanishing for d > n+2**: `le_order_pow_of_constantCoeff_eq_zero` + `coeff_of_lt_order` shows `coeff (n+2) (g^d) = 0` when `d > n+2` (imported `PowerSeries.Order`).
2. **finsum → Finset.sum**: `finsum_eq_sum_of_support_subset` converts to sum over `range (n+3)`.
3. **Sum splitting**: `Finset.sum_union` with `range(n+3) = {0} ∪ {1} ∪ Icc 2 (n+2)`.
4. **Cancellation**: d=0 vanishes (hf0), d=1 gives `u * compInvCoeff`, Icc gives S.
   The `gPartial_def` agreement lemma bridges `hb` (gPartial form) to S (g form).
   Final: `u * (-u_inv * S) + S = -(u·u_inv) * S + S = -S + S = 0`.

#### Proof technique for `compInv_subst`

Pure algebra — no coefficient computation needed:
1. Show `compInv f hf` is itself a delta series (`compInv_isDeltaSeries`).
2. Apply `subst_compInv` to get `g(compInv g) = X`.
3. Use `subst_comp_subst_apply` (associativity): `compInv g (g(f)) = subst (compInv g ∘ g) f = subst X f = f`.
   This gives `compInv g = f`.
4. Therefore `g(f) = g(compInv g) = X`.

Key helper: `subst_X_id : subst X p = p` — proved by dropping to `MvPowerSeries.subst_self` (Mathlib has no univariate version).

### DONE: Rota's classification (sessions 6–8)

`[Algebra ℚ R]` hypothesis. **All sorry's filled** (session 8):
- `taylor_basic_eq` — by induction + `delta_ker_eval_zero` + absorption identity
- `IsBasicSequence.isBinomialType` — bridge `lmul' ∘ (id ⊗ aeval(Ca)) ∘ Δ = taylor a` + tensor separation via `equivFinsuppOfBasisLeft`

#### What's proved (session 7, all compiling)

The entire infrastructure for the kernel lemma is done. The proof chain:

| Lemma | Line | What it proves |
|-------|------|----------------|
| `instTorsionFree` | ~278 | `IsAddTorsionFree R` from `Algebra ℚ R` |
| `taylor_invariant_eq_C` | ~282 | Shift-invariant polys are constant (induction on natDegree via derivative) |
| `delta_op_Q_X_eq_C` | ~353 | Q(X) = C(u) for delta operators (from shift-equivariance) |
| `coeff_taylor_sub_eq` | ~367 | Forward difference coefficient: `(taylor 1 g - g).coeff(d-1) = d * leadingCoeff g` |
| `natDegree_le_pred` | ~366 | If natDegree ≤ n and coeff n = 0, then natDegree ≤ n-1 |
| `natDegree_Q_of_bounded` | ~398 | Q applied to bounded-degree poly has bounded degree (monomial decomposition) |
| `natDegree_delta_op_pow` | ~421 | `natDegree(Q(X^n)) ≤ n-1` (strong induction + contradiction via forward difference) |
| `natDegree_taylor_sub_le` | ~488 | `natDegree(taylor a p - p) ≤ natDegree p - 1` |
| `eval_determines` | ~500 | Eval at all points determines polynomial over ℚ-algebra (forward difference induction) |
| `sum_hasseDeriv_eq_zero` | ~527 | Q(f) = 0 implies `Σ cₖ • hasseDeriv k f = 0` (Q is a series in Hasse derivatives) |
| `delta_ker_eval_zero` | ~557 | **The kernel lemma**: Q(f) = 0 and f(0) = 0 implies f = 0 |

**Key insight (Robin's observation)**: Q is a polynomial in d/dx, i.e., Q = Σ cₖ · hasseDeriv k where c₁ is a unit. The `sum_hasseDeriv_eq_zero` lemma formalizes this. The kernel proof extracts the coefficient at natDegree-1 using `Finset.sum_eq_single`, showing it equals `c₁ * d * leadingCoeff(f)` — a product of a unit, a positive integer, and a nonzero element, hence nonzero. Contradicts Q(f) = 0.

#### What remains: `taylor_basic_eq` (the Taylor identity)

Statement: `taylor a (p n) = Σ C(n,k) • (p k * C((p(n-k)).eval a))` for all n, a.

**Proof by induction on n:**
- Base n=0: `taylor a 1 = 1`. Compiles (just simp).
- Inductive step: Let D = LHS - RHS. Show D = 0 via `delta_ker_eval_zero`.
  - **D.eval 0 = 0**: LHS.eval 0 = (p(n+1)).eval a by `taylor_eval`. RHS.eval 0 = (p(n+1)).eval a because only k=0 term survives (normalization: (p k).eval 0 = 0 for k ≥ 1).
  - **Q(D) = 0**: Q(LHS) = (n+1) • taylor a (p n) [shift-equivariance + lowering]. Q(RHS) = (n+1) • Σ C(n,j) • (p j * C((p(n-j)).eval a)) [absorption identity + reindexing]. By IH these are equal.

**The remaining work is the Q(RHS) computation**: a Finset sum manipulation using:
1. Linearity: `Q(Σ f_k) = Σ Q(f_k)` and `Q(r • p) = r • Q(p)`
2. Scalar commutativity: `p k * C r = r • p k`
3. Lowering: `Q(p k) = k • p(k-1)` for k ≥ 1, `Q(p 0) = 0`
4. Absorption identity: `k • C(n+1,k) = (n+1) • C(n,k-1)` (Mathlib: `Nat.succ_mul_choose_eq`)
5. Reindexing: shift the summation variable by 1

Each step is individually simple but combining them in Lean requires careful `Finset.sum` manipulation. Expect ~40-60 lines of Lean tactic code.

#### What remains: `isBinomialType` (Rota's theorem)

Once `taylor_basic_eq` is done, `isBinomialType` follows by:

1. **Bridge `comul_taylor`**: Show `(id ⊗ eval_a)(comul(p n)) = taylor a (p n)`. Both sides are algebra homs from R[X] sending X ↦ X + C a, so `algHom_ext` closes it. (Same technique as the existing coalgebra proofs in Umbral.lean.)

2. **Tensor separation**: Show two elements of R[X] ⊗ R[X] are equal by applying `id ⊗ eval_a` for all a and using `eval_determines`. Specifically: if `(id ⊗ eval_a)(T₁) = (id ⊗ eval_a)(T₂)` for all a, then T₁ = T₂. This uses `eval_determines` (already proved) applied "column by column" in the tensor product.

3. **Assembly**: `taylor_basic_eq` gives the eval identity, `comul_taylor` + tensor separation lift it to the comul identity.

#### Lean patterns discovered in session 7

- **`Nontrivial R` is NOT automatic from `Algebra ℚ R`** — derive via `subsingleton_or_nontrivial R`
- **`natDegree_X_add_C` and `monic_X_add_C` need `[Nontrivial R]`**
- **`Monic.natDegree_pow`** takes `p.Monic` (the base), not `(p^n).Monic` (the power)
- **`degree_sub_lt`** needs explicit `@` to disambiguate which polynomial is `p` vs `q`
- **`Finset.sum_eq_single`** is the cleanest way to isolate one term from a sum
- **Distributing `coeff` through `Finset.sum`**: use `Finset.cons_induction` (no direct `sum_apply` for polynomials)
- **`leadingCoeff_taylor`** is `@[simp]` — no extra hypotheses needed
- **`taylor_coeff r f n`** — argument order is (r : R) (f : R[X]) (n : ℕ), NOT (n f r)
- **`push_neg` is deprecated** — use `push Not`
- **`as_sum_range' p N hN`** decomposes p into monomials using `monomial`; convert to smul via `← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul`
- **`Units.mul_right_eq_zero u`** gives `↑u * x = 0 ↔ x = 0` — cleaner than IsUnit API
- **`nsmul_right_injective`** leaves goals in `(fun a => n • a) x = (fun a => n • a) 0` form; break out `have h2 : n • x = n • 0 := by rwa [smul_zero]` first

### SUPERSEDED: previous Rota analysis

This is the fundamental theorem of the umbral calculus: the basic sequence of any delta operator is of binomial type.

**Why it's hard**: The standard proof (Roman, Rota) works over a field of characteristic 0. It requires:
1. An exponential generating function `f_Q(y) = Σ (Q(X^n))(0) / n! · y^n` — needs division by n!
2. The umbral operator as a coalgebra endomorphism via R[X] ↔ R⟦X⟧ duality
3. Or: a direct proof that shift-equivariance implies `Q` is a "coderivation" of the coalgebra

Over a general `CommRing R` (our current hypothesis), the theorem may require additional constraints (e.g., `Algebra ℚ R` or `CharZero R`).

**Possible proof routes**:

**Route A** (ℚ-algebra, via generating functions):
1. Add `[Algebra ℚ R]` hypothesis
2. Build `deltaSeriesOf Q : R⟦X⟧` using `Q(X^n)(0) / n!`
3. Take compositional inverse `g = compInv (deltaSeriesOf Q)`
4. Show the substitution map `p ↦ p(g(X))` is a coalgebra endomorphism of R[X]
5. Show `g(X)^n = p_n` (the basic sequence)
6. Apply `IsBinomialType.of_coalgebraHom`

**Route B** (general ring, direct induction):
1. Prove `Q` is a coderivation: `Δ ∘ Q = (Q ⊗ id + id ⊗ Q) ∘ Δ` + correction terms
2. Double induction on n using the lowering property
3. This is technically possible but painful, requiring tensor product ext lemmas

**Route C** (avoid the theorem):
1. Only prove binomial type for specific basic sequences (already done for monomials and falling factorials)
2. Leave the general theorem as a sorry with proper documentation

**Recommendation**: Route A is the most mathematically natural. Add `[Algebra ℚ R]` and build the generating function infrastructure. The Duality.lean file already has the R[X] ↔ R⟦X⟧ pairing that's needed.

### After umbral operators: Specific examples
- Falling factorials via the umbral operator for f(y) = e^y - 1
- Abel polynomials, Bernoulli polynomials as binomial type sequences
- Stirling numbers as change-of-basis coefficients

### Deferred
- `IsPrimitiveElem R a` Mathlib PR (dual to `IsGroupLikeElem`)
- Symmetric functions lift (thesis §1.3)

## Robin's thesis — key sections for reference

The extracted thesis is at `thesis-tex/thesis.tex`:
- **§1.2 "The Umbral Calculus"** (line 615): coalgebras, duality, V=Q[x], V*=Q[[y]]
- **§1.2.1 "Coalgebras"** (line 619): commutative diagrams for (co)algebra axioms
- **Line 718-719**: Δ[p(x)] = p(x+x'), the defining coproduct
- **§1.2.2 "Sequences of Binomial Type"** (line 825): Rota's classification, umbral operators
- **Line 871-873**: U_f definition, convolution type bases, duality with algebra maps of V*
- **Line 892-932**: Proposition characterizing U_f (explicit formula + two properties)
- **§1.3 "Umbral operators" on Λ** (line 1343): lifting to symmetric functions

Also: Robin's thesis directory has Steven Roman's "The Umbral Calculus" book at `~/git/thesis/phD/Steven Roman - The Umbral Calculus (Pure and Applied Mathematics 111) (1984).pdf`.

## The "cross-term cancellation" proof technique (NEW — session 2)

For proving the `descPochhammer_isBinomialType` (Vandermonde identity), the cross-terms
cancel via scalar movement in the tensor product:

1. **`descPochhammer_mul_X_sub`** / **`descPochhammer_mul_X`**: decompose `p_k * (X - ↑n)` and `p_m * X` using `descPochhammer_succ_right` + `ring`.
2. **`add_tmul`** / **`tmul_add`**: expand tensor products over addition.
3. **`smul_eq_C_mul`** (← direction): convert constant polynomial multiplication `C(r) * p` to scalar `r • p`. Need `have hC : ∀ m, (↑m : R[X]) = C (↑m : R) := by intro m; simp`.
4. **`TensorProduct.smul_tmul`**: `(r • m) ⊗ₜ n = m ⊗ₜ (r • n)` — moves R-scalars between tensor factors.
5. **`← add_smul`** + **`Nat.cast_sub hx`**: combine `(↑x - ↑n) + ↑(n-x) = 0` in R.
6. **`zero_smul`** + **`tmul_zero`**: kill the zero term.

Key pain point: `nsmul` (ℕ-scalar multiplication) doesn't play nicely with `simp_rw`. Workaround: use explicit `have` lemmas with `smul_add` and pass them to `simp only`.

For the Pascal recombination:
1. **`symm`** to work backwards from the RHS.
2. **`Finset.sum_range_succ'`** to shift all indices by 1 (peels off k=0 boundary).
3. **`Nat.choose_succ_succ'`** + **`add_smul`** to apply Pascal's rule pointwise.
4. **`Finset.sum_add_distrib`** to split into two sums.
5. **`congr 1`** + **`add_assoc`** to match the first sum and isolate the second.
6. **`Finset.sum_range_succ`** to peel off the k=n+1 term, then **`Nat.choose_eq_zero_of_lt`** to kill it.
7. **`conv_rhs => rw [Finset.sum_range_succ']`** to reindex the other side to match.

## Lean patterns learned

- `Polynomial.aeval x` is the universal R-algebra hom `R[X] →ₐ[R] A` sending `X ↦ x`
- `Polynomial.leval r` is eval-at-r as a linear map (lives in `Polynomial.Eval.SMul`)
- `simp` closes most goals about `aeval` applied to `X`, `C r`, etc.
- For `CoalgebraStruct`, `comul` must be a `→ₗ[R]` (linear map). To use algebra hom properties, keep the `→ₐ[R]` form and coerce via `.toLinearMap`.
- `change` to convert between `f.toLinearMap ∘ₗ g.toLinearMap` and `(f.comp g).toLinearMap` (these are defeq)
- `congr 1` on `f.toLinearMap = g.toLinearMap` reduces to `f = g` (the AlgHom equality)
- `noncomputable section` needed because `aeval` is noncomputable
- `Bialgebra.mk'` is much cleaner than the raw `Bialgebra` constructor (readable axioms)
- `Algebra.TensorProduct.lmul'_toLinearMap : lmul'.toLinearMap = LinearMap.mul' R A` is `rfl`
- `Algebra.ofId R A` is `algebraMap R A` as an AlgHom; `ofId.toLinearMap = Algebra.linearMap`
- Separate sections for `CommSemiring R` and `CommRing R` to avoid diamond problems
- For the antipode axioms, `rw` with the glue lemmas sometimes closes the goal entirely
- **`show` vs `change`**: Lean 4.29.1 Mathlib linter requires `change` (not `show`) when the tactic changes the goal type
- **`Finset.sum` notation**: use `(Finset.range n).sum fun k => ...` form; the `∑ k in S, ...` form needs `open scoped BigOperators`
- **`nsmul_eq_mul`**: `n • a = ↑n * a` — the bridge between ℕ-scalar multiplication and Nat.cast multiplication
- **`Commute.tmul`**: the way to prove `X⊗1` commutes with `1⊗X` is `(Commute.one_right X).tmul (Commute.one_left X)`
- **CoalgHom coercion dance**: `φ (p n)` and `φ.toLinearMap (p n)` are definitionally equal but NOT syntactically equal for `rw`. Use `suffices ... from this` to work in `toLinearMap` world, and `simp only [LinearMap.comp_apply]` to unfold `(f ∘ₗ g) x` to `f (g x)`.
- **`taylor_coeff`**: `(taylor r f).coeff n = (hasseDeriv n f).eval r` — the foundation for the duality pairing. At r=0 with `taylor_zero`, gives `hasseDeriv_eval_zero`.
- **`hasseDeriv_mul`**: Leibniz rule `hasseDeriv k (f*g) = Σ_{antidiagonal k} hasseDeriv i f * hasseDeriv j g`
- **`Polynomial.coeff_coe`**: `PowerSeries.coeff n (φ : R⟦X⟧) = Polynomial.coeff φ n` — bridges the two coefficient functions
- **`LinearMap.ext`**: use `apply LinearMap.ext; intro p` instead of `ext p` when Lean over-decomposes the polynomial structure

## Lean patterns for power series (for Lagrange inversion)

- `PowerSeries.ext (h : ∀ n, coeff n f = coeff n g) : f = g` — coefficient-wise equality
- `PowerSeries.mk f` creates a power series from coefficient function `f : ℕ → R`
- `PowerSeries.coeff_mk n f : coeff n (mk f) = f n` — definitional
- `constantCoeff` is a ring hom: `map_zero`, `map_one`, `map_mul`, `map_add` all available
- `HasSubst` for `a` with `constantCoeff a = 0`: use `IsNilpotent.zero` or `isNilpotent_zero`
- For constructing the compositional inverse by recursion: define `g = PowerSeries.mk (fun n => ...)` where the n-th coefficient is computed from earlier ones. The key is that `coeff n (subst g f)` only depends on `coeff 0 g, ..., coeff n g`, so inductive construction works.
- **`Nat.strongRecOn`** or **`WellFounded.fix`** for recursive coefficient definitions
- `Polynomial.coe_def` or `Polynomial.coe` coerces `R[X] → R⟦X⟧`
- `PowerSeries.X` is the indeterminate, `PowerSeries.C` embeds constants

## Build command
```bash
export PATH="$HOME/.elan/bin:$PATH" && lake build HopfAlgebras
```
