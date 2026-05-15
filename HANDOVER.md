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
│   ├── DeltaOperator.lean # Delta operators, forward diff, basic sequences
│   └── Polynomial.lean    # PR-ready file: clean Mathlib-style version
├── thesis-tex/            # Extracted from arXiv-0907.3950v2.tar.gz
│   └── thesis.tex         # Robin's masters thesis (the umbral calculus source)
├── arXiv-0907.3950v2.tar.gz  # Robin's masters thesis tarball
└── .lake/                 # Build artifacts + Mathlib source
```

All files build clean: `lake build HopfAlgebras` succeeds (one expected `sorry` warning in DeltaOperator.lean — Rota's classification theorem, deferred pending Lagrange inversion).

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

**leanprover-community/mathlib4#39410** — submitted 2026-05-15.

- **CI had a build failure** due to Lean 4.30.0 `module` system change — **fixed and pushed** (commit 83446f3)
- The fix: added `module` keyword and `public import` to match v4.30.0 syntax
- **Important**: the local project (v4.29.1) uses old-style `import`; the fork (v4.30.0-rc2) uses `module` / `public import`. Don't mix them.
- PR file: `Mathlib/RingTheory/HopfAlgebra/Polynomial.lean`
- Fork: `~/git/mathlib4-fork/` on branch `feat/polynomial-hopf-algebra`
- Awaiting CI re-run and review

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
- **NO compositional inverse** — `∃ g, subst g f = X` is NOT proved for any f

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

### Immediate: Monitor PR #39410
- CI fix pushed (commit `1980b82`): added `public section` and removed unused simp args
- The two CI issues were: `linter.privateModule` (Lean 4.30.0 defaults to private) and `linter.unusedSimpArgs` (deprecated `AlgEquiv.toAlgHom_eq_coe` + unused `AlgHom.coe_coe`, `Algebra.TensorProduct.assoc_tmul`)
- Be prepared to split into 3 files if reviewers request it
- Introduce yourself on Zulip (the welcome bot suggested this)

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
| `IsBasicSequence.isBinomialType` | DeltaOperator.lean | SORRY — Rota's classification |

### NEXT: Lagrange inversion / compositional inverse (BLOCKS THE SORRY)

The `sorry` in `IsBasicSequence.isBinomialType` is the bridge between the polynomial side (delta operators) and the power series side (duality). Robin's thesis (lines 868-873) crosses this bridge via: delta series f → substitution algebra hom φ_f on R⟦X⟧ → adjoint U_f = coalgebra hom on R[X] → apply `comp_coalgebraHom` (already proved!). **Once we have compositional inverses, the sorry becomes trivial.**

An alternative proof via the coderivation property `(Q ⊗ id) ∘ Δ = Δ ∘ Q` was investigated but requires tensor product ext lemmas + `[Infinite R]` and is harder than the duality approach.

**Situation**: Lagrange inversion is a known gap in Mathlib (tracked as Q544292 in 1000.yaml, no declaration). The substitution infrastructure exists (`PowerSeries.subst`, `substAlgHom`, `subst_comp_subst`, chain rule) but no compositional inverse.

**Two levels:**
1. **Existence** (recursive coefficient construction) — only needs `a₁` unit, works over CommRing
2. **Explicit formula** `[yⁿ] g = (1/n) [yⁿ⁻¹] (y/f(y))ⁿ` — needs CharZero / ℚ-algebra

**Recommended scope:**
1. Define `IsDeltaSeries f` on `R⟦X⟧`: `constantCoeff f = 0` and `IsUnit (coeff 1 f)`
2. Construct the compositional inverse `g` by coefficient recursion using `PowerSeries.mk`
3. Prove `subst g f = X` and `subst f g = X` (formal inverse)
4. This would be a standalone Mathlib PR (filling a 1000-theorems gap!)
5. Fill the sorry: construct the umbral operator as adjoint of substAlgHom, apply `comp_coalgebraHom`

**Then connect both sides:**
- Delta series f ↔ delta operator Q = f(D) ↔ basic sequence {p_n} ↔ umbral operator U

### After: Specific examples
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
