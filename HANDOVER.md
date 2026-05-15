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
│   └── Polynomial.lean    # PR-ready file: clean Mathlib-style version
├── thesis-tex/            # Extracted from arXiv-0907.3950v2.tar.gz
│   └── thesis.tex         # Robin's masters thesis (the umbral calculus source)
├── arXiv-0907.3950v2.tar.gz  # Robin's masters thesis tarball
└── .lake/                 # Build artifacts + Mathlib source
```

All files build clean: `lake build HopfAlgebras` succeeds (one expected `sorry` warning in BinomialType.lean).

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
| `descPochhammer_isBinomialType` | BinomialType.lean | SORRY — falling factorials, proof strategy documented |

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

## The "binomial theorem" proof technique (NEW)

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

### NEXT: Umbral operators (thesis §1.2.2, lines 871-932)

The duality framework (Duality.lean) is now in place. The next step is defining umbral operators.

**What we have to build on:**
- `CoalgHom R R[X] R[X]` — Mathlib's bundled coalgebra homs (`Mathlib.RingTheory.Coalgebra.Hom`)
- `comp_coalgebraHom` — coalgebra endomorphisms preserve binomial type (BinomialType.lean)
- `hasseDeriv_eval_zero` — the Hasse derivative bridges R[X] and R⟦X⟧ (Duality.lean)

**Two approaches (pick one):**

**(A) Properties-first (thesis Prop, line 892):** Define U_f by its characterising properties:
  - `D ∘ U_f = U_f ∘ g(D)` where g is compositional inverse of a delta series f
  - `L ∘ U_f = L` where L = eval 0 (= coalgebra counit)
  - Show U_f is a coalgebra endomorphism, hence images are binomial type
  - Needs: `PowerSeries.comp` for formal composition, compositional inverses
  - Pro: follows thesis exactly. Con: needs formal composition infrastructure

**(B) Action-first:** Define U_f by its action on the divided power basis:
  - `U_f(X^n/n!) = p_n` where {p_n} is the convolution-type sequence dual to {g(y)^k}
  - Or more concretely: define U_f as a linear map R[X] → R[X] via its matrix (Jabotinsky matrix)
  - Show it's a coalgebra endomorphism using `comp_coalgebraHom`
  - Pro: avoids formal composition. Con: more combinatorial, less conceptual

**What's needed from Mathlib for either approach:**
- `PowerSeries.comp` or `PowerSeries.subst` — formal composition f(g(y))
- `PowerSeries.inv` or compositional inverse — g(y) such that f(g(y)) = y
- These exist but require topological/nilpotency assumptions (`HasSubst`, `HasEval`)

**Recommended scope for next session:**
1. Define a "delta series" predicate: `IsDeltaSeries f` iff `constantCoeff f = 0` and `coeff 1 f` is a unit
2. Define the umbral operator U_f as a linear map R[X] → R[X]
3. Prove it's a coalgebra endomorphism (so images are automatically binomial type)
4. The canonical example: f = X (identity delta series) gives U_X = id

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

## Build command
```bash
export PATH="$HOME/.elan/bin:$PATH" && lake build HopfAlgebras
```
