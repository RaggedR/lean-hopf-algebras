# Future Luxury: Connecting to Module.Dual

## Observation

Mathlib has `Module.Dual R M := M →ₗ[R] R` with dual bases (`Basis.toDual`),
the double-dual isomorphism (`Module.evalEquiv`), and annihilators.

Our coefficient pairing in `Duality.lean` — where `lcoeff n` extracts the nth
coefficient — is exactly `Basis.toDual` applied to `Polynomial.basisMonomials R`.
This means:

```
Module.Dual R R[X] ≅ R⟦X⟧
```

where a power series g corresponds to the functional f ↦ Σ (coeff n g) * (coeff n f).

## Reformulation of Rota's Classification

Once this bridge is in place, the classification theorem (`UmbralOperator.lean`)
can be restated as:

> Delta operators on R[X] correspond bijectively to elements of the dual
> with vanishing constant term and unit linear coefficient.

This is a one-line reformulation of what `deltaSeriesOf` already proves concretely
via compositional inversion of formal power series.

## What it would take

| Step | Difficulty | Notes |
|------|-----------|-------|
| `lcoeff_eq_toDual : (basisMonomials R).toDual = lcoeff R` | Easy | Bridge lemma |
| `dualEquivPowerSeries : Module.Dual R R[X] ≃ₗ[R] R⟦X⟧` | Medium | Every functional determined by values on monomials |
| Coalgebra dualizes to algebra on R⟦X⟧ | Hard | General "dual of coalgebra = algebra" not in Mathlib |
| Delta operators as dual elements | Easy | Follows from the above once established |

## Why it matters

This would connect our concrete umbral calculus formalization to Mathlib's abstract
linear algebra, making it possible to:
- State theorems about delta operators in coordinate-free language
- Leverage Mathlib's dual space API (annihilators, reflexivity) for free
- Potentially upstream the "dual of a coalgebra is an algebra" result

---

## Extension: Sheffer Sequences (and Appell as special case)

### The mathematical picture

A **Sheffer sequence** `{sₙ}` relative to a delta operator `Q` satisfies:

```
Q(sₙ₊₁) = (n+1) • sₙ
```

Same recurrence as a basic sequence, but we drop the initial condition `sₙ(0) = δₙ₀`.
Instead, there exists an invertible power series `A(t)` (with `A(0) ≠ 0`) such that:

```
Σ sₙ(x) tⁿ/n! = (1/A(f(t))) · exp(x · g(t))
```

where `f` is the delta series of `Q` and `g` is its compositional inverse.

Equivalently: `sₙ = A⁻¹(pₙ)` where `pₙ` is the basic sequence and `A⁻¹` is an
invertible shift-invariant operator (an element of the "umbral algebra").

**Appell sequences** are the special case `Q = D` (ordinary derivative):
- Basic sequence of D is `{xⁿ}`, so `g(t) = t`
- Generating function: `Σ sₙ(x) tⁿ/n! = (1/A(t)) · exp(xt)`
- Examples: Bernoulli polynomials (`A(t) = (eᵗ - 1)/t`), Hermite (`A(t) = e^{t²/2}`)

### How this extends what we have

Our current formalization has:
1. Delta operators with `IsDeltaOperator` ✓
2. Basic sequences with `IsBasicSequence` (includes `pₙ(0) = δₙ₀`) ✓
3. Delta series and compositional inverse via `deltaSeriesOf` ✓
4. The classification: basic sequences ↔ sequences of binomial type ✓

The extension is:

| New concept | Definition strategy | Depends on |
|-------------|-------------------|------------|
| `IsShefferSequence Q A s` | `Q(s(n+1)) = (n+1) • s(n)` | `IsDeltaOperator` |
| `IsAppellSequence s` | `IsShefferSequence derivative A s` | above |
| Sheffer identity | `sₙ(x+y) = Σ C(n,k) pₖ(y) · sₙ₋ₖ(x)` | `IsBinomialType` |
| Appell identity | `sₙ(x+y) = Σ C(n,k) sₖ(x) · yⁿ⁻ᵏ` | specialization |
| Generating function | `1/A(f(t)) · exp(x·g(t))` | `deltaSeriesOf`, `substInvOfIsUnit` |

### The key insight: invertible operators in the umbral algebra

A shift-invariant operator `T : R[X] →ₗ[R] R[X]` that commutes with all Taylor
shifts can be expanded as a power series in any delta operator Q:

```
T = Σ aₖ Qᵏ    where aₖ = (T(pₖ)).eval 0 / k!
```

This is already implicit in our `deltaSeriesOf` — the delta series *is* this
expansion for `T = Q` expressed in terms of itself. For Sheffer sequences, we need
the expansion for a general invertible `T` (the "transfer operator" — note the
connection to `Transfer.lean`!).

### Concrete plan

1. **Define `IsShefferSequence`**: weaken `IsBasicSequence` by dropping `eval_zero`
2. **Prove uniqueness**: given Q and initial values `{sₙ(0)}`, the Sheffer sequence
   is unique (same induction as basic sequences, but with different base case)
3. **Sheffer = A⁻¹(basic)**: show that `sₙ = A⁻¹(pₙ)` where `A` is determined by
   the generating series of initial values `Σ sₙ(0) tⁿ/n!`
4. **Appell specialization**: for `Q = D`, basic sequence is `{xⁿ}`, so
   `sₙ = A⁻¹(xⁿ)` and the Appell identity follows from binomial theorem
5. **Examples**: Bernoulli polynomials, Euler polynomials, Hermite polynomials

### What's already in Mathlib

- `Polynomial.bernoulli` exists in Mathlib (the Bernoulli polynomials)
- We could prove they form an Appell sequence as a nice application
- Hermite polynomials are in `Mathlib.Analysis.SpecialFunctions.Hermite` (probabilist's)

### Difficulty estimate

Medium. The core definitions and the Sheffer identity should follow the same
patterns as `DeltaOperator.lean`. The generating function connection requires
composing what `UmbralOperator.lean` already does with one additional power series
division (by `A(f(t))`), which is just `PowerSeries.invOfUnit` composed with
substitution.
