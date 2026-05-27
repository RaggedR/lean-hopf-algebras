# Hopf Algebras, Umbral Calculus, and Symmetric Graphs in Lean 4

A formalization of the **umbral calculus** (Rota's finite operator calculus) and
**Sabidussi's representation theorem** for vertex-transitive graphs, built on
[Mathlib](https://github.com/leanprover-community/mathlib4).

**4,185 lines of Lean 4. Zero sorry's** (except 3 in an in-progress module).

## What's here

### Hopf Algebra on R[X] — the additive group scheme G_a

The polynomial ring R[X] carries a Hopf algebra structure dual to the
multiplicative group scheme G_m already in Mathlib:

| File | Content |
|------|---------|
| `Polynomial.lean` | Coalgebra, bialgebra, and Hopf algebra instances on R[X] via Delta(X) = X tensor 1 + 1 tensor X, epsilon(X) = 0, S(X) = -X. Submitted to Mathlib as [PR #39410](https://github.com/leanprover-community/mathlib4/pull/39410). |
| `Duality.lean` | The Hasse-eval bridge: `(hasseDeriv k p).eval 0 = p.coeff k`. Leibniz-convolution correspondence showing R[[X]] multiplication is dual to the coalgebra comultiplication. Submitted as [PR #39465](https://github.com/leanprover-community/mathlib4/pull/39465). |

### Rota's Classification of Sheffer Sequences

The main theorem: **basic sequences of delta operators are exactly the sequences
of binomial type.** This is the fundamental theorem of the umbral calculus.

| File | Content |
|------|---------|
| `BinomialType.lean` | Definition of binomial type sequences. Proofs that monomials X^n and falling factorials satisfy the binomial convolution. Coalgebra endomorphisms preserve binomial type. |
| `DeltaOperator.lean` | Delta operators, shift-equivariance, basic sequences. **Rota's classification theorem** (`IsBasicSequence.isBinomialType`): the proof reduces the coproduct identity to a Taylor identity via `comul_taylor_bridge`, then lifts back using `eval_tensor_zero`. |
| `AscPochhammer.lean` | Rising factorials are of binomial type, via the backward difference operator. |

### Umbral Operators via Generating Functions

The "second half" of the umbral calculus: recovering basic sequences from
compositional inverses of delta series, and proving the lowering property
via Jabotinsky duality.

| File | Content |
|------|---------|
| `UmbralOperator.lean` | Delta series, compositional inverses (via Mathlib's `substInvOfIsUnit`), umbral polynomials, **Jabotinsky identity**, orthogonality of the derivative pairing, adjoint property, non-degeneracy, and the lowering property `Q(p_{n+1}) = (n+1) * p_n`. Submitted as [PR #39498](https://github.com/leanprover-community/mathlib4/pull/39498). |
| `LagrangeInversion.lean` | Compositional inverse of formal power series by coefficient recursion. `IsDeltaSeries`, `compInv`, both left and right inverse properties. |
| `Lah.lean` | Lah numbers `L(n,k) = C(n-1,k-1) * n!/k!` as Jabotinsky matrix entries of the geometric series `y/(1-y)`. |
| `Composition.lean` | Compositional inverse relationship between exp and log as formal power series: `log(exp(X)) = X`. |
| `Transfer.lean` | The transfer formula: expanding one basic sequence in another. Basic sequences form a basis (degree n, unit leading coefficient). *In progress: 3 sorry's.* |

### Sabidussi's Representation Theorem and Lorimer's Theorem

A formalization of the theory of symmetric (arc-transitive) graphs from
[arXiv:1306.4798](https://arxiv.org/abs/1306.4798).

| File | Content |
|------|---------|
| `GraphAction.lean` | Group actions on simple graphs. `GraphAction`, `IsVertexTransitive`, `IsArcTransitive`. Vertex-transitive + locally transitive implies arc-transitive. |
| `CosetGraph.lean` | Sabidussi's coset graph construction `Sab(G, H, D)` with connection set axioms (double-coset stable, symmetric, disjoint from H). Coset graphs are vertex-transitive. |
| `Representation.lean` | **Sabidussi's representation theorem**: every vertex-transitive graph is isomorphic to a coset graph. The orbit-stabilizer equivalence is a graph isomorphism. |
| `Symmetric.lean` | **Lorimer's theorem** (forward): `Sab(G, H, HaH)` is arc-transitive when `a` is an involution not in `H`. (Reverse): arc-transitive graphs have a single double coset. |
| `Quotient.lean` | **Lorimer's quotient theorem**: the quotient of `Sab(G, H, D)` by a G-invariant partition is `Sab(G, K, KDK)`. |

## Relationship to Mathlib

Three components have been submitted as standalone Mathlib PRs:

- **[#39410](https://github.com/leanprover-community/mathlib4/pull/39410)** — Hopf algebra instance on R[X] (`Polynomial.lean`)
- **[#39465](https://github.com/leanprover-community/mathlib4/pull/39465)** — Hasse-eval duality bridge (`Duality.lean`)
- **[#39498](https://github.com/leanprover-community/mathlib4/pull/39498)** — Umbral operators and Jabotinsky duality (`UmbralOperator.lean`)

This repository contains the complete standalone formalization, including the
parts that depend on all three PRs together (Rota's classification, the transfer
formula, Sabidussi theory).

## References

- Langer, R., *Determinantal bases and the symmetric group*, [arXiv:0907.3950](https://arxiv.org/abs/0907.3950)
- Langer, R., *Symmetric Graphs and their Quotients*, [arXiv:1306.4798](https://arxiv.org/abs/1306.4798)
- Roman, S., *The Umbral Calculus*, Academic Press, 1984
- Rota, G.-C., Kahaner, D., Odlyzko, A., *Finite Operator Calculus*, JMAA 42 (1973)
- Sabidussi, G., *Vertex-transitive graphs*, Monatsh. Math. 68 (1964), 426-438

## Building

Requires Lean 4.30 and Mathlib.

```bash
lake build
```

## License

MIT
