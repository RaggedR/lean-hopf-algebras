# Lessons Learned

## Lean 4 / Mathlib Patterns

### `set_option ... in` syntax
The `set_option maxHeartbeats N in` directive must come BEFORE the docstring, not between the docstring and the theorem. Correct:
```lean
set_option maxHeartbeats 800000 in
/-- Docstring -/
theorem foo ...
```

### `set` vs `rw` conflict
`set f := expr` creates a let-binding and replaces `expr` with `f` in the goal. But `rw [lemma]` does SYNTACTIC matching — it won't find `f` when the lemma's statement uses `expr`. Fix: use `exact lemma` (uses definitional equality) or `unfold_let f` before `rw`.

### `Finset.mem_range` and `omega`
`omega` cannot reason about `k ∈ Finset.range (n + 1)`. Always extract the numeric fact first:
```lean
have hk : k < n + 1 := Finset.mem_range.mp hk
```

### `pow_succ` direction
`pow_succ a n : a ^ (n + 1) = a ^ n * a` (right multiplication). So `f^{m+1} = f^m * f`, and the antidiagonal of `coeff_mul` has pairs `(i, j)` where `i` indexes `f^m` and `j` indexes `f`. Use `(m, 1)` not `(1, m)`.

### `PowerSeries.coeff_of_lt_order` — no named arg `f`
The power series argument is implicit (`φ`). Use positional: `coeff_of_lt_order i (lt_of_lt_of_le ...)`.

### `push_neg` deprecated
Use `push Not` instead.

## Proof Architecture

### Duality proofs beat coefficient grinds
When a result follows from a bilinear pairing + non-degeneracy, build the pairing infrastructure (even if it's more code) rather than doing coefficient-by-coefficient computation. The individual lemmas (orthogonality, adjoint, non-degeneracy) are reusable.

### `Finset.sum_eq_single` for triangular arguments
When only one term of a sum survives (others vanish by order bounds or induction), `Finset.sum_eq_single` is the cleanest approach — it isolates the main term and gives two side goals (other terms vanish, element is in the set).
