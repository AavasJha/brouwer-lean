# Brouwer's Laplacian conjecture and the Grone–Merris–Bai theorem in Lean 4

This repository has a complete, unconditional Lean 4 / Mathlib formalization of two theorems about Laplacian eigenvalues of finite simple graphs.

1. **The Grone–Merris–Bai theorem** (conjectured by R. Grone and R. Merris in 1994, proved by H. Bai, *Trans. AMS* 363 (2011), [arXiv:0911.2172](https://arxiv.org/abs/0911.2172)). The Laplacian spectrum is majorized by the conjugate degree sequence.
2. **Brouwer's Laplacian conjecture**, following the proof by P. K. Kothari and S. Tudose ([arXiv:2606.12197](https://arxiv.org/abs/2606.12197), June 2026). This proof uses the Grone–Merris–Bai theorem.

## Main theorems

```lean
theorem Brouwer.grone_merris_bai {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    topSum (G.isHermitian_lapMatrix ℝ) k ≤ ∑ v, (min (G.degree v) k : ℝ)

theorem Brouwer.brouwer {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    topSum (G.isHermitian_lapMatrix ℝ) k ≤ G.edgeFinset.card + (k * (k + 1) / 2 : ℝ)
```

- `topSum hA k` is the sum of the `k` largest eigenvalues. It uses `Matrix.IsHermitian.eigenvalues₀`, which lists them in decreasing order.
- `∑ v, min (deg v) k` is the sum of the first `k` terms of the conjugate degree sequence.

`#print axioms` for both theorems lists only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry` anywhere in the repository.

## Structure

| File | Contents |
|---|---|
| `Brouwer/Algebra.lean` | Lemmas 5.2, 5.5, 5.3 and 5.6 of Kothari–Tudose, for a symmetric idempotent `P` with `P·1 = 0`. |
| `Brouwer/Spectral.lean` | The easy half of Ky Fan's maximum principle, the eigenvector facts used, and the statement `GroneMerrisBai`. |
| `Brouwer/Main.lean` | Brouwer's conjecture assuming Grone–Merris–Bai (`brouwer_of_GMB`). |
| `Brouwer/Stage2/KyFan.lean` | The other half of Ky Fan's principle, subadditivity, and monotonicity. |
| `Brouwer/Stage2/CourantFischer.lean` | Courant–Fischer bounds for single eigenvalues, by a dimension count. |
| `Brouwer/Stage2/DavisKahan.lean` | Spectral projections and a Davis–Kahan bound in the Frobenius norm. |
| `Brouwer/Stage2/Blueprint.lean` | Edge deletion, monotonicity, Bai's Proposition 5(a) for split graphs, and the case `k = 1`. |
| `Brouwer/Stage2/Core.lean` | Bai's analytic core, Lemmas 6 to 11. This covers the homotopy, the uniform gap, continuity, the Riccati identity, the sign argument and the trace bound. |
| `Brouwer/Stage2/Assembly.lean` | Complements (Proposition 12), Lemma 13, the split graph `Ĝ`, the case analysis, and the final theorems. |

## Differences from the papers

**Kothari–Tudose.**
1. No nuclear or operator norms are used. Inequality (5.4) is exactly Lemma 3.3 for the split graphs `G_r`. It follows from Grone–Merris–Bai and the easy half of Ky Fan.
2. The routing inequality (Lemma 5.5) is proved by induction on the number of distinct values. No sorting or Abel summation is needed.
3. Lemma 5.1 uses the eigenvectors with positive eigenvalue. These are automatically orthogonal to the all-ones vector.

**Bai.**
1. Continuity of the top eigenspace along the homotopy (Lemma 10) comes from a quantitative Davis–Kahan bound. The bound uses a uniform eigenvalue gap that is proved explicitly, which makes the spectral projection Lipschitz in `α`. The matrix `V` is then continuous, because it is built from the projection and the inverse of its clique block.
2. The clique block is invertible for every `α` by a dimension argument. No separate perturbation theory is needed.
3. The final trace bound is proved vertex by vertex, against `Σ_v min(deg v, N)` directly. This avoids the identity in Proposition 5(b).
4. Proposition 12 is used only in the two directions the argument needs. One is an eigenvalue bound for the complement, by Courant–Fischer. The other is a trace inequality, by Ky Fan with the projection `I − Q − J/n`.
5. The case `k = 1`, which the paper does not treat separately, is proved directly.

## Building

Lean `v4.37.0-rc1`, Mathlib commit `90e6eec9fe53b02d431c90718e4a1d22d67a204e` (pinned in `lake-manifest.json`).

```
lake exe cache get   # optional
lake build
lake env lean Check.lean
```

## AI assistance

This formalization was produced with substantial AI assistance (Anthropic's Claude), directed by the repository author. Lean checks every proof.
