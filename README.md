# Brouwer's Laplacian conjecture in Lean 4 (conditional on Grone–Merris–Bai)

This repository has a complete Lean 4 / Mathlib formalization of the proof of **Brouwer's Laplacian conjecture** by P. K. Kothari and S. Tudose ([arXiv:2606.12197](https://arxiv.org/abs/2606.12197), June 2026). The only assumption is the **Grone–Merris–Bai theorem** (H. Bai, *Trans. AMS* 363 (2011)), which enters as an explicit hypothesis.

## Main theorem

```lean
theorem Brouwer.brouwer_of_GMB {V : Type*} [Fintype V] [DecidableEq V]
    (hGMB : GroneMerrisBai V) (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    topSum (G.isHermitian_lapMatrix ℝ) k ≤ G.edgeFinset.card + (k * (k + 1) / 2 : ℝ)
```

- `topSum hA k` is the sum of the `k` largest eigenvalues (`Matrix.IsHermitian.eigenvalues₀`, sorted in decreasing order).
- `GroneMerrisBai V` says that every graph `H` on `V` satisfies `topSum (L_H) k ≤ ∑ v, min (deg v) k` for all `k`. The right side is the sum of the first `k` terms of the conjugate degree sequence.

`#print axioms Brouwer.brouwer_of_GMB` lists only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`.

## Structure

| File | Contents |
|---|---|
| `Brouwer/Algebra.lean` | Lemmas 5.2, 5.5, 5.3 and 5.6 of the paper, for a symmetric idempotent `P` with `P·1 = 0`. |
| `Brouwer/Spectral.lean` | The easy half of Ky Fan's maximum principle, the eigenvector facts used, and the statement of Grone–Merris–Bai. |
| `Brouwer/Main.lean` | The trace formula `tr(P L_H) = ½ Σ_{i~j} ‖P(e_i − e_j)‖²`, the split graphs, Lemma 3.3 for split graphs from GMB, the projection onto top eigenvectors (Lemma 5.1), and the main theorem. |

## Differences from the paper

1. **No nuclear or operator norms.** Inequality (5.4) in the proof of Lemma 5.5 is exactly Lemma 3.3 (the split trace inequality) for the split graphs `G_r`. We derive it from GMB together with the easy half of Ky Fan, so Lemma 3.2 is not needed.
2. **No sorting or Abel summation.** The routing inequality (Lemma 5.5) is proved by induction on the number of distinct values of `x`. Each step lowers the top level set to the next value.
3. **Lemma 5.1 uses eigenvectors with positive eigenvalue.** These are automatically orthogonal to the all-ones vector, which avoids choosing an eigenbasis that contains `1/√n`.

## Building

Lean `v4.37.0-rc1`, Mathlib commit `90e6eec9fe53b02d431c90718e4a1d22d67a204e` (pinned in `lake-manifest.json`).

```
lake exe cache get   # optional
lake build
lake env lean Check.lean
```

## Status

Unconditional formalization (proving Grone–Merris–Bai itself) is in progress.

## AI assistance

This formalization was produced with substantial AI assistance (Anthropic's Claude), directed by the repository author. All proofs are checked by Lean.
