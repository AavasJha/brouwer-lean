/-
  Brouwer's Laplacian conjecture, following Kothari–Tudose (arXiv:2606.12197).
  Part (B)+(D): eigenvalues, the easy half of Ky Fan, the projection onto the top
  eigenvectors, split graphs, and the main theorem (assuming Grone–Merris–Bai).
-/
import Brouwer.Algebra
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Fin

open Finset Matrix

namespace Brouwer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Sum of the `k` largest eigenvalues of a real symmetric matrix. -/
noncomputable def topSum {A : Matrix V V ℝ} (hA : A.IsHermitian) (k : ℕ) : ℝ :=
  ∑ t ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < k), hA.eigenvalues₀ t

/-- The Grone–Merris–Bai theorem (Bai, Trans. AMS 2011), stated for graphs on `V`:
the sum of the `k` largest Laplacian eigenvalues is at most `∑_v min(deg v, k)`,
which is the sum of the first `k` terms of the conjugate degree sequence. -/
def GroneMerrisBai (V : Type*) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ),
    topSum (H.isHermitian_lapMatrix ℝ) k ≤ ∑ v, (min (H.degree v) k : ℝ)

section Spec

variable {A : Matrix V V ℝ} (hA : A.IsHermitian)

/-- The `j`-th eigenvector, as a plain function. -/
noncomputable def ev (j : V) : V → ℝ := ⇑(hA.eigenvectorBasis j)

lemma ev_ortho (i j : V) : ∑ a, ev hA i a * ev hA j a = if i = j then 1 else 0 := by
  have h := congrFun (congrFun (Unitary.coe_star_mul_self hA.eigenvectorUnitary) i) j
  simpa [Matrix.mul_apply, ev, Matrix.one_apply] using h

lemma ev_complete (a b : V) : ∑ j, ev hA j a * ev hA j b = if a = b then 1 else 0 := by
  have h := congrFun (congrFun (Unitary.coe_mul_star_self hA.eigenvectorUnitary) a) b
  simpa [Matrix.mul_apply, ev, Matrix.one_apply] using h

lemma ev_eig (j a : V) : ∑ c, A a c * ev hA j c = hA.eigenvalues j * ev hA j a := by
  have := congrFun (hA.mulVec_eigenvectorBasis j) a
  simpa [Matrix.mulVec, dotProduct, ev] using this

lemma A_spec (a b : V) : A a b = ∑ j, hA.eigenvalues j * ev hA j a * ev hA j b := by
  calc A a b = ∑ c, A a c * (if c = b then 1 else 0) := by simp
    _ = ∑ c, A a c * ∑ j, ev hA j c * ev hA j b := by simp_rw [ev_complete]
    _ = ∑ j, (∑ c, A a c * ev hA j c) * ev hA j b := by
        simp_rw [mul_sum, sum_mul, mul_assoc]; exact sum_comm
    _ = _ := by simp_rw [ev_eig]

end Spec

/-- Quadratic forms of symmetric idempotents are nonnegative. -/
lemma qf_nonneg (Q : Matrix V V ℝ) (hs : ∀ i j, Q i j = Q j i)
    (hi : ∀ i j, ∑ l, Q i l * Q l j = Q i j) (x : V → ℝ) :
    0 ≤ ∑ a, ∑ b, x a * Q a b * x b := by
  have h : ∑ a, ∑ b, x a * Q a b * x b = ∑ l, (∑ a, x a * Q a l) ^ 2 := by
    have e : ∀ l, (∑ a, x a * Q a l) ^ 2 = ∑ a, ∑ b, x a * (Q a l * Q l b) * x b := by
      intro l
      rw [sq, sum_mul_sum]
      refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
      rw [hs b l]; ring
    calc ∑ a, ∑ b, x a * Q a b * x b = ∑ a, ∑ b, ∑ l, x a * (Q a l * Q l b) * x b := by
          refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
          rw [← hi a b, mul_sum, sum_mul]
      _ = ∑ l, ∑ a, ∑ b, x a * (Q a l * Q l b) * x b := by
          rw [sum_congr rfl (fun a _ => sum_comm)]; exact sum_comm
      _ = _ := sum_congr rfl (fun l _ => (e l).symm)
  rw [h]; exact sum_nonneg (fun l _ => sq_nonneg _)

/-- The "fractional knapsack" bound behind the easy half of Ky Fan's principle. -/
lemma knapsack {n : ℕ} (lam : Fin n → ℝ) (hanti : Antitone lam) (q : Fin n → ℝ)
    (h0 : ∀ t, 0 ≤ q t) (h1 : ∀ t, q t ≤ 1) (k : ℕ) (hsum : ∑ t, q t = k) :
    ∑ t, lam t * q t ≤ ∑ t ∈ univ.filter (fun t : Fin n => t.val < k), lam t := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hkn : k ≤ n := by
    have : ∑ t, q t ≤ ∑ _t : Fin n, (1 : ℝ) := sum_le_sum (fun t _ => h1 t)
    rw [hsum] at this; simp at this; exact_mod_cast this
  -- pivot value
  obtain ⟨c, hc1, hc2⟩ : ∃ c : ℝ, (∀ t : Fin n, t.val < k → c ≤ lam t) ∧
      (∀ t : Fin n, k ≤ t.val → lam t ≤ c) := by
    by_cases hk : k < n
    · exact ⟨lam ⟨k, hk⟩, fun t ht => hanti (Fin.le_def.mpr (by simp; omega)),
        fun t ht => hanti (Fin.le_def.mpr (by simpa using ht))⟩
    · refine ⟨lam ⟨n - 1, by omega⟩, fun t _ => hanti (Fin.le_def.mpr (by simp; omega)),
        fun t ht => absurd t.isLt (by omega)⟩
  have hcard : (univ.filter (fun t : Fin n => t.val < k)).card = k := by
    rw [Fin.card_filter_val_lt]; omega
  have key : ∀ t : Fin n, lam t * q t - (if t.val < k then lam t else 0) ≤
      c * (q t - if t.val < k then 1 else 0) := by
    intro t
    by_cases ht : t.val < k
    · simp only [ht, if_true]
      have := hc1 t ht
      nlinarith [h1 t]
    · simp only [ht, if_false, sub_zero]
      have := hc2 t (by omega)
      nlinarith [h0 t]
  have hs := sum_le_sum (fun t (_ : t ∈ univ) => key t)
  rw [sum_sub_distrib, ← mul_sum, sum_sub_distrib, hsum, ← sum_filter, ← sum_filter] at hs
  simp only [sum_const, hcard, nsmul_eq_mul, mul_one, sub_self, mul_zero] at hs
  linarith

/-- Easy half of Ky Fan's maximum principle: for a symmetric idempotent `P` of trace `k`,
`tr(P A) ≤ λ₁ + ⋯ + λ_k`. -/
theorem kyFan {A : Matrix V V ℝ} (hA : A.IsHermitian) (P : Matrix V V ℝ)
    (hs : ∀ i j, P i j = P j i) (hi : ∀ i j, ∑ l, P i l * P l j = P i j)
    (k : ℕ) (htr : ∑ i, P i i = k) :
    ∑ a, ∑ b, P a b * A b a ≤ topSum hA k := by
  set q : V → ℝ := fun j => ∑ a, ∑ b, ev hA j a * P a b * ev hA j b with hq
  have htrace : ∑ a, ∑ b, P a b * A b a = ∑ j, hA.eigenvalues j * q j := by
    have e1 : ∀ a b, P a b * A b a =
        ∑ j, hA.eigenvalues j * (ev hA j a * P a b * ev hA j b) := by
      intro a b; rw [A_spec hA b a, mul_sum]
      exact sum_congr rfl (fun j _ => by ring)
    rw [sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => e1 a b))]
    simp only [hq, mul_sum]
    symm; rw [sum_comm]
    refine sum_congr rfl (fun a _ => ?_)
    rw [sum_comm]
  have hq0 : ∀ j, 0 ≤ q j := fun j => qf_nonneg P hs hi _
  have hq1 : ∀ j, q j ≤ 1 := by
    intro j
    let Q : Matrix V V ℝ := fun a b => (if a = b then 1 else 0) - P a b
    have hQs : ∀ i j, Q i j = Q j i := by
      intro i j; simp only [Q, hs i j, eq_comm]
    have hQi : ∀ i j, ∑ l, Q i l * Q l j = Q i j := by
      intro i j
      simp only [Q, sub_mul, mul_sub, sum_sub_distrib, ite_mul, one_mul, zero_mul, mul_ite,
        mul_one, mul_zero, sum_ite_eq, sum_ite_eq', mem_univ, if_true, hi i j]
      ring
    have := qf_nonneg Q hQs hQi (ev hA j)
    have hone : ∑ a, ∑ b, ev hA j a * (if a = b then (1:ℝ) else 0) * ev hA j b = 1 := by
      simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
      have := ev_ortho hA j j
      simpa using this
    have e : ∑ a, ∑ b, ev hA j a * Q a b * ev hA j b = 1 - q j := by
      rw [← hone, hq]
      simp only [Q, mul_sub, sub_mul, sum_sub_distrib]
    linarith
  have hqsum : ∑ j, q j = k := by
    have e1 : ∀ j, q j = ∑ a, ∑ b, P a b * (ev hA j a * ev hA j b) := by
      intro j
      exact sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => by ring))
    rw [← htr, sum_congr rfl (fun j _ => e1 j), sum_comm]
    refine sum_congr rfl (fun a _ => ?_)
    rw [sum_comm]
    simp_rw [← mul_sum, ev_complete]
    simp
  -- reindex to the sorted eigenvalues
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V)) with he
  have hre : ∀ t, hA.eigenvalues (e t) = hA.eigenvalues₀ t := by
    intro t; simp [Matrix.IsHermitian.eigenvalues, he]
  rw [htrace, ← e.sum_comp]
  simp_rw [hre]
  apply knapsack _ hA.eigenvalues₀_antitone (fun t => q (e t)) (fun t => hq0 _)
    (fun t => hq1 _) k
  rw [e.sum_comp (fun j => q j), hqsum]

end Brouwer
