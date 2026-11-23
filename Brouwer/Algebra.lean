/-
  Brouwer's Laplacian conjecture, following Kothari–Tudose (arXiv:2606.12197).
  Part (C): the purely algebraic core (paper's Lemmas 5.2, 5.3, 5.5, 5.6).

  Everything here is about a real symmetric idempotent matrix `P` with `P 1 = 0` and trace `k`.
  The "cut hypothesis" `CutHyp` is exactly the paper's Lemma 3.3 applied to the split graphs
  used in the proof of Lemma 5.5; it is supplied later from the Grone–Merris–Bai theorem.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Finset

set_option linter.unusedSectionVars false

namespace Brouwer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `a P i j = P i i + P j j - 2 P i j`, i.e. `‖P (e_i - e_j)‖²`. -/
def a (P : Matrix V V ℝ) (i j : V) : ℝ := P i i + P j j - 2 * P i j

/-- The "capacity" `w = 1 - |a - 1|`. -/
def w (P : Matrix V V ℝ) (i j : V) : ℝ := 1 - |a P i j - 1|

/-- `P` is a symmetric idempotent with `P 1 = 0` and trace `k`. -/
structure IsProj (P : Matrix V V ℝ) (k : ℝ) : Prop where
  symm : ∀ i j, P i j = P j i
  idem : ∀ i j, ∑ l, P i l * P l j = P i j
  one : ∀ i, ∑ j, P i j = 0
  tr : ∑ i, P i i = k

/-- The cut hypothesis (Lemma 3.3 for split graphs, rewritten in terms of `a`). -/
def CutHyp (P : Matrix V V ℝ) (k : ℝ) : Prop :=
  ∀ K : Finset V,
    (∑ i ∈ K, ∑ j ∈ K, a P i j) / 2 + ∑ i ∈ K, ∑ j ∈ Kᶜ, max (a P i j - 1) 0 ≤ K.card * k

variable {P : Matrix V V ℝ} {k : ℝ}

lemma a_self (P : Matrix V V ℝ) (i : V) : a P i i = 0 := by unfold a; ring

lemma a_symm (hP : IsProj P k) (i j : V) : a P i j = a P j i := by
  unfold a; rw [hP.symm i j]; ring

lemma w_symm (hP : IsProj P k) (i j : V) : w P i j = w P j i := by
  unfold w; rw [a_symm hP]

lemma col_sum (hP : IsProj P k) (j : V) : ∑ i, P i j = 0 := by
  rw [← hP.one j]; exact sum_congr rfl (fun i _ => hP.symm i j)

lemma row_sum_a (hP : IsProj P k) (i : V) :
    ∑ j, a P i j = (Fintype.card V : ℝ) * P i i + k := by
  unfold a
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, hP.one, hP.tr, sum_const, card_univ,
    nsmul_eq_mul]
  ring

lemma sum_sq_P (hP : IsProj P k) : ∑ i, ∑ j, P i j ^ 2 = k := by
  have h : ∀ i, ∑ j, P i j ^ 2 = P i i := fun i => by
    rw [← hP.idem i i]; exact sum_congr rfl (fun j _ => by rw [sq, hP.symm j i])
  rw [sum_congr rfl (fun i _ => h i), hP.tr]

/-- Paper's Lemma 5.2: `Σ a² - Σ (P_ii - P_jj)² = 4 k (k+1)` (sum over all ordered pairs). -/
lemma lemma52 (hP : IsProj P k) :
    ∑ i, ∑ j, a P i j ^ 2 - ∑ i, ∑ j, (P i i - P j j) ^ 2 = 4 * k * (k + 1) := by
  have e : ∀ i j, a P i j ^ 2 - (P i i - P j j) ^ 2 =
      4 * (P i i * P j j) - 4 * (P i i * P i j) - 4 * (P j j * P i j) + 4 * P i j ^ 2 := by
    intro i j; unfold a; ring
  have h1 : ∑ i, ∑ j, P i i * P j j = k * k := by
    rw [← sum_mul_sum, hP.tr]
  have h2 : ∑ i, ∑ j, P i i * P i j = 0 := by
    simp [← mul_sum, hP.one]
  have h3 : ∑ i, ∑ j, P j j * P i j = 0 := by
    rw [sum_comm]; simp [← mul_sum, col_sum hP]
  have h4 := sum_sq_P hP
  rw [← sum_sub_distrib]
  have : ∀ i, ∑ j, a P i j ^ 2 - ∑ j, (P i i - P j j) ^ 2 =
      4 * ∑ j, P i i * P j j - 4 * ∑ j, P i i * P i j - 4 * ∑ j, P j j * P i j
        + 4 * ∑ j, P i j ^ 2 := by
    intro i
    rw [← sum_sub_distrib, mul_sum, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib,
      ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl (fun j _ => e i j)
  rw [sum_congr rfl (fun i _ => this i)]
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
    ← mul_sum, h1, h2, h3, h4]
  ring

lemma key_pt (x : ℝ) : x - 2 * max (x - 1) 0 = 1 - |x - 1| := by
  rcases le_total (x - 1) 0 with h | h
  · rw [max_eq_right h, abs_of_nonpos h]; ring
  · rw [max_eq_left h, abs_of_nonneg h]; ring

lemma pos_part_pt (x : ℝ) : max (x - 1) 0 = (x ^ 2 - (1 - |x - 1|) ^ 2) / 4 := by
  rcases le_total (x - 1) 0 with h | h
  · rw [max_eq_right h, abs_of_nonpos h]; ring
  · rw [max_eq_left h, abs_of_nonneg h]; ring

/-- Inequality (5.4): the cut condition for `v_i = n P_ii - k`. -/
lemma cut_ineq (hP : IsProj P k) (hC : CutHyp P k) (K : Finset V) :
    ∑ i ∈ K, ((Fintype.card V : ℝ) * P i i - k) ≤ ∑ i ∈ K, ∑ j ∈ Kᶜ, w P i j := by
  have h1 : ∀ i, (Fintype.card V : ℝ) * P i i - k =
      ∑ j ∈ K, a P i j + ∑ j ∈ Kᶜ, a P i j - 2 * k := by
    intro i; rw [sum_add_sum_compl, row_sum_a hP]; ring
  have h2 : ∑ i ∈ K, ∑ j ∈ Kᶜ, w P i j =
      ∑ i ∈ K, ∑ j ∈ Kᶜ, a P i j - 2 * ∑ i ∈ K, ∑ j ∈ Kᶜ, max (a P i j - 1) 0 := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl (fun j _ => ?_)
    rw [key_pt]; rfl
  rw [sum_congr rfl (fun i _ => h1 i), sum_sub_distrib, sum_add_distrib, h2, sum_const,
    nsmul_eq_mul]
  have := hC K
  linarith

/-- Abstract "routing" lemma (paper's Lemma 5.5), proved by induction on the number of
distinct values of `x` instead of by sorting and Abel summation. -/
lemma routing (v : V → ℝ) (c : V → V → ℝ) (hc : ∀ i j, c i j = c j i)
    (hv0 : ∑ i, v i = 0)
    (hcut : ∀ K : Finset V, ∑ i ∈ K, v i ≤ ∑ i ∈ K, ∑ j ∈ Kᶜ, c i j) :
    ∀ x : V → ℝ, 2 * ∑ i, v i * x i ≤ ∑ i, ∑ j, c i j * |x i - x j| := by
  intro x
  induction hN : (univ.image x).card using Nat.strong_induction_on generalizing x with
  | _ N ih =>
  by_cases hsmall : N ≤ 1
  · -- `x` is constant
    have hconst : ∀ i j, x i = x j := by
      intro i j
      have hi : x i ∈ univ.image x := mem_image_of_mem x (mem_univ i)
      have hj : x j ∈ univ.image x := mem_image_of_mem x (mem_univ j)
      exact Finset.card_le_one.mp (hN ▸ hsmall) _ hi _ hj
    rcases isEmpty_or_nonempty V with hV | ⟨⟨i0⟩⟩
    · simp
    · have hl : ∑ i, v i * x i = 0 := by
        rw [sum_congr rfl (fun i _ => by rw [hconst i i0]), ← sum_mul, hv0, zero_mul]
      have hr : ∑ i, ∑ j, c i j * |x i - x j| = 0 := by
        refine sum_eq_zero (fun i _ => sum_eq_zero (fun j _ => ?_))
        rw [hconst i j, sub_self, abs_zero, mul_zero]
      rw [hl, hr]; norm_num
  · push Not at hsmall
    set S := univ.image x with hS
    have hSne : S.Nonempty := by
      rw [← Finset.card_pos]; omega
    set t := S.max' hSne with ht
    have hS'ne : (S.erase t).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (S.max'_mem hSne)]; omega
    set t' := (S.erase t).max' hS'ne with ht'
    have ht't : t' < t := by
      have hmem := (S.erase t).max'_mem hS'ne
      rw [← ht'] at hmem
      have h1 := Finset.ne_of_mem_erase hmem
      have h2 := S.le_max' t' (Finset.mem_of_mem_erase hmem)
      rw [← ht] at h2
      exact lt_of_le_of_ne h2 h1
    have hle_t : ∀ i, x i ≤ t := fun i => S.le_max' _ (mem_image_of_mem x (mem_univ i))
    have hle_t' : ∀ i, x i ≠ t → x i ≤ t' := fun i hi =>
      (S.erase t).le_max' _ (Finset.mem_erase.mpr ⟨hi, mem_image_of_mem x (mem_univ i)⟩)
    set K := univ.filter (fun i => x i = t) with hK
    let x' : V → ℝ := fun i => if x i = t then t' else x i
    -- the image of `x'` is `S.erase t`
    have himg : univ.image x' = S.erase t := by
      ext y
      simp only [mem_image, mem_univ, true_and, Finset.mem_erase, hS]
      constructor
      · rintro ⟨i, rfl⟩
        by_cases hi : x i = t
        · simp only [x', hi, if_true]
          have hmem := (S.erase t).max'_mem hS'ne
          rw [← ht'] at hmem
          refine ⟨ne_of_lt ht't, ?_⟩
          have := Finset.mem_of_mem_erase hmem
          rw [hS, mem_image] at this
          simpa using this
        · simp only [x', hi, if_false]; exact ⟨hi, i, rfl⟩
      · rintro ⟨hy, i, rfl⟩
        exact ⟨i, by simp [x', hy]⟩
    have hcard : (univ.image x').card < N := by
      rw [himg, Finset.card_erase_of_mem (S.max'_mem hSne), ← hN]; omega
    have IH := ih _ hcard x' rfl
    -- decompose `x = x' + (t - t') 1_K`
    have hx : ∀ i, x i = x' i + (if i ∈ K then t - t' else 0) := by
      intro i
      by_cases hi : x i = t <;> simp [x', K, hi]
    have hlin : ∑ i, v i * x i = ∑ i, v i * x' i + (t - t') * ∑ i ∈ K, v i := by
      have e : ∀ i, v i * x i = v i * x' i + (if i ∈ K then (t - t') * v i else 0) := by
        intro i; rw [hx i]; split_ifs <;> ring
      rw [sum_congr rfl (fun i _ => e i), sum_add_distrib, ← sum_filter, mul_sum,
        show univ.filter (fun i => i ∈ K) = K by ext; simp]
    -- pointwise decomposition of the right-hand side
    have hpt : ∀ i j, c i j * |x i - x j| = c i j * |x' i - x' j| +
        (t - t') * ((if i ∈ K ∧ j ∉ K then c i j else 0) +
          (if i ∉ K ∧ j ∈ K then c i j else 0)) := by
      intro i j
      have hiK : i ∈ K ↔ x i = t := by simp [K]
      have hjK : j ∈ K ↔ x j = t := by simp [K]
      by_cases hi : x i = t <;> by_cases hj : x j = t
      · simp [x', hi, hj, hiK, hjK]
      · have hj' := hle_t' j hj
        simp only [x', hi, hj, hiK, hjK, if_true, if_false, not_true, not_false_eq_true,
          and_true, true_and, and_false, false_and, add_zero]
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; ring
      · have hi' := hle_t' i hi
        simp only [x', hi, hj, hiK, hjK, if_true, if_false, not_true, not_false_eq_true,
          and_true, true_and, and_false, false_and, zero_add]
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; ring
      · simp [x', hi, hj, hiK, hjK]
    have hcross : ∑ i, ∑ j, (if i ∉ K ∧ j ∈ K then c i j else 0) =
        ∑ i, ∑ j, (if i ∈ K ∧ j ∉ K then c i j else 0) := by
      rw [sum_comm]
      refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
      rw [hc j i]
      by_cases hi : i ∈ K <;> by_cases hj : j ∈ K <;> simp [hi, hj]
    have hcutK : ∑ i, ∑ j, (if i ∈ K ∧ j ∉ K then c i j else 0) =
        ∑ i ∈ K, ∑ j ∈ Kᶜ, c i j := by
      rw [← sum_filter_add_sum_filter_not univ (fun i => i ∈ K)]
      have hz : ∑ i ∈ univ.filter (fun i => i ∉ K),
          ∑ j, (if i ∈ K ∧ j ∉ K then c i j else 0) = 0 := by
        refine sum_eq_zero (fun i hi => sum_eq_zero (fun j _ => ?_))
        rw [mem_filter] at hi; simp [hi.2]
      rw [hz, add_zero]
      have : univ.filter (fun i => i ∈ K) = K := by ext; simp
      rw [this]
      refine sum_congr rfl (fun i hi => ?_)
      rw [← sum_filter]
      congr 1; ext j; simp [hi]
    have hR : ∑ i, ∑ j, c i j * |x i - x j| =
        ∑ i, ∑ j, c i j * |x' i - x' j| + 2 * (t - t') * ∑ i ∈ K, ∑ j ∈ Kᶜ, c i j := by
      rw [sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => hpt i j))]
      simp only [sum_add_distrib, ← mul_sum]
      rw [hcross, hcutK]; ring
    rw [hlin, hR]
    have := hcut K
    have hpos : 0 ≤ t - t' := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hpos]

/-- Paper's Lemma 5.6: `Σ_{i,j} (a_ij - 1)_+ ≤ k (k+1)`. -/
theorem lemma56 (hP : IsProj P k) (hC : CutHyp P k) :
    ∑ i, ∑ j, max (a P i j - 1) 0 ≤ k * (k + 1) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set v : V → ℝ := fun i => n * P i i - k with hv
  have hv0 : ∑ i, v i = 0 := by
    simp only [hv, sum_sub_distrib, ← mul_sum, hP.tr, sum_const, card_univ, nsmul_eq_mul]
    ring
  have hroute := routing v (w P) (w_symm hP) hv0 (cut_ineq hP hC) v
  -- Cauchy–Schwarz
  have hCS : (∑ i, ∑ j, w P i j * |v i - v j|) ^ 2 ≤
      (∑ i, ∑ j, w P i j ^ 2) * ∑ i, ∑ j, (v i - v j) ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (V × V))
      (fun p => w P p.1 p.2) (fun p => |v p.1 - v p.2|)
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at this
    simpa [sq_abs] using this
  have hvv : ∑ i, ∑ j, (v i - v j) ^ 2 = 2 * n * ∑ i, v i ^ 2 := by
    have e : ∀ i j, (v i - v j) ^ 2 = v i ^ 2 + v j ^ 2 - 2 * v i * v j := by
      intro i j; ring
    simp only [e, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    have : ∑ i, ∑ j, 2 * v i * v j = 0 := by
      simp [← mul_sum, hv0]
    rw [this, ← hn, ← mul_sum]; ring
  set Sv := ∑ i, v i ^ 2 with hSv
  have hSv0 : 0 ≤ Sv := sum_nonneg (fun i _ => sq_nonneg _)
  have hW0 : 0 ≤ ∑ i, ∑ j, w P i j ^ 2 := sum_nonneg (fun i _ => sum_nonneg (fun j _ => sq_nonneg _))
  have hvx : ∑ i, v i * v i = Sv := by rw [hSv]; exact sum_congr rfl (fun i _ => (sq _).symm)
  rw [hvx] at hroute
  -- 2 Sv ≤ n Σ w²
  have hmain : 2 * Sv ≤ n * ∑ i, ∑ j, w P i j ^ 2 := by
    rcases eq_or_lt_of_le hSv0 with h0 | hpos
    · rw [← h0]; have : (0:ℝ) ≤ n := by positivity
      nlinarith
    · have h1 : (2 * Sv) ^ 2 ≤ (∑ i, ∑ j, w P i j ^ 2) * (2 * n * Sv) := by
        rw [← hvv]
        calc (2 * Sv) ^ 2 ≤ (∑ i, ∑ j, w P i j * |v i - v j|) ^ 2 := by
              apply pow_le_pow_left₀ (by positivity) hroute
          _ ≤ _ := hCS
      nlinarith
  -- Σ (P_ii - P_jj)² ≤ Σ w²
  have hdd : ∑ i, ∑ j, (P i i - P j j) ^ 2 ≤ ∑ i, ∑ j, w P i j ^ 2 := by
    rcases isEmpty_or_nonempty V with hV | hV
    · simp
    have hnpos : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
    have e : ∀ i j, (P i i - P j j) ^ 2 = (v i - v j) ^ 2 * (n ^ 2)⁻¹ := by
      intro i j; simp only [hv]; field_simp; ring
    simp only [e, ← sum_mul]
    rw [hvv, mul_inv_le_iff₀ (by positivity)]
    nlinarith
  -- conclude
  have hpp : ∑ i, ∑ j, max (a P i j - 1) 0 =
      (∑ i, ∑ j, a P i j ^ 2 - ∑ i, ∑ j, w P i j ^ 2) * (1 / 4) := by
    have e : ∀ i j, max (a P i j - 1) 0 = (a P i j ^ 2 - w P i j ^ 2) * (1 / 4) := by
      intro i j; rw [pos_part_pt]; unfold w; ring
    simp only [e, ← sum_mul, ← sum_sub_distrib]
  rw [hpp]
  have := lemma52 hP
  linarith

end Brouwer
