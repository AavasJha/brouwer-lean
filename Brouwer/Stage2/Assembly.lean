/-
  Stage 2: assembling the Grone–Merris–Bai theorem from Bai's lemmas
  (minimal counterexample, the split graph `Ĝ`, the three cases, complements).
-/
import Brouwer.Stage2.Core

open Finset Matrix Module

set_option linter.unusedSectionVars false

namespace Brouwer.Stage2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Spectral helpers -/

lemma qf_mono (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (hGH : G ≤ H)
    (x : V → ℝ) : qf (G.lapMatrix ℝ) x ≤ qf (H.lapMatrix ℝ) x := by
  unfold qf; rw [lap_qform, lap_qform]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  refine sum_le_sum (fun a _ => sum_le_sum (fun b _ => ?_))
  by_cases hG : G.Adj a b
  · simp [hG, hGH hG]
  · simp only [hG, if_false]; split_ifs <;> positivity

lemma qf_ge_of_mem_espan_le {A : Matrix V V ℝ} (hA : A.IsHermitian) (t : Fin (Fintype.card V))
    {x : V → ℝ} (hx : x ∈ espan hA (fun s => s ≤ t)) :
    hA.eigenvalues₀ t * nsq x ≤ qf A x := by
  obtain ⟨c, hc, rfl⟩ := mem_espan hA _ hx
  rw [qf_comb, nsq_comb, mul_sum]
  refine sum_le_sum (fun s _ => ?_)
  by_cases hs : s ≤ t
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone hs) (sq_nonneg _)
  · simp [hc s hs]

lemma qf_le_of_mem_espan_ge {A : Matrix V V ℝ} (hA : A.IsHermitian) (t : Fin (Fintype.card V))
    {x : V → ℝ} (hx : x ∈ espan hA (fun s => t ≤ s)) :
    qf A x ≤ hA.eigenvalues₀ t * nsq x := by
  obtain ⟨c, hc, rfl⟩ := mem_espan hA _ hx
  rw [qf_comb, nsq_comb, mul_sum]
  refine sum_le_sum (fun s _ => ?_)
  by_cases hs : t ≤ s
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone hs) (sq_nonneg _)
  · simp [hc s hs]

lemma finrank_espan_le {A : Matrix V V ℝ} (hA : A.IsHermitian) (t : Fin (Fintype.card V)) :
    finrank ℝ (espan hA (fun s => s ≤ t)) = t.val + 1 := by
  rw [finrank_espan]
  have : univ.filter (fun s : Fin (Fintype.card V) => s ≤ t) =
      univ.filter (fun s : Fin (Fintype.card V) => s.val < t.val + 1) := by
    ext s; simp only [mem_filter, mem_univ, true_and, Fin.le_iff_val_le_val]; omega
  rw [this, Fin.card_filter_val_lt]; omega

lemma finrank_espan_ge {A : Matrix V V ℝ} (hA : A.IsHermitian) (t : Fin (Fintype.card V)) :
    finrank ℝ (espan hA (fun s => t ≤ s)) = Fintype.card V - t.val := by
  rw [finrank_espan]
  have h1 : (univ.filter (fun s : Fin (Fintype.card V) => t ≤ s)).card +
      (univ.filter (fun s : Fin (Fintype.card V) => ¬ t ≤ s)).card = Fintype.card V := by
    rw [card_filter_add_card_filter_not]; simp
  have h2 : univ.filter (fun s : Fin (Fintype.card V) => ¬ t ≤ s) =
      univ.filter (fun s : Fin (Fintype.card V) => s.val < t.val) := by
    ext s; simp only [mem_filter, mem_univ, true_and, Fin.le_iff_val_le_val]; omega
  rw [h2, Fin.card_filter_val_lt] at h1
  have := t.isLt
  omega

/-- Eigenvalue monotonicity (Weyl): adding edges raises every Laplacian eigenvalue. -/
theorem eig_mono (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (hGH : G ≤ H)
    (t : Fin (Fintype.card V)) :
    (G.isHermitian_lapMatrix ℝ).eigenvalues₀ t ≤ (H.isHermitian_lapMatrix ℝ).eigenvalues₀ t := by
  apply le_eig_of_subspace (H.isHermitian_lapMatrix ℝ) t
    (espan (G.isHermitian_lapMatrix ℝ) (fun s => s ≤ t))
  · intro x hx
    exact (qf_ge_of_mem_espan_le _ t hx).trans (qf_mono G H hGH x)
  · rw [finrank_espan_le]

lemma eig_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (t : Fin (Fintype.card V)) :
    0 ≤ (G.isHermitian_lapMatrix ℝ).eigenvalues₀ t := by
  have := le_eig_of_subspace (G.isHermitian_lapMatrix ℝ) t ⊤ 0
    (fun x _ => by rw [zero_mul]; exact lap_qform_nonneg G x)
    (by rw [finrank_top, Module.finrank_fintype_fun_eq_card]; exact t.isLt)
  exact this

/-- `λ_l = S_l - S_{l-1}` (1-indexed). -/
lemma eig_eq_S_sub (G : SimpleGraph V) [DecidableRel G.Adj] (l : ℕ) (hl : 1 ≤ l)
    (hln : l ≤ Fintype.card V) :
    (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨l - 1, by omega⟩ = S G l - S G (l - 1) := by
  unfold S
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [topSum_succ _ _ (by omega)]

lemma lap_entry (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    G.lapMatrix ℝ a b = (if a = b then (G.degree a : ℝ) else 0) - (if G.Adj a b then 1 else 0) := by
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply]

lemma trace_lapM (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ a, G.lapMatrix ℝ a a = ∑ a, (G.degree a : ℝ) := by
  refine sum_congr rfl (fun a _ => ?_)
  rw [lap_entry]; simp

lemma topP_full {A : Matrix V V ℝ} (hA : A.IsHermitian) (k : ℕ) (hk : Fintype.card V ≤ k)
    (a b : V) : topP hA k a b = if a = b then 1 else 0 := by
  unfold topP
  have : univ.filter (fun t : Fin (Fintype.card V) => t.val < k) = univ := by
    ext t; simp only [mem_filter, mem_univ, true_and, iff_true]; omega
  rw [this, sev_complete]

/-- For `k ≥ n`, the top-`k` sum is the trace `Σ deg`. -/
lemma S_full (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : Fintype.card V ≤ k) :
    S G k = ∑ a, (G.degree a : ℝ) := by
  unfold S
  rw [← trace_topP]
  simp_rw [topP_full _ k hk, ite_mul, one_mul, zero_mul]
  rw [← trace_lapM]
  exact sum_congr rfl (fun a _ => by rw [sum_ite_eq]; simp)

lemma degree_lt_card (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v ≤ Fintype.card V - 1 := by
  have := G.degree_lt_card_verts v
  omega

lemma D_full (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : Fintype.card V - 1 ≤ k) :
    D G k = ∑ a, (G.degree a : ℝ) := by
  unfold D
  refine sum_congr rfl (fun a _ => ?_)
  have := degree_lt_card G a
  rw [min_eq_left (by exact_mod_cast (le_trans this hk))]

lemma S_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : 0 ≤ S G k := by
  unfold S topSum
  exact sum_nonneg (fun t _ => eig_nonneg G t)

lemma D_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : 0 ≤ D G k :=
  sum_nonneg (fun _ _ => by positivity)

lemma S_le_D_full (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hk : Fintype.card V - 1 ≤ k) : S G k ≤ D G k := by
  rw [D_full G k hk]
  by_cases hkn : Fintype.card V ≤ k
  · rw [S_full G k hkn]
  · have hk' : k = Fintype.card V - 1 := by omega
    have hn : 1 ≤ Fintype.card V := by omega
    have := eig_eq_S_sub G (Fintype.card V) hn le_rfl
    have h0 := eig_nonneg G ⟨Fintype.card V - 1, by omega⟩
    rw [S_full G _ le_rfl] at this
    rw [hk']; linarith

/-- `D_k - D_{k-1} = #{v : deg v ≥ k}`. -/
lemma D_sub (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k) :
    D G k - D G (k - 1) = ((univ.filter (fun v => k ≤ G.degree v)).card : ℝ) := by
  unfold D
  rw [← sum_sub_distrib, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_congr rfl (fun v _ => ?_)
  by_cases hv : k ≤ G.degree v
  · rw [if_pos hv, min_eq_right (by exact_mod_cast hv),
      min_eq_right (by exact_mod_cast (le_trans (Nat.sub_le k 1) hv))]
    push_cast [hk]; ring
  · rw [if_neg hv]
    push Not at hv
    rw [min_eq_left (by exact_mod_cast hv.le), min_eq_left (by
      have : G.degree v ≤ k - 1 := by omega
      exact_mod_cast this)]
    simp

/-! ### Complements (Bai's Proposition 12, the two directions we need) -/

lemma qf_compl (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    qf (G.lapMatrix ℝ) x + qf (Gᶜ.lapMatrix ℝ) x =
      (Fintype.card V : ℝ) * nsq x - (∑ a, x a) ^ 2 := by
  unfold qf; rw [lap_qform, lap_qform, ← add_div, ← sum_add_distrib]
  have e : ∀ a, (∑ b, if G.Adj a b then (x a - x b) ^ 2 else 0) +
      (∑ b, if Gᶜ.Adj a b then (x a - x b) ^ 2 else 0) = ∑ b, (x a - x b) ^ 2 := by
    intro a
    rw [← sum_add_distrib]
    refine sum_congr rfl (fun b _ => ?_)
    by_cases hab : a = b
    · subst hab; simp
    · by_cases hG : G.Adj a b
      · simp [hG, SimpleGraph.compl_adj, hab]
      · simp [hG, SimpleGraph.compl_adj, hab]
  rw [sum_congr rfl (fun a _ => e a)]
  have := sq_diff_sum (univ : Finset V) x
  rw [card_univ] at this
  rw [this]; unfold nsq; ring

lemma deg_compl_real (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) :
    (Gᶜ.degree a : ℝ) = Fintype.card V - 1 - G.degree a := by
  rw [G.degree_compl]
  have h2 := degree_lt_card G a
  have : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
  rw [Nat.cast_sub h2, Nat.cast_sub this, Nat.cast_one]

lemma lap_compl_entry (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    Gᶜ.lapMatrix ℝ a b =
      (Fintype.card V : ℝ) * (if a = b then 1 else 0) - 1 - G.lapMatrix ℝ a b := by
  rw [lap_entry, lap_entry]
  by_cases hab : a = b
  · subst hab
    simp [deg_compl_real G a]
  · by_cases hG : G.Adj a b
    · simp [hab, hG, SimpleGraph.compl_adj]
    · simp [hab, hG, SimpleGraph.compl_adj]

/-- Complement, eigenvalue direction: `λ_M(Gᶜ) ≥ n - λ_N(G)` with `M = n - N`. -/
theorem compl_eig_ge (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hN : 1 ≤ N)
    (hNn : N < Fintype.card V) :
    (Fintype.card V : ℝ) - (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨N - 1, by omega⟩ ≤
      (Gᶜ.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - N - 1, by omega⟩ := by
  set hG := G.isHermitian_lapMatrix ℝ
  set E := espan hG (fun s => (⟨N - 1, by omega⟩ : Fin (Fintype.card V)) ≤ s)
  set B := LinearMap.ker (sumL (V := V))
  apply le_eig_of_subspace (Gᶜ.isHermitian_lapMatrix ℝ) _ (E ⊓ B)
  · intro x hx
    have h1 := qf_le_of_mem_espan_ge hG _ (Submodule.mem_inf.mp hx).1
    have h2 := (Submodule.mem_inf.mp hx).2
    rw [LinearMap.mem_ker, sumL_apply] at h2
    have h3 := qf_compl G x
    rw [h2] at h3
    linarith
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq E B
    have h2 : finrank ℝ ↥(E ⊔ B) ≤ Fintype.card V := by
      have := Submodule.finrank_le (E ⊔ B)
      rwa [Module.finrank_fintype_fun_eq_card] at this
    have h4 : Fintype.card V - 1 ≤ finrank ℝ B := finrank_ker_sumL (V := V)
    have h5 : finrank ℝ E = Fintype.card V - (N - 1) := finrank_espan_ge hG _
    show Fintype.card V - N - 1 + 1 ≤ _
    omega

/-- Complement, sum direction: `S_r(G) + n(n-1-r) - 2m ≤ S_{n-1-r}(Gᶜ)` when `λ_r(G) > 0`. -/
theorem compl_S_transfer (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 1 ≤ r)
    (hrn : r + 1 ≤ Fintype.card V)
    (hpos : 0 < (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨r - 1, by omega⟩) :
    S G r + (Fintype.card V : ℝ) * (Fintype.card V - 1 - r) - ∑ a, (G.degree a : ℝ) ≤
      S Gᶜ (Fintype.card V - 1 - r) := by
  set hG := G.isHermitian_lapMatrix ℝ
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : (0 : ℝ) < n := by
    rw [hn]; exact_mod_cast (show 0 < Fintype.card V by omega)
  set Q := topP hG r
  have hQs : ∀ a b, Q a b = Q b a := topP_symm hG r
  have hrow : ∀ a, ∑ b, G.lapMatrix ℝ a b = 0 := fun a => by
    have := congrFun (G.lapMatrix_mulVec_one_eq_zero ℝ) a
    simpa [mulVec, dotProduct] using this
  have hQcol : ∀ b, ∑ a, Q a b = 0 := topP_colsum hG r hrow (fun t ht => by
    have : hG.eigenvalues₀ ⟨r - 1, by omega⟩ ≤ hG.eigenvalues₀ t :=
      hG.eigenvalues₀_antitone (Fin.le_iff_val_le_val.mpr (by simp; omega))
    linarith)
  have hQrow : ∀ a, ∑ b, Q a b = 0 := fun a => by
    rw [← hQcol a]; exact sum_congr rfl (fun b _ => hQs a b)
  have hQtr : ∑ a, Q a a = r := by
    simp only [Q, topP]
    rw [sum_comm]
    have : ∀ t : Fin (Fintype.card V), ∑ a, sev hG t a * sev hG t a = 1 := fun t => by
      have := sev_ortho hG t t; simpa using this
    simp_rw [this]
    simp [Fin.card_filter_val_lt, show r ≤ Fintype.card V by omega]
  set P : Matrix V V ℝ := fun a b => (if a = b then 1 else 0) - Q a b - 1 / n
  have hPs : ∀ a b, P a b = P b a := fun a b => by
    simp only [P, hQs a b, eq_comm (a := a)]
  have hPi : ∀ a b, ∑ l, P a l * P l b = P a b := by
    intro a b
    have hQQ : ∑ l, Q a l * Q l b = Q a b := topP_idem hG r a b
    have e : ∀ l, P a l * P l b =
        ((if a = l then 1 else 0) * (if l = b then 1 else 0) - (if a = l then 1 else 0) * Q l b
          - (if a = l then 1 else 0) / n) -
        (Q a l * (if l = b then 1 else 0) - Q a l * Q l b - Q a l / n) -
        ((if l = b then 1 else 0) / n - Q l b / n - 1 / n ^ 2) := by
      intro l; simp only [P]; ring
    rw [sum_congr rfl (fun l _ => e l)]
    simp only [sum_sub_distrib, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      sum_ite_eq, sum_ite_eq', mem_univ, if_true, ← sum_div, hQQ, hQrow a, hQcol b, sum_const,
      card_univ, nsmul_eq_mul]
    simp only [P]
    field_simp
    rw [← hn]; ring
  have hPtr : ∑ i, P i i = ((Fintype.card V - 1 - r : ℕ) : ℝ) := by
    simp only [P, if_true, sum_sub_distrib, hQtr, sum_const, card_univ, nsmul_eq_mul]
    push_cast [show r ≤ Fintype.card V - 1 by omega, show 1 ≤ Fintype.card V by omega]
    rw [← hn]; field_simp; ring
  have hky := kyFan (Gᶜ.isHermitian_lapMatrix ℝ) P hPs hPi (Fintype.card V - 1 - r) hPtr
  have htr : ∑ a, ∑ b, P a b * Gᶜ.lapMatrix ℝ b a =
      S G r + n * (Fintype.card V - 1 - r) - ∑ a, (G.degree a : ℝ) := by
    have hQL : ∑ a, ∑ b, Q a b * G.lapMatrix ℝ b a = topSum hG r := trace_topP hG r
    have e : ∀ a b, P a b * Gᶜ.lapMatrix ℝ b a =
        (if a = b then 1 else 0) * Gᶜ.lapMatrix ℝ b a -
          (n * (Q a b * (if b = a then 1 else 0)) - Q a b - Q a b * G.lapMatrix ℝ b a) -
          Gᶜ.lapMatrix ℝ b a / n := by
      intro a b; rw [lap_compl_entry G b a]; simp only [P]; rw [← hn]; ring
    rw [sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => e a b))]
    simp only [sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, if_true,
      ← mul_sum, mul_ite, mul_one, mul_zero, sum_ite_eq', ← sum_div]
    have hrowc : ∀ b, ∑ a, Gᶜ.lapMatrix ℝ b a = 0 := fun b => by
      have := congrFun (Gᶜ.lapMatrix_mulVec_one_eq_zero ℝ) b
      simpa [mulVec, dotProduct] using this
    rw [sum_comm (f := fun a b => Gᶜ.lapMatrix ℝ b a)]
    simp only [hrowc, sum_const_zero, zero_div, sub_zero, hQtr, hQrow, hQL]
    rw [trace_lapM]
    have hdeg : ∀ a, (Gᶜ.degree a : ℝ) = n - 1 - G.degree a := fun a => deg_compl_real G a
    simp only [hdeg, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    unfold S; rw [← hn]; ring
  rw [htr] at hky
  unfold S at hky ⊢
  push_cast [show r ≤ Fintype.card V - 1 by omega, show 1 ≤ Fintype.card V by omega] at hky ⊢
  linarith

lemma D_compl (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hrn : r + 1 ≤ Fintype.card V) :
    D Gᶜ (Fintype.card V - 1 - r) =
      (Fintype.card V : ℝ) * (Fintype.card V - 1 - r) - ∑ a, (G.degree a : ℝ) + D G r := by
  unfold D
  have hr : ((Fintype.card V - 1 - r : ℕ) : ℝ) = Fintype.card V - 1 - r := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  have pt : ∀ a, (min (Gᶜ.degree a : ℝ) ((Fintype.card V - 1 - r : ℕ) : ℝ)) =
      (Fintype.card V - 1 - r) - G.degree a + min (G.degree a : ℝ) r := by
    intro a
    rw [deg_compl_real, hr]
    have h2 := degree_lt_card G a
    by_cases hd : G.degree a ≤ r
    · have hd' : (G.degree a : ℝ) ≤ r := by exact_mod_cast hd
      rw [min_eq_left hd', min_eq_right (by linarith)]; ring
    · push Not at hd
      have hd' : (r : ℝ) ≤ G.degree a := by exact_mod_cast hd.le
      rw [min_eq_right hd', min_eq_left (by linarith)]; ring
  rw [sum_congr rfl (fun a _ => pt a), sum_add_distrib, sum_sub_distrib, sum_const, card_univ,
    nsmul_eq_mul]

/-! ### Combinatorial pieces of Bai's argument -/

lemma deg_real (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) :
    (G.degree a : ℝ) = ∑ b, if G.Adj a b then (1:ℝ) else 0 := G.degree_eq_sum_if_adj (R := ℝ) a

/-- Deleting an edge between two vertices of degree `≤ k` lowers `D_k` by `2`. -/
lemma D_delete_edge (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (huv : G.Adj u v)
    (k : ℕ) (hu : G.degree u ≤ k) (hv : G.degree v ≤ k) :
    D (G.deleteEdges {s(u, v)}) k + 2 ≤ D G k := by
  set G' := G.deleteEdges {s(u, v)}
  have hne : u ≠ v := G.ne_of_adj huv
  have hdeg : ∀ a, (G'.degree a : ℝ) ≤ G.degree a - (if a = u then 1 else 0) -
      (if a = v then 1 else 0) := by
    intro a
    rw [deg_real, deg_real]
    have e : ∀ b, (if G'.Adj a b then (1:ℝ) else 0) ≤ (if G.Adj a b then 1 else 0) -
        (if a = u ∧ b = v then 1 else 0) - (if a = v ∧ b = u then 1 else 0) := by
      intro b
      have hG' : G'.Adj a b ↔ G.Adj a b ∧ ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) := by
        simp only [G', SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
      by_cases h1 : a = u ∧ b = v
      · obtain ⟨rfl, rfl⟩ := h1
        have : ¬ (a = b ∧ b = a) := fun h => hne h.1
        simp [hG', huv, hne, Ne.symm hne]
      · by_cases h2 : a = v ∧ b = u
        · obtain ⟨rfl, rfl⟩ := h2
          simp [hG', huv.symm, hne, Ne.symm hne]
        · by_cases hab : G.Adj a b
          · simp [hG', hab, h1, h2]
          · have : ¬ G'.Adj a b := fun h => hab (hG'.mp h).1
            simp [this, hab, h1, h2]
    have := sum_le_sum (fun b (_ : b ∈ univ) => e b)
    rw [sum_sub_distrib, sum_sub_distrib] at this
    have s1 : ∑ b, (if a = u ∧ b = v then (1:ℝ) else 0) = if a = u then 1 else 0 := by
      by_cases ha : a = u
      · simp [ha]
      · simp [ha]
    have s2 : ∑ b, (if a = v ∧ b = u then (1:ℝ) else 0) = if a = v then 1 else 0 := by
      by_cases ha : a = v
      · simp [ha]
      · simp [ha]
    rw [s1, s2] at this; exact this
  unfold D
  have pt : ∀ a, (min (G'.degree a : ℝ) k) ≤ min (G.degree a : ℝ) k -
      (if a = u then 1 else 0) - (if a = v then 1 else 0) := by
    intro a
    have h := hdeg a
    by_cases hau : a = u
    · subst hau
      have : (G.degree a : ℝ) ≤ k := by exact_mod_cast hu
      rw [min_eq_left this]
      simp only [if_true, if_neg hne] at h ⊢
      linarith [min_le_left (G'.degree a : ℝ) k]
    · by_cases hav : a = v
      · subst hav
        have : (G.degree a : ℝ) ≤ k := by exact_mod_cast hv
        rw [min_eq_left this]
        simp only [if_true, if_neg hau] at h ⊢
        linarith [min_le_left (G'.degree a : ℝ) k]
      · simp only [hau, hav, if_false, sub_zero] at h ⊢
        exact min_le_min_right _ h
  have := sum_le_sum (fun a (_ : a ∈ univ) => pt a)
  rw [sum_sub_distrib, sum_sub_distrib, sum_ite_eq', sum_ite_eq'] at this
  simp only [mem_univ, if_true] at this
  linarith

/-- The graph `Ĝ`: `G` with the vertex set `K` completed to a clique. -/
def Ghat (G : SimpleGraph V) (K : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∨ (a ≠ b ∧ a ∈ K ∧ b ∈ K)
  symm := ⟨fun a b h => h.elim (fun h => Or.inl h.symm)
    (fun h => Or.inr ⟨h.1.symm, h.2.2, h.2.1⟩)⟩
  loopless := ⟨fun a h => h.elim (fun h => G.loopless.irrefl _ h) (fun h => h.1 rfl)⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) : DecidableRel (Ghat G K).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj a b ∨ (a ≠ b ∧ a ∈ K ∧ b ∈ K)))

lemma le_Ghat (G : SimpleGraph V) (K : Finset V) : G ≤ Ghat G K := fun _ _ h => Or.inl h

lemma Ghat_deg_out (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (v : V) (hv : v ∉ K) :
    ((Ghat G K).degree v : ℝ) = G.degree v := by
  rw [deg_real, deg_real]
  refine sum_congr rfl (fun b _ => ?_)
  have : (Ghat G K).Adj v b ↔ G.Adj v b := by
    simp only [Ghat]; constructor
    · rintro (h | h)
      · exact h
      · exact absurd h.2.1 hv
    · exact Or.inl
  by_cases hb : G.Adj v b
  · simp [hb, this.mpr hb]
  · have hb' : ¬ (Ghat G K).Adj v b := fun h => hb (this.mp h)
    simp [hb, hb']

lemma Ghat_deg_ge (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (v : V) :
    (G.degree v : ℝ) ≤ (Ghat G K).degree v := by
  rw [deg_real, deg_real]
  refine sum_le_sum (fun b _ => ?_)
  by_cases hb : G.Adj v b
  · simp [hb, (le_Ghat G K) hb]
  · simp only [hb, if_false]; split_ifs <;> norm_num

lemma deg_in_ge (H : SimpleGraph V) [DecidableRel H.Adj] (K : Finset V)
    (hK : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → H.Adj i j) (v : V) (hv : v ∈ K) :
    (K.card : ℝ) - 1 ≤ H.degree v := by
  rw [deg_real]
  have e : ∀ c, (if c ∈ K then (1:ℝ) else 0) - (if c = v then 1 else 0) ≤
      if H.Adj v c then 1 else 0 := by
    intro c
    by_cases hcv : c = v
    · subst hcv; simp [hv]
    · by_cases hc : c ∈ K
      · simp [hc, hcv, hK v hv c hc (fun e => hcv e.symm)]
      · simp only [hc, hcv, if_false]; split_ifs <;> norm_num
  have := sum_le_sum (fun c (_ : c ∈ univ) => e c)
  rw [sum_sub_distrib, sum_ite_K, sum_ite_eq'] at this
  simpa using this

lemma deg_out_le (H : SimpleGraph V) [DecidableRel H.Adj] (K : Finset V)
    (hK : ∀ i ∉ K, ∀ j ∉ K, ¬ H.Adj i j) (v : V) (hv : v ∉ K) : H.degree v ≤ K.card := by
  have : (H.degree v : ℝ) ≤ K.card := by
    rw [deg_real, show (K.card : ℝ) = K.card * 1 by ring, ← sum_ite_K K 1]
    refine sum_le_sum (fun c _ => ?_)
    by_cases hadj : H.Adj v c
    · have hc : c ∈ K := by by_contra hc; exact hK v hv c hc hadj
      simp [hadj, hc]
    · simp only [hadj, if_false]; split_ifs <;> norm_num
  exact_mod_cast this

/-- Number of ordered adjacent pairs: the measure for the inner induction. -/
def mu (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (univ.filter (fun p : V × V => G.Adj p.1 p.2)).card

lemma mu_delete (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (huv : G.Adj u v) :
    mu (G.deleteEdges {s(u, v)}) < mu G := by
  unfold mu
  apply card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨(u, v), by simp [huv], by simp⟩
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, SimpleGraph.deleteEdges_adj] at hp ⊢
    exact hp.1

lemma S_zero (G : SimpleGraph V) [DecidableRel G.Adj] : S G 0 = 0 := by
  unfold S topSum; simp

/-- **The Grone–Merris–Bai theorem**, by Bai's minimal counterexample argument. -/
theorem gmb_le (k : ℕ) : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], S G k ≤ D G k := by
  induction k using Nat.strong_induction_on with
  | _ k IHk =>
  have main : ∀ m (G : SimpleGraph V) [DecidableRel G.Adj], mu G = m → S G k ≤ D G k := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IHm =>
    intro G _ hm
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · rw [S_zero]; exact D_nonneg G 0
      · exact gmb_one G
    by_cases hkn : Fintype.card V - 1 ≤ k
    · exact S_le_D_full G k hkn
    push Not at hkn
    by_contra hlt
    push Not at hlt
    have hprev : S G (k - 1) ≤ D G (k - 1) := IHk (k - 1) (by omega) G
    -- Bai's Lemma 13
    have L13 : ∀ u v, G.Adj u v → G.degree u ≤ k → G.degree v ≤ k → False := by
      intro u v huv hu hv
      have h1 := S_le_of_delete_edge G u v huv k (by omega)
      have h2 := IHm _ (hm ▸ mu_delete G u v huv) (G.deleteEdges {s(u, v)}) rfl
      have h3 := D_delete_edge G u v huv k hu hv
      linarith
    set K := univ.filter (fun v => k ≤ G.degree v) with hK
    set N := K.card with hN
    have hmemK : ∀ v, v ∈ K ↔ k ≤ G.degree v := fun v => by simp [hK]
    have hNreal : (N : ℝ) = D G k - D G (k - 1) := (D_sub G k (by omega)).symm
    have hlamG : (N : ℝ) < (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨k - 1, by omega⟩ := by
      rw [eig_eq_S_sub G k (by omega) (by omega)]; linarith
    set H := Ghat G K with hH
    have hsplit : IsSplit H K := by
      refine ⟨fun i hi j hj hij => Or.inr ⟨hij, hi, hj⟩, fun i hi j hj hadj => ?_⟩
      rcases hadj with hadj | hadj
      · have hi' : G.degree i ≤ k := by have := (hmemK i).not.mp hi; omega
        have hj' : G.degree j ≤ k := by have := (hmemK j).not.mp hj; omega
        exact L13 i j hadj hi' hj'
      · exact hi hadj.2.1
    have hDH : D H k = D G k := by
      unfold D
      refine sum_congr rfl (fun v _ => ?_)
      by_cases hv : v ∈ K
      · have h1 : (k : ℝ) ≤ G.degree v := by exact_mod_cast (hmemK v).mp hv
        have h2 := Ghat_deg_ge G K v
        rw [min_eq_right h1, min_eq_right (h1.trans h2)]
      · rw [Ghat_deg_out G K v hv]
    have hSH : S G k ≤ S H k := S_mono G H (le_Ghat G K) k (by omega)
    have hlamH : (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨k - 1, by omega⟩ ≤
        (H.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨k - 1, by omega⟩ :=
      eig_mono G H (le_Ghat G K) _
    have hout : ∀ v ∉ K, (H.degree v : ℝ) ≤ (k : ℝ) - 1 := by
      intro v hv
      rw [Ghat_deg_out G K v hv]
      have : G.degree v + 1 ≤ k := by have := (hmemK v).not.mp hv; omega
      have : ((G.degree v + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast this
      push_cast at this; linarith
    have hNn : N ≤ Fintype.card V := card_le_univ K
    rcases lt_trichotomy N k with hNk | hNk | hNk
    · -- Case `N < k`
      have h1 := split_lambda_succ_le H K hsplit N (fun v hv => deg_out_le H K hsplit.2 v hv)
        (by omega)
      have h2 : (H.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨k - 1, by omega⟩ ≤
          (H.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨N, by omega⟩ :=
        (H.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone
          (Fin.le_iff_val_le_val.mpr (by simp; omega))
      have h3 := eig_eq_S_sub H (N + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at h3
      rw [h3] at h2
      linarith
    · -- Case `N = k`
      have idx : (⟨K.card - 1, by omega⟩ : Fin (Fintype.card V)) = ⟨k - 1, by omega⟩ :=
        Fin.ext (by simp; omega)
      have hyp : Hyp H K ((k : ℝ) - 1) :=
        { split := hsplit
          deg := hout
          δN := by rw [← hN, hNk]; linarith
          pos := by omega
          lt := by omega
          lam := by rw [idx, ← hN, hNk]; rw [hNk] at hlamG; linarith
          str := Or.inl (by rw [idx, ← hN]; linarith) }
      have := bai_lemma6_core hyp
      rw [← hN, hNk] at this
      linarith
    · -- Case `k < N`
      have hpred := split_lambda_pred_ge H K hsplit (by omega)
      rw [← hN] at hpred
      obtain ⟨p, hp⟩ : ∃ p, N = p + 2 := ⟨N - 2, by omega⟩
      have hN1 : N - 1 = p + 1 := by omega
      have hN2 : N - 2 = p := by omega
      have e2 := eig_eq_S_sub H (p + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at e2
      rw [hN1, hN2] at hpred
      have hstep : ∀ l, k ≤ l → l + 1 ≤ N - 1 →
          S H l - D H l ≤ S H (l + 1) - D H (l + 1) := by
        intro l hkl hlN
        have e1 := eig_eq_S_sub H (l + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at e1
        have hmono : (H.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨p, by omega⟩ ≤
            (H.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨l, by omega⟩ :=
          (H.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone
            (Fin.le_iff_val_le_val.mpr (by simp; omega))
        have hD := D_sub H (l + 1) (by omega)
        simp only [Nat.add_sub_cancel] at hD
        have hcard : (univ.filter (fun v => l + 1 ≤ H.degree v)).card ≤ N := by
          apply card_le_card
          intro v hv
          simp only [mem_filter, mem_univ, true_and] at hv
          by_contra hvK
          have := hout v hvK
          have : ((l + 1 : ℕ) : ℝ) ≤ H.degree v := by exact_mod_cast hv
          have : (k : ℝ) ≤ l := by exact_mod_cast hkl
          push_cast at *; linarith
        have : ((univ.filter (fun v => l + 1 ≤ H.degree v)).card : ℝ) ≤ N := by
          exact_mod_cast hcard
        linarith
      have hC : ∀ l, k ≤ l → l ≤ N - 1 → S H k - D H k ≤ S H l - D H l := by
        intro l hkl hlN
        induction l, hkl using Nat.le_induction with
        | base => exact le_rfl
        | succ l hkl ih => exact (ih (by omega)).trans (hstep l hkl hlN)
      have hpos : 0 < S H (N - 1) - D H (N - 1) := by
        have := hC (N - 1) (by omega) le_rfl
        linarith
      by_cases hNeq : N = Fintype.card V
      · have := S_le_D_full H (N - 1) (by omega)
        linarith
      have hNlt : N < Fintype.card V := lt_of_le_of_ne hNn hNeq
      have idxN : (⟨K.card - 1, by omega⟩ : Fin (Fintype.card V)) = ⟨N - 1, by omega⟩ :=
        Fin.ext rfl
      by_cases hlamN : (N : ℝ) ≤ (H.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨N - 1, by omega⟩
      · -- Subcase `λ_N(Ĝ) ≥ N`
        have hyp : Hyp H K ((k : ℝ) - 1) :=
          { split := hsplit
            deg := hout
            δN := by
              have : (k : ℝ) ≤ N := by exact_mod_cast hNk.le
              rw [← hN]; linarith
            pos := by omega
            lt := by omega
            lam := by rw [idxN, ← hN]; exact hlamN
            str := Or.inr (by
              have : (k : ℝ) ≤ N := by exact_mod_cast hNk.le
              rw [← hN]; linarith) }
        have h6 := bai_lemma6_core hyp
        rw [← hN] at h6
        have e1 := eig_eq_S_sub H N (by omega) (by omega)
        have hD := D_sub H N (by omega)
        have hcard : (univ.filter (fun v => N ≤ H.degree v)).card ≤ N := by
          apply card_le_card
          intro v hv
          simp only [mem_filter, mem_univ, true_and] at hv
          by_contra hvK
          have := hout v hvK
          have : (N : ℝ) ≤ H.degree v := by exact_mod_cast hv
          have : (k : ℝ) < N := by exact_mod_cast hNk
          linarith
        have : ((univ.filter (fun v => N ≤ H.degree v)).card : ℝ) ≤ N := by
          exact_mod_cast hcard
        linarith
      · -- Subcase `λ_N(Ĝ) < N`: pass to the complement
        push Not at hlamN
        have hKc : Kᶜ.card = Fintype.card V - N := card_compl K
        have hge := compl_eig_ge H N (by omega) hNlt
        have idxM : (⟨Kᶜ.card - 1, by omega⟩ : Fin (Fintype.card V)) =
            ⟨Fintype.card V - N - 1, by omega⟩ := Fin.ext (by simp [hKc])
        have hMreal : (Kᶜ.card : ℝ) = Fintype.card V - N := by
          rw [hKc]; push_cast [hNn]; ring
        have hyp : Hyp Hᶜ Kᶜ (Kᶜ.card : ℝ) :=
          { split := by
              refine ⟨fun i hi j hj hij => ?_, fun i hi j hj hadj => ?_⟩
              · rw [SimpleGraph.compl_adj]
                exact ⟨hij, hsplit.2 i (by simpa using hi) j (by simpa using hj)⟩
              · rw [SimpleGraph.compl_adj] at hadj
                exact hadj.2 (hsplit.1 i (by simpa using hi) j (by simpa using hj) hadj.1)
            deg := by
              intro v hv
              have hvK : v ∈ K := by simpa using hv
              rw [deg_compl_real]
              have := deg_in_ge H K hsplit.1 v hvK
              rw [hMreal]; rw [← hN] at this; linarith
            δN := le_rfl
            pos := by omega
            lt := by omega
            lam := by rw [idxM, hMreal]; linarith
            str := Or.inl (by rw [idxM, hMreal]; linarith) }
        have h6 := bai_lemma6_core hyp
        have hpos' : 0 < (H.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨N - 1 - 1, by omega⟩ := by
          have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
          have hidx : (⟨N - 1 - 1, by omega⟩ : Fin (Fintype.card V)) = ⟨p, by omega⟩ :=
            Fin.ext (by simp; omega)
          rw [hidx, e2]; linarith
        have htr := compl_S_transfer H (N - 1) (by omega) (by omega) hpos'
        have hDc := D_compl H (N - 1) (by omega)
        have e3 : Fintype.card V - 1 - (N - 1) = Kᶜ.card := by rw [hKc]; omega
        rw [e3] at htr hDc
        linarith
  exact fun G _ => main _ G rfl

/-- The Grone–Merris–Bai theorem in the form used by Stage 1. -/
theorem groneMerrisBai : GroneMerrisBai V := fun H _ k => gmb_le k H

end Brouwer.Stage2

namespace Brouwer

/-- **Brouwer's Laplacian conjecture**, unconditionally: for every finite simple graph `G`
with `m` edges and every `k`, the sum of the `k` largest Laplacian eigenvalues is at most
`m + k(k+1)/2`. -/
theorem brouwer {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) :
    topSum (G.isHermitian_lapMatrix ℝ) k ≤ G.edgeFinset.card + (k * (k + 1) / 2 : ℝ) :=
  brouwer_of_GMB Stage2.groneMerrisBai G k

/-- **The Grone–Merris–Bai theorem**: the Laplacian spectrum is majorized by the conjugate
degree sequence, i.e. `λ₁ + ⋯ + λ_k ≤ Σ_v min(deg v, k)` for every `k`. -/
theorem grone_merris_bai {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) :
    topSum (G.isHermitian_lapMatrix ℝ) k ≤ ∑ v, (min (G.degree v) k : ℝ) :=
  Stage2.groneMerrisBai G k

end Brouwer
