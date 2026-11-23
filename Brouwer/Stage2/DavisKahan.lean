/-
  Stage 2 infrastructure: the spectral projection onto the top `N` eigenvectors and a
  Davis–Kahan type perturbation bound in the Frobenius norm.
-/
import Brouwer.Stage2.CourantFischer

open Finset Matrix Module

set_option linter.unusedSectionVars false

namespace Brouwer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Plain inner product. -/
def ip (x y : V → ℝ) : ℝ := ∑ a, x a * y a

/-- Frobenius norm squared, as a plain sum. -/
def frob (C : Matrix V V ℝ) : ℝ := ∑ a, ∑ b, C a b ^ 2

lemma symm_of_herm {A : Matrix V V ℝ} (hA : A.IsHermitian) (a b : V) : A a b = A b a := by
  have := congrFun (congrFun hA.eq b) a
  simpa using this

section Proj

variable {A : Matrix V V ℝ} (hA : A.IsHermitian)

lemma sev_complete (a b : V) :
    ∑ t, sev hA t a * sev hA t b = if a = b then 1 else 0 := by
  unfold sev
  rw [Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V)))
    (fun j => ev hA j a * ev hA j b)]
  exact ev_complete hA a b

lemma ip_sev_sev (t s : Fin (Fintype.card V)) :
    ip (sev hA t) (sev hA s) = if t = s then 1 else 0 := sev_ortho hA t s

/-- Parseval's identity in the sorted eigenbasis. -/
lemma parseval (x : V → ℝ) : ∑ t, ip (sev hA t) x ^ 2 = nsq x := by
  unfold ip nsq
  have e : ∀ t, (∑ a, sev hA t a * x a) ^ 2 =
      ∑ a, ∑ b, x a * x b * (sev hA t a * sev hA t b) := by
    intro t; rw [sq, sum_mul_sum]
    exact sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => by ring))
  simp_rw [e]
  rw [sum_comm]
  refine sum_congr rfl (fun a _ => ?_)
  rw [sum_comm]
  simp_rw [← mul_sum, sev_complete]
  simp

/-- Spectral projection onto the top `N` sorted eigenvectors. -/
noncomputable def topP (N : ℕ) : Matrix V V ℝ := fun a b =>
  ∑ t ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < N), sev hA t a * sev hA t b

lemma topP_symm (N : ℕ) (a b : V) : topP hA N a b = topP hA N b a := by
  unfold topP; exact sum_congr rfl (fun t _ => mul_comm _ _)

/-- `P x = Σ_{t<N} ⟨u_t, x⟩ u_t`. -/
lemma topP_apply (N : ℕ) (x : V → ℝ) (a : V) :
    ∑ b, topP hA N a b * x b =
      ∑ t ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < N),
        ip (sev hA t) x * sev hA t a := by
  unfold topP ip
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl (fun t _ => ?_)
  exact sum_congr rfl (fun b _ => by ring)

lemma topP_sev (N : ℕ) (s : Fin (Fintype.card V)) (a : V) :
    ∑ b, topP hA N a b * sev hA s b = if s.val < N then sev hA s a else 0 := by
  rw [topP_apply]
  simp_rw [ip_sev_sev]
  simp only [ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq']
  simp

end Proj

section DK

variable {A B : Matrix V V ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)

lemma sum_topP_mul (N : ℕ) :
    ∑ a, ∑ b, topP hA N a b * topP hB N a b =
      ∑ t ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < N),
        ∑ s ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < N),
          ip (sev hA t) (sev hB s) ^ 2 := by
  unfold topP ip
  have e : ∀ a b, (∑ t ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < N),
        sev hA t a * sev hA t b) *
      (∑ s ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < N),
        sev hB s a * sev hB s b) =
      ∑ t ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < N),
        ∑ s ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < N),
          (sev hA t a * sev hB s a) * (sev hA t b * sev hB s b) := by
    intro a b; rw [sum_mul_sum]
    exact sum_congr rfl (fun t _ => sum_congr rfl (fun s _ => by ring))
  simp_rw [e]
  have sw : ∀ {α β γ : Type _} (X : Finset α) (Y : Finset β) (Z : Finset γ)
      (f : α → β → γ → ℝ), ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f x y z =
        ∑ y ∈ Y, ∑ z ∈ Z, ∑ x ∈ X, f x y z := by
    intro α β γ X Y Z f
    rw [sum_comm]; exact sum_congr rfl (fun y _ => sum_comm)
  rw [sum_congr rfl (fun a _ => sw _ _ _ _)]
  rw [sw]
  refine sum_congr rfl (fun t _ => sum_congr rfl (fun s _ => ?_))
  rw [sq, sum_mul_sum]

lemma card_lt_filter (N : ℕ) (hN : N ≤ Fintype.card V) :
    (univ.filter (fun t : Fin (Fintype.card V) => t.val < N)).card = N := by
  rw [Fin.card_filter_val_lt]; omega

lemma sum_topP_sq (N : ℕ) (hN : N ≤ Fintype.card V) :
    ∑ a, ∑ b, topP hA N a b * topP hA N a b = N := by
  rw [sum_topP_mul hA hA]
  simp_rw [ip_sev_sev]
  have : ∀ t ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < N),
      ∑ s ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < N),
        ((if t = s then (1:ℝ) else 0)) ^ 2 = 1 := by
    intro t ht
    simp only [ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [sum_ite_eq]; simp [ht]
  rw [sum_congr rfl this]
  simp [card_lt_filter N hN]

/-- `⟨u_t, C w_s⟩` summed in squares over both bases is the Frobenius norm of `C`. -/
lemma parseval2 (C : Matrix V V ℝ) :
    ∑ t, ∑ s, (∑ a, ∑ b, sev hA t a * C a b * sev hB s b) ^ 2 = frob C := by
  have e : ∀ t s, ∑ a, ∑ b, sev hA t a * C a b * sev hB s b =
      ip (sev hB s) (fun b => ∑ a, sev hA t a * C a b) := by
    intro t s; unfold ip
    rw [sum_comm]
    refine sum_congr rfl (fun b _ => ?_)
    rw [mul_sum]; exact sum_congr rfl (fun a _ => by ring)
  simp_rw [e, parseval hB]
  unfold nsq frob
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl (fun b _ => ?_)
  have := parseval hA (fun a => C a b)
  unfold ip nsq at this
  simpa [sq] using this

/-- **Davis–Kahan** (Frobenius form): if the `N`-th eigenvalue of `B` exceeds the
`(N+1)`-th eigenvalue of `A` by at least `g > 0`, the top-`N` projections are close. -/
theorem davis_kahan (N : ℕ) (hN : N < Fintype.card V) (hN0 : 0 < N) (g : ℝ) (hg : 0 < g)
    (hgap : hA.eigenvalues₀ ⟨N, hN⟩ + g ≤ hB.eigenvalues₀ ⟨N - 1, by omega⟩) :
    frob (topP hA N - topP hB N) * g ^ 2 ≤ 2 * frob (B - A) := by
  classical
  set F := univ.filter (fun t : Fin (Fintype.card V) => t.val < N) with hF
  set c : Fin (Fintype.card V) → Fin (Fintype.card V) → ℝ :=
    fun t s => ip (sev hA t) (sev hB s) with hc
  -- ‖P - Q‖² = 2 Σ_{s<N} Σ_{t≥N} c² .
  have hexp : frob (topP hA N - topP hB N) =
      2 * ∑ s ∈ F, ∑ t ∈ univ.filter (fun t : Fin (Fintype.card V) => ¬ t.val < N),
        c t s ^ 2 := by
    have h1 : frob (topP hA N - topP hB N) =
        ∑ a, ∑ b, topP hA N a b * topP hA N a b + ∑ a, ∑ b, topP hB N a b * topP hB N a b
          - 2 * ∑ a, ∑ b, topP hA N a b * topP hB N a b := by
      unfold frob
      simp only [Matrix.sub_apply]
      rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl (fun a _ => ?_)
      rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl (fun b _ => by ring)
    rw [h1, sum_topP_sq hA N hN.le, sum_topP_sq hB N hN.le, sum_topP_mul hA hB]
    have hpar : ∀ s, ∑ t, c t s ^ 2 = 1 := by
      intro s
      have := parseval hA (sev hB s)
      rw [this]; unfold nsq
      have := sev_ortho hB s s; simpa using this
    have hN' : (N : ℝ) = ∑ s ∈ F, ∑ t, c t s ^ 2 := by
      simp_rw [hpar]; simp [hF, card_lt_filter N hN.le]
    have hsplit : ∀ s, ∑ t, c t s ^ 2 = ∑ t ∈ F, c t s ^ 2 +
        ∑ t ∈ univ.filter (fun t : Fin (Fintype.card V) => ¬ t.val < N), c t s ^ 2 := by
      intro s; rw [hF, sum_filter_add_sum_filter_not]
    rw [hN']
    simp_rw [hsplit, sum_add_distrib]
    rw [sum_comm (s := F) (t := F)]
    ring
  -- each coefficient is controlled by `B - A`.
  have hkey : ∀ s ∈ F, ∀ t ∈ univ.filter (fun t : Fin (Fintype.card V) => ¬ t.val < N),
      c t s ^ 2 * g ^ 2 ≤ (∑ a, ∑ b, sev hA t a * (B - A) a b * sev hB s b) ^ 2 := by
    intro s hs t ht
    simp only [hF, mem_filter, mem_univ, true_and] at hs ht
    have hBs : ∑ a, ∑ b, sev hA t a * B a b * sev hB s b =
        hB.eigenvalues₀ s * c t s := by
      have : ∀ a, ∑ b, sev hA t a * B a b * sev hB s b =
          sev hA t a * (hB.eigenvalues₀ s * sev hB s a) := by
        intro a; rw [← sev_eig hB, mul_sum]
        exact sum_congr rfl (fun b _ => by ring)
      rw [sum_congr rfl (fun a _ => this a), hc]; unfold ip
      rw [mul_sum]; exact sum_congr rfl (fun a _ => by ring)
    have hAs : ∑ a, ∑ b, sev hA t a * A a b * sev hB s b =
        hA.eigenvalues₀ t * c t s := by
      rw [sum_comm]
      have : ∀ b, ∑ a, sev hA t a * A a b * sev hB s b =
          (hA.eigenvalues₀ t * sev hA t b) * sev hB s b := by
        intro b; rw [← sev_eig hA, sum_mul]
        exact sum_congr rfl (fun a _ => by rw [symm_of_herm hA a b]; ring)
      rw [sum_congr rfl (fun b _ => this b), hc]; unfold ip
      rw [mul_sum]; exact sum_congr rfl (fun a _ => by ring)
    have hdiff : ∑ a, ∑ b, sev hA t a * (B - A) a b * sev hB s b =
        (hB.eigenvalues₀ s - hA.eigenvalues₀ t) * c t s := by
      have : ∑ a, ∑ b, sev hA t a * (B - A) a b * sev hB s b =
          ∑ a, ∑ b, sev hA t a * B a b * sev hB s b -
            ∑ a, ∑ b, sev hA t a * A a b * sev hB s b := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl (fun a _ => ?_)
        rw [← sum_sub_distrib]
        refine sum_congr rfl (fun b _ => ?_)
        simp only [Matrix.sub_apply]; ring
      rw [this, hBs, hAs]; ring
    have h1 : hA.eigenvalues₀ t ≤ hA.eigenvalues₀ ⟨N, hN⟩ :=
      hA.eigenvalues₀_antitone (Fin.le_iff_val_le_val.mpr (by simp; omega))
    have h2 : hB.eigenvalues₀ ⟨N - 1, by omega⟩ ≤ hB.eigenvalues₀ s :=
      hB.eigenvalues₀_antitone (Fin.le_iff_val_le_val.mpr (by simp; omega))
    have hge : g ≤ hB.eigenvalues₀ s - hA.eigenvalues₀ t := by linarith
    rw [hdiff, mul_pow, mul_comm]
    have : g ^ 2 ≤ (hB.eigenvalues₀ s - hA.eigenvalues₀ t) ^ 2 := by
      have := hg.le; nlinarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hsum : (∑ s ∈ F, ∑ t ∈ univ.filter (fun t : Fin (Fintype.card V) => ¬ t.val < N),
      c t s ^ 2) * g ^ 2 ≤ frob (B - A) := by
    rw [sum_mul]
    calc ∑ s ∈ F, (∑ t ∈ univ.filter (fun t : Fin (Fintype.card V) => ¬ t.val < N),
          c t s ^ 2) * g ^ 2
        ≤ ∑ s ∈ F, ∑ t ∈ univ.filter (fun t : Fin (Fintype.card V) => ¬ t.val < N),
          (∑ a, ∑ b, sev hA t a * (B - A) a b * sev hB s b) ^ 2 := by
          refine sum_le_sum (fun s hs => ?_)
          rw [sum_mul]
          exact sum_le_sum (fun t ht => hkey s hs t ht)
      _ ≤ ∑ s, ∑ t, (∑ a, ∑ b, sev hA t a * (B - A) a b * sev hB s b) ^ 2 := by
          refine sum_le_sum_of_subset_of_nonneg (subset_univ F) (fun s _ _ =>
            sum_nonneg (fun t _ => sq_nonneg _)) |>.trans' ?_
          refine sum_le_sum (fun s _ => ?_)
          exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun t _ _ => sq_nonneg _)
      _ = frob (B - A) := by rw [sum_comm]; exact parseval2 hA hB (B - A)
  rw [hexp]
  nlinarith [hsum]

end DK

end Brouwer
