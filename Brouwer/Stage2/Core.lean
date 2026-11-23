/-
  Stage 2: the analytic core of Bai's proof (Lemmas 7–11 and Lemma 6).

  Part A: the homotopy `L_α = (1-α) L(K_N ∨ \bar K_M) + α L(G)` between the complete split
  graph and a split graph `G`, and a uniform gap between its `N`-th and `(N+1)`-th
  eigenvalues (Bai's Lemma 8, made quantitative).
-/
import Brouwer.Stage2.Blueprint
import Brouwer.Stage2.DavisKahan

open Finset Matrix Module

set_option linter.unusedSectionVars false

namespace Brouwer.Stage2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete split graph with clique `K` and independent set `Kᶜ`. -/
def Gc (K : Finset V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (a ∈ K ∨ b ∈ K)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (K : Finset V) : DecidableRel (Gc K).Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ (a ∈ K ∨ b ∈ K)))

lemma herm_of_symm {A : Matrix V V ℝ} (h : ∀ a b, A a b = A b a) : A.IsHermitian := by
  ext a b; rw [conjTranspose_apply, star_trivial, h]

lemma lap_symm (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    G.lapMatrix ℝ a b = G.lapMatrix ℝ b a := ((G.isSymm_lapMatrix ℝ).apply a b).symm

lemma sq_diff_sum (U : Finset V) (x : V → ℝ) :
    ∑ a ∈ U, ∑ b ∈ U, (x a - x b) ^ 2 =
      2 * (U.card : ℝ) * ∑ a ∈ U, x a * x a - 2 * (∑ a ∈ U, x a) ^ 2 := by
  have : ∀ a b, (x a - x b) ^ 2 = x a * x a + x b * x b - 2 * (x a * x b) := fun a b => by ring
  simp only [this, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum,
    ← sum_mul, sq]
  ring

lemma compl_eq_filter (K : Finset V) : Kᶜ = univ.filter (fun a => a ∉ K) := by
  ext a; simp

lemma sum_compl_eq (K : Finset V) (f : V → ℝ) :
    ∑ a ∈ Kᶜ, f a = ∑ a, if a ∈ K then 0 else f a := by
  rw [compl_eq_filter, sum_filter]
  exact sum_congr rfl (fun a _ => by by_cases h : a ∈ K <;> simp [h])

lemma lap_qform_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    0 ≤ qf (G.lapMatrix ℝ) x := by
  unfold qf; rw [lap_qform]
  apply div_nonneg _ (by norm_num)
  exact sum_nonneg (fun a _ => sum_nonneg (fun b _ => by split_ifs <;> positivity))

/-- Quadratic form of the complete split graph. -/
lemma qf_Gc (K : Finset V) (x : V → ℝ) :
    qf ((Gc K).lapMatrix ℝ) x = (Fintype.card V : ℝ) * nsq x - (∑ a, x a) ^ 2 -
      ((Kᶜ.card : ℝ) * ∑ a ∈ Kᶜ, x a * x a - (∑ a ∈ Kᶜ, x a) ^ 2) := by
  unfold qf; rw [lap_qform]
  have hpt : ∀ a b, (if (Gc K).Adj a b then (x a - x b) ^ 2 else 0) =
      (x a - x b) ^ 2 - (if a ∈ K then 0 else if b ∈ K then 0 else (x a - x b) ^ 2) := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp
    · by_cases ha : a ∈ K
      · simp [Gc, hab, ha]
      · by_cases hb : b ∈ K
        · simp [Gc, hab, ha, hb]
        · simp [Gc, hab, ha, hb]
  simp only [hpt, sum_sub_distrib]
  have h1 := sq_diff_sum univ x
  have h2 := sq_diff_sum Kᶜ x
  rw [card_univ] at h1
  have e2 : ∑ a, ∑ b, (if a ∈ K then 0 else if b ∈ K then 0 else (x a - x b) ^ 2) =
      ∑ a ∈ Kᶜ, ∑ b ∈ Kᶜ, (x a - x b) ^ 2 := by
    rw [sum_compl_eq]
    refine sum_congr rfl (fun a _ => ?_)
    by_cases ha : a ∈ K
    · simp [ha]
    · simp only [ha, if_false]; rw [sum_compl_eq]
  rw [e2, h1, h2]
  unfold nsq
  ring

/-- Quadratic forms are linear in the matrix. -/
lemma qf_comb2 (s t : ℝ) (A B : Matrix V V ℝ) (x : V → ℝ) :
    qf (s • A + t • B) x = s * qf A x + t * qf B x := by
  unfold qf
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun a _ => ?_)
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl (fun b _ => by ring)

/-- The clamp of `α` to `[0,1]`. -/
noncomputable def cl (α : ℝ) : ℝ := max 0 (min 1 α)

lemma cl_nonneg (α : ℝ) : 0 ≤ cl α := le_max_left _ _
lemma cl_le_one (α : ℝ) : cl α ≤ 1 := max_le (by norm_num) (min_le_left _ _)
lemma cl_of_mem {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) : cl α = α := by
  unfold cl; rw [min_eq_right h1, max_eq_right h0]
lemma cl_lip (α β : ℝ) : |cl α - cl β| ≤ |α - β| := by
  unfold cl
  have h1 := abs_max_sub_max_le_max (0:ℝ) (min 1 α) 0 (min 1 β)
  have h2 := abs_min_sub_min_le_max (1:ℝ) α 1 β
  simp only [sub_self, abs_zero] at h1 h2
  rw [max_eq_right (abs_nonneg (min 1 α - min 1 β))] at h1
  rw [max_eq_right (abs_nonneg (α - β))] at h2
  exact h1.trans h2

section Homotopy

variable (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V)

/-- The homotopy `L_α`. -/
noncomputable def Lh (α : ℝ) : Matrix V V ℝ :=
  (1 - cl α) • (Gc K).lapMatrix ℝ + cl α • G.lapMatrix ℝ

lemma Lh_symm (α : ℝ) (a b : V) : Lh G K α a b = Lh G K α b a := by
  simp only [Lh, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, lap_symm G a b, lap_symm (Gc K) a b]

lemma Lh_herm (α : ℝ) : (Lh G K α).IsHermitian := herm_of_symm (Lh_symm G K α)

lemma qf_Lh (α : ℝ) (x : V → ℝ) :
    qf (Lh G K α) x = (1 - cl α) * qf ((Gc K).lapMatrix ℝ) x + cl α * qf (G.lapMatrix ℝ) x :=
  qf_comb2 _ _ _ _ x

lemma Lh_rowsum (α : ℝ) (a : V) : ∑ b, Lh G K α a b = 0 := by
  have h0 := congrFun ((Gc K).lapMatrix_mulVec_one_eq_zero ℝ) a
  have h1 := congrFun (G.lapMatrix_mulVec_one_eq_zero ℝ) a
  simp only [mulVec, dotProduct, Pi.one_apply, mul_one, Pi.zero_apply] at h0 h1
  simp only [Lh, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, h0, h1]
  ring

lemma Lh_sub (α β : ℝ) : Lh G K α - Lh G K β =
    (cl α - cl β) • (G.lapMatrix ℝ - (Gc K).lapMatrix ℝ) := by
  ext a b
  simp only [Lh, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end Homotopy

/-- An eigenvector with nonzero eigenvalue of a matrix with zero row sums is orthogonal to
the all-ones vector. -/
lemma sev_sum_zero {A : Matrix V V ℝ} (hA : A.IsHermitian) (hrow : ∀ a, ∑ b, A a b = 0)
    (t : Fin (Fintype.card V)) (ht : hA.eigenvalues₀ t ≠ 0) : ∑ a, sev hA t a = 0 := by
  have h : hA.eigenvalues₀ t * ∑ a, sev hA t a = 0 := by
    rw [mul_sum]
    simp_rw [← sev_eig hA]
    rw [sum_comm]
    refine sum_eq_zero (fun c _ => ?_)
    rw [← sum_mul]
    have : ∑ a, A a c = 0 := by
      rw [← hrow c]; exact sum_congr rfl (fun a _ => symm_of_herm hA a c)
    rw [this, zero_mul]
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h ht
  · exact h

/-- On the span of the top `N` eigenvectors the quadratic form is at least `λ_N`. -/
lemma qf_ge_of_mem_espan {A : Matrix V V ℝ} (hA : A.IsHermitian) (N : ℕ) (hN0 : 0 < N)
    (hN : N ≤ Fintype.card V) {x : V → ℝ}
    (hx : x ∈ espan hA (fun t => t.val < N)) :
    hA.eigenvalues₀ ⟨N - 1, by omega⟩ * nsq x ≤ qf A x := by
  obtain ⟨c, hc, rfl⟩ := mem_espan hA _ hx
  rw [qf_comb, nsq_comb, mul_sum]
  refine sum_le_sum (fun t _ => ?_)
  by_cases ht : t.val < N
  · exact mul_le_mul_of_nonneg_right
      (hA.eigenvalues₀_antitone (Fin.le_iff_val_le_val.mpr (by simp; omega))) (sq_nonneg _)
  · simp [hc t ht]

lemma finrank_espan_lt {A : Matrix V V ℝ} (hA : A.IsHermitian) (N : ℕ)
    (hN : N ≤ Fintype.card V) : finrank ℝ (espan hA (fun t => t.val < N)) = N := by
  rw [finrank_espan, Fin.card_filter_val_lt]; omega

lemma nsq_nonneg (x : V → ℝ) : 0 ≤ nsq x := sum_nonneg (fun a _ => mul_self_nonneg _)

section Gap

variable (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V)

/-- Bai's Lemma 8, upper half: `λ_{N+1}(L_α) ≤ N - α (N - δ)`. -/
theorem eig_up (hG : IsSplit G K) (δ : ℝ) (hδ : ∀ v ∉ K, (G.degree v : ℝ) ≤ δ)
    (hM : K.card < Fintype.card V) (α : ℝ) :
    (Lh_herm G K α).eigenvalues₀ ⟨K.card, hM⟩ ≤ K.card - cl α * (K.card - δ) := by
  apply eig_le_of_subspace (Lh_herm G K α) ⟨K.card, hM⟩ (coordSub K)
  · intro x hx
    have hz := coordSub_zero hx
    have hs : ∑ a, x a = ∑ a ∈ Kᶜ, x a := by
      symm; exact sum_subset (subset_univ _) (fun a _ ha => hz a (by simpa using ha))
    have hq : ∑ a ∈ Kᶜ, x a * x a = nsq x := by
      unfold nsq
      exact sum_subset (subset_univ _) (fun a _ ha => by simp [hz a (by simpa using ha)])
    have h0 : qf ((Gc K).lapMatrix ℝ) x = K.card * nsq x := by
      rw [qf_Gc, hs, hq, card_compl]
      have : K.card ≤ Fintype.card V := card_le_univ K
      push_cast [this]; ring
    have h1 : qf (G.lapMatrix ℝ) x ≤ δ * nsq x := by
      rw [qf_lap_of_edge_zero G x]
      · unfold nsq
        rw [mul_sum]
        refine sum_le_sum (fun a _ => ?_)
        by_cases ha : a ∈ K
        · simp [hz a ha]
        · exact mul_le_mul_of_nonneg_right (hδ a ha) (mul_self_nonneg _)
      · intro a b hab
        by_cases ha : a ∈ K
        · simp [hz a ha]
        · by_cases hb : b ∈ K
          · simp [hz b hb]
          · exact absurd hab (hG.2 a ha b hb)
    rw [qf_Lh, h0]
    have := cl_nonneg α; have := cl_le_one α
    nlinarith [nsq_nonneg x]
  · rw [finrank_coordSub (V := V) K]; simp only [Fin.val_mk]; omega

/-- Bai's Lemma 8, first lower bound: `λ_N(L_α) ≥ N + α (λ_N(G) - N)`. -/
theorem eig_lo1 (hK : 0 < K.card) (hM : K.card < Fintype.card V)
    (hlam : (K.card : ℝ) ≤ (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨K.card - 1, by omega⟩)
    (α : ℝ) :
    K.card + cl α * ((G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨K.card - 1, by omega⟩ - K.card)
      ≤ (Lh_herm G K α).eigenvalues₀ ⟨K.card - 1, by omega⟩ := by
  set hL := G.isHermitian_lapMatrix ℝ
  set lam := hL.eigenvalues₀ ⟨K.card - 1, by omega⟩
  apply le_eig_of_subspace (Lh_herm G K α) ⟨K.card - 1, by omega⟩
    (espan hL (fun t => t.val < K.card))
  · intro x hx
    have h1 := qf_ge_of_mem_espan hL K.card hK hM.le hx
    have hsum : ∑ a, x a = 0 := by
      obtain ⟨c, hc, rfl⟩ := mem_espan hL _ hx
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [sum_comm]
      refine sum_eq_zero (fun t _ => ?_)
      by_cases ht : t.val < K.card
      · rw [← mul_sum, sev_sum_zero hL (fun a => by
            have := congrFun (G.lapMatrix_mulVec_one_eq_zero ℝ) a
            simpa [mulVec, dotProduct] using this) t ?_, mul_zero]
        have : lam ≤ hL.eigenvalues₀ t :=
          hL.eigenvalues₀_antitone (Fin.le_iff_val_le_val.mpr (by simp; omega))
        have : (0 : ℝ) < K.card := by exact_mod_cast hK
        intro h0; linarith
      · simp [hc t ht]
    have h0 : (K.card : ℝ) * nsq x ≤ qf ((Gc K).lapMatrix ℝ) x := by
      rw [qf_Gc, hsum]
      have hq : ∑ a ∈ Kᶜ, x a * x a ≤ nsq x :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun a _ _ => mul_self_nonneg _)
      have hc : (Kᶜ.card : ℝ) = Fintype.card V - K.card := by
        rw [card_compl]; have : K.card ≤ Fintype.card V := card_le_univ K
        push_cast [this]; ring
      rw [hc]
      have : (K.card : ℝ) ≤ Fintype.card V := by exact_mod_cast (card_le_univ K)
      nlinarith [sq_nonneg (∑ a ∈ Kᶜ, x a), nsq_nonneg x,
        mul_le_mul_of_nonneg_left hq (by linarith : (0:ℝ) ≤ Fintype.card V - K.card)]
    rw [qf_Lh]
    have := cl_nonneg α; have := cl_le_one α
    nlinarith [nsq_nonneg x, mul_le_mul_of_nonneg_left h0 (by linarith : (0:ℝ) ≤ 1 - cl α),
      mul_le_mul_of_nonneg_left h1 (cl_nonneg α)]
  · rw [finrank_espan_lt hL _ hM.le]; simp only [Fin.val_mk]; omega

/-- Bai's Lemma 8, second lower bound: `λ_N(L_α) ≥ (1 - α) n`. -/
theorem eig_lo2 (hK : 0 < K.card) (hM : K.card < Fintype.card V) (α : ℝ) :
    (1 - cl α) * Fintype.card V ≤ (Lh_herm G K α).eigenvalues₀ ⟨K.card - 1, by omega⟩ := by
  classical
  obtain ⟨j0, hj0⟩ : ∃ j0, j0 ∉ K := by
    by_contra h; push Not at h
    have : univ ⊆ K := fun a _ => h a
    have := card_le_card this; rw [card_univ] at this; omega
  let φ : (V → ℝ) →ₗ[ℝ] ({j // j ∉ K ∧ j ≠ j0} → ℝ) :=
    LinearMap.pi (fun j : {j // j ∉ K ∧ j ≠ j0} =>
      ((LinearMap.proj j.val : (V → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j0))
  have hφ : ∀ x, φ x = fun j => x j.val - x j0 := fun x => by
    ext j; simp [φ]
  have hcard : Fintype.card {j // j ∉ K ∧ j ≠ j0} + 1 = Kᶜ.card := by
    rw [Fintype.card_subtype]
    have : univ.filter (fun j => j ∉ K ∧ j ≠ j0) = Kᶜ.erase j0 := by
      ext j; simp [and_comm]
    rw [this, card_erase_of_mem (by simpa using hj0)]
    have : 0 < Kᶜ.card := card_pos.mpr ⟨j0, by simpa using hj0⟩
    omega
  have hkerφ : Fintype.card V - Fintype.card {j // j ∉ K ∧ j ≠ j0} ≤
      finrank ℝ (LinearMap.ker φ) := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    have h1 : finrank ℝ (LinearMap.range φ) ≤ Fintype.card {j // j ∉ K ∧ j ≠ j0} := by
      have := Submodule.finrank_le (LinearMap.range φ)
      simpa [Module.finrank_fintype_fun_eq_card] using this
    rw [Module.finrank_fintype_fun_eq_card] at h
    omega
  set A := LinearMap.ker φ
  set B := LinearMap.ker (sumL (V := V))
  apply le_eig_of_subspace (Lh_herm G K α) ⟨K.card - 1, by omega⟩ (A ⊓ B)
  · intro x hx
    have hxA := (Submodule.mem_inf.mp hx).1
    have hxB := (Submodule.mem_inf.mp hx).2
    rw [LinearMap.mem_ker, hφ] at hxA
    rw [LinearMap.mem_ker, sumL_apply] at hxB
    have hc : ∀ j, j ∉ K → x j = x j0 := by
      intro j hj
      by_cases hjj : j = j0
      · rw [hjj]
      · have := congrFun hxA ⟨j, hj, hjj⟩
        simp only [Pi.zero_apply] at this; linarith
    have e1 : ∑ a ∈ Kᶜ, x a * x a = Kᶜ.card * (x j0 * x j0) := by
      rw [← nsmul_eq_mul, ← sum_const]
      exact sum_congr rfl (fun a ha => by rw [hc a (by simpa using ha)])
    have e2 : ∑ a ∈ Kᶜ, x a = Kᶜ.card * x j0 := by
      rw [← nsmul_eq_mul, ← sum_const]
      exact sum_congr rfl (fun a ha => by rw [hc a (by simpa using ha)])
    have h0 : qf ((Gc K).lapMatrix ℝ) x = Fintype.card V * nsq x := by
      rw [qf_Gc, hxB, e1, e2]; ring
    rw [qf_Lh, h0]
    have := cl_nonneg α; have := cl_le_one α
    nlinarith [mul_nonneg (cl_nonneg α) (lap_qform_nonneg G x), nsq_nonneg x]
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq A B
    have h2 : finrank ℝ ↥(A ⊔ B) ≤ Fintype.card V := by
      have := Submodule.finrank_le (A ⊔ B)
      rwa [Module.finrank_fintype_fun_eq_card] at this
    have h4 : Fintype.card V - 1 ≤ finrank ℝ B := finrank_ker_sumL (V := V)
    have h5 : Kᶜ.card = Fintype.card V - K.card := card_compl K
    show K.card - 1 + 1 ≤ _
    omega

/-- Elementary arithmetic behind the uniform gap. -/
lemma gap_arith (n N c1 c2 t lo up : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc : 0 < c1 + c2)
    (hN0 : 0 ≤ N) (hNn : N < n) (ht0 : 0 ≤ t)
    (hlo1 : N + t * c1 ≤ lo) (hlo2 : (1 - t) * n ≤ lo) (hup : up = N - t * c2) :
    (n - N) * (c1 + c2) / (c1 + c2 + n) ≤ lo - N + (N - up) := by
  have hpos : 0 < c1 + c2 + n := by linarith
  rw [div_le_iff₀ hpos, hup]
  have htc : 0 ≤ t * c2 := mul_nonneg ht0 hc2
  by_cases h : n - N ≤ t * (c1 + c2 + n)
  · have k1 : t * (c1 + c2) ≤ lo - N + (N - (N - t * c2)) := by linarith
    have k2 : (n - N) * (c1 + c2) ≤ t * (c1 + c2) * (c1 + c2 + n) := by
      nlinarith [mul_le_mul_of_nonneg_right h hc.le]
    nlinarith [mul_le_mul_of_nonneg_right k1 hpos.le]
  · push Not at h
    have k1 : (n - N) - t * n ≤ lo - N + (N - (N - t * c2)) := by nlinarith
    have k2 : (n - N) * (c1 + c2) ≤ ((n - N) - t * n) * (c1 + c2 + n) := by
      nlinarith [mul_le_mul_of_nonneg_left h.le (by linarith : (0:ℝ) ≤ n)]
    nlinarith [mul_le_mul_of_nonneg_right k1 hpos.le]

/-- **Uniform gap**: for any two parameters, one of the two cross gaps is at least `g₀`. -/
theorem eig_gap (hG : IsSplit G K) (δ : ℝ) (hδ : ∀ v ∉ K, (G.degree v : ℝ) ≤ δ)
    (hδN : δ ≤ K.card) (hK : 0 < K.card) (hM : K.card < Fintype.card V)
    (hlam : (K.card : ℝ) ≤ (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨K.card - 1, by omega⟩)
    (hstr : (K.card : ℝ) < (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨K.card - 1, by omega⟩ ∨
      δ < K.card) (α β : ℝ) :
    let c1 := (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨K.card - 1, by omega⟩ - K.card
    let c2 := (K.card : ℝ) - δ
    let g0 := (Fintype.card V - K.card) * (c1 + c2) / (c1 + c2 + Fintype.card V)
    g0 ≤ (Lh_herm G K β).eigenvalues₀ ⟨K.card - 1, by omega⟩ -
        (Lh_herm G K α).eigenvalues₀ ⟨K.card, hM⟩ ∨
      g0 ≤ (Lh_herm G K α).eigenvalues₀ ⟨K.card - 1, by omega⟩ -
        (Lh_herm G K β).eigenvalues₀ ⟨K.card, hM⟩ := by
  intro c1 c2 g0
  have hc1 : 0 ≤ c1 := by simp only [c1]; linarith
  have hc2 : 0 ≤ c2 := by simp only [c2]; linarith
  have hc : 0 < c1 + c2 := by
    rcases hstr with h | h
    · simp only [c1, c2]; linarith
    · simp only [c1, c2]; linarith
  have hNn : (K.card : ℝ) < Fintype.card V := by exact_mod_cast hM
  have ha := gap_arith (Fintype.card V) K.card c1 c2 (cl α)
    ((Lh_herm G K α).eigenvalues₀ ⟨K.card - 1, by omega⟩) (K.card - cl α * c2) hc1 hc2 hc (Nat.cast_nonneg _) hNn
    (cl_nonneg α) (eig_lo1 G K hK hM hlam α) (eig_lo2 G K hK hM α) rfl
  have hb := gap_arith (Fintype.card V) K.card c1 c2 (cl β)
    ((Lh_herm G K β).eigenvalues₀ ⟨K.card - 1, by omega⟩) (K.card - cl β * c2) hc1 hc2 hc (Nat.cast_nonneg _) hNn
    (cl_nonneg β) (eig_lo1 G K hK hM hlam β) (eig_lo2 G K hK hM β) rfl
  have ua := eig_up G K hG δ hδ hM α
  have ub := eig_up G K hG δ hδ hM β
  by_contra hcon
  push Not at hcon
  simp only [c2] at ha hb
  linarith [hcon.1, hcon.2]

end Gap

end Brouwer.Stage2

namespace Brouwer.Stage2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Hypotheses of Bai's Lemma 6, bundled. -/
structure Hyp (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (δ : ℝ) : Prop where
  split : IsSplit G K
  deg : ∀ v ∉ K, (G.degree v : ℝ) ≤ δ
  δN : δ ≤ K.card
  pos : 0 < K.card
  lt : K.card < Fintype.card V
  lam : (K.card : ℝ) ≤ (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨K.card - 1, by omega⟩
  str : (K.card : ℝ) < (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨K.card - 1, by omega⟩ ∨
    δ < K.card

lemma frob_nonneg (C : Matrix V V ℝ) : 0 ≤ frob C :=
  sum_nonneg (fun a _ => sum_nonneg (fun b _ => sq_nonneg _))

lemma frob_neg_sub (A B : Matrix V V ℝ) : frob (A - B) = frob (B - A) := by
  unfold frob
  refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
  simp only [Matrix.sub_apply]; ring

lemma frob_smul (s : ℝ) (C : Matrix V V ℝ) : frob (s • C) = s ^ 2 * frob C := by
  unfold frob
  rw [mul_sum]
  refine sum_congr rfl (fun a _ => ?_)
  rw [mul_sum]
  refine sum_congr rfl (fun b _ => ?_)
  simp only [Matrix.smul_apply, smul_eq_mul]; ring

lemma entry_sq_le_frob (C : Matrix V V ℝ) (a b : V) : C a b ^ 2 ≤ frob C := by
  unfold frob
  calc C a b ^ 2 ≤ ∑ b', C a b' ^ 2 :=
        single_le_sum (f := fun b' => C a b' ^ 2) (fun _ _ => sq_nonneg _) (mem_univ b)
    _ ≤ ∑ a', ∑ b', C a' b' ^ 2 :=
        single_le_sum (f := fun a' => ∑ b', C a' b' ^ 2)
          (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _)) (mem_univ a)

section Cont

variable {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V} {δ : ℝ}

/-- The top-`N` spectral projection along the homotopy. -/
noncomputable def Ph (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (α : ℝ) :
    Matrix V V ℝ := topP (Lh_herm G K α) K.card

/-- The gap constant. -/
noncomputable def g0 (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (δ : ℝ)
    (h : Hyp G K δ) : ℝ :=
  let c1 := (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨K.card - 1, by have := h.lt; omega⟩ - K.card
  let c2 := (K.card : ℝ) - δ
  (Fintype.card V - K.card) * (c1 + c2) / (c1 + c2 + Fintype.card V)

lemma g0_pos (h : Hyp G K δ) : 0 < g0 G K δ h := by
  unfold g0
  have hNn : (K.card : ℝ) < Fintype.card V := by exact_mod_cast h.lt
  have hc1 := h.lam
  have hc2 := h.δN
  have hc : 0 < (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨K.card - 1, by have := h.lt; omega⟩
      - K.card + (K.card - δ) := by
    rcases h.str with h' | h' <;> linarith
  apply div_pos (mul_pos (by linarith) hc)
  have : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  linarith

lemma gap_or (h : Hyp G K δ) (α β : ℝ) :
    g0 G K δ h ≤ (Lh_herm G K β).eigenvalues₀ ⟨K.card - 1, by have := h.lt; omega⟩ -
        (Lh_herm G K α).eigenvalues₀ ⟨K.card, h.lt⟩ ∨
      g0 G K δ h ≤ (Lh_herm G K α).eigenvalues₀ ⟨K.card - 1, by have := h.lt; omega⟩ -
        (Lh_herm G K β).eigenvalues₀ ⟨K.card, h.lt⟩ :=
  eig_gap G K h.split δ h.deg h.δN h.pos h.lt h.lam h.str α β

/-- Lipschitz bound for the spectral projection. -/
lemma frob_Ph_sub (h : Hyp G K δ) (α β : ℝ) :
    frob (Ph G K α - Ph G K β) * g0 G K δ h ^ 2 ≤
      2 * ((cl α - cl β) ^ 2 * frob (G.lapMatrix ℝ - (Gc K).lapMatrix ℝ)) := by
  have hg := g0_pos h
  rcases gap_or h α β with hab | hab
  · have := davis_kahan (Lh_herm G K α) (Lh_herm G K β) K.card h.lt h.pos (g0 G K δ h) hg
      (by linarith)
    unfold Ph
    rw [Lh_sub, frob_smul] at this
    calc _ ≤ 2 * ((cl β - cl α) ^ 2 * frob (G.lapMatrix ℝ - (Gc K).lapMatrix ℝ)) := this
      _ = _ := by ring
  · have := davis_kahan (Lh_herm G K β) (Lh_herm G K α) K.card h.lt h.pos (g0 G K δ h) hg
      (by linarith)
    unfold Ph
    rw [Lh_sub, frob_smul, frob_neg_sub] at this
    exact this

lemma Ph_entry_lip (h : Hyp G K δ) (a b : V) (α β : ℝ) :
    |Ph G K α a b - Ph G K β a b| ≤
      Real.sqrt (2 * frob (G.lapMatrix ℝ - (Gc K).lapMatrix ℝ) / g0 G K δ h ^ 2) * |α - β| := by
  have hg := g0_pos h
  have hF := frob_nonneg (G.lapMatrix ℝ - (Gc K).lapMatrix ℝ)
  have h1 := entry_sq_le_frob (Ph G K α - Ph G K β) a b
  have h2 := frob_Ph_sub h α β
  have h3 := cl_lip α β
  have hsq : (Ph G K α a b - Ph G K β a b) ^ 2 ≤
      (2 * frob (G.lapMatrix ℝ - (Gc K).lapMatrix ℝ) / g0 G K δ h ^ 2) * (α - β) ^ 2 := by
    rw [Matrix.sub_apply] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h4 : (cl α - cl β) ^ 2 ≤ (α - β) ^ 2 := by
      rw [← sq_abs, ← sq_abs (α - β)]
      exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg (g0 G K δ h)),
      mul_le_mul_of_nonneg_left h4 hF]
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs (α - β), ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hsq

lemma Ph_entry_cont (h : Hyp G K δ) (a b : V) : Continuous (fun α => Ph G K α a b) := by
  set C := Real.sqrt (2 * frob (G.lapMatrix ℝ - (Gc K).lapMatrix ℝ) / g0 G K δ h ^ 2)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  apply LipschitzWith.continuous (K := Real.toNNReal C)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hC]
  exact Ph_entry_lip h a b x y

end Cont

end Brouwer.Stage2

namespace Brouwer.Stage2

variable {V : Type*} [Fintype V] [DecidableEq V]

section TopP

variable {A : Matrix V V ℝ} (hA : A.IsHermitian) (N : ℕ)

lemma topP_idem (a b : V) : ∑ l, topP hA N a l * topP hA N l b = topP hA N a b := by
  rw [topP_apply hA N (fun l => topP hA N l b) a]
  have e : ∀ t, ip (sev hA t) (fun l => topP hA N l b) = if t.val < N then sev hA t b else 0 := by
    intro t
    rw [← topP_sev hA N t b]
    unfold ip
    exact sum_congr rfl (fun l _ => by simp only; rw [topP_symm hA N l b]; ring)
  simp_rw [e]
  unfold topP
  refine sum_congr rfl (fun t ht => ?_)
  simp only [mem_filter, mem_univ, true_and] at ht
  simp [ht, mul_comm]

lemma topP_comm (a b : V) : ∑ l, topP hA N a l * A l b = ∑ l, A a l * topP hA N l b := by
  have h1 : ∑ l, topP hA N a l * A l b =
      ∑ t ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < N),
        sev hA t a * (hA.eigenvalues₀ t * sev hA t b) := by
    unfold topP
    simp_rw [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl (fun t _ => ?_)
    rw [← sev_eig hA, mul_sum]
    exact sum_congr rfl (fun l _ => by rw [symm_of_herm hA l b]; ring)
  have h2 : ∑ l, A a l * topP hA N l b =
      ∑ t ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < N),
        sev hA t a * (hA.eigenvalues₀ t * sev hA t b) := by
    unfold topP
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl (fun t _ => ?_)
    have := sev_eig hA t a
    calc ∑ l, A a l * (sev hA t l * sev hA t b) = (∑ l, A a l * sev hA t l) * sev hA t b := by
          rw [sum_mul]; exact sum_congr rfl (fun l _ => by ring)
      _ = _ := by rw [this]; ring
  rw [h1, h2]

lemma topP_colsum (hrow : ∀ a, ∑ b, A a b = 0)
    (hne : ∀ t : Fin (Fintype.card V), t.val < N → hA.eigenvalues₀ t ≠ 0) (b : V) :
    ∑ a, topP hA N a b = 0 := by
  unfold topP
  rw [sum_comm]
  refine sum_eq_zero (fun t ht => ?_)
  simp only [mem_filter, mem_univ, true_and] at ht
  rw [← sum_mul, sev_sum_zero hA hrow t (hne t ht), zero_mul]

lemma mem_espan_of_fixed {x : V → ℝ} (hx : ∀ a, ∑ b, topP hA N a b * x b = x a) :
    x ∈ espan hA (fun t => t.val < N) := by
  have : x = ∑ t ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < N),
      ip (sev hA t) x • sev hA t := by
    ext a
    rw [← hx a, topP_apply]
    simp [Finset.sum_apply]
  rw [this]
  refine Submodule.sum_mem _ (fun t ht => Submodule.smul_mem _ _ ?_)
  simp only [mem_filter, mem_univ, true_and] at ht
  exact Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩

lemma fixed_of_mem_espan {x : V → ℝ} (hx : x ∈ espan hA (fun t => t.val < N)) (a : V) :
    ∑ b, topP hA N a b * x b = x a := by
  obtain ⟨c, hc, rfl⟩ := mem_espan hA _ hx
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun t _ => ?_)
  have := topP_sev hA N t a
  calc ∑ b, topP hA N a b * (c t * sev hA t b) = c t * ∑ b, topP hA N a b * sev hA t b := by
        rw [mul_sum]; exact sum_congr rfl (fun b _ => by ring)
    _ = c t * sev hA t a := by
        rw [this]; split_ifs with h
        · rfl
        · rw [hc t h]; simp

lemma ip_sev_of_P_zero {x : V → ℝ} (hx : ∀ a, ∑ b, topP hA N a b * x b = 0)
    (s : Fin (Fintype.card V)) (hs : s.val < N) : ip (sev hA s) x = 0 := by
  have h : ∑ a, (∑ b, topP hA N a b * x b) * sev hA s a = 0 := by simp [hx]
  simp_rw [topP_apply, sum_mul] at h
  rw [sum_comm] at h
  have e : ∀ t ∈ univ.filter (fun t : Fin (Fintype.card V) => t.val < N),
      ∑ a, ip (sev hA t) x * sev hA t a * sev hA s a =
        if t = s then ip (sev hA t) x else 0 := by
    intro t _
    have : ∑ a, ip (sev hA t) x * sev hA t a * sev hA s a =
        ip (sev hA t) x * ∑ a, sev hA t a * sev hA s a := by
      rw [mul_sum]; exact sum_congr rfl (fun a _ => by ring)
    rw [this, sev_ortho]; split_ifs <;> simp
  rw [sum_congr rfl e, sum_ite_eq'] at h
  simpa [hs] using h

end TopP

section Proj

variable {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V} {δ : ℝ}

lemma self_gap (h : Hyp G K δ) (α : ℝ) :
    g0 G K δ h ≤ (Lh_herm G K α).eigenvalues₀ ⟨K.card - 1, by have := h.lt; omega⟩ -
      (K.card - cl α * (K.card - δ)) := by
  have hNn : (K.card : ℝ) < Fintype.card V := by exact_mod_cast h.lt
  have hc : 0 < (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨K.card - 1, by have := h.lt; omega⟩
      - K.card + (K.card - δ) := by
    have := h.lam; have := h.δN
    rcases h.str with h' | h' <;> linarith
  have := gap_arith (Fintype.card V) K.card
    ((G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨K.card - 1, by have := h.lt; omega⟩ - K.card)
    (K.card - δ) (cl α) _ (K.card - cl α * (K.card - δ)) (by linarith [h.lam])
    (by linarith [h.δN]) hc (Nat.cast_nonneg _) hNn (cl_nonneg α)
    (eig_lo1 G K h.pos h.lt h.lam α) (eig_lo2 G K h.pos h.lt α) rfl
  unfold g0
  dsimp only
  linarith

lemma lamN_pos (h : Hyp G K δ) (α : ℝ) (t : Fin (Fintype.card V)) (ht : t.val < K.card) :
    0 < (Lh_herm G K α).eigenvalues₀ t := by
  have h1 := eig_lo1 G K h.pos h.lt h.lam α
  have h2 : (Lh_herm G K α).eigenvalues₀ ⟨K.card - 1, by have := h.lt; omega⟩ ≤
      (Lh_herm G K α).eigenvalues₀ t :=
    (Lh_herm G K α).eigenvalues₀_antitone (Fin.le_iff_val_le_val.mpr (by simp; omega))
  have h3 : (0:ℝ) < K.card := by exact_mod_cast h.pos
  have h4 := h.lam
  have h5 := mul_nonneg (cl_nonneg α) (by linarith : (0:ℝ) ≤
    (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨K.card - 1, by have := h.lt; omega⟩ - K.card)
  linarith

lemma qf_Lh_vanish (h : Hyp G K δ) (α : ℝ) {x : V → ℝ} (hz : ∀ i ∈ K, x i = 0) :
    qf (Lh G K α) x ≤ (K.card - cl α * (K.card - δ)) * nsq x := by
  have hs : ∑ a, x a = ∑ a ∈ Kᶜ, x a := by
    symm; exact sum_subset (subset_univ _) (fun a _ ha => hz a (by simpa using ha))
  have hq : ∑ a ∈ Kᶜ, x a * x a = nsq x := by
    unfold nsq
    exact sum_subset (subset_univ _) (fun a _ ha => by simp [hz a (by simpa using ha)])
  have h0 : qf ((Gc K).lapMatrix ℝ) x = K.card * nsq x := by
    rw [qf_Gc, hs, hq, card_compl]
    have : K.card ≤ Fintype.card V := card_le_univ K
    push_cast [this]; ring
  have h1 : qf (G.lapMatrix ℝ) x ≤ δ * nsq x := by
    rw [qf_lap_of_edge_zero G x]
    · unfold nsq
      rw [mul_sum]
      refine sum_le_sum (fun a _ => ?_)
      by_cases ha : a ∈ K
      · simp [hz a ha]
      · exact mul_le_mul_of_nonneg_right (h.deg a ha) (mul_self_nonneg _)
    · intro a b hab
      by_cases ha : a ∈ K
      · simp [hz a ha]
      · by_cases hb : b ∈ K
        · simp [hz b hb]
        · exact absurd hab (h.split.2 a ha b hb)
  rw [qf_Lh, h0]
  have := cl_nonneg α; have := cl_le_one α
  nlinarith [nsq_nonneg x]

lemma nsq_eq_zero {x : V → ℝ} (h : nsq x ≤ 0) : x = 0 := by
  by_contra hx
  have := nsq_pos hx
  linarith

/-- A vector in the top eigenspace that vanishes on the clique is zero. -/
lemma vanish_zero (h : Hyp G K δ) (α : ℝ) {x : V → ℝ}
    (hx : ∀ a, ∑ b, Ph G K α a b * x b = x a) (hz : ∀ i ∈ K, x i = 0) : x = 0 := by
  have hE := mem_espan_of_fixed (Lh_herm G K α) K.card hx
  have h1 := qf_ge_of_mem_espan (Lh_herm G K α) K.card h.pos h.lt.le hE
  have h2 := qf_Lh_vanish h α hz
  have h3 := self_gap h α
  have h4 := g0_pos h
  apply nsq_eq_zero
  nlinarith [nsq_nonneg x]

lemma espan_sup_top (h : Hyp G K δ) (α : ℝ) :
    espan (Lh_herm G K α) (fun t => t.val < K.card) ⊔ coordSub K = ⊤ := by
  set E := espan (Lh_herm G K α) (fun t => t.val < K.card)
  have hinf : E ⊓ coordSub K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    exact vanish_zero h α (fixed_of_mem_espan _ _ (Submodule.mem_inf.mp hx).1)
      (coordSub_zero (Submodule.mem_inf.mp hx).2)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq E (coordSub K)
  rw [hinf, finrank_bot, finrank_espan_lt _ _ h.lt.le, finrank_coordSub] at h1
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fintype_fun_eq_card]
  have := h.lt
  omega

/-- Extension by zero from the clique. -/
def extK (K : Finset V) (y : K → ℝ) : V → ℝ := fun a => if h : a ∈ K then y ⟨a, h⟩ else 0

lemma sum_mul_extK (K : Finset V) (f : V → ℝ) (y : K → ℝ) :
    ∑ b, f b * extK K y b = ∑ i : K, f i * y i := by
  rw [← sum_subset (subset_univ K) (fun b _ hb => by simp [extK, hb])]
  rw [← Finset.sum_coe_sort K]
  refine sum_congr rfl (fun i _ => ?_)
  simp [extK, i.2]

/-- The clique block `P₁₁` of the projection. -/
noncomputable def Qm (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (α : ℝ) :
    Matrix K K ℝ := fun i i' => Ph G K α i i'

lemma Qm_det_ne (h : Hyp G K δ) (α : ℝ) : (Qm G K α).det ≠ 0 := by
  intro hd
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  set x := extK K y
  set P := Ph G K α
  set Px : V → ℝ := fun a => ∑ b, P a b * x b
  have hPxK : ∀ k ∈ K, Px k = 0 := by
    intro k hk
    have := congrFun hy ⟨k, hk⟩
    simp only [mulVec, dotProduct, Qm, Pi.zero_apply] at this
    simp only [Px, x]
    rw [sum_mul_extK]; exact this
  have hPxfix : ∀ a, ∑ b, P a b * Px b = Px a := by
    intro a
    simp only [Px]
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl (fun c _ => ?_)
    rw [show ∑ l, P a l * (P l c * x c) = (∑ l, P a l * P l c) * x c by
      rw [sum_mul]; exact sum_congr rfl (fun _ _ => by ring)]
    simp only [P, Ph]; rw [topP_idem]
  have hPx0 := vanish_zero h α hPxfix hPxK
  have hip : ∀ s : Fin (Fintype.card V), s.val < K.card → ip (sev (Lh_herm G K α) s) x = 0 :=
    ip_sev_of_P_zero _ _ (fun a => congrFun hPx0 a)
  have horth : ∀ z ∈ espan (Lh_herm G K α) (fun t => t.val < K.card) ⊔ coordSub K,
      ip x z = 0 := by
    intro z hz
    obtain ⟨e, he, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
    have h1 : ip x e = 0 := by
      obtain ⟨c, hc, rfl⟩ := mem_espan _ _ he
      unfold ip
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_eq_zero (fun t _ => ?_)
      by_cases ht : t.val < K.card
      · have := hip t ht
        unfold ip at this
        calc ∑ a, x a * (c t * sev (Lh_herm G K α) t a) =
            c t * ∑ a, sev (Lh_herm G K α) t a * x a := by
              rw [mul_sum]; exact sum_congr rfl (fun a _ => by ring)
          _ = 0 := by rw [this, mul_zero]
      · simp [hc t ht]
    have h2 : ip x w = 0 := by
      have hwz := coordSub_zero hw
      unfold ip
      refine sum_eq_zero (fun a _ => ?_)
      by_cases ha : a ∈ K
      · simp [hwz a ha]
      · simp [x, extK, ha]
    unfold ip at h1 h2 ⊢
    simp only [Pi.add_apply, mul_add, sum_add_distrib, h1, h2, add_zero]
  rw [espan_sup_top h α] at horth
  have hx0 : x = 0 := by
    apply nsq_eq_zero
    have := horth x Submodule.mem_top
    unfold ip at this; unfold nsq; linarith
  apply hy0
  ext i
  have := congrFun hx0 i
  simpa [x, extK, i.2] using this

end Proj

end Brouwer.Stage2

namespace Brouwer.Stage2

variable {V : Type*} [Fintype V] [DecidableEq V]

section W

variable {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V} {δ : ℝ}

/-- Columns of `[I; V]`: the vector `w_i` in the top eigenspace with `w_i|_K = e_i`. -/
noncomputable def wv (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (α : ℝ) (i : K) :
    V → ℝ := fun a => ∑ i' : K, Ph G K α a i' * (Qm G K α)⁻¹ i' i

lemma wv_K (h : Hyp G K δ) (α : ℝ) (i k : K) : wv G K α i k = if k = i then 1 else 0 := by
  have hu : IsUnit (Qm G K α).det := isUnit_iff_ne_zero.mpr (Qm_det_ne h α)
  have := congrFun (congrFun (Matrix.mul_nonsing_inv _ hu) k) i
  simp only [Matrix.mul_apply, Matrix.one_apply, Qm] at this
  exact this

lemma wv_K' (h : Hyp G K δ) (α : ℝ) (i : K) (c : V) (hc : c ∈ K) :
    wv G K α i c = if c = (i : V) then 1 else 0 := by
  have := wv_K h α i ⟨c, hc⟩
  simp only at this
  rw [this]
  simp [Subtype.ext_iff]

lemma wv_fix (α : ℝ) (i : K) (a : V) :
    ∑ b, Ph G K α a b * wv G K α i b = wv G K α i a := by
  unfold wv
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun i' _ => ?_)
  rw [show ∑ b, Ph G K α a b * (Ph G K α b i' * (Qm G K α)⁻¹ i' i) =
      (∑ b, Ph G K α a b * Ph G K α b i') * (Qm G K α)⁻¹ i' i by
    rw [sum_mul]; exact sum_congr rfl (fun _ _ => by ring)]
  unfold Ph; rw [topP_idem]

lemma wv_sum (h : Hyp G K δ) (α : ℝ) (i : K) : ∑ a, wv G K α i a = 0 := by
  unfold wv
  rw [sum_comm]
  refine sum_eq_zero (fun i' _ => ?_)
  rw [← sum_mul]
  have : ∑ a, Ph G K α a i' = 0 :=
    topP_colsum _ _ (Lh_rowsum G K α) (fun t ht => (lamN_pos h α t ht).ne') _
  rw [this, zero_mul]

/-- Every vector of the top eigenspace is `Σ_k x_k w_k`. -/
lemma decomp (h : Hyp G K δ) (α : ℝ) {x : V → ℝ}
    (hx : ∀ a, ∑ b, Ph G K α a b * x b = x a) (a : V) :
    x a = ∑ k : K, x k * wv G K α k a := by
  set y : V → ℝ := fun a => x a - ∑ k : K, x k * wv G K α k a
  have hy : ∀ a, ∑ b, Ph G K α a b * y b = y a := by
    intro a
    simp only [y, mul_sub, sum_sub_distrib, hx a]
    congr 1
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl (fun k _ => ?_)
    rw [← wv_fix α k a, mul_sum]
    exact sum_congr rfl (fun b _ => by ring)
  have hz : ∀ c ∈ K, y c = 0 := by
    intro c hc
    simp only [y]
    simp_rw [wv_K' h α _ c hc]
    have : ∑ k : K, x k * (if c = (k : V) then 1 else 0) = x c := by
      rw [Fintype.sum_eq_single ⟨c, hc⟩ (fun k hk => by
        rw [if_neg (fun h' => hk (Subtype.ext h'.symm))]; ring)]
      simp
    rw [this, sub_self]
  have := congrFun (vanish_zero h α hy hz) a
  simp only [y, Pi.zero_apply] at this
  linarith

/-- `L_α w_i` again lies in the top eigenspace. -/
lemma Lw_fix (α : ℝ) (i : K) (a : V) :
    ∑ b, Ph G K α a b * (∑ c, Lh G K α b c * wv G K α i c) =
      ∑ c, Lh G K α a c * wv G K α i c := by
  simp_rw [mul_sum]
  rw [sum_comm]
  have e : ∀ c, ∑ b, Ph G K α a b * (Lh G K α b c * wv G K α i c) =
      (∑ b, Ph G K α a b * Lh G K α b c) * wv G K α i c := by
    intro c; rw [sum_mul]; exact sum_congr rfl (fun _ _ => by ring)
  simp_rw [e]
  unfold Ph
  simp_rw [topP_comm (Lh_herm G K α) K.card a]
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl (fun l _ => ?_)
  have := wv_fix (G := G) (K := K) α i l
  unfold Ph at this
  rw [← this, mul_sum]
  exact sum_congr rfl (fun b _ => by ring)

lemma Qm_cont (h : Hyp G K δ) : Continuous (fun α => Qm G K α) :=
  continuous_matrix (fun i i' => Ph_entry_cont h i i')

lemma Qinv_cont (h : Hyp G K δ) (i' i : K) : Continuous (fun α => (Qm G K α)⁻¹ i' i) := by
  have e : ∀ α, (Qm G K α)⁻¹ i' i = ((Qm G K α).det)⁻¹ * (Qm G K α).adjugate i' i := by
    intro α; rw [Matrix.inv_def, Ring.inverse_eq_inv]; rfl
  simp_rw [e]
  apply Continuous.mul
  · exact ((Qm_cont h).matrix_det).inv₀ (fun α => Qm_det_ne h α)
  · exact ((Qm_cont h).matrix_adjugate).matrix_elem i' i

lemma wv_cont (h : Hyp G K δ) (i : K) (a : V) : Continuous (fun α => wv G K α i a) := by
  unfold wv
  exact continuous_finsetSum _ (fun i' _ => (Ph_entry_cont h a i').mul (Qinv_cont h i' i))

end W

end Brouwer.Stage2

namespace Brouwer.Stage2

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma lap_row (Gr : SimpleGraph V) [DecidableRel Gr.Adj] (x : V → ℝ) (a : V) :
    ∑ b, Gr.lapMatrix ℝ a b * x b = ∑ b, if Gr.Adj a b then x a - x b else 0 := by
  have := Gr.lapMatrix_mulVec_apply' (R := ℝ) a x
  simp only [mulVec, dotProduct] at this
  rw [this, SimpleGraph.neighborFinset_eq_filter, sum_filter]

lemma sum_ite_K (K : Finset V) (r : ℝ) : ∑ b, (if b ∈ K then r else 0) = K.card * r := by
  rw [← sum_filter]; simp

section Riccati

variable {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V} {δ : ℝ}

/-- Real-valued degree. -/
noncomputable def dh (G : SimpleGraph V) [DecidableRel G.Adj] (b : V) : ℝ :=
  ∑ c, if G.Adj b c then (1 : ℝ) else 0

/-- The non-adjacency sum `T_k = Σ_{b ∉ K, b ≁ k} (w_i)_b`. -/
noncomputable def Tk (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (α : ℝ)
    (i : K) (k : V) : ℝ :=
  ∑ b, if b ∈ K then 0 else if G.Adj k b then 0 else wv G K α i b

lemma Lh_row (α : ℝ) (x : V → ℝ) (a : V) :
    ∑ b, Lh G K α a b * x b = (1 - cl α) * ∑ b, (Gc K).lapMatrix ℝ a b * x b +
      cl α * ∑ b, G.lapMatrix ℝ a b * x b := by
  simp only [Lh, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl (fun b _ => by ring)

/-- **Bai's formula (1)** (Lemma 9), in the form used for the sign argument. -/
theorem riccati (h : Hyp G K δ) (α : ℝ) (i : K) (j : V) (hj : j ∉ K) :
    wv G K α i j * ((1 - cl α) * (Fintype.card V - K.card) + cl α * (dh G i + 1 - dh G j)) =
      -(1 - cl α) - cl α * (if G.Adj j i then 1 else 0) -
        cl α * ∑ k : K, wv G K α k j * Tk G K α i k := by
  set c := cl α with hc_def
  set w := wv G K α i with hw_def
  set y : V → ℝ := fun a => ∑ b, Lh G K α a b * w b
  have hdec := decomp h α (x := y) (fun a => Lw_fix α i a) j
  have hwK : ∀ b ∈ K, w b = if b = (i : V) then 1 else 0 := wv_K' h α i
  have hsum : ∑ a, w a = 0 := wv_sum h α i
  have hK1 : ∑ b, (if b ∈ K then w b else 0) = 1 := by
    have : ∀ b, (if b ∈ K then w b else 0) = if b = (i : V) then 1 else 0 := by
      intro b
      by_cases hb : b ∈ K
      · rw [if_pos hb, hwK b hb]
      · rw [if_neg hb, if_neg (fun e => hb (by rw [e]; exact i.2))]
    simp_rw [this]; simp
  have hKc : ∑ b, (if b ∈ K then 0 else w b) = -1 := by
    have : ∀ b, (if b ∈ K then 0 else w b) = w b - (if b ∈ K then w b else 0) := by
      intro b; split_ifs <;> ring
    simp_rw [this]; rw [sum_sub_distrib, hsum, hK1]; ring
  -- the `j`-th row
  have hyj : y j = (1 - c) * (K.card * w j - 1) +
      c * (dh G j * w j - (if G.Adj j i then 1 else 0)) := by
    simp only [y]
    rw [Lh_row, lap_row, lap_row]
    have e0 : ∀ b, (if (Gc K).Adj j b then w j - w b else 0) =
        (if b ∈ K then w j else 0) - (if b ∈ K then w b else 0) := by
      intro b
      by_cases hb : b ∈ K
      · have : (Gc K).Adj j b := ⟨fun e => hj (e ▸ hb), Or.inr hb⟩
        simp [this, hb]
      · have : ¬ (Gc K).Adj j b := fun hh => by
          rcases hh.2 with h' | h'
          · exact hj h'
          · exact hb h'
        simp [this, hb]
    have e1 : ∀ b, (if G.Adj j b then w j - w b else 0) =
        (if G.Adj j b then 1 else 0) * w j -
          (if b = (i : V) then (if G.Adj j i then 1 else 0) else 0) := by
      intro b
      by_cases hab : G.Adj j b
      · have hb : b ∈ K := by
          by_contra hb; exact h.split.2 j hj b hb hab
        rw [if_pos hab, hwK b hb]
        by_cases hbi : b = (i : V)
        · subst hbi; simp [hab]
        · simp [hbi, hab]
      · rw [if_neg hab]
        by_cases hbi : b = (i : V)
        · subst hbi; simp [hab]
        · simp [hbi, hab]
    simp_rw [e0, e1]
    rw [sum_sub_distrib, sum_ite_K, hK1, sum_sub_distrib, ← sum_mul, sum_ite_eq']
    simp only [mem_univ, if_true]
    unfold dh; ring
  -- the `k`-th rows
  have hyk : ∀ k : K, y k = (if k = i then (1 - c) * Fintype.card V + c * dh G i + c else 0) +
      c * Tk G K α i k := by
    intro k
    simp only [y]
    rw [Lh_row, lap_row, lap_row]
    have hwk : w k = if k = i then 1 else 0 := wv_K h α i k
    have hwK' : ∀ b ∈ K, w b = if b = (i : V) then 1 else 0 := hwK
    have e0 : ∀ b, (if (Gc K).Adj k b then w k - w b else 0) = w k - w b := by
      intro b
      by_cases hb : b = (k : V)
      · subst hb; simp
      · have : (Gc K).Adj k b := ⟨fun e => hb e.symm, Or.inl k.2⟩
        simp [this]
    have e1 : ∀ b, (if G.Adj k b then w k - w b else 0) =
        (if G.Adj k b then 1 else 0) * w k -
          ((if b = (i : V) then (if (k : V) = (i : V) then 0 else 1) else 0) +
            ((if b ∈ K then 0 else w b) - (if b ∈ K then 0 else if G.Adj k b then 0 else w b))) := by
      intro b
      by_cases hb : b ∈ K
      · have hadj : G.Adj k b ↔ b ≠ (k : V) := by
          constructor
          · intro hh e; subst e; exact G.loopless.irrefl _ hh
          · intro hne; exact h.split.1 k k.2 b hb (fun e => hne e.symm)
        rw [hwK b hb]
        by_cases hbi : b = (i : V)
        · subst hbi
          by_cases hki : (k : V) = (i : V)
          · have : ¬ G.Adj k i := fun hh => (hadj.mp hh) hki.symm
            simp [hb, this, hki]
          · have : G.Adj k i := hadj.mpr (fun e => hki e.symm)
            simp [hb, this, hki]
        · by_cases hadjb : G.Adj k b
          · simp [hb, hadjb, hbi]
          · simp [hb, hadjb, hbi]
      · by_cases hbi : b = (i : V)
        · exact absurd (hbi ▸ i.2) hb
        · by_cases hadjb : G.Adj k b
          · simp [hb, hadjb, hbi]
          · simp [hb, hadjb, hbi]
    simp_rw [e0, e1]
    rw [sum_sub_distrib, sum_const, card_univ, hsum, sum_sub_distrib, ← sum_mul, sum_add_distrib,
      sum_ite_eq', sum_sub_distrib, hKc]
    simp only [mem_univ, if_true, nsmul_eq_mul]
    unfold Tk dh
    rw [hwk]
    by_cases hki : k = i
    · subst hki; simp
      rw [hc_def, hw_def]; ring
    · have : (k : V) ≠ (i : V) := fun e => hki (Subtype.ext e)
      simp [hki, this]
      rw [hc_def, hw_def]
  rw [hyj, sum_congr rfl (fun k _ => by rw [hyk k])] at hdec
  simp only [add_mul, sum_add_distrib, ite_mul, zero_mul] at hdec
  rw [Fintype.sum_ite_eq'] at hdec
  have e3 : ∑ k : K, c * Tk G K α i k * wv G K α k j =
      c * ∑ k : K, wv G K α k j * Tk G K α i k := by
    rw [mul_sum]; exact sum_congr rfl (fun _ _ => by ring)
  rw [e3] at hdec
  simp only [w] at hdec ⊢
  linarith

end Riccati

end Brouwer.Stage2

namespace Brouwer.Stage2

variable {V : Type*} [Fintype V] [DecidableEq V]

section Sign

variable {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V} {δ : ℝ}

lemma dh_out_le (h : Hyp G K δ) (j : V) (hj : j ∉ K) : dh G j ≤ K.card := by
  unfold dh
  rw [show (K.card : ℝ) = K.card * 1 by ring, ← sum_ite_K K 1]
  refine sum_le_sum (fun c _ => ?_)
  by_cases hadj : G.Adj j c
  · have hc : c ∈ K := by by_contra hc; exact h.split.2 j hj c hc hadj
    simp [hadj, hc]
  · simp only [hadj, if_false]; split_ifs <;> norm_num

lemma dh_in_ge (h : Hyp G K δ) (i : K) : (K.card : ℝ) - 1 ≤ dh G i := by
  unfold dh
  have e : ∀ c, (if c ∈ K then (1:ℝ) else 0) - (if c = (i : V) then 1 else 0) ≤
      if G.Adj i c then 1 else 0 := by
    intro c
    by_cases hci : c = (i : V)
    · subst hci; simp [i.2]
    · by_cases hc : c ∈ K
      · have : G.Adj i c := h.split.1 i i.2 c hc (fun e => hci e.symm)
        simp [hc, hci, this]
      · simp only [hc, hci, if_false]; split_ifs <;> norm_num
  have := sum_le_sum (fun c (_ : c ∈ univ) => e c)
  rw [sum_sub_distrib, sum_ite_K, sum_ite_eq'] at this
  simpa using this

lemma kappa_pos (h : Hyp G K δ) (α : ℝ) (hα : cl α < 1) (i : K) (j : V) (hj : j ∉ K) :
    0 < (1 - cl α) * (Fintype.card V - K.card) + cl α * (dh G i + 1 - dh G j) := by
  have h1 := dh_out_le h j hj
  have h2 := dh_in_ge h i
  have h3 : (K.card : ℝ) < Fintype.card V := by exact_mod_cast h.lt
  have h4 := cl_nonneg α
  have := mul_pos (by linarith : (0:ℝ) < 1 - cl α) (by linarith : (0:ℝ) < Fintype.card V - K.card)
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ dh G i + 1 - dh G j)]

/-- Bai's Lemma 11, openness step: if `V^α ≤ 0` and `α < 1` then `V^α < 0`. -/
theorem neg_of_nonpos (h : Hyp G K δ) (α : ℝ) (hα : cl α < 1)
    (hsgn : ∀ k : K, ∀ b, b ∉ K → wv G K α k b ≤ 0) (i : K) (j : V) (hj : j ∉ K) :
    wv G K α i j < 0 := by
  have hr := riccati h α i j hj
  have hk := kappa_pos h α hα i j hj
  have hT : 0 ≤ ∑ k : K, wv G K α k j * Tk G K α i k := by
    refine sum_nonneg (fun k _ => ?_)
    apply mul_nonneg_of_nonpos_of_nonpos (hsgn k j hj)
    unfold Tk
    refine sum_nonpos (fun b _ => ?_)
    split_ifs with hb
    · exact le_refl _
    · exact le_refl _
    · exact hsgn i b hb
  have hA : (0:ℝ) ≤ if G.Adj j i then 1 else 0 := by split_ifs <;> norm_num
  have hc := cl_nonneg α
  have hrhs : -(1 - cl α) - cl α * (if G.Adj j i then 1 else 0) -
      cl α * ∑ k : K, wv G K α k j * Tk G K α i k < 0 := by
    nlinarith [mul_nonneg hc hA, mul_nonneg hc hT]
  by_contra hcon
  push Not at hcon
  have := mul_nonneg hcon hk.le
  linarith

/-- Bai's Lemma 11, base case: `V^0 = -J/M`, in particular `< 0`. -/
theorem neg_at_zero (h : Hyp G K δ) (i : K) (j : V) (hj : j ∉ K) : wv G K 0 i j < 0 := by
  have hr := riccati h 0 i j hj
  have h0 : cl 0 = 0 := cl_of_mem le_rfl zero_le_one
  rw [h0] at hr
  have h3 : (K.card : ℝ) < Fintype.card V := by exact_mod_cast h.lt
  simp only [sub_zero, one_mul, zero_mul, add_zero, zero_sub] at hr
  by_contra hcon
  push Not at hcon
  have := mul_nonneg hcon (by linarith : (0:ℝ) ≤ Fintype.card V - K.card)
  linarith

/-- **Bai's Lemma 11**: along the whole homotopy, `V^α ≤ 0`; in particular at `α = 1`. -/
theorem nonpos_at_one (h : Hyp G K δ) (k : K) (b : V) (hb : b ∉ K) : wv G K 1 k b ≤ 0 := by
  set Γ : Set ℝ := {α | ∀ k : K, ∀ b : {b // b ∉ K}, wv G K α k b ≤ 0} with hΓ
  have hclosed : IsClosed Γ := by
    have : Γ = ⋂ k : K, ⋂ b : {b // b ∉ K}, {α | wv G K α k b ≤ 0} := by
      ext α; simp [hΓ]
    rw [this]
    exact isClosed_iInter (fun k => isClosed_iInter (fun b =>
      isClosed_le (wv_cont h k b) continuous_const))
  have h0 : (0:ℝ) ∈ Γ := fun k b => (neg_at_zero h k b b.2).le
  have hstep : ∀ x ∈ Γ ∩ Set.Ico (0:ℝ) 1, Γ ∈ nhdsWithin x (Set.Ioi x) := by
    intro x ⟨hxΓ, hx0, hx1⟩
    have hcl : cl x < 1 := by rw [cl_of_mem hx0 hx1.le]; exact hx1
    set U : Set ℝ := ⋂ k : K, ⋂ b : {b // b ∉ K}, {α | wv G K α k b < 0}
    have hU : IsOpen U := isOpen_iInter_of_finite (fun k => isOpen_iInter_of_finite (fun b =>
      isOpen_lt (wv_cont h k b) continuous_const))
    have hxU : x ∈ U := by
      simp only [U, Set.mem_iInter, Set.mem_setOf_eq]
      intro k b
      exact neg_of_nonpos h x hcl (fun k' b' hb' => hxΓ k' ⟨b', hb'⟩) k b b.2
    have hUΓ : U ⊆ Γ := by
      intro α hα k b
      simp only [U, Set.mem_iInter, Set.mem_setOf_eq] at hα
      exact (hα k b).le
    exact nhdsWithin_le_nhds (Filter.mem_of_superset (hU.mem_nhds hxU) hUΓ)
  have hsub := IsClosed.Icc_subset_of_forall_mem_nhdsWithin (a := (0:ℝ)) (b := 1)
    (hclosed.inter isClosed_Icc) h0 hstep
  exact hsub ⟨zero_le_one, le_rfl⟩ k ⟨b, hb⟩

end Sign

end Brouwer.Stage2

namespace Brouwer.Stage2

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma trace_topP {A : Matrix V V ℝ} (hA : A.IsHermitian) (N : ℕ) :
    ∑ a, ∑ b, topP hA N a b * A b a = topSum hA N := by
  unfold topP topSum
  simp_rw [sum_mul]
  have sw : ∀ (X : Finset (Fin (Fintype.card V))) (f : V → V → Fin (Fintype.card V) → ℝ),
      ∑ a, ∑ b, ∑ t ∈ X, f a b t = ∑ t ∈ X, ∑ a, ∑ b, f a b t := by
    intro X f
    rw [sum_congr rfl (fun a _ => sum_comm)]; exact sum_comm
  rw [sw]
  refine sum_congr rfl (fun t _ => ?_)
  have e : ∀ a, ∑ b, sev hA t a * sev hA t b * A b a =
      sev hA t a * (hA.eigenvalues₀ t * sev hA t a) := by
    intro a; rw [← sev_eig hA, mul_sum]
    exact sum_congr rfl (fun b _ => by rw [symm_of_herm hA b a]; ring)
  simp_rw [e]
  have := sev_ortho hA t t
  simp only [if_true] at this
  calc ∑ a, sev hA t a * (hA.eigenvalues₀ t * sev hA t a) =
      hA.eigenvalues₀ t * ∑ a, sev hA t a * sev hA t a := by
        rw [mul_sum]; exact sum_congr rfl (fun a _ => by ring)
    _ = _ := by rw [this, mul_one]

section Final

variable {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V} {δ : ℝ}

lemma trace_eq_diag (h : Hyp G K δ) (α : ℝ) :
    ∑ a, ∑ b, Ph G K α a b * Lh G K α b a =
      ∑ k : K, ∑ c, Lh G K α k c * wv G K α k c := by
  have hcol : ∀ a b, Ph G K α a b = ∑ k : K, Ph G K α k b * wv G K α k a := by
    intro a b
    exact decomp h α (x := fun a => Ph G K α a b) (fun a => by unfold Ph; exact topP_idem _ _ a b) a
  rw [sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => by rw [hcol a b]))]
  simp_rw [sum_mul]
  rw [sum_comm]
  have e : ∀ b, ∑ a, ∑ k : K, Ph G K α k b * wv G K α k a * Lh G K α b a =
      ∑ k : K, Ph G K α k b * ∑ c, Lh G K α b c * wv G K α k c := by
    intro b
    rw [sum_comm]
    refine sum_congr rfl (fun k _ => ?_)
    rw [mul_sum]; exact sum_congr rfl (fun a _ => by ring)
  simp_rw [e]
  rw [sum_comm]
  refine sum_congr rfl (fun k _ => ?_)
  exact Lw_fix α k k

lemma Lh_one : Lh G K 1 = G.lapMatrix ℝ := by
  unfold Lh
  rw [cl_of_mem zero_le_one le_rfl, sub_self, zero_smul, zero_add, one_smul]

/-- Cross degree of a clique vertex. -/
noncomputable def dout (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (k : V) : ℝ :=
  ∑ c, if c ∈ K then 0 else if G.Adj k c then 1 else 0

lemma dh_split (h : Hyp G K δ) (k : K) : dh G k = (K.card - 1) + dout G K k := by
  unfold dh dout
  have e : ∀ c, (if G.Adj k c then (1:ℝ) else 0) =
      ((if c ∈ K then 1 else 0) - (if c = (k : V) then 1 else 0)) +
        (if c ∈ K then 0 else if G.Adj k c then 1 else 0) := by
    intro c
    by_cases hck : c = (k : V)
    · subst hck; simp [k.2]
    · by_cases hc : c ∈ K
      · have : G.Adj k c := h.split.1 k k.2 c hc (fun e => hck e.symm)
        simp [hc, hck, this]
      · simp [hc, hck]
  rw [sum_congr rfl (fun c _ => e c)]
  rw [sum_add_distrib, sum_sub_distrib, sum_ite_K, sum_ite_eq']
  simp only [mem_univ, if_true]; ring

lemma diag_bound (h : Hyp G K δ) (k : K) :
    ∑ c, Lh G K 1 k c * wv G K 1 k c ≤ (min (G.degree k) K.card : ℝ) + dout G K k := by
  rw [Lh_one, lap_row]
  set w := wv G K 1 k with hw
  have hwk : w k = 1 := by rw [hw, wv_K h 1 k k]; simp
  have hwK : ∀ c ∈ K, w c = if c = (k : V) then 1 else 0 := wv_K' h 1 k
  have hsum : ∑ a, w a = 0 := wv_sum h 1 k
  have hK1 : ∑ b, (if b ∈ K then w b else 0) = 1 := by
    have : ∀ b, (if b ∈ K then w b else 0) = if b = (k : V) then 1 else 0 := by
      intro b
      by_cases hb : b ∈ K
      · rw [if_pos hb, hwK b hb]
      · rw [if_neg hb, if_neg (fun e => hb (by rw [e]; exact k.2))]
    simp_rw [this]; simp
  have hKc : ∑ b, (if b ∈ K then 0 else w b) = -1 := by
    have : ∀ b, (if b ∈ K then 0 else w b) = w b - (if b ∈ K then w b else 0) := by
      intro b; split_ifs <;> ring
    simp_rw [this]; rw [sum_sub_distrib, hsum, hK1]; ring
  have hsgn : ∀ b, b ∉ K → w b ≤ 0 := fun b hb => nonpos_at_one h k b hb
  have e : ∀ c, (if G.Adj k c then w k - w c else 0) =
      (if G.Adj k c then 1 else 0) + (if c ∈ K then 0 else if G.Adj k c then -w c else 0) := by
    intro c
    rw [hwk]
    by_cases hc : c ∈ K
    · by_cases hadj : G.Adj k c
      · have hck : c ≠ (k : V) := fun e => by subst e; exact G.loopless.irrefl _ hadj
        simp [hc, hadj, hwK c hc, hck]
      · simp [hc, hadj]
    · by_cases hadj : G.Adj k c <;> simp [hc, hadj] <;> ring
  simp_rw [e]
  rw [sum_add_distrib]
  have hdeg : (G.degree k : ℝ) = dh G k := by
    unfold dh; rw [G.degree_eq_sum_if_adj (R := ℝ) k]
  have hdh := dh_split h k
  change dh G k + _ ≤ _
  by_cases hex : ∃ c, c ∉ K ∧ G.Adj k c
  · obtain ⟨c0, hc0, hadj0⟩ := hex
    have hd1 : 1 ≤ dout G K k := by
      unfold dout
      have := single_le_sum (f := fun c => if c ∈ K then (0:ℝ) else if G.Adj k c then 1 else 0)
        (fun c _ => by split_ifs <;> norm_num) (mem_univ c0)
      simpa [hc0, hadj0] using this
    have hR : ∑ c, (if c ∈ K then 0 else if G.Adj k c then -w c else 0) ≤ 1 := by
      rw [← neg_neg (1:ℝ), ← hKc, ← sum_neg_distrib]
      refine sum_le_sum (fun c _ => ?_)
      by_cases hc : c ∈ K
      · simp [hc]
      · have := hsgn c hc
        by_cases hadj : G.Adj k c <;> simp [hc, hadj] <;> linarith
    have hmin : (min (G.degree k) K.card : ℝ) = K.card := by
      rw [min_eq_right]; rw [hdeg, hdh]; linarith
    rw [hmin, hdh]; linarith
  · push Not at hex
    have hR : ∑ c, (if c ∈ K then 0 else if G.Adj k c then -w c else 0) = 0 := by
      refine sum_eq_zero (fun c _ => ?_)
      by_cases hc : c ∈ K
      · simp [hc]
      · simp [hc, hex c hc]
    have hd0 : dout G K k = 0 := by
      unfold dout
      refine sum_eq_zero (fun c _ => ?_)
      by_cases hc : c ∈ K
      · simp [hc]
      · simp [hc, hex c hc]
    have hmin : (min (G.degree k) K.card : ℝ) = G.degree k := by
      rw [min_eq_left]; rw [hdeg, hdh, hd0]; linarith
    rw [hmin, hdeg, hR, hd0]

lemma sum_dout (h : Hyp G K δ) :
    ∑ k ∈ K, dout G K k = ∑ v ∈ Kᶜ, (min (G.degree v) K.card : ℝ) := by
  have hmin : ∀ v ∈ Kᶜ, (min (G.degree v) K.card : ℝ) = ∑ c ∈ K, if G.Adj v c then 1 else 0 := by
    intro v hv
    have hv' : v ∉ K := by simpa using hv
    have hdeg : (G.degree v : ℝ) = dh G v := by
      unfold dh; rw [G.degree_eq_sum_if_adj (R := ℝ) v]
    rw [min_eq_left (by rw [hdeg]; exact dh_out_le h v hv'), hdeg]
    unfold dh
    symm
    apply sum_subset (subset_univ K)
    intro c _ hc
    have : ¬ G.Adj v c := fun hh => h.split.2 v hv' c hc hh
    simp [this]
  rw [sum_congr rfl hmin]
  unfold dout
  have e : ∀ k, (∑ c, if c ∈ K then (0:ℝ) else if G.Adj k c then 1 else 0) =
      ∑ c ∈ Kᶜ, if G.Adj k c then 1 else 0 := by
    intro k; rw [sum_compl_eq]
  simp_rw [e]
  rw [sum_comm]
  refine sum_congr rfl (fun v _ => sum_congr rfl (fun c _ => ?_))
  simp only [G.adj_comm]

/-- **Bai's Lemma 6.** A split graph with clique `K` (`|K| = N`) whose `N`-th Laplacian
eigenvalue is at least `N`, and either `λ_N > N` or all outside degrees are `< N`,
satisfies the Grone–Merris inequality at `N`. -/
theorem bai_lemma6_core (h : Hyp G K δ) : S G K.card ≤ D G K.card := by
  unfold S
  rw [topSum_congr Lh_one.symm (G.isHermitian_lapMatrix ℝ) (Lh_herm G K 1)]
  rw [← trace_topP, ← Ph, trace_eq_diag h 1]
  calc ∑ k : K, ∑ c, Lh G K 1 k c * wv G K 1 k c
      ≤ ∑ k : K, ((min (G.degree k) K.card : ℝ) + dout G K k) :=
        sum_le_sum (fun k _ => diag_bound h k)
    _ = ∑ k ∈ K, ((min (G.degree k) K.card : ℝ) + dout G K k) :=
        Finset.sum_coe_sort K (fun k => (min (G.degree k) K.card : ℝ) + dout G K k)
    _ = D G K.card := by
        rw [sum_add_distrib, sum_dout h]
        unfold D
        exact sum_add_sum_compl K _

end Final

end Brouwer.Stage2
