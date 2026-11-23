/-
  Stage 2: the finite-dimensional lemmas of Bai's proof of the Grone–Merris conjecture
  (Trans. AMS 2011), stated with top-eigenvalue sums `topSum`: edge deletion (used in Lemma 13),
  monotonicity, Proposition 5(a) for split graphs, and the case `k = 1`.
-/
import Brouwer.Stage2.KyFan
import Brouwer.Stage2.CourantFischer
import Brouwer.Main

open Finset Matrix

set_option linter.unusedSectionVars false

namespace Brouwer.Stage2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `S_k(G)`: sum of the `k` largest Laplacian eigenvalues. -/
noncomputable def S (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℝ :=
  topSum (G.isHermitian_lapMatrix ℝ) k

/-- `D_k(G) = Σ_v min(deg v, k)`, the sum of the first `k` conjugate degrees. -/
noncomputable def D (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℝ :=
  ∑ v, (min (G.degree v) k : ℝ)

lemma a_symm' (P : Matrix V V ℝ) (hs : ∀ i j, P i j = P j i) (i j : V) :
    Brouwer.a P i j = Brouwer.a P j i := by
  unfold Brouwer.a; rw [hs i j]; ring

lemma topSum_congr {A A' : Matrix V V ℝ} (h : A = A') (hA : A.IsHermitian)
    (hA' : A'.IsHermitian) (k : ℕ) : topSum hA k = topSum hA' k := by
  subst h; rfl

/-- Quadratic form of a graph Laplacian. -/
lemma lap_qform (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    ∑ a, ∑ b, x a * G.lapMatrix ℝ a b * x b =
      (∑ a, ∑ b, if G.Adj a b then (x a - x b) ^ 2 else 0) / 2 := by
  have h := trace_lap (fun a b => x a * x b) (fun i j => mul_comm _ _) G
  have hsym : ∀ a b, G.lapMatrix ℝ a b = G.lapMatrix ℝ b a := fun a b => by
    have := (G.isSymm_lapMatrix ℝ).apply a b; exact this.symm
  have e1 : ∑ a, ∑ b, x a * G.lapMatrix ℝ a b * x b =
      ∑ a, ∑ b, x a * x b * G.lapMatrix ℝ b a := by
    refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
    rw [hsym a b]; ring
  rw [e1, h]
  congr 1
  refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
  split_ifs <;> simp [Brouwer.a] <;> ring


lemma topSum_succ {A : Matrix V V ℝ} (hA : A.IsHermitian) (k : ℕ) (hk : k < Fintype.card V) :
    topSum hA (k + 1) - topSum hA k = hA.eigenvalues₀ ⟨k, hk⟩ := by
  unfold topSum
  have : univ.filter (fun t : Fin (Fintype.card V) => t.val < k + 1) =
      insert ⟨k, hk⟩ (univ.filter (fun t : Fin (Fintype.card V) => t.val < k)) := by
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  rw [this, sum_insert (by simp)]; ring

/-- Coordinate subspace of vectors vanishing on `K`. -/
noncomputable def coordSub (K : Finset V) : Submodule ℝ (V → ℝ) :=
  Submodule.span ℝ (Set.range (fun j : {j // j ∉ K} => (Pi.single j.val (1:ℝ) : V → ℝ)))

lemma finrank_coordSub (K : Finset V) :
    Module.finrank ℝ (coordSub K) = Fintype.card V - K.card := by
  unfold coordSub
  have hli : LinearIndependent ℝ (fun j : {j // j ∉ K} => (Pi.single j.val (1:ℝ) : V → ℝ)) := by
    have := (Pi.basisFun ℝ V).linearIndependent
    have h2 := this.comp (Subtype.val : {j // j ∉ K} → V) Subtype.val_injective
    convert h2 using 1
    ext j; simp
  rw [finrank_span_eq_card hli, Fintype.card_subtype_compl, Fintype.card_coe]

lemma coordSub_zero {K : Finset V} {x : V → ℝ} (hx : x ∈ coordSub K) : ∀ i ∈ K, x i = 0 := by
  unfold coordSub at hx
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  intro i hi
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine sum_eq_zero (fun j _ => ?_)
  have : j.val ≠ i := fun h => j.2 (h ▸ hi)
  simp [Pi.single_apply, Ne.symm this]

/-- If `x_a x_b = 0` on every edge, the Laplacian form is `Σ deg(a) x_a²`. -/
lemma qf_lap_of_edge_zero (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ)
    (h : ∀ a b, G.Adj a b → x a * x b = 0) :
    qf (G.lapMatrix ℝ) x = ∑ a, (G.degree a : ℝ) * (x a * x a) := by
  unfold qf
  rw [lap_qform]
  have hpt : ∀ a b, (if G.Adj a b then (x a - x b) ^ 2 else 0) =
      (if G.Adj a b then x a * x a else 0) + (if G.Adj a b then x b * x b else 0) := by
    intro a b
    by_cases hab : G.Adj a b
    · simp only [hab, if_true]; have := h a b hab; nlinarith
    · simp [hab]
  simp only [hpt, sum_add_distrib]
  have h1 : ∑ a, ∑ b, (if G.Adj a b then x b * x b else 0) =
      ∑ a, ∑ b, (if G.Adj a b then x a * x a else 0) := by
    rw [sum_comm]
    refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
    simp only [G.adj_comm b a]
  have h2 : ∀ a, ∑ b, (if G.Adj a b then x a * x a else 0) = (G.degree a : ℝ) * (x a * x a) := by
    intro a
    rw [G.degree_eq_sum_if_adj (R := ℝ) a, sum_mul]
    exact sum_congr rfl (fun b _ => by split_ifs <;> simp)
  rw [h1, sum_congr rfl (fun a _ => h2 a)]; ring

/-- Deleting an edge `ij` with both endpoints of degree `≤ k` lowers `D_k` by 2,
and `S_k` by at most 2 (Ky Fan subadditivity with the rank-one Laplacian of the edge).
This is Bai's Lemma 13. -/
theorem S_le_of_delete_edge (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V)
    (hij : G.Adj i j) (k : ℕ) (hk : k ≤ Fintype.card V) :
    S G k ≤ S (G.deleteEdges {s(i, j)}) k + 2 := by
  classical
  set G' := G.deleteEdges {s(i, j)} with hG'
  have hne : i ≠ j := G.ne_of_adj hij
  set B := G.lapMatrix ℝ - G'.lapMatrix ℝ with hBdef
  have hBs : ∀ a b, B a b = B b a := by
    intro a b
    simp only [hBdef, Matrix.sub_apply]
    rw [(G.isSymm_lapMatrix ℝ).apply a b, (G'.isSymm_lapMatrix ℝ).apply a b]
  have hBH : B.IsHermitian := by
    ext a b; simp [Matrix.conjTranspose_apply, hBs a b]
  have hsum : G'.lapMatrix ℝ + B = G.lapMatrix ℝ := by rw [hBdef]; abel
  have hAB : (G'.lapMatrix ℝ + B).IsHermitian := by
    rw [hsum]; exact G.isHermitian_lapMatrix ℝ
  have h1 := topSum_add_le (G'.isHermitian_lapMatrix ℝ) hBH hAB k hk
  rw [topSum_congr hsum hAB (G.isHermitian_lapMatrix ℝ)] at h1
  -- bound `topSum B ≤ 2`
  obtain ⟨P, hPs, hPi, hPtr, hval, -⟩ := kyFan_attained hBH k hk
  have htrB : ∑ a, ∑ b, P a b * B b a = Brouwer.a P i j := by
    have e : ∑ a, ∑ b, P a b * B b a =
        ∑ a, ∑ b, P a b * G.lapMatrix ℝ b a - ∑ a, ∑ b, P a b * G'.lapMatrix ℝ b a := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl (fun a _ => ?_)
      rw [← sum_sub_distrib]
      refine sum_congr rfl (fun b _ => ?_)
      simp only [hBdef, Matrix.sub_apply]; ring
    rw [e, trace_lap P hPs G, trace_lap P hPs G', ← sub_div, ← sum_sub_distrib]
    have hpt : ∀ a b, ((if G.Adj a b then Brouwer.a P a b else 0) -
        (if G'.Adj a b then Brouwer.a P a b else 0)) =
        (if a = i ∧ b = j then Brouwer.a P a b else 0) +
        (if a = j ∧ b = i then Brouwer.a P a b else 0) := by
      intro a b
      have hadj' : G'.Adj a b ↔ G.Adj a b ∧ ¬ ((a = i ∧ b = j) ∨ (a = j ∧ b = i)) := by
        rw [hG', SimpleGraph.deleteEdges_adj]
        simp [Sym2.eq_iff]
      by_cases h1 : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := h1
        have : ¬ (a = b ∧ b = a) := fun h => hne h.1
        simp [hadj', hij, this]
      · by_cases h2 : a = j ∧ b = i
        · obtain ⟨rfl, rfl⟩ := h2
          have hji : G.Adj a b := hij.symm
          simp [hadj', hji, h1]
        · rw [if_neg h1, if_neg h2, add_zero]
          by_cases hab : G.Adj a b <;> simp [hadj', hab, h1, h2]
    simp only [← sum_sub_distrib, hpt, sum_add_distrib]
    have hs1 : ∀ p q : V, ∑ x, ∑ y, (if x = p ∧ y = q then Brouwer.a P x y else 0) =
        Brouwer.a P p q := by
      intro p q
      rw [Finset.sum_eq_single p]
      · rw [Finset.sum_eq_single q]
        · simp
        · intro y _ hy; simp [hy]
        · simp
      · intro x _ hx; exact sum_eq_zero (fun y _ => by simp [hx])
      · simp
    rw [hs1, hs1, a_symm' P hPs j i]; ring
  have hle2 : Brouwer.a P i j ≤ 2 := by
    let Q : Matrix V V ℝ := fun a b => (if a = b then 1 else 0) - P a b
    have hQs : ∀ a b, Q a b = Q b a := by
      intro a b; simp only [Q, hPs a b, eq_comm]
    have hQi : ∀ a b, ∑ l, Q a l * Q l b = Q a b := by
      intro a b
      simp only [Q, sub_mul, mul_sub, sum_sub_distrib, ite_mul, one_mul, zero_mul, mul_ite,
        mul_one, mul_zero, sum_ite_eq, sum_ite_eq', mem_univ, if_true, hPi a b]
      ring
    let x : V → ℝ := fun a => (if a = i then 1 else 0) - (if a = j then 1 else 0)
    have hq := qf_nonneg Q hQs hQi x
    have e : ∑ a, ∑ b, x a * Q a b * x b = 2 - Brouwer.a P i j := by
      simp only [x, Q, Brouwer.a, sub_mul, mul_sub, ite_mul, one_mul, zero_mul, mul_ite,
        mul_one, mul_zero, sum_sub_distrib, sum_ite_eq, sum_ite_eq', mem_univ, if_true,
        Ne.symm hne, hne, if_false, hPs j i]
      ring
    linarith
  unfold S
  linarith

/-- Adding edges never decreases `S_k` (the added Laplacian is PSD). -/
theorem S_mono (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) (k : ℕ) (hk : k ≤ Fintype.card V) : S G k ≤ S H k := by
  set B := H.lapMatrix ℝ - G.lapMatrix ℝ with hBdef
  have hBs : ∀ i j, B i j = B j i := by
    intro i j
    simp only [hBdef, Matrix.sub_apply]
    rw [(H.isSymm_lapMatrix ℝ).apply i j, (G.isSymm_lapMatrix ℝ).apply i j]
  have hBpsd : ∀ x : V → ℝ, 0 ≤ ∑ a, ∑ b, x a * B a b * x b := by
    intro x
    have e : ∑ a, ∑ b, x a * B a b * x b =
        ∑ a, ∑ b, x a * H.lapMatrix ℝ a b * x b - ∑ a, ∑ b, x a * G.lapMatrix ℝ a b * x b := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl (fun a _ => ?_)
      rw [← sum_sub_distrib]
      refine sum_congr rfl (fun b _ => ?_)
      simp only [hBdef, Matrix.sub_apply]; ring
    rw [e, lap_qform, lap_qform, ← sub_div, ← sum_sub_distrib]
    apply div_nonneg _ (by norm_num)
    refine sum_nonneg (fun a _ => ?_)
    rw [← sum_sub_distrib]
    refine sum_nonneg (fun b _ => ?_)
    by_cases hG : G.Adj a b
    · simp [hG, hGH hG]
    · by_cases hH : H.Adj a b
      · simp [hG, hH, sq_nonneg]
      · simp [hG, hH]
  have hsum : G.lapMatrix ℝ + B = H.lapMatrix ℝ := by rw [hBdef]; abel
  have hAB : (G.lapMatrix ℝ + B).IsHermitian := by rw [hsum]; exact H.isHermitian_lapMatrix ℝ
  have := topSum_le_add_psd (G.isHermitian_lapMatrix ℝ) hAB hBs hBpsd k hk
  unfold S
  rw [topSum_congr hsum hAB (H.isHermitian_lapMatrix ℝ)] at this
  exact this

/-- A split graph: clique `K`, independent complement. -/
def IsSplit (G : SimpleGraph V) (K : Finset V) : Prop :=
  (∀ i ∈ K, ∀ j ∈ K, i ≠ j → G.Adj i j) ∧ (∀ i ∉ K, ∀ j ∉ K, ¬ G.Adj i j)

/-- Bai's Prop 5(a), upper half: in a split graph with clique of
size `N`, `λ_{N+1} ≤ max co-degree`, i.e. `S_{N+1} - S_N ≤ δ`. -/
theorem split_lambda_succ_le (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V)
    (hG : IsSplit G K) (δ : ℕ) (hδ : ∀ v ∉ K, G.degree v ≤ δ)
    (hN : K.card + 1 ≤ Fintype.card V) :
    S G (K.card + 1) - S G K.card ≤ δ := by
  have hk : K.card < Fintype.card V := by omega
  unfold S
  rw [topSum_succ _ _ hk]
  apply eig_le_of_subspace (G.isHermitian_lapMatrix ℝ) ⟨K.card, hk⟩ (coordSub K) δ
  · intro x hx
    have hz := coordSub_zero hx
    rw [qf_lap_of_edge_zero G x]
    · unfold nsq
      rw [mul_sum]
      refine sum_le_sum (fun a _ => ?_)
      by_cases ha : a ∈ K
      · simp [hz a ha]
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hδ a ha) (mul_self_nonneg _)
    · intro a b hab
      by_cases ha : a ∈ K
      · simp [hz a ha]
      · by_cases hb : b ∈ K
        · simp [hz b hb]
        · exact absurd hab (hG.2 a ha b hb)
  · rw [finrank_coordSub (V := V) K]; simp only [Fin.val_mk]; omega

/-- The linear functional `x ↦ Σ x`. -/
noncomputable def sumL : (V → ℝ) →ₗ[ℝ] ℝ := ∑ a, LinearMap.proj a

lemma sumL_apply (x : V → ℝ) : sumL x = ∑ a, x a := by
  simp [sumL]

lemma finrank_ker_sumL : Fintype.card V - 1 ≤ Module.finrank ℝ (LinearMap.ker (sumL (V := V))) := by
  have h := LinearMap.finrank_range_add_finrank_ker (sumL (V := V))
  have h1 : Module.finrank ℝ (LinearMap.range (sumL (V := V))) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (sumL (V := V)))
    simpa using this
  rw [Module.finrank_fintype_fun_eq_card] at h
  omega

/-- Prop 5(a), lower half: `λ_{N-1} ≥ N`. -/
theorem split_lambda_pred_ge (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V)
    (hG : IsSplit G K) (hN : 2 ≤ K.card) :
    (K.card : ℝ) ≤ S G (K.card - 1) - S G (K.card - 2) := by
  have hKn : K.card ≤ Fintype.card V := Finset.card_le_univ K
  have hk : K.card - 2 < Fintype.card V := by omega
  unfold S
  have e : K.card - 1 = (K.card - 2) + 1 := by omega
  rw [e, topSum_succ _ _ hk]
  set A := coordSub (V := V) Kᶜ
  set B := LinearMap.ker (sumL (V := V))
  apply le_eig_of_subspace (G.isHermitian_lapMatrix ℝ) ⟨K.card - 2, hk⟩ (A ⊓ B) (K.card : ℝ)
  · intro x hx
    have hz : ∀ i, i ∉ K → x i = 0 := fun i hi =>
      coordSub_zero (Submodule.mem_inf.mp hx).1 i (by simpa using hi)
    have hs : ∑ a, x a = 0 := by
      have := (Submodule.mem_inf.mp hx).2
      rw [LinearMap.mem_ker, sumL_apply] at this; exact this
    have hsK : ∑ a ∈ K, x a = 0 := by
      rw [← hs]
      exact sum_subset (subset_univ K) (fun a _ ha => hz a ha)
    have hnK : nsq x = ∑ a ∈ K, x a * x a := by
      unfold nsq; symm
      exact sum_subset (subset_univ K) (fun a _ ha => by simp [hz a ha])
    have hid : ∑ a ∈ K, ∑ b ∈ K, (x a - x b) ^ 2 =
        2 * (K.card : ℝ) * ∑ a ∈ K, x a * x a - 2 * (∑ a ∈ K, x a) ^ 2 := by
      have : ∀ a b, (x a - x b) ^ 2 = x a * x a + x b * x b - 2 * (x a * x b) := fun a b => by ring
      simp only [this, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum,
        ← sum_mul, sq]
      ring
    have key : ∑ a ∈ K, ∑ b ∈ K, (x a - x b) ^ 2 ≤
        ∑ a, ∑ b, (if G.Adj a b then (x a - x b) ^ 2 else 0) := by
      have hnn : ∀ a b, 0 ≤ (if G.Adj a b then (x a - x b) ^ 2 else 0) := fun a b => by
        split_ifs <;> positivity
      calc ∑ a ∈ K, ∑ b ∈ K, (x a - x b) ^ 2
          ≤ ∑ a ∈ K, ∑ b, (if G.Adj a b then (x a - x b) ^ 2 else 0) := by
            refine sum_le_sum (fun a ha => ?_)
            calc ∑ b ∈ K, (x a - x b) ^ 2
                ≤ ∑ b ∈ K, (if G.Adj a b then (x a - x b) ^ 2 else 0) := by
                  refine sum_le_sum (fun b hb => ?_)
                  by_cases hab : a = b
                  · subst hab; simp only [sub_self]; simp
                  · simp [hG.1 a ha b hb hab]
              _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ K)
                  (fun b _ _ => hnn a b)
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ K)
            (fun a _ _ => sum_nonneg (fun b _ => hnn a b))
    unfold qf
    rw [lap_qform, hnK]
    rw [hid, hsK] at key
    linarith
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq A B
    have h2 : Module.finrank ℝ ↥(A ⊔ B) ≤ Fintype.card V := by
      have := Submodule.finrank_le (A ⊔ B)
      rwa [Module.finrank_fintype_fun_eq_card] at this
    have h3 : Module.finrank ℝ A = K.card := by
      rw [finrank_coordSub (V := V) Kᶜ, Finset.card_compl]; omega
    have h4 : Fintype.card V - 1 ≤ Module.finrank ℝ B := finrank_ker_sumL (V := V)
    show K.card - 2 + 1 ≤ _
    omega

/-- The case `k = 1`: `λ_1 ≤ d'_1` (number of non-isolated vertices). -/
theorem gmb_one (G : SimpleGraph V) [DecidableRel G.Adj] : S G 1 ≤ D G 1 := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
  · unfold S topSum
    have : (univ.filter (fun t : Fin (Fintype.card V) => t.val < 1)) = ∅ := by
      ext t; exact absurd t.isLt (by omega)
    rw [this, sum_empty]
    exact sum_nonneg (fun v _ => by positivity)
  set U := univ.filter (fun v => 0 < G.degree v) with hU
  have hD : D G 1 = (U.card : ℝ) := by
    unfold D
    rw [hU, card_eq_sum_ones, Nat.cast_sum, sum_filter]
    refine sum_congr rfl (fun v _ => ?_)
    rcases Nat.eq_zero_or_pos (G.degree v) with h | h
    · simp [h]
    · simp [h, Nat.one_le_iff_ne_zero.mpr (by omega : G.degree v ≠ 0)]
  have hadjU : ∀ a b, G.Adj a b → a ∈ U := fun a b h => by
    rw [hU, mem_filter]; exact ⟨mem_univ _, G.degree_pos_iff_exists_adj a |>.mpr ⟨b, h⟩⟩
  have h0 : topSum (G.isHermitian_lapMatrix ℝ) 0 = 0 := by
    unfold topSum
    have : (univ.filter (fun t : Fin (Fintype.card V) => t.val < 0)) = ∅ := by
      ext t; simp
    rw [this, sum_empty]
  unfold S
  have e := topSum_succ (G.isHermitian_lapMatrix ℝ) 0 hn
  rw [h0, sub_zero] at e
  rw [e, hD]
  apply eig_le_of_subspace (G.isHermitian_lapMatrix ℝ) ⟨0, hn⟩ ⊤ (U.card : ℝ)
  · intro x _
    unfold qf
    rw [lap_qform]
    have hnn : ∀ a b, 0 ≤ (if G.Adj a b then (x a - x b) ^ 2 else 0) := fun a b => by
      split_ifs <;> positivity
    have hred : ∑ a, ∑ b, (if G.Adj a b then (x a - x b) ^ 2 else 0) =
        ∑ a ∈ U, ∑ b ∈ U, (if G.Adj a b then (x a - x b) ^ 2 else 0) := by
      symm
      rw [sum_subset (subset_univ U) (fun a _ ha => sum_eq_zero (fun b _ => by
        have : ¬ G.Adj a b := fun h => ha (hadjU a b h)
        simp [this]))]
      refine sum_congr rfl (fun a _ => ?_)
      refine sum_subset (subset_univ U) (fun b _ hb => ?_)
      have : ¬ G.Adj a b := fun h => hb (hadjU b a h.symm)
      simp [this]
    have hle : ∑ a ∈ U, ∑ b ∈ U, (if G.Adj a b then (x a - x b) ^ 2 else 0) ≤
        ∑ a ∈ U, ∑ b ∈ U, (x a - x b) ^ 2 :=
      sum_le_sum (fun a _ => sum_le_sum (fun b _ => by split_ifs <;> [exact le_rfl; positivity]))
    have hid : ∑ a ∈ U, ∑ b ∈ U, (x a - x b) ^ 2 =
        2 * (U.card : ℝ) * ∑ a ∈ U, x a * x a - 2 * (∑ a ∈ U, x a) ^ 2 := by
      have : ∀ a b, (x a - x b) ^ 2 = x a * x a + x b * x b - 2 * (x a * x b) := fun a b => by ring
      simp only [this, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum,
        ← sum_mul, sq]
      ring
    have hU2 : ∑ a ∈ U, x a * x a ≤ nsq x :=
      sum_le_sum_of_subset_of_nonneg (subset_univ U) (fun a _ _ => mul_self_nonneg _)
    have hc : (0 : ℝ) ≤ U.card := by positivity
    rw [hred]
    nlinarith [sq_nonneg (∑ a ∈ U, x a), mul_le_mul_of_nonneg_left hU2 hc]
  · rw [finrank_top, Module.finrank_fintype_fun_eq_card]; simp

end Brouwer.Stage2
