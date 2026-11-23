/-
  Brouwer's Laplacian conjecture, following Kothari–Tudose (arXiv:2606.12197).
  Part (D): the projection onto top eigenvectors, split graphs, and the main theorem.
-/
import Brouwer.Spectral

open Finset Matrix

set_option linter.unusedSectionVars false

namespace Brouwer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `tr(P L_H) = ½ Σ_{a ~ b} a_P(a,b)` for symmetric `P`. -/
lemma trace_lap (P : Matrix V V ℝ) (hs : ∀ i j, P i j = P j i)
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∑ a, ∑ b, P a b * H.lapMatrix ℝ b a =
      (∑ a, ∑ b, if H.Adj a b then Brouwer.a P a b else 0) / 2 := by
  have hL : ∀ b a, H.lapMatrix ℝ b a =
      (if b = a then ∑ c, (if H.Adj b c then (1:ℝ) else 0) else 0) -
        (if H.Adj b a then 1 else 0) := by
    intro b a
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
      Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]
    rw [H.degree_eq_sum_if_adj (R := ℝ) b]
  simp_rw [hL, mul_sub, sum_sub_distrib, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
  -- first term: Σ_b P b b deg b = Σ_a Σ_b [a~b] P a a
  have h1 : ∑ a, P a a * ∑ c, (if H.Adj a c then (1:ℝ) else 0) =
      ∑ a, ∑ b, if H.Adj a b then P a a else 0 := by
    refine sum_congr rfl (fun a _ => ?_)
    rw [mul_sum]; simp
  have h2 : ∑ a, ∑ b, (if H.Adj b a then P a b * 1 else 0) =
      ∑ a, ∑ b, if H.Adj a b then P a b else 0 := by
    refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
    simp only [H.adj_comm b a, mul_one]
  have h3 : ∑ a, ∑ b, (if H.Adj a b then P b b else 0) =
      ∑ a, ∑ b, if H.Adj a b then P a a else 0 := by
    rw [sum_comm]
    refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
    simp only [H.adj_comm b a]
  have h4 : ∑ a, ∑ b, (if H.Adj a b then Brouwer.a P a b else 0) =
      ∑ a, ∑ b, (if H.Adj a b then P a a else 0) + ∑ a, ∑ b, (if H.Adj a b then P b b else 0)
        - 2 * ∑ a, ∑ b, (if H.Adj a b then P a b else 0) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl (fun a _ => ?_)
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl (fun b _ => ?_)
    by_cases h : H.Adj a b <;> simp [h, Brouwer.a]
  rw [h1, h2, h4, h3]; ring

/-- Turning a double sum with membership conditions into a sum over `K × L`. -/
lemma sum_sum_ite_mem (K L : Finset V) (f : V → V → ℝ) (p : V → V → Prop)
    [∀ i j, Decidable (p i j)] :
    ∑ i, ∑ j, (if i ∈ K ∧ j ∈ L ∧ p i j then f i j else 0) =
      ∑ i ∈ K, ∑ j ∈ L, if p i j then f i j else 0 := by
  rw [← sum_filter_add_sum_filter_not univ (fun i => i ∈ K)]
  have hz : ∑ i ∈ univ.filter (fun i => i ∉ K),
      ∑ j, (if i ∈ K ∧ j ∈ L ∧ p i j then f i j else 0) = 0 := by
    refine sum_eq_zero (fun i hi => sum_eq_zero (fun j _ => ?_))
    rw [mem_filter] at hi; simp [hi.2]
  rw [hz, add_zero, show univ.filter (fun i => i ∈ K) = K by ext; simp]
  refine sum_congr rfl (fun i hi => ?_)
  rw [← sum_filter_add_sum_filter_not univ (fun j => j ∈ L)]
  have hz2 : ∑ j ∈ univ.filter (fun j => j ∉ L),
      (if i ∈ K ∧ j ∈ L ∧ p i j then f i j else 0) = 0 := by
    refine sum_eq_zero (fun j hj => ?_)
    rw [mem_filter] at hj; simp [hj.2]
  rw [hz2, add_zero, show univ.filter (fun j => j ∈ L) = L by ext; simp]
  refine sum_congr rfl (fun j hj => ?_)
  simp [hi, hj]

/-- The split graph used for the cut hypothesis: clique `K`, and a cross edge `ij`
exactly when `a_P(i,j) ≥ 1`. -/
def splitG (P : Matrix V V ℝ) (hs : ∀ i j, P i j = P j i) (K : Finset V) : SimpleGraph V where
  Adj i j := i ≠ j ∧ ((i ∈ K ∧ j ∈ K) ∨ (i ∈ K ∧ j ∉ K ∧ 1 ≤ a P i j) ∨
    (i ∉ K ∧ j ∈ K ∧ 1 ≤ a P i j))
  symm := ⟨by
    intro i j ⟨hne, h⟩
    have hsym : a P j i = a P i j := by unfold a; rw [hs i j]; ring
    refine ⟨hne.symm, ?_⟩
    rw [hsym]; tauto⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- The cut hypothesis follows from Grone–Merris–Bai (via the easy half of Ky Fan). -/
theorem cutHyp_of_GMB (hGMB : GroneMerrisBai V) (P : Matrix V V ℝ) (k : ℕ)
    (hP : IsProj P k) : CutHyp P k := by
  intro K
  classical
  let H := splitG P hP.symm K
  have hKF := kyFan (H.isHermitian_lapMatrix ℝ) P hP.symm hP.idem k hP.tr
  have hG := hGMB H k
  rw [trace_lap P hP.symm H] at hKF
  -- decompose the edge sum of `H`
  set X := ∑ i ∈ K, ∑ j ∈ Kᶜ, (if 1 ≤ a P i j then a P i j else 0) with hX
  set Y := ∑ i ∈ K, ∑ j ∈ Kᶜ, (if 1 ≤ a P i j then (1:ℝ) else 0) with hY
  have hedge : ∑ a', ∑ b, (if H.Adj a' b then Brouwer.a P a' b else 0) =
      ∑ i ∈ K, ∑ j ∈ K, a P i j + 2 * X := by
    have hpt : ∀ i j, (if H.Adj i j then a P i j else 0) =
        (if i ∈ K ∧ j ∈ K ∧ True then a P i j else 0) +
        (if i ∈ K ∧ j ∈ Kᶜ ∧ 1 ≤ a P i j then a P i j else 0) +
        (if j ∈ K ∧ i ∈ Kᶜ ∧ 1 ≤ a P j i then a P j i else 0) := by
      intro i j
      have hsym : a P j i = a P i j := (a_symm hP i j).symm
      by_cases hij : i = j
      · subst hij
        have hadj : ¬ H.Adj i i := H.loopless.irrefl i
        simp [hadj, a_self]
      · have hadj : H.Adj i j ↔ ((i ∈ K ∧ j ∈ K) ∨ (i ∈ K ∧ j ∉ K ∧ 1 ≤ a P i j) ∨
            (i ∉ K ∧ j ∈ K ∧ 1 ≤ a P i j)) := by
          show (i ≠ j ∧ _) ↔ _
          simp [hij]
        rw [hsym]
        by_cases hi : i ∈ K <;> by_cases hj : j ∈ K <;> by_cases ha : 1 ≤ a P i j <;>
          simp [hadj, hi, hj, ha]
    rw [sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => hpt i j))]
    simp only [sum_add_distrib]
    rw [sum_sum_ite_mem K K (a P) (fun _ _ => True),
      sum_sum_ite_mem K Kᶜ (a P) (fun i j => 1 ≤ a P i j)]
    have hswap : ∑ i, ∑ j, (if j ∈ K ∧ i ∈ Kᶜ ∧ 1 ≤ a P j i then a P j i else 0) =
        ∑ i, ∑ j, (if i ∈ K ∧ j ∈ Kᶜ ∧ 1 ≤ a P i j then a P i j else 0) := sum_comm
    rw [hswap, sum_sum_ite_mem K Kᶜ (a P) (fun i j => 1 ≤ a P i j)]
    simp only [if_true, hX]; ring
  have hdeg : ∑ v, (min (H.degree v) k : ℝ) ≤ K.card * k + Y := by
    rw [← sum_add_sum_compl K]
    have hA : ∑ v ∈ K, (min (H.degree v) k : ℝ) ≤ K.card * k := by
      calc ∑ v ∈ K, (min (H.degree v) k : ℝ) ≤ ∑ _v ∈ K, (k : ℝ) :=
            sum_le_sum (fun v _ => by exact_mod_cast min_le_right _ _)
        _ = K.card * k := by rw [sum_const, nsmul_eq_mul]
    have hB : ∑ v ∈ Kᶜ, (min (H.degree v) k : ℝ) ≤ Y := by
      calc ∑ v ∈ Kᶜ, (min (H.degree v) k : ℝ) ≤ ∑ v ∈ Kᶜ, (H.degree v : ℝ) :=
            sum_le_sum (fun v _ => by exact_mod_cast min_le_left _ _)
        _ = ∑ v ∈ Kᶜ, ∑ c ∈ K, (if 1 ≤ a P c v then (1:ℝ) else 0) := by
            refine sum_congr rfl (fun v hv => ?_)
            rw [H.degree_eq_sum_if_adj (R := ℝ) v]
            rw [← sum_filter_add_sum_filter_not univ (fun c => c ∈ K)]
            have hz : ∑ c ∈ univ.filter (fun c => c ∉ K),
                (if H.Adj v c then (1:ℝ) else 0) = 0 := by
              refine sum_eq_zero (fun c hc => ?_)
              rw [mem_filter] at hc
              have : ¬ H.Adj v c := by
                rintro ⟨_, h⟩; rw [mem_compl] at hv; tauto
              simp [this]
            rw [hz, add_zero, show univ.filter (fun c => c ∈ K) = K by ext; simp]
            refine sum_congr rfl (fun c hc => ?_)
            have hvK : v ∉ K := mem_compl.mp hv
            have hne : v ≠ c := fun h => hvK (h ▸ hc)
            have hiff : H.Adj v c ↔ 1 ≤ a P c v := by
              show (v ≠ c ∧ _) ↔ _
              rw [a_symm hP c v]; simp [hne, hvK, hc]
            by_cases h : 1 ≤ a P c v
            · rw [if_pos (hiff.mpr h), if_pos h]
            · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
        _ = Y := by rw [hY]; exact sum_comm
    linarith
  have hmax : ∑ i ∈ K, ∑ j ∈ Kᶜ, max (a P i j - 1) 0 = X - Y := by
    rw [hX, hY, ← sum_sub_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    rw [← sum_sub_distrib]
    refine sum_congr rfl (fun j _ => ?_)
    by_cases h : 1 ≤ a P i j
    · simp [h]
    · simp only [h, if_false, sub_zero]; push_neg at h
      exact max_eq_right (by linarith)
  rw [hmax]
  rw [hedge] at hKF
  linarith

/-- **Brouwer's conjecture**, assuming the Grone–Merris–Bai theorem. -/
theorem brouwer_of_GMB (hGMB : GroneMerrisBai V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) :
    topSum (G.isHermitian_lapMatrix ℝ) k ≤ G.edgeFinset.card + (k * (k + 1) / 2 : ℝ) := by
  classical
  set L := G.lapMatrix ℝ with hLdef
  have hL : L.IsHermitian := G.isHermitian_lapMatrix ℝ
  set n := Fintype.card V with hn
  set e := Fintype.equivOfCardEq (Fintype.card_fin n) with he
  let u : Fin n → V → ℝ := fun t => ev hL (e t)
  have hre : ∀ t, hL.eigenvalues (e t) = hL.eigenvalues₀ t := by
    intro t; simp [Matrix.IsHermitian.eigenvalues, he]
  have hnn : ∀ t, 0 ≤ hL.eigenvalues₀ t := fun t => by
    rw [← hre]; exact (G.posSemidef_lapMatrix ℝ).eigenvalues_nonneg _
  set J := univ.filter (fun t : Fin n => t.val < k ∧ 0 < hL.eigenvalues₀ t) with hJ
  let P : Matrix V V ℝ := fun a b => ∑ t ∈ J, u t a * u t b
  have hortho : ∀ t s, ∑ a, u t a * u s a = if t = s then 1 else 0 := by
    intro t s; simp only [u]; rw [ev_ortho]; simp [e.injective.eq_iff]
  have hsymL : ∀ a b, L a b = L b a := fun a b => by
    have := (G.isSymm_lapMatrix ℝ).apply a b
    rw [← hLdef] at this; exact this.symm
  have heig : ∀ t a, ∑ c, L a c * u t c = hL.eigenvalues₀ t * u t a := by
    intro t a; simp only [u]; rw [ev_eig, hre]
  have hsum0 : ∀ t ∈ J, ∑ a, u t a = 0 := by
    intro t ht
    have hpos := (mem_filter.mp ht).2.2
    have h1 : ∑ a, ∑ c, L a c * u t c = hL.eigenvalues₀ t * ∑ a, u t a := by
      simp_rw [heig, mul_sum]
    have hcol : ∀ c, ∑ a, L a c = 0 := by
      intro c
      have := congrFun (G.lapMatrix_mulVec_one_eq_zero ℝ) c
      simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one, Pi.zero_apply] at this
      rw [← this]; exact sum_congr rfl (fun a _ => hsymL a c)
    have h2 : ∑ a, ∑ c, L a c * u t c = 0 := by
      rw [sum_comm]
      refine sum_eq_zero (fun c _ => ?_)
      rw [← sum_mul, hcol c, zero_mul]
    rw [h2] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hpos.ne'
  have hP : IsProj P J.card := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j; exact sum_congr rfl (fun t _ => mul_comm _ _)
    · intro i j
      have e1 : ∀ l, P i l * P l j = ∑ t ∈ J, ∑ s ∈ J, u t i * u s j * (u t l * u s l) := by
        intro l; simp only [P]; rw [sum_mul_sum]
        exact sum_congr rfl (fun t _ => sum_congr rfl (fun s _ => by ring))
      rw [sum_congr rfl (fun l _ => e1 l), sum_comm]
      refine sum_congr rfl (fun t ht => ?_)
      rw [sum_comm]
      have e2 : ∀ s, ∑ l, u t i * u s j * (u t l * u s l) =
          if t = s then u t i * u s j else 0 := by
        intro s; rw [← mul_sum, hortho t s]; split_ifs <;> simp
      rw [sum_congr rfl (fun s _ => e2 s), sum_ite_eq]
      simp [ht]
    · intro i; simp only [P]; rw [sum_comm]
      exact sum_eq_zero (fun t ht => by rw [← mul_sum, hsum0 t ht, mul_zero])
    · simp only [P]; rw [sum_comm]
      rw [sum_congr rfl (fun t _ => by rw [hortho t t, if_pos rfl])]
      simp
  -- the trace of `P L` is the top eigenvalue sum
  have htr : ∑ a, ∑ b, P a b * L b a = ∑ t ∈ J, hL.eigenvalues₀ t := by
    have e1 : ∀ a, ∑ b, P a b * L b a = ∑ t ∈ J, hL.eigenvalues₀ t * (u t a * u t a) := by
      intro a
      simp only [P, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl (fun t _ => ?_)
      have := heig t a
      calc ∑ b, u t a * u t b * L b a = u t a * ∑ b, L a b * u t b := by
            rw [mul_sum]; exact sum_congr rfl (fun b _ => by rw [hsymL b a]; ring)
        _ = _ := by rw [this]; ring
    rw [sum_congr rfl (fun a _ => e1 a), sum_comm]
    refine sum_congr rfl (fun t _ => ?_)
    rw [← mul_sum, hortho t t, if_pos rfl, mul_one]
  have htop : topSum hL k = ∑ t ∈ J, hL.eigenvalues₀ t := by
    unfold topSum
    rw [← sum_filter_add_sum_filter_not _ (fun t => 0 < hL.eigenvalues₀ t)]
    have hz : ∑ t ∈ (univ.filter (fun t : Fin n => t.val < k)).filter
        (fun t => ¬ 0 < hL.eigenvalues₀ t), hL.eigenvalues₀ t = 0 := by
      refine sum_eq_zero (fun t ht => ?_)
      rw [mem_filter] at ht
      exact le_antisymm (not_lt.mp ht.2) (hnn t)
    rw [hz, add_zero, hJ, filter_filter]
  have hcut := cutHyp_of_GMB hGMB P J.card hP
  have h56 := lemma56 hP hcut
  have hJk : (J.card : ℝ) ≤ k := by
    have : J.card ≤ (univ.filter (fun t : Fin n => t.val < k)).card :=
      card_le_card (fun t ht => by
        rw [mem_filter] at ht ⊢; exact ⟨ht.1, ht.2.1⟩)
    rw [Fin.card_filter_val_lt] at this
    exact_mod_cast this.trans (min_le_right _ _)
  have hedges : ∑ a', ∑ b, (if G.Adj a' b then (1:ℝ) else 0) = 2 * G.edgeFinset.card := by
    have := G.sum_degrees_eq_twice_card_edges
    have h' : ∑ v, (G.degree v : ℝ) = 2 * G.edgeFinset.card := by exact_mod_cast this
    rw [← h']
    exact sum_congr rfl (fun v _ => (G.degree_eq_sum_if_adj (R := ℝ) v).symm)
  have hbound : ∑ a', ∑ b, (if G.Adj a' b then a P a' b else 0) ≤
      ∑ a', ∑ b, max (a P a' b - 1) 0 + ∑ a', ∑ b, (if G.Adj a' b then (1:ℝ) else 0) := by
    rw [← sum_add_distrib]
    refine sum_le_sum (fun i _ => ?_)
    rw [← sum_add_distrib]
    refine sum_le_sum (fun j _ => ?_)
    by_cases h : G.Adj i j
    · simp only [h, if_true]; linarith [le_max_left (a P i j - 1) 0]
    · simp only [h, if_false, add_zero]; exact le_max_right _ _
  have htl := trace_lap P hP.symm G
  rw [htr] at htl
  rw [htop, htl]
  have hJ0 : (0:ℝ) ≤ J.card := by positivity
  have hk2 : (J.card : ℝ) * (J.card + 1) ≤ k * (k + 1) := by nlinarith
  rw [hedges] at hbound
  linarith

end Brouwer
