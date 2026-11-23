/-
  Stage 2 infrastructure: Courant–Fischer type bounds for individual eigenvalues,
  via a dimension count against the span of eigenvectors.
-/
import Brouwer.Stage2.KyFan

open Finset Matrix Module

set_option linter.unusedSectionVars false

namespace Brouwer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Quadratic form and squared norm, as plain sums. -/
def qf (A : Matrix V V ℝ) (x : V → ℝ) : ℝ := ∑ a, ∑ b, x a * A a b * x b
def nsq (x : V → ℝ) : ℝ := ∑ a, x a * x a

section CF

variable {A : Matrix V V ℝ} (hA : A.IsHermitian)

/-- Sorted eigenvectors. -/
noncomputable def sev (t : Fin (Fintype.card V)) : V → ℝ :=
  ev hA (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V)) t)

lemma sev_ortho (t s : Fin (Fintype.card V)) :
    ∑ a, sev hA t a * sev hA s a = if t = s then 1 else 0 := by
  unfold sev; rw [ev_ortho]; simp [(Fintype.equivOfCardEq _).injective.eq_iff]

lemma sev_eig (t : Fin (Fintype.card V)) (a : V) :
    ∑ c, A a c * sev hA t c = hA.eigenvalues₀ t * sev hA t a := by
  unfold sev; rw [ev_eig]; simp [Matrix.IsHermitian.eigenvalues]

/-- Quadratic form and norm of a combination of sorted eigenvectors. -/
lemma qf_comb (c : Fin (Fintype.card V) → ℝ) :
    qf A (∑ t, c t • sev hA t) = ∑ t, hA.eigenvalues₀ t * c t ^ 2 := by
  unfold qf
  have hx : ∀ a, (∑ t, c t • sev hA t) a = ∑ t, c t * sev hA t a := by
    intro a; simp [Finset.sum_apply]
  simp_rw [hx]
  have h1 : ∀ a, ∑ b, (∑ t, c t * sev hA t a) * A a b * (∑ s, c s * sev hA s b) =
      (∑ t, c t * sev hA t a) * ∑ s, c s * (hA.eigenvalues₀ s * sev hA s a) := by
    intro a
    rw [mul_sum]
    simp_rw [← sev_eig hA, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl (fun s _ => ?_)
    exact sum_congr rfl (fun b _ => by ring)
  simp_rw [h1, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun t _ => ?_)
  rw [sum_comm]
  have h2 : ∀ s, ∑ a, c t * sev hA t a * (c s * (hA.eigenvalues₀ s * sev hA s a)) =
      if t = s then hA.eigenvalues₀ t * c t ^ 2 else 0 := by
    intro s
    have : ∑ a, c t * sev hA t a * (c s * (hA.eigenvalues₀ s * sev hA s a)) =
        c t * c s * hA.eigenvalues₀ s * ∑ a, sev hA t a * sev hA s a := by
      rw [mul_sum]; exact sum_congr rfl (fun a _ => by ring)
    rw [this, sev_ortho]; split_ifs with h <;> [subst h; skip] <;> ring
  rw [sum_congr rfl (fun s _ => h2 s)]; simp

lemma nsq_comb (c : Fin (Fintype.card V) → ℝ) :
    nsq (∑ t, c t • sev hA t) = ∑ t, c t ^ 2 := by
  unfold nsq
  have hx : ∀ a, (∑ t, c t • sev hA t) a = ∑ t, c t * sev hA t a := by
    intro a; simp [Finset.sum_apply]
  simp_rw [hx, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun t _ => ?_)
  rw [sum_comm]
  have h2 : ∀ s, ∑ a, c t * sev hA t a * (c s * sev hA s a) =
      if t = s then c t ^ 2 else 0 := by
    intro s
    have : ∑ a, c t * sev hA t a * (c s * sev hA s a) =
        c t * c s * ∑ a, sev hA t a * sev hA s a := by
      rw [mul_sum]; exact sum_congr rfl (fun a _ => by ring)
    rw [this, sev_ortho]; split_ifs with h <;> [subst h; skip] <;> ring
  rw [sum_congr rfl (fun s _ => h2 s)]; simp

/-- Span of the sorted eigenvectors indexed by `p`. -/
noncomputable def espan (p : Fin (Fintype.card V) → Prop) : Submodule ℝ (V → ℝ) :=
  Submodule.span ℝ (Set.range (fun t : {t // p t} => sev hA t.val))

lemma sev_linInd (p : Fin (Fintype.card V) → Prop) :
    LinearIndependent ℝ (fun t : {t // p t} => sev hA t.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg s
  have h := congrArg (fun x : V → ℝ => ∑ a, x a * sev hA s.val a) hg
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul,
    sum_const_zero, sum_mul] at h
  rw [sum_comm] at h
  have e : ∀ i : {t // p t}, ∑ a, g i * sev hA i.val a * sev hA s.val a =
      if i = s then g i else 0 := by
    intro i
    have : ∑ a, g i * sev hA i.val a * sev hA s.val a =
        g i * ∑ a, sev hA i.val a * sev hA s.val a := by
      rw [mul_sum]; exact sum_congr rfl (fun a _ => by ring)
    rw [this, sev_ortho]
    by_cases hi : i = s
    · subst hi; simp
    · have : i.val ≠ s.val := fun h => hi (Subtype.ext h)
      simp [hi, this]
  rw [sum_congr rfl (fun i _ => e i)] at h
  simpa using h

lemma finrank_espan (p : Fin (Fintype.card V) → Prop) [DecidablePred p] :
    finrank ℝ (espan hA p) = (univ.filter p).card := by
  unfold espan
  rw [finrank_span_eq_card (sev_linInd hA p), Fintype.card_subtype]

lemma mem_espan (p : Fin (Fintype.card V) → Prop) [DecidablePred p] {x : V → ℝ}
    (hx : x ∈ espan hA p) :
    ∃ c : Fin (Fintype.card V) → ℝ, (∀ t, ¬ p t → c t = 0) ∧ x = ∑ t, c t • sev hA t := by
  unfold espan at hx
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c', hc'⟩ := hx
  refine ⟨fun t => if h : p t then c' ⟨t, h⟩ else 0, fun t ht => by simp [ht], ?_⟩
  rw [← hc', ← Fintype.sum_subtype_add_sum_subtype p]
  have hz : ∑ t : {t // ¬ p t}, (fun t => if h : p t then c' ⟨t, h⟩ else 0) t.val •
      sev hA t.val = 0 := by
    refine sum_eq_zero (fun t _ => ?_)
    simp [t.2]
  rw [hz, add_zero]
  refine sum_congr rfl (fun t _ => ?_)
  simp [t.2]

lemma nsq_pos {x : V → ℝ} (hx : x ≠ 0) : 0 < nsq x := by
  unfold nsq
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hx
  have hpos : 0 < x a * x a := mul_self_pos.mpr ha
  calc 0 < x a * x a := hpos
    _ ≤ ∑ b, x b * x b :=
      single_le_sum (f := fun b => x b * x b) (fun b _ => mul_self_nonneg _) (mem_univ a)

/-- Intersection of a subspace with an eigen-span, by dimension count. -/
lemma exists_common (W E : Submodule ℝ (V → ℝ))
    (h : Fintype.card V < finrank ℝ W + finrank ℝ E) :
    ∃ x, x ∈ W ∧ x ∈ E ∧ x ≠ 0 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W E
  have h2 : finrank ℝ ↥(W ⊔ E) ≤ Fintype.card V := by
    have := Submodule.finrank_le (W ⊔ E)
    simpa [Module.finrank_fintype_fun_eq_card] using this
  have h3 : W ⊓ E ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at h1
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h3
  exact ⟨x, (Submodule.mem_inf.mp hx).1, (Submodule.mem_inf.mp hx).2, hx0⟩

/-- Courant–Fischer, upper bound: if `xᵀAx ≤ c‖x‖²` on a subspace `W` with
`dim W + k > n`, then the `k`-th largest eigenvalue is `≤ c`. -/
theorem eig_le_of_subspace (k : Fin (Fintype.card V)) (W : Submodule ℝ (V → ℝ)) (c : ℝ)
    (hW : ∀ x ∈ W, qf A x ≤ c * nsq x)
    (hdim : Fintype.card V < finrank ℝ W + (k.val + 1)) :
    hA.eigenvalues₀ k ≤ c := by
  classical
  have hE : finrank ℝ (espan hA (fun t => t ≤ k)) = k.val + 1 := by
    rw [finrank_espan]
    have : univ.filter (fun t : Fin (Fintype.card V) => t ≤ k) =
        univ.filter (fun t : Fin (Fintype.card V) => t.val < k.val + 1) := by
      ext t; simp only [mem_filter, mem_univ, true_and, Fin.le_iff_val_le_val]; omega
    rw [this, Fin.card_filter_val_lt]; omega
  obtain ⟨x, hxW, hxE, hx0⟩ := exists_common W _ (by rw [hE]; exact hdim)
  obtain ⟨cf, hcf, rfl⟩ := mem_espan hA _ hxE
  have hq := hW _ hxW
  rw [qf_comb] at hq
  have hn := nsq_pos hx0
  rw [nsq_comb] at hn hq
  have hlow : hA.eigenvalues₀ k * ∑ t, cf t ^ 2 ≤ ∑ t, hA.eigenvalues₀ t * cf t ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum (fun t _ => ?_)
    by_cases ht : t ≤ k
    · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone ht) (sq_nonneg _)
    · rw [hcf t ht]; simp
  by_contra hcon
  push Not at hcon
  nlinarith

/-- Courant–Fischer, lower bound: if `c‖x‖² ≤ xᵀAx` on a subspace `W` with `dim W ≥ k`,
then the `k`-th largest eigenvalue is `≥ c`. -/
theorem le_eig_of_subspace (k : Fin (Fintype.card V)) (W : Submodule ℝ (V → ℝ)) (c : ℝ)
    (hW : ∀ x ∈ W, c * nsq x ≤ qf A x)
    (hdim : k.val + 1 ≤ finrank ℝ W) :
    c ≤ hA.eigenvalues₀ k := by
  classical
  have hE : finrank ℝ (espan hA (fun t => k ≤ t)) = Fintype.card V - k.val := by
    rw [finrank_espan]
    have h1 : (univ.filter (fun t : Fin (Fintype.card V) => k ≤ t)).card +
        (univ.filter (fun t : Fin (Fintype.card V) => ¬ k ≤ t)).card = Fintype.card V := by
      rw [card_filter_add_card_filter_not]; simp
    have h2 : univ.filter (fun t : Fin (Fintype.card V) => ¬ k ≤ t) =
        univ.filter (fun t : Fin (Fintype.card V) => t.val < k.val) := by
      ext t; simp only [mem_filter, mem_univ, true_and, Fin.le_iff_val_le_val]; omega
    rw [h2, Fin.card_filter_val_lt] at h1
    have := k.isLt
    omega
  obtain ⟨x, hxW, hxE, hx0⟩ := exists_common W _ (by rw [hE]; have := k.isLt; omega)
  obtain ⟨cf, hcf, rfl⟩ := mem_espan hA _ hxE
  have hq := hW _ hxW
  rw [qf_comb] at hq
  have hn := nsq_pos hx0
  rw [nsq_comb] at hn hq
  have hup : ∑ t, hA.eigenvalues₀ t * cf t ^ 2 ≤ hA.eigenvalues₀ k * ∑ t, cf t ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum (fun t _ => ?_)
    by_cases ht : k ≤ t
    · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone ht) (sq_nonneg _)
    · rw [hcf t ht]; simp
  by_contra hcon
  push Not at hcon
  nlinarith

end CF

end Brouwer
