/-
  Stage 2 infrastructure: Ky Fan's maximum principle (both halves) and its consequences
  (subadditivity and monotonicity of top-eigenvalue sums).
-/
import Brouwer.Spectral

open Finset Matrix

set_option linter.unusedSectionVars false

namespace Brouwer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The other half of Ky Fan: the projection onto the top `k` eigenvectors attains `topSum`.
It also has nonnegative trace against every positive semidefinite `B`. -/
theorem kyFan_attained {A : Matrix V V ℝ} (hA : A.IsHermitian) (k : ℕ)
    (hk : k ≤ Fintype.card V) :
    ∃ P : Matrix V V ℝ, (∀ i j, P i j = P j i) ∧ (∀ i j, ∑ l, P i l * P l j = P i j) ∧
      (∑ i, P i i = k) ∧ (∑ a, ∑ b, P a b * A b a = topSum hA k) ∧
      (∀ B : Matrix V V ℝ, (∀ i j, B i j = B j i) →
        (∀ x : V → ℝ, 0 ≤ ∑ a, ∑ b, x a * B a b * x b) → 0 ≤ ∑ a, ∑ b, P a b * B b a) := by
  classical
  set n := Fintype.card V with hn
  set e := Fintype.equivOfCardEq (Fintype.card_fin n) with he
  let u : Fin n → V → ℝ := fun t => ev hA (e t)
  have hre : ∀ t, hA.eigenvalues (e t) = hA.eigenvalues₀ t := by
    intro t; simp [Matrix.IsHermitian.eigenvalues, he]
  set J := univ.filter (fun t : Fin n => t.val < k) with hJ
  let P : Matrix V V ℝ := fun a b => ∑ t ∈ J, u t a * u t b
  have hortho : ∀ t s, ∑ a, u t a * u s a = if t = s then 1 else 0 := by
    intro t s; simp only [u]; rw [ev_ortho]; simp [e.injective.eq_iff]
  have heig : ∀ t a, ∑ c, A a c * u t c = hA.eigenvalues₀ t * u t a := by
    intro t a; simp only [u]; rw [ev_eig, hre]
  have hsymA : ∀ a b, A a b = A b a := fun a b => by
    have := congrFun (congrFun hA.eq b) a
    simpa using this
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
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
  · simp only [P]; rw [sum_comm]
    rw [sum_congr rfl (fun t _ => by rw [hortho t t, if_pos rfl])]
    simp only [sum_const, nsmul_eq_mul, mul_one, hJ]
    rw [Fin.card_filter_val_lt]; simp [hk]
  · have e1 : ∀ a, ∑ b, P a b * A b a = ∑ t ∈ J, hA.eigenvalues₀ t * (u t a * u t a) := by
      intro a
      simp only [P, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl (fun t _ => ?_)
      have := heig t a
      calc ∑ b, u t a * u t b * A b a = u t a * ∑ b, A a b * u t b := by
            rw [mul_sum]; exact sum_congr rfl (fun b _ => by rw [hsymA b a]; ring)
        _ = _ := by rw [this]; ring
    rw [sum_congr rfl (fun a _ => e1 a), sum_comm]
    unfold topSum
    refine sum_congr rfl (fun t _ => ?_)
    rw [← mul_sum, hortho t t, if_pos rfl, mul_one]
  · intro B hBs hB
    have e1 : ∀ a b, P a b * B b a = ∑ t ∈ J, u t a * B a b * u t b := by
      intro a b; simp only [P, sum_mul]
      exact sum_congr rfl (fun t _ => by rw [hBs b a]; ring)
    rw [sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => e1 a b))]
    rw [sum_congr rfl (fun a _ => sum_comm), sum_comm]
    exact sum_nonneg (fun t _ => hB (u t))

/-- Ky Fan subadditivity: `topSum (A + B) ≤ topSum A + topSum B`. -/
theorem topSum_add_le {A B : Matrix V V ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (A + B).IsHermitian) (k : ℕ) (hk : k ≤ Fintype.card V) :
    topSum hAB k ≤ topSum hA k + topSum hB k := by
  obtain ⟨P, hs, hi, htr, hval, -⟩ := kyFan_attained hAB k hk
  have h1 := kyFan hA P hs hi k htr
  have h2 := kyFan hB P hs hi k htr
  rw [← hval]
  have : ∑ a, ∑ b, P a b * (A + B) b a =
      ∑ a, ∑ b, P a b * A b a + ∑ a, ∑ b, P a b * B b a := by
    simp only [Matrix.add_apply, mul_add, sum_add_distrib]
  rw [this]; linarith

/-- Monotonicity: adding a positive semidefinite matrix does not decrease `topSum`. -/
theorem topSum_le_add_psd {A B : Matrix V V ℝ} (hA : A.IsHermitian)
    (hAB : (A + B).IsHermitian) (hBs : ∀ i j, B i j = B j i)
    (hB : ∀ x : V → ℝ, 0 ≤ ∑ a, ∑ b, x a * B a b * x b) (k : ℕ) (hk : k ≤ Fintype.card V) :
    topSum hA k ≤ topSum hAB k := by
  obtain ⟨P, hs, hi, htr, hval, hpsd⟩ := kyFan_attained hA k hk
  have h1 := kyFan hAB P hs hi k htr
  have h2 := hpsd B hBs hB
  rw [← hval]
  have : ∑ a, ∑ b, P a b * (A + B) b a =
      ∑ a, ∑ b, P a b * A b a + ∑ a, ∑ b, P a b * B b a := by
    simp only [Matrix.add_apply, mul_add, sum_add_distrib]
  linarith

end Brouwer
