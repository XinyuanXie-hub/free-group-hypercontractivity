module

public import Template.Model
public import Template.CancellationWords
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

public section

namespace FreeGroupHypercontractivity

open scoped BigOperators
open Finset
open FreeGroup Cancellation

variable {ι α : Type*} [DecidableEq α]

/-- Multiplying a positive kernel entrywise by the Hamming kernel preserves
positivity. This is the finite Schur multiplier estimate for word length. -/
theorem hamming_schur_nonneg (s : Finset ι) (edges : Finset α) (A : ι → Finset α)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (K : ι → ι → ℂ)
    (hK : ∀ c : ι → ℂ, 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (star (c i) * K i j * c j).re)
    (c : ι → ℂ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, (star (c i) * K i j * c j).re *
      (∏ e ∈ edges, if (e ∈ A i ↔ e ∈ A j) then 1 else ρ) := by
  classical
  induction edges using Finset.induction_on generalizing c with
  | empty => simpa using hK c
  | @insert e E he ih =>
    let c₁ (i : ι) : ℂ := if e ∈ A i then c i else 0
    let c₀ (i : ι) : ℂ := if e ∈ A i then 0 else c i
    let W (i j : ι) : ℝ := ∏ d ∈ E, if (d ∈ A i ↔ d ∈ A j) then 1 else ρ
    have hpoint (i j : ι) :
        (star (c i) * K i j * c j).re *
          (∏ d ∈ insert e E, if (d ∈ A i ↔ d ∈ A j) then 1 else ρ) =
        ρ * ((star (c i) * K i j * c j).re * W i j) +
          (1 - ρ) * ((star (c₁ i) * K i j * c₁ j).re * W i j +
            (star (c₀ i) * K i j * c₀ j).re * W i j) := by
      rw [Finset.prod_insert he]
      by_cases hi : e ∈ A i <;> by_cases hj : e ∈ A j <;>
        simp only [hi, hj, iff_self, iff_true, iff_false, not_true_eq_false,
          ite_true, ite_false, c₁, c₀, star_zero, zero_mul, mul_zero, Complex.zero_re, add_zero,
          zero_add] <;> dsimp [W] <;> ring
    simp only [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
    exact add_nonneg (mul_nonneg hρ (ih c))
      (mul_nonneg (sub_nonneg.mpr hρ₁) (add_nonneg (ih c₁) (ih c₀)))

private theorem card_inits (u : List α) : u.inits.toFinset.card = u.length + 1 := by
  rw [List.toFinset_card_of_nodup, List.length_inits]
  induction u with
  | nil => simp
  | cons a u ih =>
    change ([] :: List.map (a :: ·) u.inits).Nodup
    rw [List.nodup_cons]
    exact ⟨by simp, ih.map List.cons_injective⟩

private theorem common_inits {s r t : List α}
    (hrt : ∀ a ∈ r.head?, ∀ b ∈ t.head?, a ≠ b) :
    (s ++ r).inits.toFinset ∩ (s ++ t).inits.toFinset = s.inits.toFinset := by
  ext u
  simp only [Finset.mem_inter, List.mem_toFinset, List.mem_inits]
  constructor
  · rintro ⟨hr, ht⟩
    by_contra h
    obtain ⟨u', hu'⟩ := (List.prefix_or_prefix_of_prefix hr (List.prefix_append s r)).resolve_left h
    subst u
    have hr' : u' <+: r := by simpa using hr
    have ht' : u' <+: t := by simpa using ht
    cases u' with
    | nil => exact h (by simp)
    | cons a u' =>
      obtain ⟨r', rfl⟩ := hr'
      obtain ⟨t', rfl⟩ := ht'
      exact hrt a (by simp) a (by simp) rfl
  · intro hu
    exact ⟨hu.trans (List.prefix_append s r), hu.trans (List.prefix_append s t)⟩

/-- The number of edges present on exactly one of two reduced word paths is
the word length of the relative group element. Prefixes include the empty
word, whose common membership contributes zero. -/
theorem word_length_eq_prefix_hamming {n : ℕ} (g h : Group n) :
    let A := g.toWord.inits.toFinset
    let B := h.toWord.inits.toFinset
    (A \ B).card + (B \ A).card = FreeGroup.norm (g⁻¹ * h) := by
  obtain ⟨s, r, t, hg, hh, hrt⟩ := exists_common_prefix g.toWord h.toWord
  dsimp only
  rw [hg, hh, Finset.card_sdiff, Finset.card_sdiff,
    Finset.inter_comm (s ++ t).inits.toFinset (s ++ r).inits.toFinset,
    common_inits hrt]
  simp only [card_inits, List.length_append]
  have hr : IsReduced r := (hg ▸ FreeGroup.isReduced_toWord).right_of_append
  have ht : IsReduced t := (hh ▸ FreeGroup.isReduced_toWord).right_of_append
  have hg' : g = FreeGroup.mk s * FreeGroup.mk r := by
    rw [← mk_toWord (x := g), hg, mul_mk]
  have hh' : h = FreeGroup.mk s * FreeGroup.mk t := by
    rw [← mk_toWord (x := h), hh, mul_mk]
  have hprod : g⁻¹ * h = (FreeGroup.mk r)⁻¹ * FreeGroup.mk t := by
    rw [hg', hh', mul_inv_rev]
    simp only [mul_assoc, inv_mul_cancel_left]
  have hrs : FreeGroup.norm (g⁻¹ * h) = r.length + t.length := by
    rw [hprod, inv_mk, mul_mk, FreeGroup.norm, toWord_mk,
      (uncancelled_append hr ht hrt).reduce_eq, List.length_append, invRev_length]
  omega


/-- The restriction of the Poisson kernel to a finite set of basis vectors
preserves positive semidefiniteness under entrywise multiplication. -/
theorem poisson_schur_nonneg {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (s : Finset ι) (g : ι → Group n)
    (K : ι → ι → ℂ)
    (hK : ∀ c : ι → ℂ, 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (star (c i) * K i j * c j).re)
    (c : ι → ℂ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, (star (c i) * K i j * c j).re *
      Real.exp (-t * (FreeGroup.norm (g i * (g j)⁻¹) : ℝ)) := by
  classical
  let A (i : ι) := (g i)⁻¹.toWord.inits.toFinset
  let E := s.biUnion A
  have hprod (i j : ι) (hi : i ∈ s) (hj : j ∈ s) :
      (∏ e ∈ E, if (e ∈ A i ↔ e ∈ A j) then 1 else Real.exp (-t)) =
        Real.exp (-t * (FreeGroup.norm (g i * (g j)⁻¹) : ℝ)) := by
    have hs : Disjoint (A i \ A j) (A j \ A i) := by
      rw [Finset.disjoint_left]
      intro e he₁ he₂
      exact (Finset.mem_sdiff.mp he₁).2 (Finset.mem_sdiff.mp he₂).1
    have hfilter : E.filter (fun e ↦ ¬(e ∈ A i ↔ e ∈ A j)) =
        (A i \ A j) ∪ (A j \ A i) := by
      ext e
      dsimp [E]
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · tauto
      · rintro (h | h)
        · exact ⟨⟨i, hi, h.1⟩, by tauto⟩
        · exact ⟨⟨j, hj, h.1⟩, by tauto⟩
    have hcard : (A i \ A j).card + (A j \ A i).card = FreeGroup.norm (g i * (g j)⁻¹) := by
      simpa only [A, inv_inv] using word_length_eq_prefix_hamming (g i)⁻¹ (g j)⁻¹
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, hfilter,
      Finset.card_union_of_disjoint hs, hcard, ← Real.exp_nat_mul, mul_comm]
  have h := hamming_schur_nonneg s E A (Real.exp (-t)) (Real.exp_nonneg _) (by
    rw [Real.exp_le_one_iff]; linarith) K hK c
  refine le_trans h (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hprod i j hi hj]

end FreeGroupHypercontractivity
