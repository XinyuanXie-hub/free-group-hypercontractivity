module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».Representation
public import «free-group-hypercontractivity».Cancellation
public import «free-group-hypercontractivity».Shell
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Positivity

public section

namespace FreeGroupHypercontractivity

open Finset Cancellation
open scoped BigOperators

private theorem support_shell {n : ℕ} (k : ℕ) (x : GroupAlgebra n) :
    (shell k x).coeff.support = x.coeff.support.filter (fun g ↦ FreeGroup.norm g = k) := by
  classical
  ext g
  simp only [mem_filter, Finsupp.mem_support_iff, shell_coeff]
  split_ifs <;> simp_all

private theorem shell_sum {n N : ℕ} (x : GroupAlgebra n)
    (hx : ∀ g ∈ x.coeff.support, FreeGroup.norm g ≤ N) :
    x = ∑ k ∈ range (N + 1), shell k x := by
  classical
  apply MonoidAlgebra.coeff_injective
  ext g
  change x.coeff g = (∑ k ∈ range (N + 1), shell k x).coeff g
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, shell_coeff]
  rw [sum_ite_eq]
  split_ifs with hg
  · rfl
  · exact Finsupp.notMem_support_iff.mp (fun h ↦ hg (mem_range.mpr (by have := hx g h; omega)))

private theorem weighted_shell_sum {n N : ℕ} (x : GroupAlgebra n)
    (hx : ∀ g ∈ x.coeff.support, FreeGroup.norm g ≤ N) (w : ℕ → ℝ) :
    (∑ k ∈ range (N + 1), w k * coeffL2Sq (shell k x)) =
      ∑ g ∈ x.coeff.support, w (FreeGroup.norm g) * ‖x.coeff g‖ ^ 2 := by
  classical
  calc
    _ = ∑ k ∈ range (N + 1), ∑ g ∈ x.coeff.support.filter (fun g ↦ FreeGroup.norm g = k),
        w (FreeGroup.norm g) * ‖x.coeff g‖ ^ 2 := by
      apply sum_congr rfl
      intro k _
      rw [coeffL2Sq, support_shell, mul_sum]
      apply sum_congr rfl
      intro g hg
      have heq := (mem_filter.mp hg).2
      simp [heq]
    _ = _ := sum_fiberwise_of_maps_to (fun g hg ↦ mem_range.mpr (by have := hx g hg; omega)) _

private theorem shell_eq_zero {n k : ℕ} (x : GroupAlgebra n)
    (hk : ∀ g ∈ x.coeff.support, FreeGroup.norm g ≠ k) : shell k x = 0 := by
  apply MonoidAlgebra.coeff_injective
  ext g
  change (shell k x).coeff g = 0
  rw [shell_coeff]
  split_ifs with h
  · exact Finsupp.notMem_support_iff.mp (fun hg ↦ hk g hg h)
  · rfl

private theorem shell_zero_of_centered {n : ℕ} (x : GroupAlgebra n) (hx : x.coeff 1 = 0) :
    shell 0 x = 0 := by
  apply shell_eq_zero
  intro g hg h
  rw [FreeGroup.norm_eq_zero.mp h] at hg
  exact Finsupp.mem_support_iff.mp hg hx

private theorem trace_shell_product {n k : ℕ} (z w : GroupAlgebra n)
    (hw : Supported k w) :
    (z * w).coeff 1 = (shell k z * w).coeff 1 := by
  rw [MonoidAlgebra.coeff_mul_apply_right, MonoidAlgebra.coeff_mul_apply_right]
  simp only [Finsupp.sum, one_mul]
  apply sum_congr rfl
  intro g hg
  simp [FreeGroup.norm_inv_eq, hw g hg]

private theorem trace_coeff_mul_le {n k : ℕ} (z w : GroupAlgebra n)
    (hz : Supported k z) (hw : Supported k w) :
    ((z * w).coeff 1).re ≤ Real.sqrt (coeffL2Sq z) * Real.sqrt (coeffL2Sq w) := by
  classical
  rw [MonoidAlgebra.coeff_mul_apply_right]
  simp only [Finsupp.sum, one_mul]
  rw [coeffL2Sq_eq_sum_wordShell hz, coeffL2Sq_eq_sum_wordShell hw]
  have hreindex : (∑ g ∈ wordShell n k, ‖z.coeff g⁻¹‖ ^ 2) =
      ∑ g ∈ wordShell n k, ‖z.coeff g‖ ^ 2 := by
    apply sum_bij (fun g _ ↦ g⁻¹)
    · intro g hg
      simpa only [mem_wordShell, FreeGroup.norm_inv_eq] using hg
    · intro g _ h _ hgh
      exact inv_injective hgh
    · intro g hg
      refine ⟨g⁻¹, ?_, inv_inv g⟩
      simpa only [mem_wordShell, FreeGroup.norm_inv_eq] using hg
    · simp
  have hsum : (∑ g ∈ w.coeff.support, z.coeff g⁻¹ * w.coeff g) =
      ∑ g ∈ wordShell n k, z.coeff g⁻¹ * w.coeff g :=
    sum_subset (fun g hg ↦ mem_wordShell.mpr (hw g hg))
      (fun g _ hg ↦ by simp [Finsupp.notMem_support_iff.mp hg])
  rw [hsum]
  calc
    _ ≤ ‖∑ g ∈ wordShell n k, z.coeff g⁻¹ * w.coeff g‖ := Complex.re_le_norm _
    _ ≤ ∑ g ∈ wordShell n k, ‖z.coeff g⁻¹‖ * ‖w.coeff g‖ := by
      simpa only [norm_mul] using norm_sum_le (wordShell n k) (fun g ↦ z.coeff g⁻¹ * w.coeff g)
    _ ≤ _ := by
      rw [← hreindex]
      exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

private theorem triangle_parameter {i j k : ℕ} (h : Admissible i j k) :
    ∃ r s t : ℕ, r ≤ j ∧ s ≤ i ∧ t ≤ i ∧ i = s + t ∧ j = r + t ∧ k = r + s := by
  obtain ⟨d, hdi, hdj, hk⟩ := (admissible_iff_exists _ _ _).mp h
  exact ⟨j-d, i-d, d, by omega, by omega, hdi, by omega, by omega, by omega⟩

open Classical in
private theorem reindex_admissible (N : ℕ) (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) :
    (∑ i ∈ range (N+1), ∑ j ∈ range (N+1), ∑ k ∈ range (N+1),
      if Admissible i j k then b i * b j * b k else 0) ≤
      ∑ r ∈ range (N+1), ∑ s ∈ range (N+1), ∑ t ∈ range (N+1),
        b (s+t) * b (r+t) * b (r+s) := by
  classical
  let indices := range (N+1) ×ˢ (range (N+1) ×ˢ range (N+1))
  let valid (p : ℕ × ℕ × ℕ) := Admissible p.1 p.2.1 p.2.2
  let changeIndex (p : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
    ((p.2.1+p.2.2-p.1)/2, (p.1+p.2.2-p.2.1)/2, (p.1+p.2.1-p.2.2)/2)
  let weight (p : ℕ × ℕ × ℕ) := b (p.2.1 + p.2.2) * b (p.1 + p.2.2) * b (p.1 + p.2.1)
  let unchangeIndex (p : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
    (p.2.1 + p.2.2, p.1 + p.2.2, p.1 + p.2.1)
  have hrestore : ∀ p, valid p → unchangeIndex (changeIndex p) = p := by
    rintro ⟨i, j, k⟩ hp
    obtain ⟨r, s, t, _, _, _, hi, hj, hk⟩ := triangle_parameter (i := i) (j := j) (k := k) hp
    have hr : (j+k-i)/2 = r := by omega
    have hs : (i+k-j)/2 = s := by omega
    have ht : (i+j-k)/2 = t := by omega
    simp only [unchangeIndex, changeIndex, hr, hs, ht, ← hi, ← hj, ← hk]
  have hmaps : ∀ p ∈ indices.filter valid, changeIndex p ∈ indices := by
    rintro ⟨i, j, k⟩ hp
    simp only [mem_filter, indices, mem_product, mem_range, valid] at hp
    obtain ⟨r, s, t, hr, hs, ht, hi, hj, hk⟩ := triangle_parameter hp.2
    simp only [indices, mem_product, mem_range, changeIndex]
    exact ⟨by omega, by omega, by omega⟩
  have hbound : (∑ p ∈ indices.filter valid, b p.1 * b p.2.1 * b p.2.2) ≤
      ∑ p ∈ indices, weight p := by
    apply sum_le_sum_of_injOn changeIndex
    · intro p hp q hq h
      rw [← hrestore p (mem_filter.mp hp).2, ← hrestore q (mem_filter.mp hq).2, h]
    · intro p hp
      rcases mem_image.mp hp with ⟨q, hq, rfl⟩
      exact hmaps q hq
    · intro p hp
      change _ ≤ b ((unchangeIndex (changeIndex p)).1) *
        b ((unchangeIndex (changeIndex p)).2.1) * b ((unchangeIndex (changeIndex p)).2.2)
      rw [hrestore p (mem_filter.mp hp).2]
    · exact fun p _ _ ↦ mul_nonneg (mul_nonneg (hb _) (hb _)) (hb _)
  simpa only [indices, sum_filter, sum_product, valid, weight] using hbound

/-- The free-group third moment bound for centered Fourier polynomials. -/
theorem third_moment_bound {n : ℕ} (x : GroupAlgebra n) (hx : x.coeff 1 = 0) :
    traceRe (regularImage x ^ 3) ≤
      3 * (∑ g ∈ x.coeff.support, ‖x.coeff g‖^2) *
        Real.sqrt (∑ g ∈ x.coeff.support, ((FreeGroup.norm g - 1 : ℕ) : ℝ) * ‖x.coeff g‖^2) +
      (Real.sqrt (∑ g ∈ x.coeff.support,
        ((FreeGroup.norm g - 1 : ℕ) : ℝ) * ‖x.coeff g‖^2)) ^ 3 := by
  classical
  let N := x.coeff.support.sup FreeGroup.norm
  have hN (g) (hg : g ∈ x.coeff.support) : FreeGroup.norm g ≤ N := le_sup hg
  let b (k : ℕ) := Real.sqrt (coeffL2Sq (shell k x))
  have hb (k : ℕ) : 0 ≤ b k := Real.sqrt_nonneg _
  have hzero : b 0 = 0 := by
    simp [b, coeffL2Sq, shell_zero_of_centered _ hx]
  have hsupport (k : ℕ) (hk : N < k) : b k = 0 := by
    have heq := shell_eq_zero x (k := k) (fun g hg ↦ ne_of_lt ((hN g hg).trans_lt hk))
    simp [b, coeffL2Sq, heq]
  have hb_sq (k : ℕ) : b k ^ 2 = coeffL2Sq (shell k x) :=
    Real.sq_sqrt (coeffL2Sq_nonneg _)
  have htriple :
      traceRe (regularImage x ^ 3) =
        ∑ i ∈ range (N+1), ∑ j ∈ range (N+1), ∑ k ∈ range (N+1),
          (((shell i x * shell j x) * shell k x).coeff 1).re := by
    rw [pow_succ, pow_two, ← regularImage_mul, ← regularImage_mul, traceRe_regularImage]
    change Complex.reLm ((x * x * x).coeff 1) = _
    conv_lhs => rw [shell_sum x hN]
    simp only [sum_mul, mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_sum]
    let f (i j k : ℕ) := (((shell i x * shell j x) * shell k x).coeff 1).re
    change (∑ k ∈ range (N+1), ∑ j ∈ range (N+1), ∑ i ∈ range (N+1), f i j k) = _
    calc
      _ = ∑ k ∈ range (N+1), ∑ i ∈ range (N+1), ∑ j ∈ range (N+1), f i j k := by
        apply sum_congr rfl
        intro k _
        exact sum_comm
      _ = ∑ i ∈ range (N+1), ∑ k ∈ range (N+1), ∑ j ∈ range (N+1), f i j k := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro i _
        exact sum_comm
  rw [htriple]
  calc
    _ ≤ ∑ i ∈ range (N+1), ∑ j ∈ range (N+1), ∑ k ∈ range (N+1),
        if Admissible i j k then b i * b j * b k else 0 := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      apply sum_le_sum
      intro k _
      rw [trace_shell_product (shell i x * shell j x) (shell k x) (shell_supported _ _)]
      split_ifs with h
      · refine (trace_coeff_mul_le _ _ (shell_supported _ _) (shell_supported _ _)).trans ?_
        change Real.sqrt (coeffL2Sq (shell k (shell i x * shell j x))) * b k ≤ b i * b j * b k
        apply mul_le_mul_of_nonneg_right _ (hb _)
        exact (Real.sqrt_le_sqrt (shell_mul_coeffL2Sq_le
          (shell_supported i x) (shell_supported j x) k)).trans_eq
          (Real.sqrt_mul (coeffL2Sq_nonneg _) _)
      · rw [shell_mul_eq_zero_of_not_admissible (shell_supported _ _) (shell_supported _ _) h]
        simp
    _ ≤ _ := by
      refine (reindex_admissible N b hb).trans ?_
      have h := shell_cubic_bound N b hb hzero hsupport
      simp_rw [hb_sq] at h
      have hnorm := weighted_shell_sum x hN (fun _ ↦ (1 : ℝ))
      simp only [one_mul] at hnorm
      simpa only [hnorm, weighted_shell_sum x hN (fun k ↦ ((k - 1 : ℕ) : ℝ))] using h

end FreeGroupHypercontractivity
