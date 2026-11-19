module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

public section

namespace FreeGroupHypercontractivity

open Finset
open scoped BigOperators

private theorem hankel_sum_sq_le (N : ℕ) (b : ℕ → ℝ)
    (hsupport : ∀ i, N < i → b i = 0) :
    (∑ r ∈ range N, ∑ s ∈ range N, b (r + 1 + (s + 1)) ^ 2) ≤
      ∑ i ∈ range (N + 1), ((i - 1 : ℕ) : ℝ) * b i ^ 2 := by
  classical
  let pairs := range N ×ˢ range N
  let degree (p : ℕ × ℕ) := p.1 + 1 + (p.2 + 1)
  let target := (range (N + 1)).sigma (fun i : ℕ ↦ range (i - 1))
  rw [← sum_product (f := fun p : ℕ × ℕ ↦ b (degree p) ^ 2)]
  change (∑ p ∈ pairs, b (degree p) ^ 2) ≤ _
  rw [← sum_filter_add_sum_filter_not pairs (fun p ↦ degree p ≤ N)]
  have hzero : (∑ p ∈ pairs.filter (fun p ↦ ¬ degree p ≤ N), b (degree p) ^ 2) = 0 := by
    apply sum_eq_zero
    intro p hp
    simp only [mem_filter, not_le] at hp
    rw [hsupport _ hp.2, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  rw [hzero, add_zero]
  calc
    _ ≤ ∑ q ∈ target, b q.1 ^ 2 := by
      apply sum_le_sum_of_injOn (fun p ↦ ⟨degree p, p.1⟩)
      · intro p _ q _ h
        have hi : degree p = degree q := congrArg Sigma.fst h
        have hj : p.1 = q.1 := congrArg (fun a : Sigma (fun _ : ℕ ↦ ℕ) ↦ a.2) h
        dsimp [degree] at hi
        exact Prod.ext hj (by omega)
      · intro q hq
        rcases mem_image.mp hq with ⟨p, hp, rfl⟩
        simp only [target, mem_sigma, mem_range]
        have h := (mem_filter.mp hp).2
        exact ⟨by omega, by dsimp [degree]; omega⟩
      · intro p _
        exact le_rfl
      · intro q _ _
        positivity
    _ = _ := by
      simp [target, sum_sigma, nsmul_eq_mul]

private theorem sum_mul_hankel_le (N : ℕ) (b : ℕ → ℝ) :
    (∑ r ∈ range N, ∑ s ∈ range N, b (r+1) * b (s+1) * b (r+1+(s+1))) ≤
      (∑ r ∈ range N, b (r+1) ^ 2) *
        Real.sqrt (∑ r ∈ range N, ∑ s ∈ range N, b (r+1+(s+1)) ^ 2) := by
  rw [← sum_product (f := fun p : ℕ × ℕ ↦ b (p.1+1) * b (p.2+1) * b (p.1+1+(p.2+1))),
    ← sum_product (f := fun p : ℕ × ℕ ↦ b (p.1+1+(p.2+1)) ^ 2)]
  refine (Real.sum_mul_le_sqrt_mul_sqrt (range N ×ˢ range N)
    (fun p ↦ b (p.1+1) * b (p.2+1)) (fun p ↦ b (p.1+1+(p.2+1)))).trans ?_
  rw [sum_product]
  simp_rw [mul_pow, ← mul_sum]
  rw [← sum_mul, ← pow_two, Real.sqrt_sq (sum_nonneg fun _ _ ↦ sq_nonneg _)]

private theorem sum_triangle_le (I : Finset ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ i j, 0 ≤ c i j) :
    (∑ r ∈ I, ∑ s ∈ I, ∑ t ∈ I, c s t * c r t * c r s) ≤
      (Real.sqrt (∑ r ∈ I, ∑ s ∈ I, c r s ^ 2)) ^ 3 := by
  let row (i : ℕ) := Real.sqrt (∑ j ∈ I, c i j ^ 2)
  calc
    _ ≤ ∑ r ∈ I, ∑ s ∈ I, row s * row r * c r s := by
      apply sum_le_sum
      intro r _
      apply sum_le_sum
      intro s _
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (Real.sum_mul_le_sqrt_mul_sqrt I (c s) (c r)) (hc r s)
    _ ≤ Real.sqrt (∑ p ∈ I ×ˢ I, (row p.2 * row p.1) ^ 2) *
        Real.sqrt (∑ p ∈ I ×ˢ I, c p.1 p.2 ^ 2) := by
      rw [← sum_product (f := fun p : ℕ × ℕ ↦ row p.2 * row p.1 * c p.1 p.2)]
      exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      rw [sum_product, sum_product]
      simp_rw [mul_pow, ← sum_mul]
      rw [← mul_sum, ← pow_two, Real.sqrt_sq (sum_nonneg fun _ _ ↦ sq_nonneg _)]
      dsimp only [row]
      simp_rw [Real.sq_sqrt (sum_nonneg fun _ _ ↦ sq_nonneg _)]
      nth_rw 1 [← Real.sq_sqrt (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg (c _ _))]
      ring

/-- The numerical third-moment bound, using the cancellation lengths
for the admissible shell triples. -/
theorem shell_cubic_bound (N : ℕ) (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) (hzero : b 0 = 0)
    (hsupport : ∀ i, N < i → b i = 0) :
    (∑ r ∈ range (N + 1), ∑ s ∈ range (N + 1), ∑ t ∈ range (N + 1),
      b (s + t) * b (r + t) * b (r + s)) ≤
      3 * (∑ i ∈ range (N + 1), b i ^ 2) *
        Real.sqrt (∑ i ∈ range (N + 1), ((i - 1 : ℕ) : ℝ) * b i ^ 2) +
        (Real.sqrt (∑ i ∈ range (N + 1), ((i - 1 : ℕ) : ℝ) * b i ^ 2)) ^ 3 := by
  let first := ∑ r ∈ range N, ∑ s ∈ range N, b (r+1) * b (s+1) * b (r+1+(s+1))
  let second := ∑ r ∈ range N, ∑ s ∈ range N, ∑ t ∈ range N,
    b (s+1+(t+1)) * b (r+1+(t+1)) * b (r+1+(s+1))
  let H := Real.sqrt (∑ r ∈ range N, ∑ s ∈ range N, b (r+1+(s+1)) ^ 2)
  let Q := Real.sqrt (∑ i ∈ range (N + 1), ((i - 1 : ℕ) : ℝ) * b i ^ 2)
  have hHQ : H ≤ Q := Real.sqrt_le_sqrt (hankel_sum_sq_le N b hsupport)
  have hfirst : first ≤ (∑ i ∈ range (N + 1), b i ^ 2) * Q := by
    rw [sum_range_succ', hzero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
    exact (sum_mul_hankel_le N b).trans (mul_le_mul_of_nonneg_left hHQ
      (sum_nonneg fun _ _ ↦ sq_nonneg _))
  have hsecond : second ≤ Q ^ 3 :=
    (sum_triangle_le (range N) (fun i j ↦ b (i+1+(j+1))) (fun _ _ ↦ hb _)).trans
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) hHQ 3)
  calc
    _ = 3 * first + second := by
      simp only [sum_range_succ', Nat.zero_add, hzero, mul_zero, zero_mul,
        sum_const_zero, add_zero, sum_add_distrib]
      dsimp only [first, second]
      simp only [mul_comm, mul_left_comm]
      ring
    _ ≤ _ := by
      linear_combination 3 * hfirst + hsecond

end FreeGroupHypercontractivity
