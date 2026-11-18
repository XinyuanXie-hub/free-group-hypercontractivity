module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

namespace FreeGroupHypercontractivity

open Finset
open scoped BigOperators

variable {X : Type*} [MetricSpace X] [CompactSpace X]

private noncomputable def spectralInterpolate (s : Finset X) (w : X → C(X, ℝ))
    (f : C(X, ℝ)) : C(X, ℝ) :=
  ∑ i ∈ s, f i • w i

omit [CompactSpace X] in
private theorem eval_sum (s : Finset X) (w : X → C(X, ℝ)) (x : X) :
    (∑ i ∈ s, w i) x = ∑ i ∈ s, w i x := by
  exact map_sum (ContinuousMap.evalCLM ℝ x) _ _

private theorem spectralInterpolate_dist_le (s : Finset X) (w : X → C(X, ℝ))
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : (∑ i ∈ s, w i) = 1) (f : C(X, ℝ))
    {ε δ : ℝ} (hε : 0 ≤ ε) (hz : ∀ i ∈ s, ∀ x, δ ≤ dist x i → w i x = 0)
    (hf : ∀ x i : X, dist x i < δ → dist (f x) (f i) ≤ ε) :
    dist f (spectralInterpolate s w f) ≤ ε := by
  rw [dist_comm, ContinuousMap.dist_le hε]
  intro x
  have hone : (∑ i ∈ s, w i x) = 1 := by
    simpa only [eval_sum, ContinuousMap.one_apply] using
      congrArg (fun F : C(X, ℝ) ↦ F x) hsum
  have hfun : spectralInterpolate s w f x - f x =
      ∑ i ∈ s, (f i - f x) * w i x := by
    simp only [spectralInterpolate, eval_sum, ContinuousMap.smul_apply,
      smul_eq_mul, sub_mul, sum_sub_distrib, ← mul_sum, hone, mul_one]
  rw [Real.dist_eq, hfun]
  calc
    _ ≤ ∑ i ∈ s, |(f i - f x) * w i x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, ε * w i x := by
      apply sum_le_sum
      intro i hi
      have hn : 0 ≤ w i x := by
        simpa only [ContinuousMap.zero_apply] using (ContinuousMap.le_def.mp (hw i hi)) x
      rw [abs_mul, abs_of_nonneg hn]
      by_cases h : dist x i < δ
      · apply mul_le_mul_of_nonneg_right _ hn
        simpa only [Real.dist_eq, abs_sub_comm] using hf x i h
      · simp [hz i hi x (le_of_not_gt h)]
    _ = ε := by rw [← mul_sum, hone, mul_one]

variable (B : C(X, ℝ) →ₗ[ℝ] C(X, ℝ) →ₗ[ℝ] ℝ)

omit [CompactSpace X] in
private theorem pairing_spectralInterpolate (s : Finset X) (w : X → C(X, ℝ))
    (f g : C(X, ℝ)) :
    B (spectralInterpolate s w f) (spectralInterpolate s w g) =
      ∑ i ∈ s, ∑ j ∈ s, f i * g j * B (w i) (w j) := by
  have heval (h : X → C(X, ℝ) →ₗ[ℝ] ℝ) (F : C(X, ℝ)) :
      (∑ i ∈ s, h i) F = ∑ i ∈ s, h i F :=
    map_sum (LinearMap.applyₗ (R := ℝ) F) _ _
  simp only [spectralInterpolate, map_sum, map_smul, heval, LinearMap.smul_apply,
    smul_eq_mul]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

omit [CompactSpace X] in
private theorem pairing_spectralInterpolate_energy (hBsym : ∀ f g, B f g = B g f)
    (s : Finset X) (w : X → C(X, ℝ)) (hsum : (∑ i ∈ s, w i) = 1) (f g : C(X, ℝ)) :
    2 * (B (spectralInterpolate s w (f * g)) 1 -
      B (spectralInterpolate s w f) (spectralInterpolate s w g)) =
        ∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (g i - g j) * B (w i) (w j) := by
  have hone : spectralInterpolate s w 1 = 1 := by simp [spectralInterpolate, hsum]
  have hdiag : B (spectralInterpolate s w (f * g)) 1 =
      ∑ i ∈ s, ∑ j ∈ s, f i * g i * B (w i) (w j) := by
    rw [← hone, pairing_spectralInterpolate]
    simp only [ContinuousMap.mul_apply, ContinuousMap.one_apply, mul_one]
  have hswap (F : X → X → ℝ) : (∑ i ∈ s, ∑ j ∈ s, F j i * B (w i) (w j)) =
      ∑ i ∈ s, ∑ j ∈ s, F i j * B (w i) (w j) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [hBsym (w j) (w i)]
  rw [hdiag, pairing_spectralInterpolate]
  have hpoint (i j : X) :
      (f i - f j) * (g i - g j) * B (w i) (w j) =
        f i * g i * B (w i) (w j) - f i * g j * B (w i) (w j) -
        f j * g i * B (w i) (w j) + f j * g j * B (w i) (w j) := by ring
  simp only [hpoint, sum_add_distrib, sum_sub_distrib,
    hswap (fun i _ ↦ f i * g i), hswap (fun i j ↦ f i * g j)]
  ring

/-- Transfer a pointwise two-variable inequality to the energies of a
positive symmetric bilinear pairing on continuous functions. -/
theorem spectralPairing_energy_le_of_grid
    (hgrid : ∀ δ > 0, ∃ s : Finset X, ∃ w : X → C(X, ℝ),
      (∀ i ∈ s, 0 ≤ w i) ∧ (∑ i ∈ s, w i) = 1 ∧
        ∀ i ∈ s, ∀ x, δ ≤ dist x i → w i x = 0)
    (hBcont : Continuous (fun p : C(X, ℝ) × C(X, ℝ) ↦ B p.1 p.2))
    (hBsym : ∀ f g, B f g = B g f)
    (hBpos : ∀ f g, 0 ≤ f → 0 ≤ g → 0 ≤ B f g)
    (a d : ℝ) (f g u v : C(X, ℝ))
    (hpoint : ∀ x y : X,
      a * (f x - f y) * (g x - g y) ≤ d * (u x - u y) * (v x - v y)) :
    a * (B (f * g) 1 - B f g) ≤ d * (B (u * v) 1 - B u v) := by
  let F : Fin 6 → C(X, ℝ) := ![f, g, u, v, f * g, u * v]
  let L (H : Fin 6 → C(X, ℝ)) : ℝ := a * (B (H 4) 1 - B (H 0) (H 1))
  let R (H : Fin 6 → C(X, ℝ)) : ℝ := d * (B (H 5) 1 - B (H 2) (H 3))
  let good := {H : Fin 6 → C(X, ℝ) | L H ≤ R H}
  have hpair (f g : (Fin 6 → C(X, ℝ)) → C(X, ℝ)) (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun H ↦ B (f H) (g H)) := hBcont.comp (hf.prodMk hg)
  have hcL : Continuous L := by
    change Continuous (fun H : Fin 6 → C(X, ℝ) ↦ a * (B (H 4) 1 - B (H 0) (H 1)))
    exact continuous_const.mul ((hpair _ _ (continuous_apply 4) continuous_const).sub
      (hpair _ _ (continuous_apply 0) (continuous_apply 1)))
  have hcR : Continuous R := by
    change Continuous (fun H : Fin 6 → C(X, ℝ) ↦ d * (B (H 5) 1 - B (H 2) (H 3)))
    exact continuous_const.mul ((hpair _ _ (continuous_apply 5) continuous_const).sub
      (hpair _ _ (continuous_apply 2) (continuous_apply 3)))
  have hc : IsClosed good := isClosed_le hcL hcR
  change F ∈ good
  apply hc.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  have huc : UniformContinuous (fun x : X ↦ fun i : Fin 6 ↦ F i x) :=
    CompactSpace.uniformContinuous_of_continuous (continuous_pi fun i ↦ (F i).continuous)
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp huc (ε/2) (by positivity)
  obtain ⟨s, w, hw, hsum, hz⟩ := hgrid δ hδ
  let H (i : Fin 6) := spectralInterpolate s w (F i)
  refine ⟨H, ?_, (dist_pi_lt_iff hε).mpr ?_⟩
  · change L H ≤ R H
    change a * (B (spectralInterpolate s w (f * g)) 1 -
        B (spectralInterpolate s w f) (spectralInterpolate s w g)) ≤
      d * (B (spectralInterpolate s w (u * v)) 1 -
        B (spectralInterpolate s w u) (spectralInterpolate s w v))
    have hsum_le :
        a * (∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (g i - g j) * B (w i) (w j)) ≤
          d * (∑ i ∈ s, ∑ j ∈ s, (u i - u j) * (v i - v j) * B (w i) (w j)) := by
      simp only [mul_sum]
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hpoint i j) (hBpos (w i) (w j) (hw i hi) (hw j hj))
    rw [← pairing_spectralInterpolate_energy B hBsym s w hsum f g,
      ← pairing_spectralInterpolate_energy B hBsym s w hsum u v] at hsum_le
    linarith only [hsum_le]
  · intro i
    refine (spectralInterpolate_dist_le s w hw hsum (F i) (show 0 ≤ ε / 2 by positivity) hz ?_).trans_lt
      (by linarith)
    intro x y hxy
    exact ((dist_pi_lt_iff (show 0 < ε/2 by positivity)).mp (hd hxy) i).le

end FreeGroupHypercontractivity
