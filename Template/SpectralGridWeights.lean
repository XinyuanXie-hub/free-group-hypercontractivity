module

public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Field

public section

namespace FreeGroupHypercontractivity

open Set Metric

/-- A compact metric space admits a finite continuous partition of unity supported by balls of
any prescribed positive radius. -/
theorem spectralGrid_exists {X : Type*} [MetricSpace X] [CompactSpace X]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ s : Finset X, ∃ w : X → C(X, ℝ),
      (∀ i ∈ s, 0 ≤ w i) ∧ (∑ i ∈ s, w i) = 1 ∧
      ∀ i ∈ s, ∀ x, δ ≤ dist x i → w i x = 0 := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun i : X ↦ Metric.ball i δ)
    (fun _ ↦ isOpen_ball)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, Metric.mem_ball_self hδ⟩)
  let bump (i x : X) : ℝ := max (δ - dist x i) 0
  have hb (i x : X) : 0 ≤ bump i x := le_max_right _ _
  have hc (i : X) : Continuous (bump i) :=
    (continuous_const.sub (continuous_id.dist continuous_const)).max continuous_const
  let total (x : X) : ℝ := ∑ i ∈ s, bump i x
  have ht : Continuous total := continuous_finsetSum _ (fun i _ ↦ hc i)
  have hp (x : X) : 0 < total x := by
    obtain ⟨i, hi, hix⟩ : ∃ i ∈ s, dist x i < δ := by
      simpa only [Set.mem_iUnion, Metric.mem_ball, exists_prop, Finset.mem_coe] using hs (Set.mem_univ x)
    have hbi : 0 < bump i x := (sub_pos.mpr hix).trans_le (le_max_left _ _)
    exact hbi.trans_le (Finset.single_le_sum (fun j _ ↦ hb j x) hi)
  let w (i : X) : C(X, ℝ) :=
    ⟨fun x ↦ bump i x / total x, (hc i).div ht (fun x ↦ (hp x).ne')⟩
  refine ⟨s, w, ?_, ?_, ?_⟩
  · intro i _
    exact ContinuousMap.le_def.mpr fun x ↦ div_nonneg (hb i x) (hp x).le
  · apply ContinuousMap.ext
    intro x
    simp only [ContinuousMap.sum_apply, ContinuousMap.one_apply]
    change (∑ i ∈ s, bump i x / total x) = 1
    rw [← Finset.sum_div]
    exact div_self (hp x).ne'
  · intro i _ x hxi
    change max (δ - dist x i) 0 / total x = 0
    rw [max_eq_right (sub_nonpos.mpr hxi), zero_div]

end FreeGroupHypercontractivity
