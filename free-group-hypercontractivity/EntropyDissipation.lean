module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».CfcEnergyCore
public import «free-group-hypercontractivity».OperatorEnergyComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

public section

namespace FreeGroupHypercontractivity

open Set
open scoped ComplexOrder Polynomial

/-- The log-Sobolev estimate at the half power of a strictly positive Fourier
polynomial, combined with the noncommutative Stroock–Varopoulos comparison. -/
theorem entropy_of_rpow_half_le_dissipation {n : ℕ} (x : GroupAlgebra n)
    (hx : 0 ≤ regularImage x) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspec : ∀ z ∈ spectrum ℂ (regularImage x), z.re ∈ Icc a b)
    {r : ℝ} (hr : 1 < r)
    (hLSI : ∀ y : GroupAlgebra n, 0 ≤ regularImage y →
      entropy (regularImage y ^ 2) ≤ 2 * traceRe (regularImage y * regularImage (generator y))) :
    let T := regularImage x
    let A := realCfcAt (fun s ↦ s ^ (r / 2)) T
    let D := traceRe (realCfcAt (fun s ↦ s ^ (r - 1)) T * regularImage (generator x))
    0 ≤ D ∧ 2 * (r - 1) * entropy (A ^ 2) ≤ r ^ 2 * D := by
  let T := polynomialInclusion n x
  have hT : (T : Operator n) = regularImage x := polynomialInclusion_coe n x
  have hTpos : 0 ≤ (T : Operator n) := hT ▸ hx
  have hTsa' := (ContinuousLinearMap.nonneg_iff_isPositive.mp hTpos).isSelfAdjoint
  have hTsa : IsSelfAdjoint T := Subtype.ext hTsa'.star_eq
  let f (s : ℝ) : ℝ := s ^ (r / 2)
  let g (s : ℝ) : ℝ := s ^ (r - 1)
  have hr2 : 0 < r / 2 := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hf : Continuous f := Real.continuous_rpow_const hr2.le
  have hg : Continuous g := Real.continuous_rpow_const hr1.le
  let A : GroupCStar n := cfc (p := IsSelfAdjoint) f T
  let B : GroupCStar n := cfc (p := IsSelfAdjoint) g T
  have hA : (A : Operator n) = realCfcAt f (regularImage x) := by
    change ((cfc (p := IsSelfAdjoint) f T : GroupCStar n) : Operator n) = _
    exact (groupCStar_coe_real_cfc f hf T hTsa).trans (congrArg (realCfcAt f) hT)
  have hB : (B : Operator n) = realCfcAt g (regularImage x) := by
    change ((cfc (p := IsSelfAdjoint) g T : GroupCStar n) : Operator n) = _
    exact (groupCStar_coe_real_cfc g hg T hTsa).trans (congrArg (realCfcAt g) hT)
  have hsa (f : ℝ → ℝ) : IsSelfAdjoint ((cfc (p := IsSelfAdjoint) f T : GroupCStar n) : Operator n) :=
    (cfc_predicate f T).map (groupCStar n).subtype
  have hspec' (z : ℝ) (hz : z ∈ spectrum ℝ T) : z ∈ Icc a b := by
    have hzc := spectrum.algebraMap_mem ℂ hz
    rw [StarSubalgebra.spectrum_eq (S := groupCStar n)] at hzc
    rw [hT] at hzc
    exact hspec _ hzc
  let P (t : ℝ) := (poissonCStar n t).restrictScalars ℝ
  have hP1 (t : ℝ) (ht : 0 ≤ t) : P t 1 = 1 := poissonCStar_one ht
  have hPpos (t : ℝ) (ht : 0 ≤ t) (U : GroupCStar n) (hU : 0 ≤ (U : Operator n)) :
      0 ≤ (P t U : Operator n) := poissonCStar_nonneg ht hU
  have hPsym (t : ℝ) (ht : 0 ≤ t) (U V : GroupCStar n)
      (hU : IsSelfAdjoint U) (hV : IsSelfAdjoint V) :
      groupTraceReCLM n (U * P t V) = groupTraceReCLM n (V * P t U) := by
    simp only [groupTraceReCLM_apply]
    exact traceRe_poisson_mul_comm ht
      (hU.map (groupCStar n).subtype) (hV.map (groupCStar n).subtype)
  have hpoly (t : ℝ) (ht : 0 ≤ t) :
      (P t T : Operator n) = regularImage (poisson t x) := by
    simp [P, T, poissonCStar_apply_polynomial ht]
  have hfinite := poissonCStar_generator_comparison (A := A) (B := B) (hsa f) (hsa g) x
    (c := 4 * (r - 1)) (d := r ^ 2) (by positivity) (by
      intro t ht
      have h := groupCStar_cfc_stroockVaropoulos hTsa hTpos (P t) (hP1 t ht.le)
        (hPpos t ht.le) (hPsym t ht.le) hr
      simp only [groupTraceReCLM_apply] at h
      change 4 * (r - 1) * traceRe ((A : Operator n) * ((A : Operator n) - (P t A : Operator n))) ≤
        r ^ 2 * traceRe ((B : Operator n) * ((T : Operator n) - (P t T : Operator n))) at h
      rw [hT, hpoly t ht.le] at h
      exact h)
  have hLSIA : entropy ((A : Operator n) ^ 2) ≤ 2 * operatorEnergy (A : Operator n) := by
    rw [hA]
    refine logSobolev_realCfc_of_lipschitz_comparison x hx hab hspec
      (f' := fun s ↦ (r / 2) * s ^ (r / 2 - 1)) ?_ ?_
      (Real.rpow_pos_of_pos ha (r / 2)) ?_ hLSI (hA ▸ hfinite.1) ?_
    · intro s hs
      exact (Real.hasDerivAt_rpow_const (.inl (ha.trans_le hs.1).ne')).hasDerivWithinAt
    · intro s hs
      exact ((Real.continuousAt_rpow_const s _ (.inl (ha.trans_le hs.1).ne')).const_mul _).continuousWithinAt
    · intro s hs
      exact Real.rpow_le_rpow ha.le hs.1 hr2.le
    · dsimp only
      intro δ p y hy hlip t ht
      let k (s : ℝ) := p.eval s - f s
      have hk : Continuous k := p.continuous.sub hf
      have hl := groupCStar_cfc_lipschitz_energy hTsa (P t) (hP1 t ht.le)
        (hPpos t ht.le) (hPsym t ht.le) k hk.continuousOn
        (L := δ) (fun s hs u hu ↦ hlip s (hspec' s hs) u (hspec' u hu))
      have hpolyC : cfc (p := IsSelfAdjoint) p.eval T = polynomialInclusion n y := by
        apply Subtype.ext
        change ((cfc (p := IsSelfAdjoint) p.eval T : GroupCStar n) : Operator n) =
          (polynomialInclusion n y : Operator n)
        exact (groupCStar_coe_real_cfc p.eval p.continuous T hTsa).trans
          ((congrArg (realCfcAt p.eval) hT).trans
            (hy.symm.trans (polynomialInclusion_coe n y).symm))
      have hsub : cfc (p := IsSelfAdjoint) k T = polynomialInclusion n y - A := by
        change cfc (p := IsSelfAdjoint) (fun s ↦ p.eval s - f s) T =
          polynomialInclusion n y - A
        rw [cfc_sub p.eval f T p.continuous.continuousOn hf.continuousOn, hpolyC]
      rw [hsub] at hl
      simp only [groupTraceReCLM_apply] at hl
      have hAeq : A = ⟨realCfcAt f (regularImage x), cfc_mem_groupCStar _ (regularImage_mem_groupCStar x)⟩ :=
        Subtype.ext hA
      rw [hAeq] at hl
      change _ ≤ δ ^ 2 * traceRe ((T : Operator n) * ((T : Operator n) - (P t T : Operator n))) at hl
      rw [hT, hpoly t ht.le] at hl
      exact hl
  let D := traceRe ((B : Operator n) * regularImage (generator x))
  have hD : 0 ≤ D := by
    have hnonneg : 0 ≤ operatorEnergy (A : Operator n) := tsum_nonneg (fun _ ↦ by positivity)
    have h : 0 ≤ r ^ 2 * D := (mul_nonneg (by positivity) hnonneg).trans hfinite.2
    exact nonneg_of_mul_nonneg_right h (sq_pos_of_pos (zero_lt_one.trans hr))
  change 0 ≤ traceRe (realCfcAt g (regularImage x) * regularImage (generator x)) ∧
    2 * (r - 1) * entropy (realCfcAt f (regularImage x) ^ 2) ≤
      r ^ 2 * traceRe (realCfcAt g (regularImage x) * regularImage (generator x))
  rw [← hA, ← hB]
  refine ⟨hD, ?_⟩
  calc
    _ ≤ 2 * (r - 1) * (2 * operatorEnergy (A : Operator n)) :=
      mul_le_mul_of_nonneg_left hLSIA (by positivity)
    _ = 4 * (r - 1) * operatorEnergy (A : Operator n) := by ring
    _ ≤ _ := hfinite.2

end FreeGroupHypercontractivity
