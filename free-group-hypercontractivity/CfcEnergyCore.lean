module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».EnergyCore
public import «free-group-hypercontractivity».FourierPoisson
public import «free-group-hypercontractivity».PositiveCoreApprox
import Mathlib.Analysis.SpecificLimits.Basic

public section

namespace FreeGroupHypercontractivity

open Filter Set
open scoped ComplexOrder Polynomial Topology

/-- Apply a real function to a self-adjoint operator by continuous functional calculus. -/
@[expose]
noncomputable def realCfcAt {n : ℕ} (f : ℝ → ℝ) (T : Operator n) : Operator n :=
  cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (f z.re)) T

/-- Operator and form approximation of strictly positive functions of a Fourier polynomial. -/
theorem logSobolev_realCfc_of_lipschitz_comparison {n : ℕ} (x : GroupAlgebra n)
    (hx : 0 ≤ regularImage x) {a b : ℝ} (hab : a ≤ b)
    (hspec : ∀ z ∈ spectrum ℂ (regularImage x), z.re ∈ Icc a b)
    {f f' : ℝ → ℝ} (hd : ∀ z ∈ Icc a b, HasDerivWithinAt f (f' z) (Icc a b) z)
    (hc : ContinuousOn f' (Icc a b)) {m : ℝ} (hm : 0 < m)
    (hf : ∀ z ∈ Icc a b, m ≤ f z)
    (hLSI : ∀ y : GroupAlgebra n, 0 ≤ regularImage y →
      entropy (regularImage y ^ 2) ≤ 2 * traceRe (regularImage y * regularImage (generator y)))
    (hdom : InEnergyDomain (realCfcAt f (regularImage x)))
    (hcompare :
      let T := regularImage x
      let A : GroupCStar n := ⟨realCfcAt f T,
        cfc_mem_groupCStar _ (regularImage_mem_groupCStar x)⟩
      ∀ (δ : ℝ) (p : ℝ[X]) (y : GroupAlgebra n),
        regularImage y = realCfcAt p.eval T →
        (∀ r ∈ Icc a b, ∀ s ∈ Icc a b,
          |(p.eval r - f r) - (p.eval s - f s)| ≤ δ * |r - s|) →
        let V := polynomialInclusion n y - A
        ∀ t : ℝ, 0 < t →
          traceRe ((V : Operator n) * ((V : Operator n) - (poissonCStar n t V : Operator n))) ≤
            δ ^ 2 * traceRe (T * (T - regularImage (poisson t x)))) :
    entropy (realCfcAt f (regularImage x) ^ 2) ≤
      2 * operatorEnergy (realCfcAt f (regularImage x)) := by
  let T := regularImage x
  let A : GroupCStar n := ⟨realCfcAt f T, cfc_mem_groupCStar _ (regularImage_mem_groupCStar x)⟩
  have hA : 0 ≤ (A : Operator n) := by
    change 0 ≤ realCfcAt f T
    unfold realCfcAt
    apply cfc_nonneg
    intro z hz
    exact Complex.real_le_real.mpr (hm.le.trans (hf z.re (hspec z hz)))
  have hTA := (ContinuousLinearMap.nonneg_iff_isPositive.mp hx).isSelfAdjoint
  let δ (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hδ (k : ℕ) : 0 < δ k := by dsimp [δ]; positivity
  choose p y hy hpos hclose hlip using fun k : ℕ ↦
    exists_positive_fourier_cfc_approx x hx hab hspec hd hc hm hf (hδ k)
  have henergy (k : ℕ) :
      InEnergyDomain (regularImage (y k) - (A : Operator n)) ∧
        operatorEnergy (regularImage (y k) - (A : Operator n)) ≤
          δ k ^ 2 * traceRe (T * regularImage (generator x)) := by
    let V := polynomialInclusion n (y k) - A
    have hV : (V : Operator n) = regularImage (y k) - (A : Operator n) := by
      change (polynomialInclusion n (y k) : Operator n) - (A : Operator n) = _
      rw [polynomialInclusion_coe]
    have hs : IsSelfAdjoint (V : Operator n) := by
      rw [hV]
      have hy' := (ContinuousLinearMap.nonneg_iff_isPositive.mp (hpos k)).isSelfAdjoint
      have hA' := (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).isSelfAdjoint
      exact hy'.sub hA'
    have hr0 := poissonCStar_generator_comparison (A := V) (B := polynomialInclusion n x)
      hs (by simpa only [polynomialInclusion_coe] using hTA) x (c := 1) (d := δ k ^ 2)
      zero_lt_one (by
        intro t ht
        simpa only [one_mul, polynomialInclusion_coe] using hcompare (δ k) (p k) (y k)
          (hy k) (hlip k) t ht)
    simpa only [hV, one_mul, polynomialInclusion_coe] using hr0
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply logSobolev_of_energy_limit (x := y) (l := atTop) hA hpos hdom
    (fun k ↦ (henergy k).1) ?_ ?_ hLSI
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hclose hδlim
  · have hl : Tendsto (fun k ↦ δ k ^ 2 * traceRe (T * regularImage (generator x))) atTop (𝓝 0) := by
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul] using
        (hδlim.pow 2).mul_const (traceRe (T * regularImage (generator x)))
    exact squeeze_zero (fun k ↦ tsum_nonneg (fun g ↦ by positivity)) (fun k ↦ (henergy k).2) hl

end FreeGroupHypercontractivity
