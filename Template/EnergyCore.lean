module

import all Template.Model

public import Template.FourierEnergy
public import Template.OperatorMajorant
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

public section

namespace FreeGroupHypercontractivity

open Filter
open scoped Topology

private theorem weightedCoeff_norm_sq {n : ℕ} (A : Operator n) (g : Group n) :
    ‖Real.sqrt (FreeGroup.norm g : ℝ) • operatorCoeff A g‖ ^ 2 =
      (FreeGroup.norm g : ℝ) * ‖operatorCoeff A g‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity)]

/-- Square-root weighted Fourier coefficients as a Hilbert-space vector. -/
noncomputable def energyVector {n : ℕ} (A : Operator n) (hA : InEnergyDomain A) : Hilbert n :=
  ⟨(fun g ↦ Real.sqrt (FreeGroup.norm g : ℝ) • operatorCoeff A g),
    memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two, weightedCoeff_norm_sq, InEnergyDomain] using hA)⟩

theorem energyVector_apply {n : ℕ} {A : Operator n} (hA : InEnergyDomain A) (g : Group n) :
    energyVector A hA g = Real.sqrt (FreeGroup.norm g : ℝ) • operatorCoeff A g := by
  rfl

theorem energyVector_norm_sq {n : ℕ} {A : Operator n} (hA : InEnergyDomain A) :
    ‖energyVector A hA‖ ^ 2 = operatorEnergy A := by
  have h := lp.norm_rpow_eq_tsum (by norm_num) (energyVector A hA)
  simpa only [operatorEnergy, ENNReal.toReal_ofNat, Real.rpow_two, energyVector_apply, weightedCoeff_norm_sq] using h

theorem energyVector_sub {n : ℕ} {A B : Operator n} (hA : InEnergyDomain A)
    (hB : InEnergyDomain B) (hAB : InEnergyDomain (A - B)) :
    energyVector (A - B) hAB = energyVector A hA - energyVector B hB := by
  ext g
  simp only [energyVector_apply, lp.coeFn_sub, Pi.sub_apply]
  have hcoeff : operatorCoeff (A - B) g = operatorCoeff A g - operatorCoeff B g := by
    simp [operatorCoeff]
  rw [hcoeff, smul_sub]

theorem nonneg_operator_sq {n : ℕ} {T : Operator n} (hT : 0 ≤ T) : 0 ≤ T ^ 2 := by
  have h := (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).isSelfAdjoint
  have hpos := star_mul_self_nonneg T
  rw [h.star_eq] at hpos
  simpa only [pow_two] using hpos

theorem continuousOn_entropy_nonneg (n : ℕ) :
    ContinuousOn (entropy (n := n)) {T : Operator n | 0 ≤ T} := by
  let f : ℂ → ℂ := fun z ↦ Complex.ofReal (z.re * Real.log z.re)
  have hf : Continuous f := Complex.continuous_ofReal.comp
    (Real.continuous_mul_log.comp Complex.continuous_re)
  have hc : ContinuousOn (cfc (p := IsStarNormal) f)
      {T : Operator n | 0 ≤ T} :=
    ContinuousOn.cfc_of_mem_nhdsSet (s := Set.univ) f Filter.univ_mem continuousOn_id
      (fun _ h ↦ (ContinuousLinearMap.nonneg_iff_isPositive.mp h).isSelfAdjoint.isStarNormal)
      hf.continuousOn
  apply ((continuous_traceRe n).comp_continuousOn hc).sub
  exact (Real.continuous_mul_log.comp (continuous_traceRe n)).continuousOn

/-- Pass the polynomial log-Sobolev bound to any positive limit admitting approximation
both in operator norm and in the norm of the quadratic form. -/
theorem logSobolev_of_energy_limit {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    {x : ι → GroupAlgebra n} {A : Operator n} (hA : 0 ≤ A)
    (hx : ∀ i, 0 ≤ regularImage (x i)) (hdomain : InEnergyDomain A)
    (hxdomain : ∀ i, InEnergyDomain (regularImage (x i) - A))
    (hnorm : Tendsto (fun i ↦ regularImage (x i)) l (𝓝 A))
    (henergy : Tendsto (fun i ↦ operatorEnergy (regularImage (x i) - A)) l (𝓝 0))
    (hLSI : ∀ y : GroupAlgebra n, 0 ≤ regularImage y →
      entropy (regularImage y ^ 2) ≤ 2 * traceRe (regularImage y * regularImage (generator y))) :
    entropy (A ^ 2) ≤ 2 * operatorEnergy A := by
  let v (i : ι) := energyVector (regularImage (x i)) (regularImage_inEnergyDomain (x i))
  let w := energyVector A hdomain
  have hvw (i : ι) : ‖v i - w‖ ^ 2 = operatorEnergy (regularImage (x i) - A) := by
    rw [← energyVector_sub _ _ (hxdomain i), energyVector_norm_sq]
  have hv : Tendsto v l (𝓝 w) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp henergy
    simpa only [Function.comp_def, Real.sqrt_zero, ← hvw, Real.sqrt_sq_eq_abs, abs_norm] using h
  have he : Tendsto (fun i ↦ operatorEnergy (regularImage (x i))) l (𝓝 (operatorEnergy A)) := by
    simpa only [v, w, energyVector_norm_sq] using hv.norm.pow 2
  have hsq : Tendsto (fun i ↦ regularImage (x i) ^ 2) l (𝓝 (A ^ 2)) := hnorm.pow 2
  have hsqWithin : Tendsto (fun i ↦ regularImage (x i) ^ 2) l
      (𝓝[{T : Operator n | 0 ≤ T}] (A ^ 2)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsq, Eventually.of_forall fun i ↦ nonneg_operator_sq (hx i)⟩
  have hleft := ((continuousOn_entropy_nonneg n) (A ^ 2) (nonneg_operator_sq hA)).tendsto.comp hsqWithin
  refine le_of_tendsto_of_tendsto hleft (he.const_mul 2) (Eventually.of_forall fun i ↦ ?_)
  change entropy (regularImage (x i) ^ 2) ≤ 2 * operatorEnergy (regularImage (x i))
  rw [operatorEnergy_regularImage (ContinuousLinearMap.nonneg_iff_isPositive.mp (hx i)).isSelfAdjoint]
  exact hLSI (x i) (hx i)

end FreeGroupHypercontractivity
