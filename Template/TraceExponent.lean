module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.SpecialFunctions.Exponential

public section

namespace FreeGroupHypercontractivity

open NormedSpace Filter
open scoped Topology

theorem cfc_rpow_eq_exp_smul_log {A : Type*} [CStarAlgebra A]
    (X : A) (hX : IsSelfAdjoint X) (hpos : ∀ x ∈ spectrum ℝ X, 0 < x) (r : ℝ) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ r) X = exp (r • cfc Real.log X) := by
  have hlog : ContinuousOn Real.log (spectrum ℝ X) :=
    fun x hx ↦ (Real.continuousAt_log (hpos x hx).ne').continuousWithinAt
  have hsmul : IsSelfAdjoint (r • cfc Real.log X) := by
    rw [← cfc_smul r Real.log X hlog]
    exact cfc_predicate _ _
  have hcont : ContinuousOn (fun x : ℝ ↦ r • Real.log x) (spectrum ℝ X) :=
    hlog.const_smul r
  calc
    _ = cfc (p := IsSelfAdjoint) (fun x ↦ Real.exp (r • Real.log x)) X := by
      apply cfc_congr
      intro x hx
      change x ^ r = Real.exp (r * Real.log x)
      rw [Real.rpow_def_of_pos (hpos x hx), mul_comm]
    _ = _ := by
      rw [cfc_comp' Real.exp _ X Real.continuous_exp.continuousOn hcont hX,
        cfc_smul r Real.log X hlog, CFC.real_exp_eq_normedSpace_exp hsmul]

private theorem cfc_rpow_mul_log_eq {A : Type*} [CStarAlgebra A]
    (X : A) (hX : IsSelfAdjoint X) (hpos : ∀ x ∈ spectrum ℝ X, 0 < x) (r : ℝ) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ r * Real.log x) X =
      exp (r • cfc Real.log X) * cfc Real.log X := by
  have hlog : ContinuousOn Real.log (spectrum ℝ X) :=
    fun x hx ↦ (Real.continuousAt_log (hpos x hx).ne').continuousWithinAt
  have hpow : ContinuousOn (fun x : ℝ ↦ x ^ r) (spectrum ℝ X) := by
    refine (Real.continuous_exp.continuousOn.comp (hlog.const_smul r)
      (Set.mapsTo_univ _ _)).congr ?_
    intro x hx
    change x ^ r = Real.exp (r * Real.log x)
    rw [Real.rpow_def_of_pos (hpos x hx), mul_comm]
  rw [cfc_mul _ Real.log X hpow hlog, cfc_rpow_eq_exp_smul_log X hX hpos]

/-- Differentiate the functional calculus of a positive operator with respect to the exponent. -/
theorem hasDerivAt_cfc_rpow_exponent {A : Type*} [CStarAlgebra A]
    (X : A) (hX : IsSelfAdjoint X) (hpos : ∀ x ∈ spectrum ℝ X, 0 < x) (r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ s) X)
      (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ r * Real.log x) X) r := by
  simp only [cfc_rpow_eq_exp_smul_log X hX hpos, cfc_rpow_mul_log_eq X hX hpos]
  exact hasDerivAt_exp_smul_const (cfc Real.log X) r

/-- Differentiate a continuous real linear functional of an operator power in its exponent. -/
theorem hasDerivAt_trace_cfc_rpow_exponent {A : Type*} [CStarAlgebra A]
    (τ : A →L[ℝ] ℝ) (X : A) (hX : IsSelfAdjoint X) (hpos : ∀ x ∈ spectrum ℝ X, 0 < x)
    (r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ s) X))
      (τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ r * Real.log x) X)) r := by
  exact τ.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_cfc_rpow_exponent X hX hpos r)

private theorem hasDerivAt_exp_smul_sub {A : Type*} [CStarAlgebra A]
    {L : ℝ → A} {r : ℝ → ℝ} {t r' : ℝ} (hL : ContinuousAt L t) (hr : HasDerivAt r r' t) :
    HasDerivAt (fun s ↦ exp (r s • L s) - exp (r t • L s))
      (r' • (exp (r t • L t) * L t)) t := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  let H (s : ℝ) : A := (r s - r t) • L s
  let B (s : ℝ) : A := exp (r t • L s)
  let D (s : ℝ) : A := exp (H s) - 1
  have hHt : H t = 0 := by simp [H]
  have hH : HasDerivAt H (r' • L t) t := by
    rw [hasDerivAt_iff_tendsto_slope]
    have h := hr.tendsto_slope.smul (hL.tendsto.mono_left nhdsWithin_le_nhds)
    convert h using 1
    ext s
    rw [slope_def_module, hHt, sub_zero, slope_def_field, div_eq_inv_mul]
    simp [H, smul_smul]
  have hD : HasDerivAt D (r' • L t) t := by
    have h := (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A)).comp_hasDerivAt_of_eq t hH hHt.symm
    simpa only [D, one_apply_eq_self, Function.comp_apply] using h.sub_const 1
  have hDt : D t = 0 := by simp [D, hHt, exp_zero]
  have hB : ContinuousAt B t := exp_continuous.continuousAt.comp (continuousAt_const.smul hL)
  have hBD : HasDerivAt (fun s ↦ B s * D s) (r' • (B t * L t)) t := by
    rw [hasDerivAt_iff_tendsto_slope, ← mul_smul_comm]
    have h := (hB.tendsto.mono_left (nhdsWithin_le_nhds (s := {t}ᶜ))).mul hD.tendsto_slope
    convert h using 1
    ext s
    simp [slope_def_module, hDt]
  convert hBD using 1
  funext s
  dsimp [B, D, H]
  have hcomm : Commute (r t • L s) ((r s - r t) • L s) :=
    ((Commute.refl (L s)).smul_left (r t)).smul_right _
  rw [mul_sub, mul_one, ← exp_add_of_commute hcomm, ← add_smul]
  rw [show r t + (r s - r t) = r s by ring]

/-- The contribution of a moving exponent when the positive operator also varies continuously. -/
theorem hasDerivAt_trace_cfc_rpow_exponent_correction {A : Type*} [CStarAlgebra A]
    (τ : A →L[ℝ] ℝ) {X : ℝ → A} {r : ℝ → ℝ} {t r' : ℝ}
    (hX : ContinuousAt X t) (hr : HasDerivAt r r' t) {K : Set ℝ}
    (hK : IsCompact K) (hpos : ∀ x ∈ K, 0 < x)
    (hXK : ∀ᶠ s in 𝓝 t, IsSelfAdjoint (X s) ∧ spectrum ℝ (X s) ⊆ K) :
    HasDerivAt (fun s ↦ τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r s)) (X s)) -
      τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r t)) (X s)))
      (r' * τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r t) * Real.log x) (X t))) t := by
  let L (s : ℝ) : A := cfc Real.log (X s)
  have hOn : ContinuousOn (cfc Real.log) {Y : A | IsSelfAdjoint Y ∧ spectrum ℝ Y ⊆ K} :=
    continuousOn_cfc A hK Real.log
      (fun x hx ↦ (Real.continuousAt_log (hpos x hx).ne').continuousWithinAt)
  have hL : ContinuousAt L t := by
    exact (hOn (X t) hXK.self_of_nhds).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hX.tendsto, hXK⟩)
  have h := τ.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_sub hL hr)
  have htarget :
      cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r t) * Real.log x) (X t) =
        exp (r t • L t) * L t :=
    cfc_rpow_mul_log_eq (X t) hXK.self_of_nhds.1
      (fun x hx ↦ hpos x (hXK.self_of_nhds.2 hx)) (r t)
  rw [htarget, ← smul_eq_mul, ← map_smul]
  apply HasDerivAt.congr_of_eventuallyEq h
  filter_upwards [hXK] with s hs
  rw [Function.comp_apply, map_sub,
    cfc_rpow_eq_exp_smul_log (X s) hs.1 (fun x hx ↦ hpos x (hs.2 hx)),
    cfc_rpow_eq_exp_smul_log (X s) hs.1 (fun x hx ↦ hpos x (hs.2 hx))]

end FreeGroupHypercontractivity
