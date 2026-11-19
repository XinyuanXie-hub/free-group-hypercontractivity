module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».Hypercontractivity
public import «free-group-hypercontractivity».HypercontractivityTraceDerivative
public import «free-group-hypercontractivity».TraceExponent
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

public section

namespace FreeGroupHypercontractivity

open Set Filter NormedSpace
open scoped Topology

section TracedPower

variable {A : Type*} [CStarAlgebra A]

/-- The derivative of a traced positive-operator power with both the
operator and the exponent varying. -/
theorem hasDerivAt_trace_rpow_path
    (τ : A →L[ℝ] ℝ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    {S : Set ℝ} (hS : IsOpen S)
    {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (X dX : ℝ → A)
    (hXd : ∀ t ∈ S, HasDerivAt X (dX t) t)
    (hXsa : ∀ t ∈ S, IsSelfAdjoint (X t))
    (hXspec : ∀ t ∈ S, spectrum ℝ (X t) ⊆ Icc a b)
    (hdXB : ∀ t ∈ S, ‖dX t‖ ≤ C)
    (r : ℝ → ℝ) {r' t : ℝ} (ht : t ∈ S)
    (hr : 1 < r t) (hr' : HasDerivAt r r' t) :
    HasDerivAt (fun s ↦ τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r s)) (X s)))
      (r' * τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r t) * Real.log x) (X t)) +
        r t * τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r t - 1)) (X t) * dX t)) t := by
  let f (x : ℝ) := x ^ (r t)
  let g (x : ℝ) := x ^ (r t - 1)
  have hG : Continuous g := Real.continuous_rpow_const (by linarith)
  have hf (x : ℝ) (_hx : x ∈ Icc a b) :
      HasDerivWithinAt f (r t * g x) (Icc a b) x :=
    (Real.hasDerivAt_rpow_const (.inr hr.le)).hasDerivWithinAt
  have hFc : ContinuousOn (fun x ↦ r t * g x) (Icc a b) := hG.continuousOn.const_mul _
  have hbase := hasDerivAt_trace_cfc τ hτ hS hab X dX hXd hXsa hXspec hdXB
    f (fun x ↦ r t * g x) hf hFc ht
  rw [cfc_const_mul _ _ _ (hG.continuousOn), smul_mul_assoc, map_smul, smul_eq_mul]
    at hbase
  have hevent : ∀ᶠ s in 𝓝 t, IsSelfAdjoint (X s) ∧ spectrum ℝ (X s) ⊆ Icc a b := by
    filter_upwards [hS.mem_nhds ht] with s hs
    exact ⟨hXsa s hs, hXspec s hs⟩
  have hcorr := hasDerivAt_trace_cfc_rpow_exponent_correction τ
    (hXd t ht).continuousAt hr' isCompact_Icc (fun x hx ↦ ha.trans_le hx.1) hevent
  simpa only [f, g, sub_add_cancel] using hcorr.fun_add hbase

/-- A traced power is continuous along a continuous positive-operator
path whose spectra lie in a fixed positive compact interval. -/
theorem continuousOn_trace_rpow_path
    (τ : A →L[ℝ] ℝ) {S : Set ℝ}
    {a b : ℝ} (ha : 0 < a) (X : ℝ → A) (r : ℝ → ℝ)
    (hX : ContinuousOn X S) (hr : ContinuousOn r S)
    (hXsa : ∀ t ∈ S, IsSelfAdjoint (X t))
    (hXspec : ∀ t ∈ S, spectrum ℝ (X t) ⊆ Icc a b) :
    ContinuousOn (fun s ↦ τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r s)) (X s))) S := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  have hlog : ContinuousOn Real.log (Icc a b) :=
    fun x hx ↦ (Real.continuousAt_log (ha.trans_le hx.1).ne').continuousWithinAt
  have hlogX : ContinuousOn (fun s ↦ cfc (p := IsSelfAdjoint) Real.log (X s)) S :=
    (continuousOn_cfc A isCompact_Icc Real.log hlog).comp hX
      (fun s hs ↦ ⟨hXsa s hs, hXspec s hs⟩)
  have hcont : ContinuousOn (fun s ↦ τ (exp (r s • cfc (p := IsSelfAdjoint) Real.log (X s)))) S :=
    τ.continuous.comp_continuousOn (exp_continuous.comp_continuousOn (hr.smul hlogX))
  refine hcont.congr (fun s hs ↦ ?_)
  rw [cfc_rpow_eq_exp_smul_log (X s) (hXsa s hs) (fun x hx ↦ ha.trans_le (hXspec s hs hx).1)]


/-- Sharp norm comparison for a tracial path satisfying the entropy-dissipation
bound. The spectral hypothesis is a common positive compact interval. -/
theorem traced_rpow_le_of_entropy_dissipation
    (τ : A →L[ℝ] ℝ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    {p q t a b C : ℝ} (hp : 1 < p) (hpq : p ≤ q) (ht : 0 < t)
    (hthreshold : (1 / 2 : ℝ) * Real.log ((q - 1) / (p - 1)) ≤ t)
    (ha : 0 < a) (hab : a ≤ b) (X dX : ℝ → A)
    (hXc : ContinuousOn X (Icc 0 t))
    (hXd : ∀ s ∈ Ioo 0 t, HasDerivAt X (-dX s) s)
    (hXsa : ∀ s ∈ Icc 0 t, IsSelfAdjoint (X s))
    (hXspec : ∀ s ∈ Icc 0 t, spectrum ℝ (X s) ⊆ Icc a b)
    (hdXB : ∀ s ∈ Ioo 0 t, ‖dX s‖ ≤ C)
    (hpos : ∀ s ∈ Icc 0 t, ∀ r : ℝ, 1 < r →
      0 < τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ r) (X s)))
    (hdiss : ∀ s ∈ Ioo 0 t, ∀ r : ℝ, 1 < r →
      0 ≤ τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r - 1)) (X s) * dX s))
    (hEnt : ∀ s ∈ Ioo 0 t, ∀ r : ℝ, 1 < r →
      let ar := τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ r) (X s))
      let br := τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ r * Real.log x) (X s))
      let dr := τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r - 1)) (X s) * dX s)
      2 * (r - 1) * (r * br - ar * Real.log ar) ≤ r ^ 2 * dr) :
    τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ q) (X t)) ^ (1 / q) ≤
      τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ p) (X 0)) ^ (1 / p) := by
  obtain ⟨r, R, hr₀, hrt, hrc, hrgt, hr', hR⟩ :=
    exists_gross_exponent_path hp hpq ht hthreshold
  let M (s : ℝ) := τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r s)) (X s))
  let B (s : ℝ) := τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r s) * Real.log x) (X s))
  let D (s : ℝ) := τ (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r s - 1)) (X s) * dX s)
  have hM' (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivAt M (R s * B s - r s * D s) s := by
    have h := hasDerivAt_trace_rpow_path τ hτ isOpen_Ioo ha hab X (fun u ↦ -dX u) hXd
      (fun u hu ↦ hXsa u (Ioo_subset_Icc_self hu))
      (fun u hu ↦ hXspec u (Ioo_subset_Icc_self hu))
      (fun u hu ↦ by simpa only [norm_neg] using hdXB u hu) r hs (hrgt s) (hr' s)
    simpa only [M, B, D, mul_neg, map_neg, sub_eq_add_neg] using h
  have h := moment_le_of_entropy_dissipation ht.le M r R B D
    (fun s hs ↦ hpos s hs (r s) (hrgt s))
    (fun s _ ↦ hrgt s)
    (continuousOn_trace_rpow_path τ ha X r hXc hrc.continuousOn hXsa hXspec)
    hrc.continuousOn hM' (fun s _ ↦ hr' s) (fun s _ ↦ hR s)
    (fun s hs ↦ hdiss s hs (r s) (hrgt s))
    (fun s hs ↦ hEnt s hs (r s) (hrgt s))
  simpa only [M, hrt, hr₀] using h

end TracedPower

end FreeGroupHypercontractivity
