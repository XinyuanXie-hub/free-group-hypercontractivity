module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».HypercontractivityGross
public import «free-group-hypercontractivity».HypercontractivityNorm
public import «free-group-hypercontractivity».HypercontractivityPath
public import «free-group-hypercontractivity».GrossEntropy

public section

namespace FreeGroupHypercontractivity

open Set
open scoped ComplexOrder

theorem regularImage_poisson_preserves_lower_bound {n : ℕ} {t a : ℝ}
    (ht : 0 ≤ t) {x : GroupAlgebra n}
    (hx : (a : ℂ) • (1 : Operator n) ≤ regularImage x) :
    (a : ℂ) • (1 : Operator n) ≤ regularImage (poisson t x) := by
  have h : 0 ≤ regularImage (x - (a : ℂ) • 1) := by
    rw [regularImage_sub, regularImage_smul, regularImage_one]
    exact sub_nonneg.mpr hx
  have hp := regularImage_poisson_nonneg ht h
  simpa only [poisson_sub, poisson_smul, poisson_one, regularImage_sub, regularImage_smul,
    regularImage_one, sub_nonneg] using hp

theorem generator_comm_poisson {n : ℕ} (t : ℝ) (x : GroupAlgebra n) :
    generator (poisson t x) = poisson t (generator x) := by
  ext g
  simp [mul_left_comm]

theorem nonneg_of_nonneg_scalar_le {n : ℕ} {T : Operator n} {a : ℝ}
    (ha : 0 ≤ a) (hT : (a : ℂ) • (1 : Operator n) ≤ T) : 0 ≤ T :=
  (ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (ContinuousLinearMap.isPositive_one.smul_of_nonneg (Complex.real_le_real.mpr ha))).trans hT

theorem le_re_spectrum_of_scalar_le {n : ℕ} {T : Operator n} {a : ℝ}
    (ha : 0 ≤ a) (hT : (a : ℂ) • (1 : Operator n) ≤ T)
    {z : ℂ} (hz : z ∈ spectrum ℂ T) : a ≤ z.re := by
  have hsa := (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (nonneg_of_nonneg_scalar_le ha hT)).isSelfAdjoint
  have hbound : algebraMap ℂ (Operator n) (Complex.ofReal a) ≤ T := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact hT
  exact (Complex.le_def.mp
    ((algebraMap_le_iff_le_spectrum (R := ℂ) hsa.isStarNormal).mp hbound z hz)).1

/-- The entropy and Dirichlet form estimates needed by the Gross evolution,
stated on strictly positive Fourier polynomials. -/
@[expose]
def PoissonEntropyDissipation (n : ℕ) : Prop :=
  ∀ x : GroupAlgebra n, (∃ a : ℝ, 0 < a ∧ (a : ℂ) • (1 : Operator n) ≤ regularImage x) →
    ∀ r : ℝ, 1 < r →
      let X := polynomialInclusion n x
      let LX := polynomialInclusion n (generator x)
      let A := groupTraceReCLM n (cfc (p := IsSelfAdjoint) (fun z : ℝ ↦ z ^ r) X)
      let B := groupTraceReCLM n (cfc (p := IsSelfAdjoint) (fun z : ℝ ↦ z ^ r * Real.log z) X)
      let D := groupTraceReCLM n (cfc (p := IsSelfAdjoint) (fun z : ℝ ↦ z ^ (r - 1)) X * LX)
      0 ≤ D ∧ 2 * (r - 1) * (r * B - A * Real.log A) ≤ r ^ 2 * D

set_option maxHeartbeats 1200000 in
/-- Sharp Poisson contractivity on a strictly positive Fourier polynomial,
given the entropy-dissipation estimates. -/
theorem lpNorm_poisson_le_of_entropy_dissipation {n : ℕ} (hEnt : PoissonEntropyDissipation n)
    {p q t : ℝ} (hp : 1 < p) (hpq : p ≤ q) (ht : 0 < t)
    (hthreshold : (1 / 2 : ℝ) * Real.log ((q - 1) / (p - 1)) ≤ t)
    {x : GroupAlgebra n}
    (hx : ∃ a : ℝ, 0 < a ∧ (a : ℂ) • (1 : Operator n) ≤ regularImage x) :
    lpNorm q (poisson t x) ≤ lpNorm p x := by
  obtain ⟨a, ha, hax⟩ := hx
  let τ := groupTraceReCLM n
  let X (s : ℝ) := polynomialInclusion n (poisson s x)
  let dX (s : ℝ) := polynomialInclusion n (generator (poisson s x))
  have hXd (s : ℝ) : HasDerivAt X (-dX s) s := hasDerivAt_poisson_path x s
  have hXc : Continuous X := continuous_iff_continuousAt.mpr fun s ↦ (hXd s).continuousAt
  have hdXc : Continuous dX := by
    simp only [dX, generator_comm_poisson]
    exact continuous_iff_continuousAt.mpr fun s ↦
      (hasDerivAt_poisson_path (generator x) s).continuousAt
  have hbound (s : ℝ) (hs : 0 ≤ s) :
      (a : ℂ) • (1 : Operator n) ≤ (X s : Operator n) := by
    simpa only [X, polynomialInclusion_coe] using regularImage_poisson_preserves_lower_bound hs hax
  have hpos (s : ℝ) (hs : 0 ≤ s) : 0 ≤ (X s : Operator n) :=
    nonneg_of_nonneg_scalar_le ha.le (hbound s hs)
  have hsa (s : ℝ) (hs : 0 ≤ s) : IsSelfAdjoint (X s) := by
    apply Subtype.ext
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp (hpos s hs)).isSelfAdjoint.star_eq
  let : Nontrivial (Hilbert n) := ⟨⟨lp.single 2 1 1, 0, by
    intro h
    have he := congrArg (fun v : Hilbert n ↦ v (1 : Group n)) h
    simp at he⟩⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
    (K := Icc (0 : ℝ) t) hXc.norm.continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (K := Icc (0 : ℝ) t) hdXc.norm.continuousOn
  have hab : a ≤ max a M := le_max_left _ _
  have hspec (s : ℝ) (hs : s ∈ Icc 0 t) : spectrum ℝ (X s) ⊆ Icc a (max a M) := by
    intro z hz
    have hzc : algebraMap ℝ ℂ z ∈ spectrum ℂ (X s) := spectrum.algebraMap_mem ℂ hz
    rw [StarSubalgebra.spectrum_eq (S := groupCStar n), Complex.coe_algebraMap] at hzc
    have hzU : z ≤ ‖(X s : Operator n)‖ := (le_abs_self z).trans (by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hzc)
    change z ≤ ‖X s‖ at hzU
    exact ⟨le_re_spectrum_of_scalar_le ha.le (hbound s hs.1) hzc,
      hzU.trans ((hM (mem_image_of_mem _ hs)).trans (le_max_right _ _))⟩
  have htracepos (s : ℝ) (hs : s ∈ Icc 0 t) (r : ℝ) (hr : 1 < r) :
      0 < τ (cfc (p := IsSelfAdjoint) (fun z : ℝ ↦ z ^ r) (X s)) := by
    exact groupTraceReCLM_cfc_rpow_pos (X s) (hsa s hs.1) ha (by linarith)
      fun z hz ↦ (hspec s hs hz).1
  have h := traced_rpow_le_of_entropy_dissipation τ (groupTraceReCLM_mul_comm) hp hpq ht
    hthreshold ha hab X dX hXc.continuousOn (fun s _ ↦ hXd s)
    (fun s hs ↦ hsa s hs.1) hspec (fun s hs ↦ hC (mem_image_of_mem _ (Ioo_subset_Icc_self hs)))
    htracepos
  have hd (s : ℝ) (hs : s ∈ Ioo 0 t) (r : ℝ) (hr : 1 < r) :=
    hEnt (poisson s x) ⟨a, ha, regularImage_poisson_preserves_lower_bound hs.1.le hax⟩ r hr
  specialize h
    (fun s hs r hr ↦ (hd s hs r hr).1)
    (fun s hs r hr ↦ (hd s hs r hr).2)
  have hxpos : 0 ≤ regularImage x := by
    have h0 := hpos 0 le_rfl
    simpa [X] using h0
  have htpos := regularImage_poisson_nonneg ht.le hxpos
  rw [lpNorm_eq_group_trace_rpow_of_nonneg (by linarith : 0 ≤ q) htpos,
    lpNorm_eq_group_trace_rpow_of_nonneg (by linarith : 0 ≤ p) hxpos]
  simpa [τ, X] using h

end FreeGroupHypercontractivity
