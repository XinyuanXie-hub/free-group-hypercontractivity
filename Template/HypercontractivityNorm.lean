module

import all Template.Model

public import Template.PoissonExtension
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

public section

namespace FreeGroupHypercontractivity

open Set Filter
open scoped Topology ComplexOrder

/-- The tracial Lp norm formula on bounded operators. -/
@[expose]
noncomputable def operatorLpNorm {n : ℕ} (p : ℝ) (T : Operator n) : ℝ :=
  (traceRe (cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (z.re ^ (p / 2)))
    (star T * T))) ^ (1 / p)

@[simp]
theorem lpNorm_eq_operatorLpNorm {n : ℕ} (p : ℝ) (x : GroupAlgebra n) :
    lpNorm p x = operatorLpNorm p (regularImage x) := by
  rw [lpNorm, operatorLpNorm]

/-- Operator-norm convergence implies convergence of the tracial Lp norms
at every positive finite exponent. -/
theorem continuous_operatorLpNorm {n : ℕ} {p : ℝ} (hp : 0 < p) :
    Continuous (operatorLpNorm (n := n) p) := by
  let F (T : Operator n) := star T * T
  let f (z : ℂ) := Complex.ofReal (z.re ^ (p / 2))
  let : Nontrivial (Hilbert n) := ⟨⟨lp.single 2 1 1, 0, by
    intro h
    have he := congrArg (fun v : Hilbert n ↦ v (1 : Group n)) h
    simp at he⟩⟩
  have hstar : Continuous (fun T : Operator n ↦ star T) := by
    simp_rw [ContinuousLinearMap.star_eq_adjoint]
    exact (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Hilbert n) (F := Hilbert n)).continuous
  have hF : Continuous F := hstar.mul continuous_id
  have hf : Continuous f := Complex.continuous_ofReal.comp
    ((Real.continuous_rpow_const (by positivity : 0 ≤ p / 2)).comp Complex.continuous_re)
  have hFcfc : Continuous (fun T ↦ cfc (p := IsStarNormal) f (F T)) := by
    apply continuous_iff_continuousAt.mpr
    intro T
    let R := ‖F T‖ + 1
    let K := Metric.closedBall (0 : ℂ) R
    have hdist : ∀ᶠ U in 𝓝 T, ‖F U‖ < R :=
      ((continuous_norm.comp hF).continuousAt.tendsto.eventually_lt_const (by dsimp [R]; linarith))
    have he : ∀ᶠ U in 𝓝 T, IsStarNormal (F U) ∧ spectrum ℂ (F U) ⊆ K :=
      hdist.mono fun U hU ↦ ⟨(IsSelfAdjoint.star_mul_self _).isStarNormal, fun z hz ↦ by
        rw [show K = Metric.closedBall (0 : ℂ) R from rfl, Metric.mem_closedBall, dist_zero_right]
        exact (spectrum.norm_le_norm_of_mem hz).trans hU.le⟩
    have hc := continuousOn_cfc (Operator n) (isCompact_closedBall (0 : ℂ) R) f hf.continuousOn
    exact (hc (F T) he.self_of_nhds).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hF.continuousAt.tendsto, he⟩)
  change Continuous (fun T ↦ traceRe (cfc (p := IsStarNormal) f (F T)) ^ (1 / p))
  exact (Real.continuous_rpow_const (by positivity : 0 ≤ 1 / p)).comp
    ((continuous_traceRe n).comp hFcfc)

/-- On a positive Fourier polynomial, one can take the power directly in
the reduced group C*-algebra. -/
theorem lpNorm_eq_group_trace_rpow_of_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p)
    {x : GroupAlgebra n} (hx : 0 ≤ regularImage x) :
    lpNorm p x =
      (groupTraceReCLM n
        (cfc (p := IsSelfAdjoint) (fun z : ℝ ↦ z ^ p) (polynomialInclusion n x))) ^ (1 / p) := by
  let T := regularImage x
  have hT : IsSelfAdjoint T := (ContinuousLinearMap.nonneg_iff_isPositive.mp hx).isSelfAdjoint
  have hT' : IsSelfAdjoint (polynomialInclusion n x) := by
    apply Subtype.ext
    change star (polynomialInclusion n x : Operator n) = (polynomialInclusion n x : Operator n)
    simpa only [polynomialInclusion_coe] using hT.star_eq
  rw [groupTraceReCLM_apply,
    groupCStar_coe_real_cfc _ (Real.continuous_rpow_const hp) _ hT', polynomialInclusion_coe,
    lpNorm_eq_operatorLpNorm, operatorLpNorm]
  change (traceRe (cfc (p := IsStarNormal)
    (fun z : ℂ ↦ Complex.ofReal (z.re ^ (p / 2))) (star T * T))) ^ (1 / p) = _
  rw [hT.star_eq, ← pow_two]
  let f (z : ℂ) := Complex.ofReal (z.re ^ (p / 2))
  have hf : Continuous f :=
    Complex.continuous_ofReal.comp ((Real.continuous_rpow_const (by positivity :
      0 ≤ p / 2)).comp Complex.continuous_re)
  have heq : cfc (p := IsStarNormal) f (T ^ 2) =
      cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (z.re ^ p)) T := by
    rw [← cfc_comp_pow f 2 T hf.continuousOn hT.isStarNormal]
    apply cfc_congr
    intro z hz
    have hzpos : 0 ≤ z := spectrum_nonneg_of_nonneg hx hz
    obtain ⟨hzre, hzim⟩ := Complex.nonneg_iff.mp hzpos
    have hreal : Complex.ofReal z.re = z := Complex.ext (by simp) (by simpa using hzim)
    rw [← hreal]
    change f ((Complex.ofReal z.re) ^ 2) = Complex.ofReal (((Complex.ofReal z.re).re) ^ p)
    rw [← Complex.ofReal_pow]
    change Complex.ofReal (((z.re ^ (2 : ℕ)) : ℝ) ^ (p / 2)) = Complex.ofReal (z.re ^ p)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hzre]
    norm_num
    congr 1
    ring
  rw [heq]

end FreeGroupHypercontractivity
