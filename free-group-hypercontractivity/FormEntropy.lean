module

import all «free-group-hypercontractivity».Model
public import «free-group-hypercontractivity».OperatorMajorant
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import «free-group-hypercontractivity».VonNeumannTrace

public section

namespace FreeGroupHypercontractivity

open scoped ComplexOrder InnerProductSpace Topology

private def cutoffValue (k : ℕ) : ℝ := (k : ℝ) + 1

private noncomputable def cutoffTransform (k : ℕ) : ℝ :=
  cutoffValue k / (1 + cutoffValue k)

private theorem cutoffValue_ge_one (k : ℕ) : 1 ≤ cutoffValue k := by
  unfold cutoffValue
  linarith [Nat.cast_nonneg (α := ℝ) k]

private theorem cutoffTransform_pos (k : ℕ) : 0 < cutoffTransform k := by
  unfold cutoffTransform
  have := cutoffValue_ge_one k
  positivity

private theorem cutoffTransform_lt_one (k : ℕ) : cutoffTransform k < 1 := by
  have := cutoffValue_ge_one k
  unfold cutoffTransform
  exact (div_lt_one (by positivity)).mpr (lt_one_add _)

private theorem cutoffTransform_mul (k : ℕ) :
    cutoffValue k * (1 - cutoffTransform k) = cutoffTransform k := by
  have := cutoffValue_ge_one k
  unfold cutoffTransform
  field_simp
  ring

private noncomputable def cutoffWeight (k : ℕ) (s : ℝ) : ℝ :=
  min 1 (cutoffValue k * (1 - s) / max (cutoffTransform k) s)

private theorem continuous_truncation (k : ℕ) :
    Continuous (boundedTransformTruncation k) := by
  change Continuous (fun s : ℝ ↦ min (max 0 s) (cutoffTransform k) /
    (1 - min (max 0 s) (cutoffTransform k)))
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro s
  exact sub_ne_zero.mpr ((min_le_right _ _).trans_lt (cutoffTransform_lt_one k)).ne'

private theorem continuous_cutoffWeight (k : ℕ) : Continuous (cutoffWeight k) := by
  unfold cutoffWeight
  apply continuous_const.min
  exact (by fun_prop : Continuous (fun s : ℝ ↦ cutoffValue k * (1 - s))).div
    (continuous_const.max continuous_id) fun s ↦
      ((cutoffTransform_pos k).trans_le (le_max_left _ _)).ne'

private theorem truncation_of_le (k : ℕ) {s : ℝ} (hs : 0 ≤ s) (hsc : s ≤ cutoffTransform k) :
    boundedTransformTruncation k s = s / (1 - s) := by
  change min (max 0 s) (cutoffTransform k) /
    (1 - min (max 0 s) (cutoffTransform k)) = _
  rw [max_eq_right hs, min_eq_left hsc]

private theorem truncation_of_ge (k : ℕ) {s : ℝ} (hsc : cutoffTransform k ≤ s) :
    boundedTransformTruncation k s = cutoffValue k := by
  have hs := (cutoffTransform_pos k).le.trans hsc
  change min (max 0 s) (cutoffTransform k) /
    (1 - min (max 0 s) (cutoffTransform k)) = _
  rw [max_eq_right hs, min_eq_right hsc, div_eq_iff (sub_ne_zero.mpr (cutoffTransform_lt_one k).ne')]
  exact (cutoffTransform_mul k).symm

private theorem cutoffWeight_of_le (k : ℕ) {s : ℝ} (hsc : s ≤ cutoffTransform k) :
    cutoffWeight k s = 1 := by
  rw [cutoffWeight, max_eq_left hsc, min_eq_left]
  apply (le_div_iff₀ (cutoffTransform_pos k)).mpr
  rw [one_mul, ← cutoffTransform_mul k]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hsc _) (zero_le_one.trans (cutoffValue_ge_one k))

private theorem cutoffWeight_of_ge (k : ℕ) {s : ℝ} (hsc : cutoffTransform k ≤ s) :
    cutoffWeight k s = cutoffValue k * (1 - s) / s := by
  rw [cutoffWeight, max_eq_right hsc, min_eq_right]
  apply (div_le_one ((cutoffTransform_pos k).trans_le hsc)).mpr
  calc
    _ ≤ cutoffValue k * (1 - cutoffTransform k) := by
      exact mul_le_mul_of_nonneg_left (sub_le_sub_left hsc _) (zero_le_one.trans (cutoffValue_ge_one k))
    _ = cutoffTransform k := cutoffTransform_mul k
    _ ≤ s := hsc

private theorem cutoffWeight_nonneg (k : ℕ) {s : ℝ} (hs : s ≤ 1) :
    0 ≤ cutoffWeight k s := by
  unfold cutoffWeight
  exact le_min zero_le_one (div_nonneg
    (mul_nonneg (zero_le_one.trans (cutoffValue_ge_one k)) (sub_nonneg.mpr hs))
    ((cutoffTransform_pos k).le.trans (le_max_left _ _)))

private theorem cutoffWeight_sq_le_one (k : ℕ) {s : ℝ} (hs : s ≤ 1) :
    cutoffWeight k s ^ 2 ≤ 1 := by
  simpa only [one_pow] using pow_le_pow_left₀ (cutoffWeight_nonneg k hs)
    (min_le_left (1 : ℝ) (cutoffValue k * (1 - s) / max (cutoffTransform k) s)) 2

private theorem truncation_mul_eq (k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (1 - s) * boundedTransformTruncation k s = cutoffWeight k s * s := by
  by_cases h : s ≤ cutoffTransform k
  · rw [truncation_of_le k hs h, cutoffWeight_of_le k h, one_mul, mul_div_cancel₀]
    exact (sub_ne_zero.mpr (h.trans_lt (cutoffTransform_lt_one k)).ne')
  · have hc : cutoffTransform k ≤ s := (le_of_not_ge h)
    rw [truncation_of_ge k hc, cutoffWeight_of_ge k hc,
      div_mul_cancel₀ _ ((cutoffTransform_pos k).trans_le hc).ne', mul_comm]

private theorem log_cutoff_domination (k : ℕ) {s e : ℝ} (hs : s ≤ 1) (he : 0 < e) :
    cutoffWeight k s * Real.log (boundedTransformTruncation k s ^ 2 + e) * cutoffWeight k s ≤
      Real.log (boundedTransformTruncation k s ^ 2 + e) := by
  by_cases h : s ≤ cutoffTransform k
  · simp [cutoffWeight_of_le k h]
  · have hc : cutoffTransform k ≤ s := le_of_not_ge h
    have hlog : 0 ≤ Real.log (boundedTransformTruncation k s ^ 2 + e) := by
      rw [truncation_of_ge k hc]
      apply Real.log_nonneg
      have := cutoffValue_ge_one k
      nlinarith
    calc
      _ = cutoffWeight k s ^ 2 * Real.log (boundedTransformTruncation k s ^ 2 + e) := by ring
      _ ≤ 1 * Real.log (boundedTransformTruncation k s ^ 2 + e) :=
        mul_le_mul_of_nonneg_right (cutoffWeight_sq_le_one k hs) hlog
      _ = _ := one_mul _

private noncomputable def realCalc {n : ℕ} (B : Operator n) (f : ℝ → ℝ) : Operator n :=
  cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (f z.re)) B

private theorem continuous_realSymbol {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun z : ℂ ↦ Complex.ofReal (f z.re)) :=
  Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)

private theorem realCalc_mul {n : ℕ} (B : Operator n) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    realCalc B (fun s ↦ f s * g s) = realCalc B f * realCalc B g := by
  simpa only [realCalc, Complex.ofReal_mul] using cfc_mul
    (fun z : ℂ ↦ Complex.ofReal (f z.re)) (fun z : ℂ ↦ Complex.ofReal (g z.re)) B
    (continuous_realSymbol hf).continuousOn (continuous_realSymbol hg).continuousOn

private theorem realCalc_one {n : ℕ} {B : Operator n} (hB : IsStarNormal B) :
    realCalc B (fun _ ↦ 1) = 1 := by
  simp only [realCalc, Complex.ofReal_one]
  exact cfc_const_one ℂ B hB

private theorem realCalc_id {n : ℕ} {B : Operator n} (hB : 0 ≤ B) :
    realCalc B id = B := by
  let hsa := (ContinuousLinearMap.nonneg_iff_isPositive.mp hB).isSelfAdjoint
  conv_rhs => rw [← cfc_id' ℂ B hsa.isStarNormal]
  unfold realCalc
  apply cfc_congr
  intro z hz
  obtain ⟨s, -, rfl⟩ := exists_ofReal_of_spectrum_nonneg hB hz
  simp

private theorem realCalc_one_sub {n : ℕ} {B : Operator n} (hB : 0 ≤ B) :
    realCalc B (fun s ↦ 1 - s) = 1 - B := by
  have hsa := (ContinuousLinearMap.nonneg_iff_isPositive.mp hB).isSelfAdjoint
  have h := cfc_sub (fun _ : ℂ ↦ (1 : ℂ)) (fun z : ℂ ↦ Complex.ofReal z.re) B
    continuous_const.continuousOn (continuous_realSymbol continuous_id).continuousOn
  have h₁ : cfc (p := IsStarNormal) (fun _ : ℂ ↦ (1 : ℂ)) B = 1 :=
    cfc_const_one ℂ B hsa.isStarNormal
  have hid : cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal z.re) B = B := realCalc_id hB
  unfold realCalc
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  exact h.trans (congrArg₂ (· - ·) h₁ hid)

private theorem realCalc_selfAdjoint {n : ℕ} (B : Operator n) (f : ℝ → ℝ) :
    IsSelfAdjoint (realCalc B f) := by
  change star (realCalc B f) = realCalc B f
  unfold realCalc
  rw [← cfc_star]
  simp

private theorem realCalc_le {n : ℕ} {B : Operator n} {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ z ∈ spectrum ℂ B, f z.re ≤ g z.re) :
    realCalc B f ≤ realCalc B g := by
  apply cfc_mono _ (continuous_realSymbol hf).continuousOn (continuous_realSymbol hg).continuousOn
  exact fun z hz ↦ Complex.real_le_real.mpr (h z hz)

private theorem quad_le {n : ℕ} {A B : Operator n} (h : A ≤ B) (v : Hilbert n) :
    (⟪v, A v⟫_ℂ).re ≤ (⟪v, B v⟫_ℂ).re := by
  have hpos := (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr h)).re_inner_nonneg_right v
  change 0 ≤ (⟪v, B v - A v⟫_ℂ).re at hpos
  rw [inner_sub_right, Complex.sub_re] at hpos
  exact sub_nonneg.mp hpos

private theorem quad_conjugate {n : ℕ} {W : Operator n}
    (hW : IsSelfAdjoint W) (K : Operator n) (v : Hilbert n) :
    (⟪v, (W * K * W) v⟫_ℂ).re = (⟪W v, K (W v)⟫_ℂ).re := by
  have hW' : W.adjoint = W := by rw [← ContinuousLinearMap.star_eq_adjoint, hW.star_eq]
  have h := ContinuousLinearMap.adjoint_inner_right W v (K (W v))
  rw [hW'] at h
  exact congrArg Complex.re h

private theorem quad_one {n : ℕ} (v : Hilbert n) :
    (⟪v, (1 : Operator n) v⟫_ℂ).re = ‖v‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) v

private theorem trace_realCalc_add_const {n : ℕ} {B : Operator n} (hB : IsStarNormal B)
    {f : ℝ → ℝ} (hf : Continuous f) (e : ℝ) :
    traceRe (realCalc B (fun s ↦ f s + e)) = traceRe (realCalc B f) + e := by
  unfold realCalc
  simp only [Complex.ofReal_add]
  rw [cfc_add_const _ _ _ (continuous_realSymbol hf).continuousOn hB, traceRe_add,
    Algebra.algebraMap_eq_smul_one, traceRe_ofReal_smul, traceRe_one, mul_one]

private theorem log_test_bound {n : ℕ} (x : PositiveAffiliatedL2 n) (E : ℝ)
    (hG : ∀ K : Operator n, K ∈ groupVonNeumann n → IsSelfAdjoint K →
      (⟪x.fourierVector, K x.fourierVector⟫_ℂ).re ≤
        E + ‖x.fourierVector‖^2 * Real.log (traceRe (NormedSpace.exp K)))
    (k : ℕ) {e : ℝ} (he : 0 < e) :
    traceRe (realCalc x.boundedTransform (fun s ↦
      boundedTransformTruncation k s ^ 2 * Real.log (boundedTransformTruncation k s ^ 2))) ≤
      E + ‖x.fourierVector‖^2 * Real.log (‖x.fourierVector‖^2 + e) := by
  let B := x.boundedTransform
  let v := x.fourierVector
  let d : Hilbert n := lp.single 2 1 1
  let f := boundedTransformTruncation k
  let w := cutoffWeight k
  let ell (s : ℝ) := Real.log (f s ^ 2 + e)
  let F := realCalc B f
  let W := realCalc B w
  let K := realCalc B ell
  have hB : 0 ≤ B := x.transform_nonneg
  have hBsa := (ContinuousLinearMap.nonneg_iff_isPositive.mp hB).isSelfAdjoint
  have hnorm := hBsa.isStarNormal
  have hf : Continuous f := continuous_truncation k
  have hw : Continuous w := continuous_cutoffWeight k
  have hell : Continuous ell := (hf.pow 2 |>.add continuous_const).log
    (fun s ↦ (add_pos_of_nonneg_of_pos (sq_nonneg _) he).ne')
  have hspectrum (z : ℂ) (hz : z ∈ spectrum ℂ B) : 0 ≤ z.re ∧ z.re ≤ 1 := by
    have h₀ := spectrum_nonneg_of_nonneg hB hz
    have h₁ := (CFC.le_one_iff (R := ℂ) B hnorm).mp x.transform_le_one z hz
    exact ⟨(Complex.nonneg_iff.mp h₀).1, (Complex.le_def.mp h₁).1⟩
  have hDW : (1 - B) * W = W * (1 - B) := by
    have hcomm : Commute W B := hBsa.commute_cfc (Commute.refl B) _
    exact ((Commute.one_right W).sub_right hcomm).eq.symm
  have hWB : W * B = (1 - B) * F := by
    calc
      _ = W * realCalc B id := congrArg (W * ·) (realCalc_id hB).symm
      _ = realCalc B (fun s ↦ w s * s) := (realCalc_mul B hw continuous_id).symm
      _ = realCalc B (fun s ↦ (1 - s) * f s) := by
        unfold realCalc
        apply cfc_congr
        intro z hz
        exact congrArg Complex.ofReal (truncation_mul_eq k (hspectrum z hz).1).symm
      _ = _ := by
        have hc : Continuous (fun s : ℝ ↦ 1 - s) := continuous_const.sub continuous_id
        rw [realCalc_mul B hc hf, realCalc_one_sub hB]
  have hWv : W v = F d := by
    apply x.one_sub_injective
    calc
      (1 - B) (W v) = W ((1 - B) v) := congrArg (fun T : Operator n ↦ T v) hDW
      _ = W (B d) := congrArg W x.resolvent_eq
      _ = (1 - B) (F d) := congrArg (fun T : Operator n ↦ T d) hWB
  have hWsa : IsSelfAdjoint W := realCalc_selfAdjoint B w
  have hFsa : IsSelfAdjoint F := realCalc_selfAdjoint B f
  have hKsa : IsSelfAdjoint K := realCalc_selfAdjoint B ell
  have hWexp : realCalc B (fun s ↦ w s ^ 2) = W * 1 * W := by
    simp only [pow_two]
    rw [realCalc_mul B hw hw, mul_one]
  have hFexp : realCalc B (fun s ↦ f s ^ 2) = F * 1 * F := by
    simp only [pow_two]
    rw [realCalc_mul B hf hf, mul_one]
  have hmass : traceRe (realCalc B (fun s ↦ f s ^ 2)) ≤ ‖v‖^2 := by
    have hop : realCalc B (fun s ↦ w s ^ 2) ≤ 1 := by
      rw [← realCalc_one hnorm]
      exact realCalc_le (hw.pow 2) continuous_const fun z hz ↦ cutoffWeight_sq_le_one k (hspectrum z hz).2
    have hv := quad_le hop v
    rw [hWexp, quad_conjugate hWsa, hWv, quad_one, quad_one] at hv
    rw [hFexp, traceRe_as_inner, quad_conjugate hFsa, quad_one]
    exact hv
  have hcompare : (⟪F d, K (F d)⟫_ℂ).re ≤ (⟪v,K v⟫_ℂ).re := by
    have hwl : Continuous (fun s ↦ w s * ell s) := hw.mul hell
    have hwlw : Continuous (fun s ↦ w s * ell s * w s) := hwl.mul hw
    have hWK : W * K * W ≤ K := by
      rw [← realCalc_mul B hw hell, ← realCalc_mul B hwl hw]
      exact realCalc_le hwlw hell fun z hz ↦ log_cutoff_domination k (hspectrum z hz).2 he
    simpa only [quad_conjugate hWsa, hWv] using quad_le hWK v
  have hmoment : traceRe (realCalc B (fun s ↦ f s ^ 2 * Real.log (f s ^ 2))) ≤
      (⟪F d,K (F d)⟫_ℂ).re := by
    have hfl : Continuous (fun s ↦ f s * ell s) := hf.mul hell
    have hflf : Continuous (fun s ↦ f s * ell s * f s) := hfl.mul hf
    have hmomentFun : Continuous (fun s ↦ f s ^ 2 * Real.log (f s ^ 2)) :=
      Real.continuous_mul_log.comp (hf.pow 2)
    have hop := realCalc_le hmomentFun hflf (B := B) (fun z _ ↦ by
        let a := f z.re ^ 2
        have ha : 0 ≤ a := sq_nonneg _
        have h₀ : a * Real.log a ≤ a * Real.log (a + e) := by
          rcases ha.eq_or_lt with ha' | ha'
          · simp [← ha']
          · exact mul_le_mul_of_nonneg_left (Real.log_le_log ha' (le_add_of_nonneg_right he.le)) ha'.le
        simpa only [a, ell, pow_two, mul_assoc, mul_left_comm, mul_comm] using h₀)
    have htrace := traceRe_mono hop
    rw [realCalc_mul B hfl hf, realCalc_mul B hf hell, traceRe_as_inner (F * K * F),
      quad_conjugate hFsa] at htrace
    exact htrace
  have hKmem : K ∈ groupVonNeumann n := cfc_mem_groupVonNeumann _ x.transform_mem
  have hExp : NormedSpace.exp K = realCalc B (fun s ↦ f s ^ 2 + e) := by
    rw [← CFC.complex_exp_eq_normedSpace_exp hKsa.isStarNormal]
    change cfc (p := IsStarNormal) Complex.exp
      (cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (ell z.re)) B) = _
    rw [← cfc_comp' Complex.exp _ B Complex.continuous_exp.continuousOn
      (continuous_realSymbol hell).continuousOn hnorm]
    unfold realCalc
    apply cfc_congr
    intro z _
    change Complex.exp (Complex.ofReal (ell z.re)) = Complex.ofReal (f z.re ^ 2 + e)
    rw [← Complex.ofReal_exp, show ell z.re = Real.log (f z.re ^ 2 + e) from rfl,
      Real.exp_log (add_pos_of_nonneg_of_pos (sq_nonneg _) he)]
  have hf₂ : Continuous (fun s ↦ f s ^ 2) := hf.pow 2
  have htraceExp : traceRe (NormedSpace.exp K) ≤ ‖v‖^2 + e := by
    rw [hExp, trace_realCalc_add_const hnorm hf₂ e]
    exact add_le_add hmass le_rfl
  have htracePos : 0 < traceRe (NormedSpace.exp K) := by
    rw [hExp, trace_realCalc_add_const hnorm hf₂ e]
    have hp : 0 ≤ realCalc B (fun s ↦ f s ^ 2) :=
      cfc_nonneg (f := fun z : ℂ ↦ Complex.ofReal (f z.re ^ 2))
        (fun z _ ↦ by
          rw [← Complex.ofReal_zero, Complex.real_le_real]
          exact sq_nonneg _)
    exact add_pos_of_nonneg_of_pos (traceRe_nonneg hp) he
  exact (hmoment.trans hcompare).trans ((hG K hKmem hKsa).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.log_le_log htracePos htraceExp)
      (sq_nonneg ‖v‖))))

/-- Testing against bounded logarithmic cutoffs recovers the entropy of a
positive affiliated L² element, including the supremum over its truncations. -/
theorem affiliated_entropySq_le_of_gibbs {n : ℕ} (x : PositiveAffiliatedL2 n) (E : ℝ)
    (hG : ∀ K : Operator n, K ∈ groupVonNeumann n → IsSelfAdjoint K →
      (⟪x.fourierVector, K x.fourierVector⟫_ℂ).re ≤
        E + ‖x.fourierVector‖^2 * Real.log (traceRe (NormedSpace.exp K))) :
    x.entropySq ≤ (E : EReal) := by
  let m := ‖x.fourierVector‖ ^ 2
  have hm : 0 ≤ m := sq_nonneg _
  have hEach (k : ℕ) :
      traceRe (realCalc x.boundedTransform (fun s ↦
        boundedTransformTruncation k s ^ 2 * Real.log (boundedTransformTruncation k s ^ 2))) ≤
        E + m * Real.log m := by
    rcases hm.eq_or_lt with hzero | hpos
    · simpa only [m, ← hzero, zero_mul, add_zero] using log_test_bound x E hG k zero_lt_one
    · have hc : ContinuousAt (fun e : ℝ ↦ E + m * Real.log (m + e)) 0 := by
        apply continuousAt_const.add
        apply continuousAt_const.mul
        apply (continuousAt_const.add continuousAt_id).log
        change m + (0 : ℝ) ≠ 0
        rw [add_zero]
        exact hpos.ne'
      have hlim := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      let _ := nhdsGT_neBot (0 : ℝ)
      apply le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa using hlim)
      filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with e he
      exact log_test_bound x E hG k he
  change (⨆ k : ℕ, (traceRe (realCalc x.boundedTransform (fun s ↦
      boundedTransformTruncation k s ^ 2 * Real.log (boundedTransformTruncation k s ^ 2))) : EReal)) -
      (↑(m * Real.log m) : EReal) ≤ ↑E
  have hsup :
      (⨆ k : ℕ, (traceRe (realCalc x.boundedTransform (fun s ↦
        boundedTransformTruncation k s ^ 2 * Real.log (boundedTransformTruncation k s ^ 2))) : EReal)) ≤
        ((E + m * Real.log m : ℝ) : EReal) :=
    iSup_le fun k ↦ EReal.coe_le_coe (hEach k)
  simpa only [← EReal.coe_sub, add_sub_cancel_right] using EReal.sub_le_sub hsup
    (le_rfl : (↑(m * Real.log m) : EReal) ≤ ↑(m * Real.log m))

end FreeGroupHypercontractivity
