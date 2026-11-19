module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».FourierEnergy
public import «free-group-hypercontractivity».HypercontractivityNorm
public import «free-group-hypercontractivity».FormExponential
public import «free-group-hypercontractivity».VonNeumannTrace
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

public section

namespace FreeGroupHypercontractivity

open Filter Set
open scoped ENNReal InnerProductSpace Topology ComplexOrder

local notation "δ₁" => lp.single 2 1 1

private theorem hilbert_norm_sq {n : ℕ} (v : Hilbert n) :
    ‖v‖ ^ 2 = ∑' g : Group n, ‖v g‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.norm_rpow_eq_tsum (by norm_num) v)

private theorem hilbert_summable_sq {n : ℕ} (v : Hilbert n) :
    Summable (fun g : Group n ↦ ‖v g‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp v).summable (by norm_num)

private noncomputable def poissonWeight (t : ℝ) (l : ℕ) : ℝ :=
  Real.exp (-(max t 0) * (l : ℝ))

private theorem poissonWeight_of_nonneg {t : ℝ} (ht : 0 ≤ t) (l : ℕ) :
    poissonWeight t l = Real.exp (-t * (l : ℝ)) := by
  simp only [poissonWeight, max_eq_left ht]

private theorem poissonWeight_nonneg (t : ℝ) (l : ℕ) :
    0 ≤ poissonWeight t l := Real.exp_nonneg _

private theorem poissonWeight_le_one (t : ℝ) (l : ℕ) :
    poissonWeight t l ≤ 1 := by
  rw [poissonWeight, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (le_max_right t 0)) (Nat.cast_nonneg l))

private noncomputable def poissonVector {n : ℕ} (t : ℝ) (v : Hilbert n) : Hilbert n :=
  ⟨fun g ↦ Complex.ofReal (poissonWeight t (FreeGroup.norm g)) * v g,
    memℓp_gen (by
      simp only [ENNReal.toReal_ofNat, Real.rpow_two]
      refine Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _) (fun g ↦ ?_)
        (hilbert_summable_sq v)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (poissonWeight_nonneg _ _)]
      exact pow_le_pow_left₀ (mul_nonneg (poissonWeight_nonneg _ _) (norm_nonneg _))
        (mul_le_of_le_one_left (norm_nonneg _) (poissonWeight_le_one _ _)) 2)⟩

private theorem poissonVector_apply {n : ℕ} (t : ℝ) (v : Hilbert n) (g : Group n) :
    poissonVector t v g = Complex.ofReal (poissonWeight t (FreeGroup.norm g)) * v g := rfl

private theorem poissonVector_tendsto {n : ℕ} (v : Hilbert n) :
    Tendsto (fun t ↦ poissonVector t v) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
  have hsum : Tendsto (fun t : ℝ ↦ ∑' g : Group n,
      ‖(poissonVector t v - v) g‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence
      (hilbert_summable_sq v)
      (g := fun _ : Group n ↦ 0)
      (f := fun t : ℝ ↦ fun g : Group n ↦ ‖(poissonVector t v - v) g‖ ^ 2)
      (𝓕 := 𝓝[>] (0 : ℝ)) ?_ ?_
    · simpa using h
    · intro g
      have hc : Continuous (fun t : ℝ ↦
          ‖Complex.ofReal (poissonWeight t (FreeGroup.norm g)) * v g - v g‖ ^ 2) := by
        unfold poissonWeight
        fun_prop
      simp only [lp.coeFn_sub, Pi.sub_apply, poissonVector_apply]
      simpa [poissonWeight] using
        (hc.continuousAt (x := (0 : ℝ))).continuousWithinAt.tendsto
    · filter_upwards with t g
      have hm : (poissonWeight t (FreeGroup.norm g) : ℂ) * v g - v g =
          ((poissonWeight t (FreeGroup.norm g) : ℂ) - 1) * v g := by
        rw [sub_mul, one_mul]
      rw [Real.norm_of_nonneg (sq_nonneg _), lp.coeFn_sub, Pi.sub_apply, poissonVector_apply,
        hm, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (poissonWeight_le_one _ _))]
      apply pow_le_pow_left₀ (mul_nonneg (by linarith [poissonWeight_le_one t (FreeGroup.norm g)])
        (norm_nonneg _)) (mul_le_of_le_one_left (norm_nonneg _) ?_) 2
      linarith [poissonWeight_nonneg t (FreeGroup.norm g)]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs : Tendsto (fun t ↦ ‖poissonVector t v - v‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [hilbert_norm_sq] using hsum
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

private theorem poissonVector_norm_sq_of_nonneg {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (v : Hilbert n) :
    ‖poissonVector t v‖ ^ 2 =
      ∑' g : Group n, Real.exp (-(2*t) * (FreeGroup.norm g : ℝ)) * ‖v g‖ ^ 2 := by
  rw [hilbert_norm_sq]
  apply tsum_congr
  intro g
  rw [poissonVector_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (poissonWeight_nonneg _ _),
    mul_pow, poissonWeight_of_nonneg ht, ← Real.exp_nat_mul]
  push_cast
  ring_nf

private theorem poissonVector_dissipation {n : ℕ} (v : Hilbert n) (hv : inFormDomain v) :
    Tendsto (fun t ↦ (‖v‖ ^ 2 - ‖poissonVector t v‖ ^ 2) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * formEnergy v)) := by
  have h := tendsto_poisson_energy (fun g : Group n ↦ (FreeGroup.norm g : ℝ))
    (fun g ↦ ‖v g‖ ^ 2) (fun _ ↦ by positivity)
    (by simpa only [inFormDomain, abs_pow, abs_norm] using hv)
  have h2t : Tendsto (fun t : ℝ ↦ 2 * t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun t : ℝ ↦ 2 * t) := by fun_prop
      simpa [ContinuousWithinAt] using hc.continuousWithinAt (s := Ioi 0) (x := 0)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos (by norm_num) ht
  have hd := (h.comp h2t).const_mul 2
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  change 2 * (∑' g : Group n, poissonDifferenceWeight (2 * t) (FreeGroup.norm g) * ‖v g‖ ^ 2) =
    (‖v‖ ^ 2 - ‖poissonVector t v‖ ^ 2) / t
  have hM : Summable (fun g : Group n ↦
      Real.exp (-(2*t) * (FreeGroup.norm g : ℝ)) * ‖v g‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun g ↦ ?_) (hilbert_summable_sq v)
    apply mul_le_of_le_one_left (sq_nonneg _)
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _))
  rw [hilbert_norm_sq, poissonVector_norm_sq_of_nonneg ht.le,
    ← (hilbert_summable_sq v).tsum_sub hM, div_eq_mul_inv, ← tsum_mul_right, ← tsum_mul_left]
  apply tsum_congr
  intro g
  rw [poissonDifferenceWeight]
  field_simp

private noncomputable def vectorTruncation {n : ℕ} (v : Hilbert n)
    (s : Finset (Group n)) : GroupAlgebra n := by
  classical
  exact MonoidAlgebra.ofCoeff (Finsupp.onFinset s (fun g ↦ if g ∈ s then v g else 0)
    (fun g hg ↦ by by_contra! he; simp [he] at hg))

private theorem vectorTruncation_coeff {n : ℕ} (v : Hilbert n) (s : Finset (Group n))
    (g : Group n) :
    (vectorTruncation v s).coeff g = if g ∈ s then v g else 0 := by
  classical
  simp [vectorTruncation, Finsupp.onFinset_apply]

private theorem traceVectorTruncation_tendsto {n : ℕ} (v : Hilbert n) :
    Tendsto (fun s : Finset (Group n) ↦ regularImage (vectorTruncation v s) δ₁)
      atTop (𝓝 v) := by
  classical
  have h (s : Finset (Group n)) :
      regularImage (vectorTruncation v s) δ₁ = ∑ g ∈ s, lp.single 2 g (v g) := by
    ext g
    rw [regularImage_delta, vectorTruncation_coeff, lp.coeFn_sum, Finset.sum_apply]
    simp [lp.single_apply, Pi.single_apply]
  have hsum : Tendsto (fun s : Finset (Group n) ↦ ∑ g ∈ s, lp.single 2 g (v g))
      atTop (𝓝 v) := lp.hasSum_single ENNReal.ofNat_ne_top v
  simpa only [h] using hsum

private theorem poisson_vectorTruncation {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (v : Hilbert n)
    (s : Finset (Group n)) :
    poisson t (vectorTruncation v s) = vectorTruncation (poissonVector t v) s := by
  classical
  ext g
  simp only [poisson_coeff, vectorTruncation_coeff, poissonVector_apply, poissonWeight_of_nonneg ht]
  split_ifs <;> simp

private theorem lpNorm_two_eq_trace_vector {n : ℕ} (x : GroupAlgebra n) :
    lpNorm 2 x = ‖regularImage x δ₁‖ := by
  rw [lpNorm_eq_operatorLpNorm]
  let T := regularImage x
  change traceRe (operatorRpow (star T * T) (2 / 2)) ^ (1 / 2) = _
  rw [show (2 : ℝ) / 2 = 1 by norm_num, operatorRpow_one (star_mul_self_nonneg T),
    traceRe_star_mul_self, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

private noncomputable def testExponent (t : ℝ) : ℝ :=
  1 - 2 / (1 + Real.exp (2 * t))

private theorem testExponent_zero : testExponent 0 = 0 := by
  norm_num [testExponent]

private theorem hasDerivAt_testExponent : HasDerivAt testExponent 1 0 := by
  have he₀ : HasDerivAt (fun t : ℝ ↦ 2 * t) 2 0 := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul 2
  have hexp := (Real.hasDerivAt_exp (2 * (0 : ℝ))).comp 0 he₀
  have he : HasDerivAt (fun t : ℝ ↦ 1 + Real.exp (2*t)) 2 0 := by
    simpa [Function.comp_def] using hexp.const_add 1
  have hfrac := (hasDerivAt_const (0 : ℝ) (2 : ℝ)).div he (by norm_num)
  convert hfrac.const_sub 1 using 1
  · rfl
  · norm_num

private theorem testExponent_rpow_slope {C : ℝ} (hC : 0 < C) :
    Tendsto (fun t ↦ (C ^ testExponent t - 1) / t) (𝓝[>] 0) (𝓝 (Real.log C)) := by
  have h := (Real.hasDerivAt_exp (Real.log C * testExponent 0)).comp 0
    (hasDerivAt_testExponent.const_mul (Real.log C))
  have hf : HasDerivAt (fun t ↦ C ^ testExponent t) (Real.log C) 0 := by
    simpa [testExponent_zero, Function.comp_def, Real.rpow_def_of_pos hC] using h
  simpa only [zero_add, testExponent_zero, Real.rpow_zero, smul_eq_mul, div_eq_inv_mul] using
    hf.tendsto_slope_zero_right

private theorem testExponent_exp_slope {n : ℕ} (K : Operator n) :
    Tendsto (fun t ↦ (t⁻¹ : ℝ) • (NormedSpace.exp (testExponent t • K) - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 K) := by
  have h := (hasDerivAt_operatorExp_smul K (testExponent 0)).scomp 0
    hasDerivAt_testExponent
  rw [testExponent_zero, zero_smul ℝ K, NormedSpace.exp_zero, one_mul, one_smul ℝ K] at h
  have hf : HasDerivAt (fun t ↦ NormedSpace.exp (testExponent t • K)) K 0 := h
  simpa only [zero_add, testExponent_zero, zero_smul ℝ K, NormedSpace.exp_zero] using
    hf.tendsto_slope_zero_right

private theorem testExponent_inner_slope {n : ℕ} (K : Operator n) (v : Hilbert n) :
    Tendsto (fun t ↦ ((⟪poissonVector t v,
      NormedSpace.exp (testExponent t • K) (poissonVector t v)⟫_ℂ).re -
      ‖poissonVector t v‖ ^ 2) / t) (𝓝[>] (0 : ℝ)) (𝓝 (⟪v, K v⟫_ℂ).re) := by
  have hv := poissonVector_tendsto v
  have hT := testExponent_exp_slope K
  have hc : Continuous (fun p : Operator n × Hilbert n ↦ p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hTv := (hc.continuousAt (x := (K, v))).tendsto.comp (hT.prodMk_nhds hv)
  have ht := Complex.continuous_re.continuousAt.tendsto.comp (hv.inner hTv)
  apply ht.congr'
  filter_upwards with t
  let w := poissonVector t v
  let E := NormedSpace.exp (testExponent t • K)
  change (⟪w, ((t⁻¹ : ℝ) • (E - 1)) w⟫_ℂ).re = ((⟪w, E w⟫_ℂ).re - ‖w‖ ^ 2) / t
  have hself : (⟪w, w⟫_ℂ).re = ‖w‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) w
  rw [smul_apply, inner_smul_right_eq_smul, Complex.smul_re, sub_apply,
    one_apply_eq_self, inner_sub_right, Complex.sub_re, hself, div_eq_inv_mul, smul_eq_mul]

private theorem form_test_of_exp_bound {n : ℕ} (v : Hilbert n) (hv : inFormDomain v)
    (K : Operator n) (hC : 0 < traceRe (NormedSpace.exp K))
    (hbound : ∀ t : ℝ, 0 < t →
      (⟪poissonVector t v, NormedSpace.exp (testExponent t • K)
        (poissonVector t v)⟫_ℂ).re ≤ ‖v‖ ^ 2 * (traceRe (NormedSpace.exp K)) ^ testExponent t) :
    (⟪v, K v⟫_ℂ).re ≤ 2 * formEnergy v + ‖v‖ ^ 2 * Real.log (traceRe (NormedSpace.exp K)) := by
  have hleft := testExponent_inner_slope K v
  have hright := (poissonVector_dissipation v hv).add
    ((testExponent_rpow_slope hC).const_mul (‖v‖ ^ 2))
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have hb := hbound t ht
  change ((⟪poissonVector t v, NormedSpace.exp (testExponent t • K)
      (poissonVector t v)⟫_ℂ).re - ‖poissonVector t v‖ ^ 2) / t ≤
    (‖v‖ ^ 2 - ‖poissonVector t v‖ ^ 2) / t +
      ‖v‖ ^ 2 * (((traceRe (NormedSpace.exp K)) ^ testExponent t - 1) / t)
  have hcalc : (‖v‖ ^ 2 - ‖poissonVector t v‖ ^ 2) / t +
      ‖v‖ ^ 2 * (((traceRe (NormedSpace.exp K)) ^ testExponent t - 1) / t) =
      (‖v‖ ^ 2 * (traceRe (NormedSpace.exp K)) ^ testExponent t -
        ‖poissonVector t v‖ ^ 2) / t := by
    ring
  rw [hcalc]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hb _) ht.le


private theorem traceRe_sandwich_eq_inner {n : ℕ} (Y E : Operator n) :
    traceRe (star Y * E * Y) = (⟪Y δ₁, E (Y δ₁)⟫_ℂ).re := by
  rw [traceRe_as_inner]
  change (⟪δ₁, Y.adjoint (E (Y δ₁))⟫_ℂ).re = _
  rw [ContinuousLinearMap.adjoint_inner_right]

private theorem traceRe_lp_power_eq_norm_sq {n : ℕ} {p : ℝ} (hp : 0 < p)
    {Y : Operator n} (hY : Y ∈ groupCStar n) :
    traceRe (operatorRpow (Y * star Y) (p / 2)) ^ (1 / (p / 2)) =
      operatorLpNorm p Y ^ 2 := by
  have hpower : Continuous (fun x : ℝ ↦ x ^ (p / 2)) :=
    continuous_id.rpow_const fun _ ↦ Or.inr (by positivity)
  have ht := traceRe_cfc_star_mul_eq_traceRe_cfc_mul_star hY hpower
  change traceRe (operatorRpow (star Y * Y) (p / 2)) =
    traceRe (operatorRpow (Y * star Y) (p / 2)) at ht
  rw [← ht]
  have htrace : 0 ≤ traceRe (operatorRpow (star Y * Y) (p / 2)) :=
    traceRe_nonneg (operatorRpow_nonneg (star_mul_self_nonneg Y))
  change traceRe (operatorRpow (star Y * Y) (p / 2)) ^ (1 / (p / 2)) =
    (traceRe (operatorRpow (star Y * Y) (p / 2)) ^ (1 / p)) ^ 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul htrace]
  congr 1
  push_cast
  field_simp

private theorem operatorLpNorm_nonneg_form {n : ℕ} (p : ℝ) (Y : Operator n) :
    0 ≤ operatorLpNorm p Y := by
  change 0 ≤ traceRe (operatorRpow (star Y * Y) (p / 2)) ^ (1 / p)
  exact Real.rpow_nonneg (traceRe_nonneg (operatorRpow_nonneg (star_mul_self_nonneg Y))) _

private theorem test_bound_fourier {n : ℕ} {t : ℝ} (ht : 0 < t)
    (K : Operator n) (hKm : K ∈ groupVonNeumann n) (hK : IsSelfAdjoint K)
    (x : GroupAlgebra n) (hcontract : lpNorm (1 + Real.exp (2*t)) (poisson t x) ≤ lpNorm 2 x) :
    let Y := regularImage (poisson t x)
    (⟪Y δ₁, NormedSpace.exp (testExponent t • K) (Y δ₁)⟫_ℂ).re ≤
      ‖regularImage x δ₁‖ ^ 2 * (traceRe (NormedSpace.exp K)) ^ testExponent t := by
  let q := 1 + Real.exp (2 * t)
  let a := testExponent t
  let r := 1 / a
  have hq : 2 < q := by
    dsimp [q]
    linarith [(Real.one_lt_exp_iff.mpr (show 0 < 2*t by positivity))]
  have haq : a = 1 - 2 / q := rfl
  have ha0 : 0 < a := by rw [haq]; exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hq)
  have ha1 : a < 1 := by rw [haq]; exact sub_lt_self _ (by positivity)
  have hr : 1 < r := (lt_div_iff₀ ha0).mpr (by simpa using ha1)
  have hra : 1 / r = a := by dsimp [r]; rw [one_div_one_div]
  have hrprod : r * a = 1 := by dsimp [r]; field_simp
  have hcr : 1 / (q / 2) + 1 / r = 1 := by
    rw [hra, haq]
    field_simp
    ring
  let V := vonNeumannStarSubalgebra n
  let Y := regularImage (poisson t x)
  let E := NormedSpace.exp (a • K)
  have hYm : Y ∈ V := mem_vonNeumannStarSubalgebra_iff.mpr (regularImage_mem_groupVonNeumann _)
  have hYstar : star Y ∈ V := star_mem hYm
  have hE0 : 0 ≤ E := operatorExp_smul_nonneg K hK a
  have hEm : E ∈ V := by
    have hKs : (a • K : Operator n) ∈ V :=
      V.smul_mem (mem_vonNeumannStarSubalgebra_iff.mpr hKm) (a : ℂ)
    exact mem_vonNeumannStarSubalgebra_iff.mpr
      (exp_mem_groupVonNeumann (mem_vonNeumannStarSubalgebra_iff.mp hKs))
  have hτ : ∀ {U W : Operator n}, U ∈ V → W ∈ V →
      traceRe (U*W) = traceRe (W*U) :=
    fun {_ _} hu hw ↦ traceRe_mul_comm_vonNeumann
      (mem_vonNeumannStarSubalgebra_iff.mp hu) (mem_vonNeumannStarSubalgebra_iff.mp hw)
  have hH := traceRe_positive_pair_holder_closed V hτ (mul_star_self_nonneg Y) hE0
    (V.mul_mem hYm hYstar) hEm (show 1 < q / 2 by linarith) hr hcr
  change traceRe ((Y * star Y) * E) ≤ _ at hH
  have hE : operatorRpow E r = NormedSpace.exp K := by
    dsimp [E]
    rw [operatorRpow_exp_smul K hK a (by linarith), hrprod, one_smul]
  have hm := traceRe_lp_power_eq_norm_sq (show 0 < q by linarith)
    (regularImage_mem_groupCStar (poisson t x))
  rw [hm, hE, hra] at hH
  have hpair : (⟪Y δ₁, E (Y δ₁)⟫_ℂ).re = traceRe ((Y * star Y) * E) := by
    rw [← traceRe_sandwich_eq_inner, hτ (V.mul_mem hYstar hEm) hYm, ← mul_assoc]
  have hcontract' : operatorLpNorm q Y ≤ ‖regularImage x δ₁‖ := by
    simpa only [lpNorm_eq_operatorLpNorm (1 + Real.exp (2*t)), lpNorm_two_eq_trace_vector] using hcontract
  change (⟪Y δ₁, E (Y δ₁)⟫_ℂ).re ≤ ‖regularImage x δ₁‖ ^ 2 *
    (traceRe (NormedSpace.exp K)) ^ a
  rw [hpair]
  refine hH.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · exact pow_le_pow_left₀ (operatorLpNorm_nonneg_form q Y) hcontract' 2
  · exact Real.rpow_nonneg (traceRe_exp_pos K hK).le _

/-- A bounded test-function version of the log-Sobolev inequality on the
Fourier form domain, deduced from sharp hypercontractivity. -/
theorem form_logSobolev_test {n : ℕ}
    (hHC : ∀ t : ℝ, 0 < t → ∀ x : GroupAlgebra n,
      lpNorm (1 + Real.exp (2*t)) (poisson t x) ≤ lpNorm 2 x)
    (v : Hilbert n) (hv : inFormDomain v)
    (K : Operator n) (hKm : K ∈ groupVonNeumann n) (hK : IsSelfAdjoint K) :
    (⟪v, K v⟫_ℂ).re ≤ 2 * formEnergy v + ‖v‖ ^ 2 * Real.log (traceRe (NormedSpace.exp K)) := by
  apply form_test_of_exp_bound v hv K (traceRe_exp_pos K hK)
  intro t ht
  let E := NormedSpace.exp (testExponent t • K)
  have hX := traceVectorTruncation_tendsto v
  have hY := traceVectorTruncation_tendsto (poissonVector t v)
  have hleft := Complex.continuous_re.continuousAt.tendsto.comp
    (hY.inner (E.continuous.continuousAt.tendsto.comp hY))
  have hright := (hX.norm.pow 2).mul_const ((traceRe (NormedSpace.exp K)) ^ testExponent t)
  apply le_of_tendsto_of_tendsto' hleft hright
  intro s
  let Y := regularImage (vectorTruncation (poissonVector t v) s)
  change (⟪Y δ₁, E (Y δ₁)⟫_ℂ).re ≤ _
  have h := test_bound_fourier ht K hKm hK (vectorTruncation v s) (hHC t ht _)
  simpa only [poisson_vectorTruncation ht.le] using h

end FreeGroupHypercontractivity
