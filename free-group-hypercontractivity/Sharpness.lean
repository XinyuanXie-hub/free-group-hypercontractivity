module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».Representation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

public section

namespace FreeGroupHypercontractivity

open Filter Set Asymptotics
open scoped Topology ENNReal

private noncomputable def quadratic (r s : ℝ) : ℝ :=
  1 + r * s + (r * (r - 1) / 2) * s ^ 2

private theorem rpow_remainder (r : ℝ) :
    (fun s : ℝ ↦ (1 + s) ^ r - quadratic r s) =o[𝓝 0] fun s ↦ s ^ 2 := by
  have hder (r a : ℝ) (ha : 0 < 1 + a) :
      HasDerivAt (fun s : ℝ ↦ (1 + s) ^ r) (r * (1 + a) ^ (r - 1)) a := by
    simpa [Function.comp_def] using (Real.hasDerivAt_rpow_const
      (x := 1 + a) (p := r) (Or.inl ha.ne')).comp a
      ((hasDerivAt_id a).const_add 1)
  let D : ℝ → ℝ := fun s ↦ r * ((1 + s) ^ (r - 1) - 1 - (r - 1) * s)
  have hD : D =o[𝓝 0] fun s : ℝ ↦ s := by
    have hd : HasDerivAt (fun s : ℝ ↦ (1 + s) ^ (r - 1)) (r - 1) 0 := by
      simpa using hder (r - 1) 0 (by norm_num)
    have hh := hd.isLittleO.const_mul_left r
    simpa [D, smul_eq_mul, mul_comm] using hh
  have h0 : (0 : ℝ) ∈ Ioi (-1 : ℝ) := by norm_num
  have hU : 𝓝[Ioi (-1)] (0 : ℝ) = 𝓝 0 := nhdsWithin_eq_nhds.2 (Ioi_mem_nhds h0)
  have h := (convex_Ioi (-1 : ℝ)).isLittleO_pow_succ_real (n := 1) h0
    (f := fun s ↦ (1 + s) ^ r - quadratic r s) (f' := D) ?_
    (by simpa [hU] using hD)
  · simpa [hU, quadratic] using h
  · intro s hs
    have hs' : 0 < 1 + s := by
      have : -1 < s := hs
      linarith
    apply HasDerivAt.hasDerivWithinAt
    have hpoly := ((hasDerivAt_const s (1 : ℝ)).add
      ((hasDerivAt_id s).const_mul r)).add
      (((hasDerivAt_id s).mul (hasDerivAt_id s)).const_mul (r * (r - 1) / 2))
    convert (hder r s hs').sub hpoly using 1
    · funext x
      simp [quadratic, pow_two, Pi.sub_apply, Pi.mul_apply]
    · simp [D]
      ring

private theorem sharpTrace_sub {n : ℕ} (A B : Operator n) :
    traceRe (A - B) = traceRe A - traceRe B := by
  simp [traceRe]

private theorem sharpTrace_add {n : ℕ} (A B : Operator n) :
    traceRe (A + B) = traceRe A + traceRe B := by
  simp [traceRe]

private theorem sharpTrace_smul {n : ℕ} (c : ℝ) (A : Operator n) :
    traceRe ((c : ℂ) • A) = c * traceRe A := by
  let v : Hilbert n := lp.single 2 1 1
  change ((c : ℂ) * A v 1).re = c * (A v 1).re
  simp [Complex.mul_re]

private theorem sharpTrace_one {n : ℕ} : traceRe (1 : Operator n) = 1 := by
  simp [traceRe]

private theorem norm_sharpTrace_le {n : ℕ} (A : Operator n) : ‖traceRe A‖ ≤ ‖A‖ := by
  let v : Hilbert n := lp.single 2 1 1
  have hv : ‖v‖ = 1 := by
    simp [v, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  exact (Complex.abs_re_le_norm (A v 1)).trans
    ((lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (A v) 1).trans
      (A.unit_le_opNorm v hv.le))

private theorem hilbert_nontrivial (n : ℕ) : Nontrivial (Hilbert n) := by
  refine ⟨⟨lp.single 2 1 1, 0, ?_⟩⟩
  intro h
  have := congrArg (fun v : Hilbert n ↦ v 1) h
  simp at this

private theorem spectrum_re {n : ℕ} {A : Operator n} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z ∈ spectrum ℂ A) : (z.re : ℂ) = z := by
  exact hA.spectrumRestricts.rightInvOn hz

private theorem complex_normal {n : ℕ} {A : Operator n} (hA : IsSelfAdjoint A) :
    IsStarNormal A := hA.isStarNormal

private noncomputable def specMoment {n : ℕ} (r : ℝ) (A : Operator n) (s : ℝ) : ℝ :=
  traceRe (cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal ((1 + s * z.re) ^ r)) A)

private theorem cfc_quadratic {n : ℕ} {A : Operator n} (hA : IsSelfAdjoint A) (r s : ℝ) :
    cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (quadratic r (s * z.re))) A =
      1 + ((r * s : ℝ) : ℂ) • A + (((r * (r - 1) / 2) * s ^ 2 : ℝ) : ℂ) • A ^ 2 := by
  have h := complex_normal hA
  let a : ℂ := Complex.ofReal (r * s)
  let b : ℂ := Complex.ofReal ((r * (r - 1) / 2) * s ^ 2)
  have ha : Continuous (fun z : ℂ ↦ a * z) := continuous_const.mul continuous_id
  have hb : Continuous (fun z : ℂ ↦ b * z ^ 2) := continuous_const.mul (continuous_id.pow 2)
  change _ = 1 + a • A + b • A ^ 2
  trans cfc (p := IsStarNormal) (fun z : ℂ ↦ 1 + a * z + b * z ^ 2) A
  · apply cfc_congr
    intro z hz
    rw [← spectrum_re hA hz]
    simp only [Complex.ofReal_re, quadratic, Complex.ofReal_add, Complex.ofReal_one, a, b,
      Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  · rw [cfc_add A (fun z : ℂ ↦ 1 + a * z) (fun z : ℂ ↦ b * z ^ 2)
        (continuous_const.add ha).continuousOn hb.continuousOn,
      cfc_const_add 1 (fun z : ℂ ↦ a * z) A ha.continuousOn h, cfc_const_mul_id _ _ h,
      cfc_const_mul b (fun z : ℂ ↦ z ^ 2) A (continuous_id.pow 2).continuousOn,
      cfc_pow_id _ _ h, map_one]

private theorem specMoment_remainder {n : ℕ} {A : Operator n} (hA : IsSelfAdjoint A)
    (htA : traceRe A = 0) (r : ℝ) (hr : 0 ≤ r) :
    (fun s ↦ specMoment r A s - 1 - (r * (r - 1) / 2 * traceRe (A ^ 2)) * s ^ 2)
      =o[𝓝 0] fun s ↦ s ^ 2 := by
  let _ := hilbert_nontrivial n
  let C : ℝ := ‖A‖ + 1
  have hC : 0 < C := by positivity
  have hC2 : 0 < C ^ 2 := by positivity
  apply IsLittleO.of_bound
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff_ball.mp
    ((rpow_remainder r).bound (div_pos hε hC2))
  refine Metric.eventually_nhds_iff_ball.mpr ⟨δ / C, div_pos hδ hC, ?_⟩
  intro s hs
  have hs' : ‖s‖ < δ / C := by simpa [Metric.mem_ball, dist_zero_right] using hs
  let f : ℂ → ℂ := fun z ↦ Complex.ofReal ((1 + s * z.re) ^ r)
  let g : ℂ → ℂ := fun z ↦ Complex.ofReal (quadratic r (s * z.re))
  have h1 : Continuous (fun z : ℂ ↦ 1 + s * z.re) :=
    continuous_const.add (continuous_const.mul Complex.continuous_re)
  have hf : Continuous f := Complex.continuous_ofReal.comp (h1.rpow_const fun _ ↦ Or.inr hr)
  have hg : Continuous g := by unfold g quadratic; fun_prop
  have hpoly : traceRe (cfc (p := IsStarNormal) g A) =
      1 + (r * (r - 1) / 2 * traceRe (A ^ 2)) * s ^ 2 := by
    rw [show cfc (p := IsStarNormal) g A = _ from cfc_quadratic hA r s,
      sharpTrace_add, sharpTrace_add, sharpTrace_smul, sharpTrace_smul, sharpTrace_one, htA]
    ring
  have hdiff : traceRe (cfc (p := IsStarNormal) (fun z ↦ f z - g z) A) =
      specMoment r A s - 1 - (r * (r - 1) / 2 * traceRe (A ^ 2)) * s ^ 2 := by
    rw [cfc_sub (a := A) f g hf.continuousOn hg.continuousOn, sharpTrace_sub, hpoly]
    unfold specMoment f
    ring
  rw [← hdiff]
  refine (norm_sharpTrace_le _).trans (norm_cfc_le (mul_nonneg hε.le (norm_nonneg _)) ?_)
  intro z hz
  have hz' : ‖z.re‖ ≤ C :=
    (Complex.abs_re_le_norm z).trans ((spectrum.norm_le_norm_of_mem hz).trans (by dsimp [C]; linarith))
  have hmem : s * z.re ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, dist_zero_right, norm_mul]
    exact ((mul_le_mul_of_nonneg_left hz' (norm_nonneg s))).trans_lt
      ((lt_div_iff₀ hC).mp hs')
  have hrem := hδ' (s * z.re) hmem
  change ‖(1 + s * z.re) ^ r - quadratic r (s * z.re)‖ ≤
    ε / C ^ 2 * ‖(s * z.re) ^ 2‖ at hrem
  rw [show f z - g z = Complex.ofReal ((1 + s * z.re) ^ r - quadratic r (s * z.re)) by
    simp [f, g], Complex.norm_real]
  refine hrem.trans ?_
  rw [norm_pow, norm_pow, norm_mul, mul_pow]
  calc
    ε / C ^ 2 * (‖s‖ ^ 2 * ‖z.re‖ ^ 2) ≤ ε / C ^ 2 * (‖s‖ ^ 2 * C ^ 2) := by gcongr
    _ = ε * ‖s‖ ^ 2 := by field_simp

private theorem rpow_specMoment_remainder {n : ℕ} {A : Operator n} (hA : IsSelfAdjoint A)
    (htA : traceRe A = 0) (r : ℝ) (hr : 0 ≤ r) (u : ℝ) :
    (fun s ↦ specMoment r A s ^ u - 1 -
      (u * (r * (r - 1) / 2 * traceRe (A ^ 2))) * s ^ 2)
      =o[𝓝 0] fun s ↦ s ^ 2 := by
  let M : ℝ → ℝ := specMoment r A
  let c : ℝ := r * (r - 1) / 2 * traceRe (A ^ 2)
  have hrem : (fun s ↦ M s - 1 - c * s ^ 2) =o[𝓝 0] fun s ↦ s ^ 2 :=
    specMoment_remainder hA htA r hr
  have hbig : (fun s ↦ M s - 1) =O[𝓝 0] fun s ↦ s ^ 2 := by
    apply (((isBigO_refl (fun s : ℝ ↦ s ^ 2) (𝓝 0)).const_mul_left c).add hrem.isBigO).congr_left
    intro s
    ring
  have hpow : Tendsto (fun s : ℝ ↦ s ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ ↦ s ^ 2) := by fun_prop
    simpa [ContinuousAt] using hc.continuousAt (x := (0 : ℝ))
  have ht : Tendsto M (𝓝 0) (𝓝 1) :=
    tendsto_sub_nhds_zero_iff.mp (hbig.trans_tendsto hpow)
  have hder : HasDerivAt (fun x : ℝ ↦ x ^ u) u 1 := by
    simpa using Real.hasDerivAt_rpow_const (x := 1) (p := u) (Or.inl one_ne_zero)
  have hpowRem : (fun s ↦ M s ^ u - 1 - u * (M s - 1)) =o[𝓝 0] fun s ↦ M s - 1 := by
    simpa [Function.comp_def, smul_eq_mul, mul_comm] using hder.isLittleO.comp_tendsto ht
  apply ((hpowRem.trans_isBigO hbig).add (hrem.const_mul_left u)).congr_left
  intro s
  change M s ^ u - 1 - u * (M s - 1) + u * (M s - 1 - c * s ^ 2) =
    M s ^ u - 1 - (u * c) * s ^ 2
  ring

private theorem lpNorm_eq_specMoment {n : ℕ} {A : Operator n} (hA : IsSelfAdjoint A)
    (r s : ℝ) (hr : 0 ≤ r) (hs : ‖s‖ < 1 / (‖A‖ + 1))
    (x : GroupAlgebra n) (hx : regularImage x = 1 + (s : ℂ) • A) :
    lpNorm r x = specMoment r A s ^ (1 / r) := by
  let _ := hilbert_nontrivial n
  let f : ℂ → ℂ := fun z ↦ 1 + (s : ℂ) * z
  let g : ℂ → ℂ := fun z ↦ Complex.ofReal (z.re ^ (r / 2))
  have hf : Continuous f := continuous_const.add (continuous_const.mul continuous_id)
  have hg : Continuous g := Complex.continuous_ofReal.comp
    (Complex.continuous_re.rpow_const fun _ ↦ Or.inr (by positivity))
  have hN := complex_normal hA
  have h₁ : cfc (p := IsStarNormal) f A = 1 + (s : ℂ) • A := by
    unfold f
    rw [cfc_const_add 1 (fun z : ℂ ↦ (s : ℂ) * z) A
      (continuous_const.mul continuous_id).continuousOn hN, cfc_const_mul_id _ _ hN, map_one]
  have h₂ : star (regularImage x) = regularImage x := by
    have hA' := ContinuousLinearMap.isSelfAdjoint_iff'.mp hA
    rw [hx, ContinuousLinearMap.star_eq_adjoint, map_add, ContinuousLinearMap.adjoint_one,
      map_smulₛₗ, hA']
    have hc : star (s : ℂ) = (s : ℂ) := by simp
    exact congrArg (fun c : ℂ ↦ 1 + c • A) hc
  unfold lpNorm specMoment
  change (traceRe (cfc (p := IsStarNormal) g (star (regularImage x) * regularImage x))) ^ _ = _
  rw [h₂, ← pow_two, hx, ← h₁, ← cfc_pow f 2 A hf.continuousOn hN,
    ← cfc_comp' g (fun z ↦ f z ^ 2) A hg.continuousOn (hf.pow 2).continuousOn hN]
  congr 2
  apply cfc_congr
  intro z hz
  have hz' : ‖z.re‖ ≤ ‖A‖ + 1 :=
    (Complex.abs_re_le_norm z).trans ((spectrum.norm_le_norm_of_mem hz).trans (by linarith))
  have hsz : ‖s * z.re‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hz' (norm_nonneg s)).trans_lt
      ((lt_div_iff₀ (by positivity : 0 < ‖A‖ + 1)).mp hs)
  have hu : 0 ≤ 1 + s * z.re := by
    have hl := (abs_lt.mp (by simpa [Real.norm_eq_abs] using hsz : |s * z.re| < 1)).1
    linarith
  have hfz : f z = Complex.ofReal (1 + s * z.re) := by
    unfold f
    rw [← spectrum_re hA hz]
    simp
  change g (f z ^ 2) = _
  rw [hfz]
  simp only [g, ← Complex.ofReal_pow, Complex.ofReal_re]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu]
  congr 1
  ring

private noncomputable def perturb {n : ℕ} (g : Group n) (s : ℝ) : GroupAlgebra n :=
  1 + (s : ℂ) • (MonoidAlgebra.single g 1 + MonoidAlgebra.single g⁻¹ 1)

private theorem poisson_perturb {n : ℕ} (g : Group n) (hg : FreeGroup.norm g = 1)
    (t s : ℝ) : poisson t (perturb g s) = perturb g (Real.exp (-t) * s) := by
  classical
  have hm (x : GroupAlgebra n) (k : Group n) :
      (poisson t x).coeff k = (Real.exp (-t * (FreeGroup.norm k : ℝ)) : ℂ) * x.coeff k := by
    rw [poisson, multiplier_coeff]
  have hne : g ≠ 1 := by
    intro he
    simp [he, FreeGroup.norm_one] at hg
  ext k
  rw [hm]
  simp only [perturb, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_smul_apply,
    Finsupp.add_apply, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply,
    smul_eq_mul, Complex.ofReal_mul]
  by_cases hk : k = 1
  · subst k
    simp [FreeGroup.norm_one, hne]
  by_cases hgk : g = k
  · subst k
    simp [Ne.symm hk, hg, mul_assoc]
  by_cases hig : g⁻¹ = k
  · subst k
    simp [hne, hgk, FreeGroup.norm_inv_eq, hg]
  simp [hgk, hig, Ne.symm hk]

private theorem trace_leftRegular {n : ℕ} (g : Group n) :
    traceRe (leftRegular g) = if g = 1 then 1 else 0 := by
  classical
  by_cases h : g = 1 <;> simp [traceRe, lp.single_apply, h]

private theorem coeff_le_of_quadratic_expansions {f g : ℝ → ℝ} {c d : ℝ}
    (hf : (fun s ↦ f s - 1 - c * s ^ 2) =o[𝓝 0] fun s ↦ s ^ 2)
    (hg : (fun s ↦ g s - 1 - d * s ^ 2) =o[𝓝 0] fun s ↦ s ^ 2)
    (hle : ∀ᶠ s in 𝓝 0, f s ≤ g s) : c ≤ d := by
  by_contra! hdc
  have hb := (hf.sub hg).bound (show 0 < (c - d) / 2 by linarith)
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.mp (hb.and hle)
  let s : ℝ := δ / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hsδ : s ∈ Metric.ball 0 δ := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hs]
    dsimp [s]
    linarith
  obtain ⟨hr, hle'⟩ := h s hsδ
  rw [Real.norm_of_nonneg (sq_nonneg s), Real.norm_eq_abs, abs_le] at hr
  have hpos : 0 < (c - d) * s ^ 2 := mul_pos (by linarith) (sq_pos_of_pos hs)
  nlinarith [hr.1]

/-- The sharp time is necessary, as detected by a degree-one self-adjoint perturbation. -/
theorem hypercontractivity_necessary (n : ℕ) (hn : 2 ≤ n) (p q t : ℝ)
    (hp : 1 < p) (hpq : p ≤ q)
    (h : ∀ x : GroupAlgebra n, lpNorm q (poisson t x) ≤ lpNorm p x) :
    (1 / 2 : ℝ) * Real.log ((q - 1) / (p - 1)) ≤ t := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  let g : Group n := FreeGroup.of i
  let A : Operator n := leftRegular g + leftRegular g⁻¹
  have hg : FreeGroup.norm g = 1 := FreeGroup.norm_of i
  have hgne : g ≠ 1 := FreeGroup.of_ne_one i
  have hgg : g * g ≠ 1 := by
    intro hh
    have hpow := FreeGroup.norm_of_pow i 2
    rw [pow_two, show FreeGroup.of i * FreeGroup.of i = g * g from rfl, hh,
      FreeGroup.norm_one] at hpow
    norm_num at hpow
  have hggi : g⁻¹ * g⁻¹ ≠ 1 := by
    rw [← mul_inv_rev, inv_ne_one]
    exact hgg
  have hA : IsSelfAdjoint A := by
    have hA' := IsSelfAdjoint.add_star_self (leftRegular g)
    simpa only [star_leftRegular] using hA'
  have htA : traceRe A = 0 := by
    simp [A, sharpTrace_add, trace_leftRegular, hgne]
  have htA2 : traceRe (A ^ 2) = 2 := by
    simp only [A, pow_two, add_mul, mul_add, ← leftRegular_mul, mul_inv_cancel,
      inv_mul_cancel, sharpTrace_add, trace_leftRegular, hgg, hggi, ite_false, ite_true]
    norm_num
  have him (s : ℝ) : regularImage (perturb g s) = 1 + (s : ℂ) • A := by
    simp only [perturb, regularImage_add, regularImage_one, regularImage_smul, regularImage_single,
      one_smul, A]
  let e := Real.exp (-t)
  let P : ℝ → ℝ := fun s ↦ specMoment p A s ^ (1 / p)
  let Q : ℝ → ℝ := fun s ↦ specMoment q A s ^ (1 / q)
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := lt_of_lt_of_le hp0 hpq
  have hpr : (fun s ↦ P s - 1 - (p - 1) * s ^ 2) =o[𝓝 0] fun s ↦ s ^ 2 := by
    apply (rpow_specMoment_remainder hA htA p hp0.le (1 / p)).congr_left
    intro s
    rw [htA2]
    have hc : 1 / p * (p * (p - 1) / 2 * 2) = p - 1 := by field_simp
    rw [hc]
  have hqr : (fun s ↦ Q s - 1 - (q - 1) * s ^ 2) =o[𝓝 0] fun s ↦ s ^ 2 := by
    apply (rpow_specMoment_remainder hA htA q hq0.le (1 / q)).congr_left
    intro s
    rw [htA2]
    have hc : 1 / q * (q * (q - 1) / 2 * 2) = q - 1 := by field_simp
    rw [hc]
  have he : Tendsto (fun s : ℝ ↦ e * s) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ ↦ e * s) := continuous_const.mul continuous_id
    simpa [ContinuousAt] using hc.continuousAt (x := (0 : ℝ))
  have hqr' : (fun s ↦ Q (e * s) - 1 - ((q - 1) * e ^ 2) * s ^ 2)
      =o[𝓝 0] fun s ↦ s ^ 2 := by
    have hqBig := hqr.comp_tendsto he
    have hqBig' := hqBig.congr_right fun s ↦ mul_pow e s 2
    apply hqBig'.of_const_mul_right.congr_left
    intro s
    dsimp [Function.comp_def]
    rw [mul_pow]
    ring
  have hsmall : ∀ᶠ s : ℝ in 𝓝 0, ‖s‖ < 1 / (‖A‖ + 1) := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨1 / (‖A‖ + 1), by positivity, ?_⟩
    intro z hz
    rwa [dist_zero_right] at hz
  have hevent : ∀ᶠ s : ℝ in 𝓝 0, Q (e * s) ≤ P s := by
    filter_upwards [hsmall, he.eventually hsmall] with s hs hes
    have h' := h (perturb g s)
    rw [poisson_perturb g hg t, lpNorm_eq_specMoment hA _ _ hq0.le hes _ (him _),
      lpNorm_eq_specMoment hA _ _ hp0.le hs _ (him _)] at h'
    exact h'
  have hc := coeff_le_of_quadratic_expansions hqr' hpr hevent
  have hpositive : 0 < (q - 1) / (p - 1) := div_pos (by linarith) (by linarith)
  have hexp : (q - 1) / (p - 1) ≤ Real.exp (2 * t) := by
    rw [div_le_iff₀ (by linarith : 0 < p - 1)]
    have heq : e ^ 2 * Real.exp (2 * t) = 1 := by
      dsimp [e]
      rw [pow_two, ← Real.exp_add, ← Real.exp_add,
        show -t + -t + 2 * t = 0 by ring, Real.exp_zero]
    have hm := mul_le_mul_of_nonneg_right hc (Real.exp_pos (2 * t)).le
    rwa [mul_assoc, heq, mul_one, mul_comm (p - 1)] at hm
  have hlog := (Real.log_le_iff_le_exp hpositive).mpr hexp
  linarith

end FreeGroupHypercontractivity
