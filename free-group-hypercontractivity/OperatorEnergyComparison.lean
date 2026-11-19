module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».GroupCStar
public import «free-group-hypercontractivity».OperatorMajorant
public import «free-group-hypercontractivity».SpectralGrid
public import «free-group-hypercontractivity».SpectralGridWeights
public import «free-group-hypercontractivity».HypercontractivityStroockVaropoulos

public section

namespace FreeGroupHypercontractivity

open scoped ComplexOrder

theorem groupTraceReCLM_mul_nonneg {n : ℕ} {U V : GroupCStar n}
    (hU : 0 ≤ (U : Operator n)) (hV : 0 ≤ (V : Operator n)) :
    0 ≤ groupTraceReCLM n (U * V) := by
  let f (z : ℂ) := Complex.ofReal (Real.sqrt z.re)
  let S := cfc (p := IsStarNormal) f (U : Operator n)
  have hf : Continuous f := Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp Complex.continuous_re)
  have hS : S ∈ groupCStar n := cfc_mem_groupCStar f U.property
  have hSsq : S * S = (U : Operator n) := by
    dsimp only [S]
    rw [← cfc_mul f f _ hf.continuousOn hf.continuousOn]
    calc
      _ = cfc (p := IsStarNormal) id (U : Operator n) := by
        apply cfc_congr
        intro z hz
        obtain ⟨v, hv, rfl⟩ := exists_ofReal_of_spectrum_nonneg hU hz
        simp [f, ← Complex.ofReal_mul, Real.mul_self_sqrt hv]
      _ = _ := cfc_id _ _ (ContinuousLinearMap.nonneg_iff_isPositive.mp hU).isSelfAdjoint.isStarNormal
  have hSnonneg : 0 ≤ S := cfc_nonneg fun z _ ↦
    Complex.nonneg_iff.mpr ⟨Real.sqrt_nonneg _, by simp [f]⟩
  simp only [groupTraceReCLM_apply]
  change 0 ≤ traceRe ((U : Operator n) * (V : Operator n))
  rw [← hSsq, mul_assoc,
    traceRe_mul_comm_closure (mem_groupCStar_iff.mp hS)
      (mem_groupCStar_iff.mp (mul_mem hS V.property))]
  exact traceRe_nonneg (conjugate_nonneg_of_nonneg hV hSnonneg)

private theorem coe_cfcL_nonneg {n : ℕ} {T : GroupCStar n} (hT : IsSelfAdjoint T)
    {f : C(spectrum ℝ T, ℝ)} (hf : 0 ≤ f) :
    0 ≤ (cfcL hT f : Operator n) := by
  let s : C(spectrum ℝ T, ℝ) := ⟨fun x ↦ Real.sqrt (f x), Real.continuous_sqrt.comp f.continuous⟩
  have hs : star s * s = f := by
    ext x
    change Real.sqrt (f x) * Real.sqrt (f x) = f x
    exact Real.mul_self_sqrt ((ContinuousMap.le_def.mp hf) x)
  rw [← hs, cfcL_apply, map_mul, map_star]
  exact star_mul_self_nonneg (cfcHom hT s : Operator n)

/-- The trace pairing of spectral functions across a continuous linear map. -/
private noncomputable def spectralOperatorPairing {n : ℕ} {T : GroupCStar n}
    (hT : IsSelfAdjoint T) (P : GroupCStar n →L[ℝ] GroupCStar n) :
    C(spectrum ℝ T, ℝ) →ₗ[ℝ] C(spectrum ℝ T, ℝ) →ₗ[ℝ] ℝ :=
  let F : C(spectrum ℝ T, ℝ) →L[ℝ] GroupCStar n := cfcL hT
  let τ := groupTraceReCLM n
  LinearMap.mk₂ ℝ (fun f g ↦ τ (F f * P (F g)))
    (fun f₁ f₂ g ↦ by simp only [map_add, add_mul])
    (fun c f g ↦ by simp only [map_smul, smul_mul_assoc])
    (fun f g₁ g₂ ↦ by simp only [map_add, mul_add])
    (fun c f g ↦ by simp only [map_smul, mul_smul_comm])

private theorem spectralOperatorPairing_apply {n : ℕ} {T : GroupCStar n} (hT : IsSelfAdjoint T)
    (P : GroupCStar n →L[ℝ] GroupCStar n) (f g : C(spectrum ℝ T, ℝ)) :
    spectralOperatorPairing hT P f g = groupTraceReCLM n (cfcL hT f * P (cfcL hT g)) := by
  rfl

set_option maxHeartbeats 400000 in
/-- A pointwise comparison of products of differences lifts to a comparison of
trace energies for a positive, unital map symmetric on self-adjoint elements. -/
theorem groupCStar_cfc_energy_le {n : ℕ} {T : GroupCStar n} (hT : IsSelfAdjoint T)
    (P : GroupCStar n →L[ℝ] GroupCStar n) (hP1 : P 1 = 1)
    (hPpos : ∀ U : GroupCStar n, 0 ≤ (U : Operator n) → 0 ≤ (P U : Operator n))
    (hPsym : ∀ U V : GroupCStar n, IsSelfAdjoint U → IsSelfAdjoint V →
      groupTraceReCLM n (U * P V) = groupTraceReCLM n (V * P U))
    (a d : ℝ) (f g u v : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ T)) (hg : ContinuousOn g (spectrum ℝ T))
    (hu : ContinuousOn u (spectrum ℝ T)) (hv : ContinuousOn v (spectrum ℝ T))
    (hpoint : ∀ x ∈ spectrum ℝ T, ∀ y ∈ spectrum ℝ T,
      a * (f x - f y) * (g x - g y) ≤ d * (u x - u y) * (v x - v y)) :
    a * groupTraceReCLM n (cfc f T * (cfc g T - P (cfc g T))) ≤
      d * groupTraceReCLM n (cfc u T * (cfc v T - P (cfc v T))) := by
  let B := spectralOperatorPairing hT P
  let F : C(spectrum ℝ T, ℝ) := ⟨_, hf.domRestrict⟩
  let G : C(spectrum ℝ T, ℝ) := ⟨_, hg.domRestrict⟩
  let U : C(spectrum ℝ T, ℝ) := ⟨_, hu.domRestrict⟩
  let V : C(spectrum ℝ T, ℝ) := ⟨_, hv.domRestrict⟩
  have hsym (F G : C(spectrum ℝ T, ℝ)) : B F G = B G F := by
    simp only [B, spectralOperatorPairing_apply, cfcL_apply]
    exact hPsym _ _ (cfcHom_predicate hT F) (cfcHom_predicate hT G)
  have hpos (F G : C(spectrum ℝ T, ℝ)) (hF : 0 ≤ F) (hG : 0 ≤ G) : 0 ≤ B F G := by
    simp only [B, spectralOperatorPairing_apply]
    exact groupTraceReCLM_mul_nonneg (coe_cfcL_nonneg hT hF) (hPpos _ (coe_cfcL_nonneg hT hG))
  have hcont : Continuous (fun p : C(spectrum ℝ T, ℝ) × C(spectrum ℝ T, ℝ) ↦ B p.1 p.2) := by
    simp only [B, spectralOperatorPairing_apply]
    let D : C(spectrum ℝ T, ℝ) →L[ℝ] GroupCStar n := cfcL hT
    exact (groupTraceReCLM n).continuous.comp ((D.continuous.comp continuous_fst).mul
      (P.continuous.comp (D.continuous.comp continuous_snd)))
  have hcompare := spectralPairing_energy_le_of_grid B spectralGrid_exists hcont hsym hpos a d F G U V
    (fun x y ↦ hpoint x x.property y y.property)
  have henergy (F G : C(spectrum ℝ T, ℝ)) :
      B (F * G) 1 - B F G =
        groupTraceReCLM n (cfcL hT F * (cfcL hT G - P (cfcL hT G))) := by
    simp [B, spectralOperatorPairing_apply, cfcL_apply, hP1, mul_sub]
  rw [henergy, henergy] at hcompare
  rw [cfc_eq_cfcL hT hf, cfc_eq_cfcL hT hg,
    cfc_eq_cfcL hT hu, cfc_eq_cfcL hT hv]
  exact hcompare

/-- Compare the real spectrum in the reduced algebra with the ambient spectrum. -/
theorem groupCStar_real_mem_complex_spectrum {n : ℕ} {T : GroupCStar n} {x : ℝ}
    (hx : x ∈ spectrum ℝ T) : Complex.ofReal x ∈ spectrum ℂ (T : Operator n) := by
  have hxc : algebraMap ℝ ℂ x ∈ spectrum ℂ T := spectrum.algebraMap_mem ℂ hx
  have hspec : spectrum ℂ T = spectrum ℂ (T : Operator n) :=
    StarSubalgebra.spectrum_eq (groupCStar n)
  rw [hspec] at hxc
  exact hxc

/-- A positive element of the reduced group algebra has nonnegative real spectrum. -/
theorem groupCStar_spectrum_nonneg {n : ℕ} {T : GroupCStar n}
    (hT : 0 ≤ (T : Operator n)) {x : ℝ} (hx : x ∈ spectrum ℝ T) : 0 ≤ x := by
  simpa only [Complex.ofReal_re] using
    (Complex.nonneg_iff.mp (spectrum_nonneg_of_nonneg hT (groupCStar_real_mem_complex_spectrum hx))).1

/-- The trace energy of a Lipschitz function is bounded by the square of its
Lipschitz constant times the trace energy of the element. -/
theorem groupCStar_cfc_lipschitz_energy {n : ℕ} {T : GroupCStar n} (hT : IsSelfAdjoint T)
    (P : GroupCStar n →L[ℝ] GroupCStar n) (hP1 : P 1 = 1)
    (hPpos : ∀ U : GroupCStar n, 0 ≤ (U : Operator n) → 0 ≤ (P U : Operator n))
    (hPsym : ∀ U V : GroupCStar n, IsSelfAdjoint U → IsSelfAdjoint V →
      groupTraceReCLM n (U * P V) = groupTraceReCLM n (V * P U))
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ T)) {L : ℝ}
    (hLip : ∀ x ∈ spectrum ℝ T, ∀ y ∈ spectrum ℝ T, |f x - f y| ≤ L * |x - y|) :
    groupTraceReCLM n (cfc f T * (cfc f T - P (cfc f T))) ≤
      L ^ 2 * groupTraceReCLM n (T * (T - P T)) := by
  have h := groupCStar_cfc_energy_le hT P hP1 hPpos hPsym 1 (L ^ 2) f f id id hf hf
    continuous_id.continuousOn continuous_id.continuousOn (by
      intro x hx y hy
      have h := pow_le_pow_left₀ (abs_nonneg _) (hLip x hx y hy) 2
      rw [sq_abs, mul_pow, sq_abs] at h
      simpa [pow_two, mul_assoc] using h)
  simpa only [one_mul, cfc_id ℝ T hT] using h

/-- Stroock–Varopoulos comparison for powers of a positive element in the
reduced group algebra. -/
theorem groupCStar_cfc_stroockVaropoulos {n : ℕ} {T : GroupCStar n}
    (hT : IsSelfAdjoint T) (hTpos : 0 ≤ (T : Operator n))
    (P : GroupCStar n →L[ℝ] GroupCStar n) (hP1 : P 1 = 1)
    (hPpos : ∀ U : GroupCStar n, 0 ≤ (U : Operator n) → 0 ≤ (P U : Operator n))
    (hPsym : ∀ U V : GroupCStar n, IsSelfAdjoint U → IsSelfAdjoint V →
      groupTraceReCLM n (U * P V) = groupTraceReCLM n (V * P U))
    {r : ℝ} (hr : 1 < r) :
    4 * (r - 1) * groupTraceReCLM n
        (cfc (fun x : ℝ ↦ x ^ (r / 2)) T *
          (cfc (fun x : ℝ ↦ x ^ (r / 2)) T - P (cfc (fun x : ℝ ↦ x ^ (r / 2)) T))) ≤
      r ^ 2 * groupTraceReCLM n
        (cfc (fun x : ℝ ↦ x ^ (r - 1)) T * (T - P T)) := by
  have hr₂ : 0 ≤ r / 2 := by linarith
  have hr₁ : 0 ≤ r - 1 := by linarith
  have hc₂ : Continuous (fun x : ℝ ↦ x ^ (r / 2)) := Real.continuous_rpow_const hr₂
  have hc₁ : Continuous (fun x : ℝ ↦ x ^ (r - 1)) := Real.continuous_rpow_const hr₁
  have h := groupCStar_cfc_energy_le hT P hP1 hPpos hPsym (4*(r-1)) (r^2)
    (fun x ↦ x ^ (r / 2)) (fun x ↦ x ^ (r / 2)) (fun x ↦ x ^ (r - 1)) id
    hc₂.continuousOn hc₂.continuousOn hc₁.continuousOn continuous_id.continuousOn (by
      intro x hx y hy
      have h := stroockVaropoulos_scalar (groupCStar_spectrum_nonneg hTpos hx)
        (groupCStar_spectrum_nonneg hTpos hy) hr
      simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using h)
  simpa only [cfc_id ℝ T hT] using h

end FreeGroupHypercontractivity
