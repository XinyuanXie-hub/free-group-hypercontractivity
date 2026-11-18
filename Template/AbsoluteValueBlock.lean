module

public import Template.PositiveReduction
public import Template.PoissonPositive
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace FreeGroupHypercontractivity

open scoped InnerProductSpace ComplexOrder

/-- The absolute value of a bounded operator. -/
@[expose] noncomputable def absoluteValueOperator {n : ℕ} (T : Operator n) : Operator n :=
  operatorRpow (star T * T) (1 / 2 : ℝ)

private noncomputable def blockRealCfc {n : ℕ} (f : ℝ → ℝ) (A : Operator n) : Operator n :=
  cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (f z.re)) A

private theorem blockRealCfc_nonneg {n : ℕ} {f : ℝ → ℝ} {A : Operator n}
    (hA : 0 ≤ A) (hf : ∀ r, 0 ≤ r → 0 ≤ f r) : 0 ≤ blockRealCfc f A := by
  unfold blockRealCfc
  apply cfc_nonneg
  intro z hz
  obtain ⟨r, hr, rfl⟩ := exists_ofReal_of_spectrum_nonneg hA hz
  rw [← Complex.ofReal_zero, Complex.real_le_real, Complex.ofReal_re]
  exact hf r hr

private theorem blockRealCfc_mul {n : ℕ} {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (A : Operator n) :
    blockRealCfc (fun x ↦ f x * g x) A = blockRealCfc f A * blockRealCfc g A := by
  unfold blockRealCfc
  exact (cfc_congr fun z _ ↦ Complex.ofReal_mul _ _).trans
    (cfc_mul _ _ A (Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)).continuousOn
      (Complex.continuous_ofReal.comp (hg.comp Complex.continuous_re)).continuousOn)

private theorem blockRealCfc_sqrt {n : ℕ} {A : Operator n} :
    blockRealCfc Real.sqrt A = operatorRpow A (1 / 2 : ℝ) := by
  unfold blockRealCfc operatorRpow
  simp only [Real.sqrt_eq_rpow]

private theorem blockRealCfc_id {n : ℕ} {A : Operator n} (hA : 0 ≤ A) :
    blockRealCfc id A = A := by
  have hN := (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).isSelfAdjoint.isStarNormal
  unfold blockRealCfc
  calc
    _ = cfc (p := IsStarNormal) (fun z : ℂ ↦ z) A := by
      apply cfc_congr
      intro z hz
      obtain ⟨r, _, rfl⟩ := exists_ofReal_of_spectrum_nonneg hA hz
      simp
    _ = _ := cfc_id' ℂ A hN

private theorem blockRealCfc_sqrt_add_const {n : ℕ} {A : Operator n}
    (hA : 0 ≤ A) (ε : ℝ) :
    blockRealCfc (fun r ↦ Real.sqrt r + ε) A =
      operatorRpow A (1 / 2 : ℝ) + (ε : ℂ) • (1 : Operator n) := by
  have hN := (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).isSelfAdjoint.isStarNormal
  have hC : Continuous (fun z : ℂ ↦ Complex.ofReal (Real.sqrt z.re)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp Complex.continuous_re)
  unfold blockRealCfc
  simp only [Complex.ofReal_add]
  rw [cfc_add_const _ _ _ hC.continuousOn hN, Algebra.algebraMap_eq_smul_one]
  exact congrArg (fun U ↦ U + (ε : ℂ) • (1 : Operator n)) blockRealCfc_sqrt

private theorem realInner_order {n : ℕ} {X Y : Operator n} (h : X ≤ Y) (v : Hilbert n) :
    (⟪v, X v⟫_ℂ).re ≤ (⟪v, Y v⟫_ℂ).re := by
  have hp := ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr h)
  have h' := hp.re_inner_nonneg_right v
  simpa only [RCLike.re_to_complex, sub_apply, inner_sub_right, Complex.sub_re,
    sub_nonneg] using h'

private theorem hermitianBlockNonneg_gram {n : ℕ} (X Y : Operator n) :
    HermitianBlockNonneg (star X * X) (star X * Y) (star Y * Y) := by
  intro v w
  change 0 ≤ (⟪v, X.adjoint (X v)⟫_ℂ).re + 2 * (⟪v, X.adjoint (Y w)⟫_ℂ).re +
    (⟪w, Y.adjoint (Y w)⟫_ℂ).re
  simp only [ContinuousLinearMap.adjoint_inner_right]
  have h := (inner_self_eq_norm_sq (𝕜 := ℂ) (X v + Y w)).symm
  have hs : 0 ≤ (⟪X v + Y w, X v + Y w⟫_ℂ).re := by
    rw [← RCLike.re_to_complex, ← h]
    positivity
  have hsym : (⟪Y w, X v⟫_ℂ).re = (⟪X v, Y w⟫_ℂ).re := by
    simpa only [RCLike.re_to_complex] using inner_re_symm (𝕜 := ℂ) (Y w) (X v)
  simp only [inner_add_left, inner_add_right, Complex.add_re, hsym] at hs
  linarith

/-- The absolute-value block of a bounded operator has nonnegative quadratic form. -/
theorem absolute_value_block_nonneg {n : ℕ} (T : Operator n) :
    HermitianBlockNonneg (absoluteValueOperator (star T)) T (absoluteValueOperator T) := by
  let A := star T * T
  let B := T * star T
  have hA : 0 ≤ A := star_mul_self_nonneg T
  have hB : 0 ≤ B := mul_star_self_nonneg T
  have hAB : SemiconjBy T A B := (mul_assoc T (star T) T).symm
  have habsA : absoluteValueOperator T = operatorRpow A (1 / 2 : ℝ) := rfl
  have habsB : absoluteValueOperator (star T) = operatorRpow B (1 / 2 : ℝ) := by
    simp only [absoluteValueOperator, star_star, B]
  intro v w
  rw [habsA, habsB]
  let Q : ℝ := (⟪v, operatorRpow B (1 / 2 : ℝ) v⟫_ℂ).re +
    2 * (⟪v, T w⟫_ℂ).re + (⟪w, operatorRpow A (1 / 2 : ℝ) w⟫_ℂ).re
  change 0 ≤ Q
  suffices hreg : ∀ ε : ℝ, 0 < ε → 0 ≤ Q + ε * ‖w‖ ^ 2 by
    apply le_of_forall_pos_le_add
    intro δ hδ
    let ε := δ / (‖w‖ ^ 2 + 1)
    have he : 0 < ε := by dsimp [ε]; positivity
    have heq : ε * (‖w‖ ^ 2 + 1) = δ := by
      dsimp [ε]
      field_simp
    linarith only [hreg ε he, heq, he]
  intro ε hε
  let g (s : ℝ) := Real.sqrt (Real.sqrt s + ε)
  let f (s : ℝ) := (g s)⁻¹
  have hgc : Continuous g := Real.continuous_sqrt.comp (Real.continuous_sqrt.add continuous_const)
  have hgpos (s : ℝ) : 0 < g s := Real.sqrt_pos.2 (by linarith [Real.sqrt_nonneg s])
  have hfc : Continuous f := hgc.inv₀ fun s ↦ (hgpos s).ne'
  let X := blockRealCfc f A * star T
  let Y := blockRealCfc g A
  have hFs : star (blockRealCfc f A) = blockRealCfc f A :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (blockRealCfc_nonneg hA fun s _ ↦ inv_nonneg.mpr (hgpos s).le)).isSelfAdjoint.star_eq
  have hYs : star Y = Y :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (blockRealCfc_nonneg hA fun s _ ↦ (hgpos s).le)).isSelfAdjoint.star_eq
  have hFG : blockRealCfc f A * Y = 1 := by
    have hN := (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).isSelfAdjoint.isStarNormal
    rw [show Y = blockRealCfc g A by rfl, ← blockRealCfc_mul hfc hgc]
    have heq : (fun s ↦ f s * g s) = fun _ ↦ (1 : ℝ) := by
      funext s
      exact inv_mul_cancel₀ (hgpos s).ne'
    rw [heq, blockRealCfc]
    simpa only [Complex.ofReal_one] using cfc_const_one ℂ A hN
  have hGsq : star Y * Y =
      operatorRpow A (1 / 2 : ℝ) + (ε : ℂ) • (1 : Operator n) := by
    rw [hYs, show Y = blockRealCfc g A by rfl, ← blockRealCfc_mul hgc hgc]
    have heq : (fun s ↦ g s * g s) = fun s ↦ Real.sqrt s + ε := by
      funext s
      change Real.sqrt _ * Real.sqrt _ = _
      exact Real.mul_self_sqrt (by linarith [Real.sqrt_nonneg s])
    rw [heq, blockRealCfc_sqrt_add_const hA]
  have hXY : star X * Y = T := by
    rw [show X = blockRealCfc f A * star T by rfl, star_mul, star_star, hFs, mul_assoc, hFG,
      mul_one]
  have hinter : T * blockRealCfc f A = blockRealCfc f B * T :=
    cfc_positive_intertwine hA hB hAB hfc
  have hXsq : star X * X ≤ operatorRpow B (1 / 2 : ℝ) := by
    rw [show X = blockRealCfc f A * star T by rfl, star_mul, star_star, hFs]
    have heq : (T * blockRealCfc f A) * (blockRealCfc f A * star T) =
        (blockRealCfc f B * blockRealCfc f B) * B := by
      calc
        _ = (T * blockRealCfc f A * blockRealCfc f A) * star T := by
          simp only [mul_assoc]
        _ = (blockRealCfc f B * (T * blockRealCfc f A)) * star T := by
          rw [hinter]
          simp only [mul_assoc]
          rw [← mul_assoc T (blockRealCfc f A) (star T), hinter]
          simp only [mul_assoc]
        _ = _ := by
          rw [hinter]
          simp only [B, mul_assoc]
    rw [heq, ← blockRealCfc_mul hfc hfc]
    conv_lhs => rhs; rw [← blockRealCfc_id hB]
    have hffc : Continuous (fun s ↦ f s * f s) := hfc.mul hfc
    rw [← blockRealCfc_mul hffc continuous_id, ← blockRealCfc_sqrt]
    unfold blockRealCfc
    apply cfc_mono _ _
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp Complex.continuous_re)).continuousOn
    · intro z hz
      obtain ⟨s, hs, rfl⟩ := exists_ofReal_of_spectrum_nonneg hB hz
      simp only [Function.comp_apply, Complex.ofReal_re, id_eq, Complex.real_le_real]
      change (g s)⁻¹ * (g s)⁻¹ * s ≤ Real.sqrt s
      have hgsq : g s * g s = Real.sqrt s + ε :=
        Real.mul_self_sqrt (by linarith [Real.sqrt_nonneg s])
      rw [← mul_inv, hgsq, inv_mul_eq_div]
      apply (div_le_iff₀ (by linarith [Real.sqrt_nonneg s])).mpr
      rw [mul_add, Real.mul_self_sqrt hs]
      exact le_add_of_nonneg_right (by positivity)
    · exact (Complex.continuous_ofReal.comp
        ((hffc.mul continuous_id).comp Complex.continuous_re)).continuousOn
  have h := hermitianBlockNonneg_gram X Y v w
  rw [hXY, hGsq] at h
  have hv := realInner_order hXsq v
  have hw : (⟪w, (operatorRpow A (1 / 2 : ℝ) + (ε : ℂ) • (1 : Operator n)) w⟫_ℂ).re =
      (⟪w, operatorRpow A (1 / 2 : ℝ) w⟫_ℂ).re + ε * ‖w‖ ^ 2 := by
    have hww : (⟪w, w⟫_ℂ).re = ‖w‖ ^ 2 := by
      simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) w
    rw [add_apply, smul_apply, one_apply_eq_self, inner_add_right, inner_smul_right,
      Complex.add_re, Complex.re_ofReal_mul, hww]
  rw [hw] at h
  dsimp [Q]
  linarith only [h, hv]

theorem operatorBlockNonneg_iff_hermitianBlockNonneg {n : ℕ} (A B C : Operator n) :
    OperatorBlockNonneg (!![A, B; star B, C] : Matrix (Fin 2) (Fin 2) (Operator n)) ↔
      HermitianBlockNonneg A B C := by
  have hform (v : Fin 2 → Hilbert n) :
      (∑ i, ∑ j, (⟪v i,
        (!![A, B; star B, C] : Matrix (Fin 2) (Fin 2) (Operator n)) i j (v j)⟫_ℂ).re) =
        (⟪v 0, A (v 0)⟫_ℂ).re + 2 * (⟪v 0, B (v 1)⟫_ℂ).re + (⟪v 1, C (v 1)⟫_ℂ).re := by
    have hsym : (⟪v 1, star B (v 0)⟫_ℂ).re = (⟪v 0, B (v 1)⟫_ℂ).re := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
      simpa only [RCLike.re_to_complex] using inner_re_symm (𝕜 := ℂ) (B (v 1)) (v 0)
    simp [Fin.sum_univ_two, hsym]
    ring
  constructor
  · intro h v w
    have hv := h ![v, w]
    rw [hform] at hv
    simpa using hv
  · intro h v
    rw [hform]
    exact h (v 0) (v 1)

end FreeGroupHypercontractivity
