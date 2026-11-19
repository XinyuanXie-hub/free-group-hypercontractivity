module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

public section

namespace FreeGroupHypercontractivity

open Set

/-- The Gross differential argument for a positive moment (A(s)) at exponent (r(s)).
The terms (B(s)) and (D(s)) are the logarithmic moment and the dissipation,
respectively. -/
theorem moment_le_of_entropy_dissipation {t : ℝ} (ht : 0 ≤ t)
    (A r R B D : ℝ → ℝ)
    (hA : ∀ s ∈ Icc 0 t, 0 < A s) (hr : ∀ s ∈ Icc 0 t, 1 < r s)
    (hAc : ContinuousOn A (Icc 0 t)) (hrc : ContinuousOn r (Icc 0 t))
    (hA' : ∀ s ∈ Ioo 0 t, HasDerivAt A (R s * B s - r s * D s) s)
    (hr' : ∀ s ∈ Ioo 0 t, HasDerivAt r (R s) s)
    (hR : ∀ s ∈ Ioo 0 t, 0 ≤ R s ∧ R s ≤ 2 * (r s - 1))
    (hD : ∀ s ∈ Ioo 0 t, 0 ≤ D s)
    (hEnt : ∀ s ∈ Ioo 0 t,
      2 * (r s - 1) * (r s * B s - A s * Real.log (A s)) ≤ r s ^ 2 * D s) :
    A t ^ (1 / r t) ≤ A 0 ^ (1 / r 0) := by
  have hF : ContinuousOn (fun s ↦ Real.log (A s) / r s) (Icc 0 t) :=
    (hAc.log fun s hs ↦ (hA s hs).ne').div hrc
      fun s hs ↦ (zero_lt_one.trans (hr s hs)).ne'
  have hF' (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivAt (fun s ↦ Real.log (A s) / r s)
        (((R s * B s - r s * D s) / A s * r s - Real.log (A s) * R s) / r s ^ 2) s :=
    ((hA' s hs).log (hA s (Ioo_subset_Icc_self hs)).ne').div (hr' s hs)
      (zero_lt_one.trans (hr s (Ioo_subset_Icc_self hs))).ne'
  have hanti : AntitoneOn (fun s ↦ Real.log (A s) / r s) (Icc 0 t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc ..) hF
    · rw [interior_Icc]
      exact fun s hs ↦ (hF' s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hF' s hs).deriv]
      have hAs := hA s (Ioo_subset_Icc_self hs)
      have hrs := hr s (Ioo_subset_Icc_self hs)
      have hrpos : 0 < r s := zero_lt_one.trans hrs
      have hfactor : 0 < 2 * (r s - 1) := by positivity
      have hden : 0 < r s ^ 2 * A s := by positivity
      rw [show ((R s * B s - r s * D s) / A s * r s - Real.log (A s) * R s) /
          r s ^ 2 =
          (R s * (r s * B s - A s * Real.log (A s)) - r s ^ 2 * D s) /
            (r s ^ 2 * A s) by field_simp; ring]
      apply div_nonpos_of_nonpos_of_nonneg _ hden.le
      rw [sub_nonpos]
      have hbound : r s * B s - A s * Real.log (A s) ≤
          (r s ^ 2 * D s) / (2 * (r s - 1)) := by
        exact (le_div_iff₀ hfactor).2 (by simpa [mul_comm] using hEnt s hs)
      calc
        _ ≤ R s * ((r s ^ 2 * D s) / (2 * (r s - 1))) :=
          mul_le_mul_of_nonneg_left hbound (hR s hs).1
        _ ≤ 2 * (r s - 1) * ((r s ^ 2 * D s) / (2 * (r s - 1))) :=
          mul_le_mul_of_nonneg_right (hR s hs).2
            (div_nonneg (mul_nonneg (sq_nonneg _) (hD s hs)) hfactor.le)
        _ = r s ^ 2 * D s := by field_simp
  have h0 : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, ht⟩
  have ht' : t ∈ Icc 0 t := ⟨ht, le_rfl⟩
  rw [Real.rpow_def_of_pos (hA t ht'), Real.rpow_def_of_pos (hA 0 h0)]
  apply Real.exp_le_exp.mpr
  simpa [div_eq_mul_inv] using hanti h0 ht' ht


/-- If the elapsed time meets the hypercontractive threshold, an exponent path
from (p) to (q) has instantaneous rate at most (2(r-1)). -/
theorem exists_gross_exponent_path {p q t : ℝ} (hp : 1 < p) (hpq : p ≤ q)
    (ht : 0 < t) (hthreshold : (1 / 2 : ℝ) * Real.log ((q - 1) / (p - 1)) ≤ t) :
    ∃ r R : ℝ → ℝ, r 0 = p ∧ r t = q ∧ Continuous r ∧
      (∀ s, 1 < r s) ∧ (∀ s, HasDerivAt r (R s) s) ∧
      ∀ s, 0 ≤ R s ∧ R s ≤ 2 * (r s - 1) := by
  let k := Real.log ((q - 1) / (p - 1)) / t
  have hp' : 0 < p - 1 := by linarith
  have hq' : 0 < q - 1 := by linarith
  have hratio : 1 ≤ (q - 1) / (p - 1) := by
    rw [le_div_iff₀ hp']
    linarith
  have hk : 0 ≤ k := div_nonneg (Real.log_nonneg hratio) ht.le
  have hk₂ : k ≤ 2 := (div_le_iff₀ ht).2 (by linarith)
  let r (s : ℝ) := 1 + (p - 1) * Real.exp (k * s)
  let R (s : ℝ) := k * ((p - 1) * Real.exp (k * s))
  have hr₀ : r 0 = p := by simp [r]
  have hrt : r t = q := by
    dsimp [r, k]
    rw [div_mul_cancel₀ _ ht.ne', Real.exp_log (div_pos hq' hp')]
    field_simp
    ring
  refine ⟨r, R, hr₀, hrt, by fun_prop, ?_, ?_, ?_⟩
  · intro s
    dsimp [r]
    have h : 0 < (p - 1) * Real.exp (k * s) := mul_pos hp' (Real.exp_pos _)
    linarith
  · intro s
    have hk' := (hasDerivAt_id s).const_mul k
    have h := ((hk'.exp).const_mul (p - 1)).const_add 1
    simpa [r, R, mul_left_comm, mul_comm] using h
  · intro s
    have hexp : 0 ≤ (p - 1) * Real.exp (k * s) := mul_nonneg hp'.le (Real.exp_nonneg _)
    constructor
    · exact mul_nonneg hk hexp
    · dsimp [R, r]
      rw [add_sub_cancel_left]
      exact mul_le_mul_of_nonneg_right hk₂ hexp


/-- The sharp time threshold can be zero only when the two exponents agree. -/
theorem exponents_eq_of_zero_time {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q)
    (hthreshold : (1 / 2 : ℝ) * Real.log ((q - 1) / (p - 1)) ≤ 0) : p = q := by
  have h₁ : 0 < p - 1 := by linarith
  have h₂ : 0 < q - 1 := by linarith
  have hlog : Real.log ((q - 1) / (p - 1)) ≤ 0 := by linarith
  have hratio := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (div_pos h₂ h₁), Real.exp_zero, div_le_iff₀ h₁, one_mul] at hratio
  exact le_antisymm hpq (by linarith)

end FreeGroupHypercontractivity
