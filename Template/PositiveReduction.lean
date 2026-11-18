module

import all Template.Model

public import Template.GroupCStar
public import Template.OperatorMajorant
public import Template.Trace
public import Template.HypercontractivityNorm
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Topology.ContinuousMap.Weierstrass

public section

namespace FreeGroupHypercontractivity

open Polynomial
open scoped InnerProductSpace ComplexOrder Topology

/-- The quadratic form of a Hermitian two-by-two operator block with entries
`A,B,B*,C` is nonnegative. -/
@[expose] def HermitianBlockNonneg {n : ℕ} (A B C : Operator n) : Prop :=
  ∀ v w : Hilbert n,
    0 ≤ (⟪v, A v⟫_ℂ).re + 2 * (⟪v, B w⟫_ℂ).re + (⟪w, C w⟫_ℂ).re

private theorem traceRe_star_mul_mul {n : ℕ} (X T Y : Operator n) :
    traceRe (star X * T * Y) =
      (⟪X (lp.single 2 1 1), T (Y (lp.single 2 1 1))⟫_ℂ).re := by
  rw [traceRe_as_inner]
  change ((⟪lp.single 2 (1 : Group n) (1 : ℂ),
    X.adjoint (T (Y (lp.single 2 1 1)))⟫_ℂ).re) = _
  rw [ContinuousLinearMap.adjoint_inner_right]

/-- The trace Cauchy–Schwarz inequality induced by a positive operator block. -/
theorem block_trace_cauchy_schwarz {n : ℕ} {A B C : Operator n}
    (h : HermitianBlockNonneg A B C) (X Y : Operator n) :
    (traceRe (star X * B * Y)) ^ 2 ≤
      traceRe (star X * A * X) * traceRe (star Y * C * Y) := by
  let v := X (lp.single 2 1 1)
  let w := Y (lp.single 2 1 1)
  rw [traceRe_star_mul_mul, traceRe_star_mul_mul, traceRe_star_mul_mul]
  change (⟪v, B w⟫_ℂ).re ^ 2 ≤ (⟪v, A v⟫_ℂ).re * (⟪w, C w⟫_ℂ).re
  have hpoly (r : ℝ) : 0 ≤ (⟪v, A v⟫_ℂ).re * (r * r) +
      (2 * (⟪v, B w⟫_ℂ).re) * r + (⟪w, C w⟫_ℂ).re := by
    have h' := h ((r : ℂ) • v) w
    change 0 ≤ (⟪(r : ℂ) • v, A ((r : ℂ) • v)⟫_ℂ).re +
      2 * (⟪(r : ℂ) • v, B w⟫_ℂ).re + (⟪w, C w⟫_ℂ).re at h'
    rw [A.map_smul] at h'
    rw [inner_smul_left, inner_smul_right, inner_smul_left] at h'
    change 0 ≤ (star (r : ℂ) * ((r : ℂ) * ⟪v, A v⟫_ℂ)).re +
      2 * (star (r : ℂ) * ⟪v, B w⟫_ℂ).re + (⟪w, C w⟫_ℂ).re at h'
    have hrc : star (r : ℂ) = (r : ℂ) := by simp
    simp only [hrc, Complex.re_ofReal_mul] at h'
    convert h' using 1
    ring
  have hdisc := discrim_le_zero hpoly
  unfold discrim at hdisc
  nlinarith only [hdisc]

private theorem trace_pair_le_average {n : ℕ} (X Y : Operator n) :
    traceRe (star X * Y) ≤ (traceRe (star X * X) + traceRe (star Y * Y)) / 2 := by
  let x := X (lp.single 2 1 1)
  let y := Y (lp.single 2 1 1)
  have hinner (U V : Operator n) : traceRe (star U * V) =
      (⟪U (lp.single 2 1 1), V (lp.single 2 1 1)⟫_ℂ).re := by
    simpa using traceRe_star_mul_mul U 1 V
  rw [hinner, hinner, hinner]
  have h := (Complex.abs_re_le_norm (⟪x, y⟫_ℂ)).trans (norm_inner_le_norm x y)
  have h' : (⟪x, y⟫_ℂ).re ≤ ‖x‖ * ‖y‖ := (le_abs_self _).trans h
  change (⟪x, y⟫_ℂ).re ≤ ((⟪x, x⟫_ℂ).re + (⟪y, y⟫_ℂ).re) / 2
  have hr (v : Hilbert n) : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [hr x, hr y]
  nlinarith only [h', sq_nonneg (‖x‖ - ‖y‖)]

private theorem midpoint_le_affine_of_bdd {f : ℝ → ℝ}
    (hmid : ∀ x ∈ Set.Icc 0 1, ∀ y ∈ Set.Icc 0 1,
      f ((x + y) / 2) ≤ (f x + f y) / 2)
    {M : ℝ} (hbdd : ∀ x ∈ Set.Icc 0 1, f x ≤ M)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    f t ≤ (1 - t) * f 0 + t * f 1 := by
  let g (x : ℝ) := f x - ((1 - x) * f 0 + x * f 1)
  have hmid' (x : ℝ) (hx : x ∈ Set.Icc 0 1) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
      g ((x + y) / 2) ≤ (g x + g y) / 2 := by
    dsimp [g]
    nlinarith only [hmid x hx y hy]
  have h0 : g 0 = 0 := by simp [g]
  have h1 : g 1 = 0 := by simp [g]
  let bound := M + |f 0| + |f 1|
  have hbase (x : ℝ) (hx : x ∈ Set.Icc 0 1) : g x ≤ bound := by
    have h2 := mul_le_mul_of_nonneg_left (neg_abs_le (f 0)) (sub_nonneg.mpr hx.2)
    have h3 := mul_le_mul_of_nonneg_left (neg_abs_le (f 1)) hx.1
    have h4 := mul_le_mul_of_nonneg_right (show 1 - x ≤ 1 by linarith [hx.1]) (abs_nonneg (f 0))
    have h5 := mul_le_mul_of_nonneg_right hx.2 (abs_nonneg (f 1))
    dsimp [g, bound]
    nlinarith only [h2, h3, h4, h5, hbdd x hx]
  have hiter (k : ℕ) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
      (2 : ℝ) ^ k * g x ≤ bound := by
    induction k generalizing x with
    | zero => simpa using hbase x hx
    | succ k ih =>
      have hstep : ∃ y ∈ Set.Icc (0 : ℝ) 1, 2 * g x ≤ g y := by
        by_cases hx' : x ≤ 1 / 2
        · refine ⟨2 * x, ⟨by linarith [hx.1], by linarith⟩, ?_⟩
          have h := hmid' 0 (by norm_num) (2 * x) ⟨by linarith [hx.1], by linarith⟩
          rw [h0, zero_add, show 2 * x / 2 = x by ring] at h
          linarith
        · refine ⟨2 * x - 1, ⟨by linarith, by linarith [hx.2]⟩, ?_⟩
          have h := hmid' 1 (by norm_num) (2 * x - 1) ⟨by linarith, by linarith [hx.2]⟩
          rw [h1, zero_add, show (1 + (2 * x - 1)) / 2 = x by ring] at h
          linarith
      obtain ⟨y, hy, hy'⟩ := hstep
      calc
        (2 : ℝ) ^ (k + 1) * g x = (2 : ℝ) ^ k * (2 * g x) := by rw [pow_succ, mul_assoc]
        _ ≤ (2 : ℝ) ^ k * g y := mul_le_mul_of_nonneg_left hy' (by positivity)
        _ ≤ bound := ih y hy
  by_contra! hh
  have hg : 0 < g t := sub_pos.mpr hh
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (bound / g t) (show (1 : ℝ) < 2 by norm_num)
  exact ((div_lt_iff₀ hg).mp hk).not_ge (hiter k t ht)

/-- The positive real power, calculated by the complex functional calculus. -/
@[expose] noncomputable def operatorRpow {n : ℕ} (A : Operator n) (r : ℝ) : Operator n :=
  cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (z.re ^ r)) A

theorem continuous_operatorRpowSymbol {r : ℝ} (hr : 0 ≤ r) :
    Continuous (fun z : ℂ ↦ Complex.ofReal (z.re ^ r)) :=
  Complex.continuous_ofReal.comp (Complex.continuous_re.rpow_const fun _ ↦ Or.inr hr)

theorem operatorRpow_nonneg {n : ℕ} {A : Operator n} (hA : 0 ≤ A) {r : ℝ} :
    0 ≤ operatorRpow A r := by
  refine cfc_nonneg (f := fun z : ℂ ↦ Complex.ofReal (z.re ^ r))
    (a := A) (fun z hz ↦ ?_)
  obtain ⟨a, ha, rfl⟩ := exists_ofReal_of_spectrum_nonneg hA hz
  rw [← Complex.ofReal_zero, Complex.real_le_real, Complex.ofReal_re]
  exact Real.rpow_nonneg ha _

theorem operatorRpow_mem_groupCStar {n : ℕ} {A : Operator n} (hA : A ∈ groupCStar n) (r : ℝ) :
    operatorRpow A r ∈ groupCStar n := cfc_mem_groupCStar _ hA

theorem operatorRpow_zero {n : ℕ} {A : Operator n} (hA : 0 ≤ A) :
    operatorRpow A 0 = 1 := by
  have hN := (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).isSelfAdjoint.isStarNormal
  simp only [operatorRpow, Real.rpow_zero, Complex.ofReal_one]
  exact cfc_const_one ℂ A hN

theorem operatorRpow_one {n : ℕ} {A : Operator n} (hA : 0 ≤ A) :
    operatorRpow A 1 = A := by
  have hN := (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).isSelfAdjoint.isStarNormal
  rw [← cfc_id' ℂ A hN]
  conv_lhs => enter [1]; rw [cfc_id' ℂ A hN]
  apply cfc_congr
  intro z hz
  obtain ⟨r, _, rfl⟩ := exists_ofReal_of_spectrum_nonneg hA hz
  simp

theorem operatorRpow_add {n : ℕ} {A : Operator n} (hA : 0 ≤ A) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    operatorRpow A (r + s) = operatorRpow A r * operatorRpow A s := by
  rw [operatorRpow, operatorRpow, operatorRpow,
    ← cfc_mul _ _ A (continuous_operatorRpowSymbol hr).continuousOn
      (continuous_operatorRpowSymbol hs).continuousOn]
  apply cfc_congr
  intro z hz
  obtain ⟨a, ha, rfl⟩ := exists_ofReal_of_spectrum_nonneg hA hz
  simp only [Complex.ofReal_re, ← Complex.ofReal_mul, Real.rpow_add_of_nonneg ha hr hs]

private theorem sharp_hilbert_nontrivial (n : ℕ) : Nontrivial (Hilbert n) := by
  refine ⟨⟨lp.single 2 1 1, 0, ?_⟩⟩
  intro h
  have := congrArg (fun v : Hilbert n ↦ v 1) h
  simp at this

private theorem norm_operatorRpow_le {n : ℕ} {A : Operator n} (hA : 0 ≤ A)
    {r m : ℝ} (hr : 0 ≤ r) (hm : r ≤ m) :
    ‖operatorRpow A r‖ ≤ (max ‖A‖ 1) ^ m := by
  let _ := sharp_hilbert_nontrivial n
  apply norm_cfc_le (Real.rpow_nonneg (by positivity) _)
  intro z hz
  obtain ⟨a, ha, rfl⟩ := exists_ofReal_of_spectrum_nonneg hA hz
  have han : a ≤ ‖A‖ := by
    simpa [Complex.norm_real, Real.norm_of_nonneg ha] using spectrum.norm_le_norm_of_mem hz
  rw [Complex.norm_real, Complex.ofReal_re, Real.norm_of_nonneg (Real.rpow_nonneg ha r)]
  exact (Real.rpow_le_rpow ha (han.trans (le_max_left _ _)) hr).trans
    (Real.rpow_le_rpow_of_exponent_le (le_max_right _ _) hm)

private theorem traceRe_norm_le {n : ℕ} (A : Operator n) : traceRe A ≤ ‖A‖ := by
  let v : Hilbert n := lp.single 2 1 1
  have hv : ‖v‖ = 1 := by
    simp [v, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  unfold traceRe
  change (A v 1).re ≤ ‖A‖
  exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans
    ((lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (A v) 1).trans
      (A.unit_le_opNorm v hv.le)))

private theorem trace_pair_powers {n : ℕ} {A B : Operator n}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAc : A ∈ groupCStar n) (hBc : B ∈ groupCStar n)
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    traceRe (star (operatorRpow A a * operatorRpow B b) *
      (operatorRpow A c * operatorRpow B d)) =
      traceRe (operatorRpow A (a + c) * operatorRpow B (b + d)) := by
  let A₁ := operatorRpow A a
  let A₂ := operatorRpow A c
  let B₁ := operatorRpow B b
  let B₂ := operatorRpow B d
  have hA₁ : star A₁ = A₁ :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (operatorRpow_nonneg hA)).isSelfAdjoint.star_eq
  have hB₁ : star B₁ = B₁ :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (operatorRpow_nonneg hB)).isSelfAdjoint.star_eq
  change traceRe (star (A₁ * B₁) * (A₂ * B₂)) = _
  have hstar : star (A₁ * B₁) = B₁ * A₁ := by
    calc
      star (A₁ * B₁) = star B₁ * star A₁ := star_mul _ _
      _ = B₁ * A₁ := by rw [hB₁, hA₁]
  have hmB₁ : B₁ ∈ groupCStar n := operatorRpow_mem_groupCStar hBc b
  have hm : (A₁ * A₂) * B₂ ∈ groupCStar n := (groupCStar n).mul_mem
    ((groupCStar n).mul_mem (operatorRpow_mem_groupCStar hAc a)
      (operatorRpow_mem_groupCStar hAc c)) (operatorRpow_mem_groupCStar hBc d)
  calc
    traceRe (star (A₁ * B₁) * (A₂ * B₂)) = traceRe (B₁ * ((A₁ * A₂) * B₂)) := by
      rw [hstar, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    _ = traceRe (((A₁ * A₂) * B₂) * B₁) :=
      traceRe_mul_comm_closure (mem_groupCStar_iff.mp hmB₁) (mem_groupCStar_iff.mp hm)
    _ = traceRe (operatorRpow A (a + c) * operatorRpow B (b + d)) := by
      rw [mul_assoc, operatorRpow_add hA ha hc, show operatorRpow B (b+d) = B₂ * B₁ by
        rw [add_comm, operatorRpow_add hB hd hb]]

/-- A trace pairing of positive powers is bounded by the affine interpolation of their
endpoint moments. -/
theorem traceRe_positive_pair_young {n : ℕ} {A B : Operator n}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAc : A ∈ groupCStar n) (hBc : B ∈ groupCStar n)
    {p q t : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (ht : t ∈ Set.Icc 0 1) :
    traceRe (operatorRpow A (p * t) * operatorRpow B (q * (1 - t))) ≤
      t * traceRe (operatorRpow A p) + (1 - t) * traceRe (operatorRpow B q) := by
  let f (s : ℝ) := traceRe (operatorRpow A (p * s) * operatorRpow B (q * (1 - s)))
  let X (s : ℝ) := operatorRpow A (p * s / 2) * operatorRpow B (q * (1 - s) / 2)
  have hpair (x : ℝ) (hx : x ∈ Set.Icc 0 1) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
      traceRe (star (X x) * X y) = f ((x + y) / 2) := by
    have hx0 := hx.1
    have hx1 := sub_nonneg.mpr hx.2
    have hy0 := hy.1
    have hy1 := sub_nonneg.mpr hy.2
    dsimp [X, f]
    rw [trace_pair_powers hA hB hAc hBc (by positivity) (by positivity)
      (by positivity) (by positivity)]
    congr 3 <;> ring
  have hmid (x : ℝ) (hx : x ∈ Set.Icc 0 1) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
      f ((x + y) / 2) ≤ (f x + f y) / 2 := by
    have h := trace_pair_le_average (X x) (X y)
    rw [hpair x hx y hy, hpair x hx x hx, hpair y hy y hy,
      show (x + x) / 2 = x by ring, show (y + y) / 2 = y by ring] at h
    exact h
  have hbdd (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
      f s ≤ (max ‖A‖ 1) ^ p * (max ‖B‖ 1) ^ q := by
    dsimp [f]
    refine (traceRe_norm_le _).trans ((norm_mul_le _ _).trans ?_)
    have hs0 := hs.1
    have hs1 := sub_nonneg.mpr hs.2
    have hA' := norm_operatorRpow_le hA (show 0 ≤ p * s by positivity)
      (mul_le_of_le_one_right hp hs.2)
    have hB' := norm_operatorRpow_le hB (show 0 ≤ q * (1 - s) by positivity)
      (mul_le_of_le_one_right hq (by linarith))
    exact mul_le_mul hA' hB' (norm_nonneg _) (by positivity)
  have h := midpoint_le_affine_of_bdd hmid hbdd ht
  have h0 : f 0 = traceRe (operatorRpow B q) := by
    simp [f, operatorRpow_zero hA]
  have h1 : f 1 = traceRe (operatorRpow A p) := by
    simp [f, operatorRpow_zero hB]
  rw [h0, h1, add_comm] at h
  exact h

theorem operatorRpow_smul {n : ℕ} {A : Operator n} (hA : 0 ≤ A) {c r : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r) :
    operatorRpow ((c : ℂ) • A) r = (Complex.ofReal (c ^ r)) • operatorRpow A r := by
  let f : ℂ → ℂ := fun z ↦ Complex.ofReal (z.re ^ r)
  have hf : Continuous f := continuous_operatorRpowSymbol hr
  have hN := (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).isSelfAdjoint.isStarNormal
  change cfc (p := IsStarNormal) f ((c : ℂ) • A) = (Complex.ofReal (c ^ r)) • cfc f A
  rw [← cfc_comp_const_mul (c : ℂ) f A hf.continuousOn hN,
    ← cfc_const_mul _ f A hf.continuousOn]
  apply cfc_congr
  intro z hz
  obtain ⟨x, hx, rfl⟩ := exists_ofReal_of_spectrum_nonneg hA hz
  simp only [f, ← Complex.ofReal_mul, Complex.ofReal_re, Real.mul_rpow hc hx]

private theorem trace_power_rescale_le_one {n : ℕ} {A : Operator n}
    (hA : 0 ≤ A) {p a : ℝ} (hp : 0 < p) (ha : 0 < a)
    (h : traceRe (operatorRpow A p) ^ (1 / p) ≤ a) :
    traceRe (operatorRpow (((a⁻¹ : ℝ) : ℂ) • A) p) ≤ 1 := by
  have hA' := traceRe_nonneg (operatorRpow_nonneg (r := p) hA)
  rw [operatorRpow_smul hA (inv_nonneg.mpr ha.le) hp.le, traceRe_ofReal_smul,
    ← Real.rpow_neg_eq_inv_rpow, Real.rpow_neg ha.le, ← div_eq_inv_mul]
  rw [div_le_iff₀ (Real.rpow_pos_of_pos ha _), one_mul]
  have h' := Real.rpow_le_rpow (Real.rpow_nonneg hA' _) h hp.le
  simpa only [one_div, Real.rpow_inv_rpow hA' hp.ne'] using h'

/-- Hölder's inequality for a trace pairing of positive operators in the reduced group
C*-algebra. -/
theorem traceRe_positive_pair_holder {n : ℕ} {A B : Operator n}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAc : A ∈ groupCStar n) (hBc : B ∈ groupCStar n)
    {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1) :
    traceRe (A * B) ≤
      traceRe (operatorRpow A p) ^ (1 / p) * traceRe (operatorRpow B q) ^ (1 / q) := by
  let P := traceRe (operatorRpow A p) ^ (1 / p)
  let Q := traceRe (operatorRpow B q) ^ (1 / q)
  have hP : 0 ≤ P := Real.rpow_nonneg (traceRe_nonneg (operatorRpow_nonneg hA)) _
  have hQ : 0 ≤ Q := Real.rpow_nonneg (traceRe_nonneg (operatorRpow_nonneg hB)) _
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hm (δ : ℝ) (hδ : 0 < δ) : traceRe (A * B) ≤ (P + δ) * (Q + δ) := by
    let a := P + δ
    let b := Q + δ
    let A' : Operator n := Complex.ofReal a⁻¹ • A
    let B' : Operator n := Complex.ofReal b⁻¹ • B
    have ha : 0 < a := by dsimp [a]; positivity
    have hb : 0 < b := by dsimp [b]; positivity
    have hA' : 0 ≤ A' := ContinuousLinearMap.nonneg_iff_isPositive.mpr
      ((ContinuousLinearMap.nonneg_iff_isPositive.mp hA).smul_of_nonneg
        (Complex.zero_le_real.mpr (inv_nonneg.mpr ha.le)))
    have hB' : 0 ≤ B' := ContinuousLinearMap.nonneg_iff_isPositive.mpr
      ((ContinuousLinearMap.nonneg_iff_isPositive.mp hB).smul_of_nonneg
        (Complex.zero_le_real.mpr (inv_nonneg.mpr hb.le)))
    have ht : 1 / p ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_iff₀ hp0).mpr (by linarith)⟩
    have hy := traceRe_positive_pair_young hA' hB'
      ((groupCStar n).smul_mem hAc _) ((groupCStar n).smul_mem hBc _) hp0.le hq0.le ht
    have hp1 : p * (1 / p) = 1 := by field_simp
    have hq1 : q * (1 - 1 / p) = 1 := by
      rw [show 1 - 1 / p = 1 / q by linarith]
      field_simp
    rw [hp1, hq1, operatorRpow_one hA', operatorRpow_one hB'] at hy
    have h1 : traceRe (operatorRpow A' p) ≤ 1 :=
      trace_power_rescale_le_one hA hp0 ha (le_add_of_nonneg_right hδ.le)
    have h2 : traceRe (operatorRpow B' q) ≤ 1 :=
      trace_power_rescale_le_one hB hq0 hb (le_add_of_nonneg_right hδ.le)
    have hy' := hy.trans (add_le_add (mul_le_mul_of_nonneg_left h1 ht.1)
      (mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr ht.2)))
    have hy'' : traceRe (A' * B') ≤ 1 := by linarith
    change traceRe (A * B) ≤ a * b
    dsimp only [A', B'] at hy''
    rw [smul_mul_smul_comm, ← Complex.ofReal_mul, traceRe_ofReal_smul,
      ← mul_inv, ← div_eq_inv_mul] at hy''
    simpa using (div_le_iff₀ (mul_pos ha hb)).mp hy''
  have hcont : Continuous (fun δ : ℝ ↦ (P + δ) * (Q + δ)) := by fun_prop
  have hlim : Filter.Tendsto (fun δ : ℝ ↦ (P + δ) * (Q + δ)) (𝓝[>] 0) (𝓝 (P * Q)) := by
    simpa [ContinuousWithinAt] using hcont.continuousWithinAt (s := Set.Ioi 0) (x := 0)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with δ hδ
  exact hm δ hδ

private theorem cfc_positive_polynomial_pair {n : ℕ} {A B : Operator n}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : ℝ → ℝ) (hf : Continuous f)
    {S : Set (Operator n × Operator n)} (hS : IsClosed S)
    (hpoly : ∀ p : ℂ[X], (aeval A p, aeval B p) ∈ S) :
    (cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (f z.re)) A,
      cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (f z.re)) B) ∈ S := by
  let _ := sharp_hilbert_nontrivial n
  let F (z : ℂ) := Complex.ofReal (f z.re)
  have hF : Continuous F := Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)
  let M := max ‖A‖ ‖B‖
  have hM : 0 ≤ M := le_trans (norm_nonneg A) (le_max_left _ _)
  apply closure_minimal (Set.range_subset_iff.mpr hpoly) hS
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 M f hf.continuousOn (ε / 2)
    (by positivity)
  let P : ℂ[X] := p.map (algebraMap ℝ ℂ)
  have happ {T : Operator n} (hT : 0 ≤ T) (hTm : ‖T‖ ≤ M) :
      ‖aeval T P - cfc (p := IsStarNormal) F T‖ ≤ ε / 2 := by
    have hTn := (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).isSelfAdjoint.isStarNormal
    rw [← cfc_polynomial P T hTn,
      ← cfc_sub (a := T) P.eval F P.continuous.continuousOn hF.continuousOn]
    apply norm_cfc_le (by positivity)
    intro z hz
    obtain ⟨a, ha, rfl⟩ := exists_ofReal_of_spectrum_nonneg hT hz
    have haT : a ≤ ‖T‖ := by
      simpa [Complex.norm_real, Real.norm_of_nonneg ha] using spectrum.norm_le_norm_of_mem hz
    change ‖P.eval ((algebraMap ℝ ℂ) a) - F (a : ℂ)‖ ≤ ε / 2
    rw [show P.eval ((algebraMap ℝ ℂ) a) = (algebraMap ℝ ℂ) (p.eval a) from
      Polynomial.eval_map_apply _ _, show F (a : ℂ) = (algebraMap ℝ ℂ) (f a) by simp [F]]
    rw [← map_sub]
    change ‖((p.eval a - f a : ℝ) : ℂ)‖ ≤ ε / 2
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hp a ⟨ha, haT.trans hTm⟩).le
  refine ⟨(aeval A P, aeval B P), ⟨P, rfl⟩, ?_⟩
  rw [Prod.dist_eq]
  exact max_lt (by rw [dist_eq_norm, norm_sub_rev]; exact (happ hA (le_max_left _ _)).trans_lt (by linarith))
    (by rw [dist_eq_norm, norm_sub_rev]; exact (happ hB (le_max_right _ _)).trans_lt (by linarith))

private theorem aeval_intertwine {n : ℕ} {A B U : Operator n}
    (h : SemiconjBy U A B) (p : ℂ[X]) :
    U * aeval A p = aeval B p * U := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, mul_add, add_mul, hp, hq]
  | monomial k c =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      mul_smul_comm, (h.pow_right k).eq]

/-- A bounded intertwiner of two positive operators also intertwines their
continuous real functional calculus. -/
theorem cfc_positive_intertwine {n : ℕ} {A B U : Operator n}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h : SemiconjBy U A B)
    {f : ℝ → ℝ} (hf : Continuous f) :
    U * cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (f z.re)) A =
      cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (f z.re)) B * U := by
  let S : Set (Operator n × Operator n) := {v | U * v.1 = v.2 * U}
  have hS : IsClosed S :=
    isClosed_eq (continuous_const.mul continuous_fst) (continuous_snd.mul continuous_const)
  exact cfc_positive_polynomial_pair hA hB f hf hS (aeval_intertwine h)

theorem operatorRpow_comp {n : ℕ} {A : Operator n} (hA : 0 ≤ A)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    operatorRpow (operatorRpow A r) s = operatorRpow A (r * s) := by
  let F (z : ℂ) := Complex.ofReal (z.re ^ r)
  let G (z : ℂ) := Complex.ofReal (z.re ^ s)
  have hN := (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).isSelfAdjoint.isStarNormal
  change cfc (p := IsStarNormal) G (cfc F A) = _
  rw [← cfc_comp' G F A (continuous_operatorRpowSymbol hs).continuousOn
    (continuous_operatorRpowSymbol hr).continuousOn hN]
  apply cfc_congr
  intro z hz
  obtain ⟨x, hx, rfl⟩ := exists_ofReal_of_spectrum_nonneg hA hz
  simp only [G, F, Complex.ofReal_re, Real.rpow_mul hx]

theorem traceRe_cfc_star_mul_eq_traceRe_cfc_mul_star {n : ℕ} {T : Operator n}
    (hT : T ∈ groupCStar n) {f : ℝ → ℝ} (hf : Continuous f) :
    traceRe (cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (f z.re)) (star T * T)) =
      traceRe (cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (f z.re)) (T * star T)) := by
  let A := star T * T
  let B := T * star T
  have hA : 0 ≤ A := star_mul_self_nonneg T
  have hB : 0 ≤ B := mul_star_self_nonneg T
  let S : Set (Operator n × Operator n) := {u | traceRe u.1 = traceRe u.2}
  have hS : IsClosed S :=
    isClosed_eq ((continuous_traceRe n).comp continuous_fst) ((continuous_traceRe n).comp continuous_snd)
  have hsT : star T ∈ groupCStar n := star_mem hT
  have hcA : A ∈ groupCStar n := (groupCStar n).mul_mem hsT hT
  have hsc : SemiconjBy T A B := by
    change T * (star T * T) = (T * star T) * T
    rw [mul_assoc]
  have hp (k : ℕ) : traceRe (A ^ k) = traceRe (B ^ k) := by
    cases k with
    | zero => simp
    | succ k =>
      calc
        traceRe (A ^ (k + 1)) = traceRe (star T * (T * A ^ k)) := by
          rw [pow_succ', ← mul_assoc]
        _ = traceRe ((T * A ^ k) * star T) :=
          traceRe_mul_comm_closure (mem_groupCStar_iff.mp hsT)
            (mem_groupCStar_iff.mp ((groupCStar n).mul_mem hT ((groupCStar n).pow_mem hcA k)))
        _ = traceRe (B ^ (k + 1)) := by rw [(hsc.pow_right k).eq, mul_assoc, pow_succ]
  apply cfc_positive_polynomial_pair hA hB f hf hS
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    change traceRe (aeval A (p + q)) = traceRe (aeval B (p + q))
    change traceRe (aeval A p) = traceRe (aeval B p) at hp
    change traceRe (aeval A q) = traceRe (aeval B q) at hq
    simp only [map_add, traceRe_add, hp, hq]
  | monomial k c =>
    change traceRe (aeval A (monomial k c)) = traceRe (aeval B (monomial k c))
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    -- The real part of the trace also scales by a complex scalar on self-adjoint arguments.
    have hsmul (U : Operator n) (hU : IsSelfAdjoint U) :
        traceRe (c • U) = c.re * traceRe U := by
      rw [traceRe_as_inner, traceRe_as_inner]
      let δ : Hilbert n := lp.single 2 1 1
      have him : (⟪δ, U δ⟫_ℂ).im = 0 := by
        have hsa := ContinuousLinearMap.isSelfAdjoint_iff'.mp hU
        have h := ContinuousLinearMap.adjoint_inner_right U δ δ
        rw [hsa, ← inner_conj_symm δ (U δ)] at h
        have h' := congrArg Complex.im h
        change (star (⟪U δ, δ⟫_ℂ)).im = (⟪U δ, δ⟫_ℂ).im at h'
        rw [Complex.star_def, Complex.conj_im] at h'
        rw [← inner_conj_symm δ (U δ)]
        change (star (⟪U δ, δ⟫_ℂ)).im = 0
        rw [Complex.star_def, Complex.conj_im]
        linarith
      change (⟪δ, c • U δ⟫_ℂ).re = c.re * (⟪δ, U δ⟫_ℂ).re
      rw [inner_smul_right, Complex.mul_re, him, mul_zero, sub_zero]
    rw [hsmul _ ((ContinuousLinearMap.nonneg_iff_isPositive.mp hA).isSelfAdjoint.pow k),
      hsmul _ ((ContinuousLinearMap.nonneg_iff_isPositive.mp hB).isSelfAdjoint.pow k), hp]

theorem traceRe_positive_pair_nonneg {n : ℕ} {A B : Operator n}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAc : A ∈ groupCStar n) (hBc : B ∈ groupCStar n) :
    0 ≤ traceRe (A * B) := by
  let X := operatorRpow A (1 / 2) * operatorRpow B (1 / 2)
  have he := trace_pair_powers hA hB hAc hBc (a := 1 / 2) (b := 1 / 2)
    (c := 1 / 2) (d := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, operatorRpow_one hA, operatorRpow_one hB] at he
  rw [← he]
  exact traceRe_nonneg (star_mul_self_nonneg X)

theorem traceRe_positive_pair_mono {n : ℕ} {A B C : Operator n}
    (hA : 0 ≤ A) (h : B ≤ C)
    (hAc : A ∈ groupCStar n) (hBc : B ∈ groupCStar n) (hCc : C ∈ groupCStar n) :
    traceRe (A * B) ≤ traceRe (A * C) := by
  have hC := traceRe_positive_pair_nonneg hA (sub_nonneg.mpr h) hAc
    ((groupCStar n).sub_mem hCc hBc)
  rwa [mul_sub, traceRe_sub, sub_nonneg] at hC

private noncomputable def positiveCFC {n : ℕ} (A : Operator n) (f : ℝ → ℝ) : Operator n :=
  cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (f z.re)) A

private theorem continuous_realSymbol {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun z : ℂ ↦ Complex.ofReal (f z.re)) :=
  Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)

private theorem positiveCFC_star {n : ℕ} (A : Operator n) (f : ℝ → ℝ) :
    star (positiveCFC A f) = positiveCFC A f := by
  unfold positiveCFC
  rw [← cfc_star]
  congr 1
  funext z
  simp

private theorem positiveCFC_mul {n : ℕ} (A : Operator n)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    positiveCFC A (fun x ↦ f x * g x) = positiveCFC A f * positiveCFC A g := by
  unfold positiveCFC
  simp only [Complex.ofReal_mul]
  exact cfc_mul _ _ A (continuous_realSymbol hf).continuousOn (continuous_realSymbol hg).continuousOn

private theorem positiveCFC_id {n : ℕ} {A : Operator n} (hA : 0 ≤ A) :
    positiveCFC A id = A := by
  have h := operatorRpow_one hA
  simpa [operatorRpow, positiveCFC] using h

private theorem positiveCFC_mono {n : ℕ} {A : Operator n} (hA : 0 ≤ A)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : ℝ, 0 ≤ x → f x ≤ g x) : positiveCFC A f ≤ positiveCFC A g := by
  refine cfc_mono (fun z hz ↦ ?_) (continuous_realSymbol hf).continuousOn
    (continuous_realSymbol hg).continuousOn
  obtain ⟨x, hx, rfl⟩ := exists_ofReal_of_spectrum_nonneg hA hz
  simpa only [Complex.ofReal_re, Complex.real_le_real] using h x hx

private noncomputable def regularizer (ε u x : ℝ) : ℝ :=
  x ^ u / Real.sqrt (max x 0 + ε)

private theorem continuous_regularizer {ε u : ℝ} (hε : 0 < ε) (hu : 0 ≤ u) :
    Continuous (regularizer ε u) := by
  have hh (x : ℝ) : 0 < max x 0 + ε := add_pos_of_nonneg_of_pos (le_max_right _ _) hε
  have hp : Continuous (fun x : ℝ ↦ x ^ u) :=
    continuous_id.rpow_const fun _ ↦ Or.inr hu
  have hq : Continuous (fun x : ℝ ↦ Real.sqrt (max x 0 + ε)) := by fun_prop
  exact hp.div hq (fun x ↦ (Real.sqrt_pos.2 (hh x)).ne')

private theorem regularizer_diag_le {ε u x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) (hu : 0 ≤ u) :
    (regularizer ε u x * regularizer ε u x) * x ≤ x ^ (u + u) := by
  simp only [regularizer, max_eq_left hx]
  rw [div_mul_div_comm, Real.mul_self_sqrt (by positivity : 0 ≤ x + ε),
    ← Real.rpow_add_of_nonneg hx hu hu]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < x + ε)]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hε.le) (by positivity)

private theorem sqrt_sub_sqrt_div_le {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) :
    0 ≤ Real.sqrt x - x / Real.sqrt (x + ε) ∧
      Real.sqrt x - x / Real.sqrt (x + ε) ≤ Real.sqrt ε := by
  have hxp : 0 < x + ε := by positivity
  have hs := Real.sqrt_pos.2 hxp
  have he2 : Real.sqrt ε ≤ Real.sqrt (x + ε) := Real.sqrt_le_sqrt (by linarith)
  have hx2 : Real.sqrt x ≤ Real.sqrt (x + ε) := Real.sqrt_le_sqrt (by linarith)
  constructor
  · apply sub_nonneg.mpr
    apply (div_le_iff₀ hs).2
    calc
      x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx).symm
      _ ≤ Real.sqrt x * Real.sqrt (x + ε) := mul_le_mul_of_nonneg_left hx2 (Real.sqrt_nonneg x)
  · have he3 : ε / Real.sqrt (x + ε) ≤ Real.sqrt ε := by
      apply (div_le_iff₀ hs).2
      calc
        ε = Real.sqrt ε * Real.sqrt ε := (Real.mul_self_sqrt hε.le).symm
        _ ≤ Real.sqrt ε * Real.sqrt (x + ε) := mul_le_mul_of_nonneg_left he2 (Real.sqrt_nonneg ε)
    have hh : x / Real.sqrt (x + ε) = Real.sqrt (x + ε) - ε / Real.sqrt (x + ε) := by
      rw [eq_sub_iff_add_eq, ← add_div]
      apply (div_eq_iff hs.ne').2
      rw [Real.mul_self_sqrt hxp.le]
    linarith

private theorem cross_scalar_bound {ε u x : ℝ} (hε : 0 < ε) (hu : 0 ≤ u) (hx : 0 ≤ x) :
    |x ^ (u + u + 1 / 2) - (regularizer ε u x * x) * x ^ u| ≤
      x ^ (u + u) * Real.sqrt ε := by
  have hxe := sqrt_sub_sqrt_div_le hx hε
  have hfactor : x ^ (u + u + 1 / 2) - (regularizer ε u x * x) * x ^ u =
      x ^ (u + u) * (Real.sqrt x - x / Real.sqrt (x + ε)) := by
    rw [Real.rpow_add_of_nonneg hx (add_nonneg hu hu) (by norm_num),
      ← Real.sqrt_eq_rpow, regularizer, max_eq_left hx, Real.rpow_add_of_nonneg hx hu hu]
    ring
  rw [hfactor, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx _) hxe.1)]
  exact mul_le_mul_of_nonneg_left hxe.2 (Real.rpow_nonneg hx _)

theorem operatorLpNorm_of_nonneg_eq_trace_rpow {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {A : Operator n} (hA : 0 ≤ A) :
    operatorLpNorm r A = traceRe (operatorRpow A r) ^ (1 / r) := by
  change traceRe (operatorRpow (star A * A) (r / 2)) ^ (1 / r) = _
  have hAs := (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).isSelfAdjoint.star_eq
  have hs : A * A = operatorRpow A (2 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, operatorRpow_add hA (by norm_num) (by norm_num),
      operatorRpow_one hA]
  rw [hAs, hs, operatorRpow_comp hA (by norm_num) (by positivity),
    show (2 : ℝ) * (r / 2) = r by ring]

theorem operatorLpNorm_absoluteValue_eq {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (A : Operator n) :
    operatorLpNorm r (operatorRpow (star A * A) (1 / 2)) = operatorLpNorm r A := by
  have hA := star_mul_self_nonneg A
  rw [operatorLpNorm_of_nonneg_eq_trace_rpow hr (operatorRpow_nonneg hA),
    operatorRpow_comp hA (by norm_num) hr, show (1 / 2 : ℝ) * r = r / 2 by ring]
  rfl

theorem operatorLpNorm_star_eq {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {A : Operator n} (hA : A ∈ groupCStar n) :
    operatorLpNorm r (star A) = operatorLpNorm r A := by
  unfold operatorLpNorm
  have hAA : star (star A) = A := star_star A
  have hf : Continuous (fun x : ℝ ↦ x ^ (r / 2)) :=
    continuous_id.rpow_const fun _ ↦ Or.inr (by positivity)
  rw [hAA, ← traceRe_cfc_star_mul_eq_traceRe_cfc_mul_star hA hf]

private theorem traceRe_sandwich_rotate {n : ℕ} {X A : Operator n}
    (hX : X ∈ groupCStar n) (hA : A ∈ groupCStar n) :
    traceRe (star X * A * X) = traceRe (A * (X * star X)) := by
  rw [mul_assoc, traceRe_mul_comm_closure (mem_groupCStar_iff.mp (star_mem hX))
    (mem_groupCStar_iff.mp ((groupCStar n).mul_mem hA hX)), mul_assoc]

private theorem trace_cross_approximation {n : ℕ} {S : Operator n} (hS : 0 ≤ S)
    {ε u : ℝ} (hε : 0 < ε) (hu : 0 ≤ u) :
    traceRe (operatorRpow S (u + u + 1 / 2)) ≤
      traceRe (positiveCFC S (fun x ↦ (regularizer ε u x * x) * x ^ u)) +
        (max ‖S‖ 1) ^ (u + u) * Real.sqrt ε := by
  let _ := sharp_hilbert_nontrivial n
  let F (x : ℝ) := x ^ (u + u + 1 / 2)
  let G (x : ℝ) := (regularizer ε u x * x) * x ^ u
  have hp : Continuous (fun x : ℝ ↦ x ^ u) := continuous_id.rpow_const fun _ ↦ Or.inr hu
  have hF : Continuous F := continuous_id.rpow_const fun _ ↦ Or.inr (by positivity)
  have hG : Continuous G := ((continuous_regularizer hε hu).mul continuous_id).mul hp
  have hnorm : ‖positiveCFC S F - positiveCFC S G‖ ≤
      (max ‖S‖ 1) ^ (u + u) * Real.sqrt ε := by
    unfold positiveCFC
    rw [← cfc_sub (a := S) _ _ (continuous_realSymbol hF).continuousOn
      (continuous_realSymbol hG).continuousOn]
    apply norm_cfc_le (by positivity)
    intro z hz
    obtain ⟨x, hx, rfl⟩ := exists_ofReal_of_spectrum_nonneg hS hz
    have hxS : x ≤ ‖S‖ := by
      simpa [Complex.norm_real, Real.norm_of_nonneg hx] using spectrum.norm_le_norm_of_mem hz
    simp only [Complex.ofReal_re, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (cross_scalar_bound hε hu hx).trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hx (hxS.trans (le_max_left _ _)) (add_nonneg hu hu))
      (Real.sqrt_nonneg _))
  have ht := (traceRe_norm_le (positiveCFC S F - positiveCFC S G)).trans hnorm
  rw [traceRe_sub] at ht
  change traceRe (operatorRpow S (u + u + 1 / 2)) -
    traceRe (positiveCFC S (fun x ↦ (regularizer ε u x * x) * x ^ u)) ≤ _ at ht
  linarith only [ht]

set_option maxHeartbeats 600000 in
private theorem block_trace_approximate {n : ℕ} {A B C : Operator n}
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hmA : A ∈ groupCStar n) (hmB : B ∈ groupCStar n) (hmC : C ∈ groupCStar n)
    (h : HermitianBlockNonneg A B C) {u ε : ℝ} (hu : 0 ≤ u) (hε : 0 < ε) :
    ∃ v : ℝ,
      traceRe (operatorRpow (star B * B) (u + u + 1 / 2)) ≤
        v + (max ‖star B * B‖ 1) ^ (u + u) * Real.sqrt ε ∧
      v ^ 2 ≤ traceRe (A * operatorRpow (B * star B) (u + u)) *
        traceRe (C * operatorRpow (star B * B) (u + u)) := by
  let S := star B * B
  let R := B * star B
  have hS : 0 ≤ S := star_mul_self_nonneg B
  have hR : 0 ≤ R := mul_star_self_nonneg B
  have hmBstar : star B ∈ groupCStar n := star_mem hmB
  have hmS : S ∈ groupCStar n := (groupCStar n).mul_mem hmBstar hmB
  have hmR : R ∈ groupCStar n := (groupCStar n).mul_mem hmB hmBstar
  let f := regularizer ε u
  let F := positiveCFC S f
  let G := positiveCFC R f
  let X := B * F
  let Y := operatorRpow S u
  have hf : Continuous f := continuous_regularizer hε hu
  have hp : Continuous (fun x : ℝ ↦ x ^ u) := continuous_id.rpow_const fun _ ↦ Or.inr hu
  have hX : X ∈ groupCStar n := (groupCStar n).mul_mem hmB (cfc_mem_groupCStar _ hmS)
  have hY : Y ∈ groupCStar n := operatorRpow_mem_groupCStar hmS u
  have hxstar : star X = F * star B :=
    (show star (B * F) = star F * star B from star_mul _ _).trans
      (congrArg (· * star B) (positiveCFC_star S f))
  have hystar : star Y = Y :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (operatorRpow_nonneg hS)).isSelfAdjoint.star_eq
  have hs : SemiconjBy B S R := by
    change B * (star B * B) = (B * star B) * B
    rw [mul_assoc]
  have hcomm : B * F = G * B := cfc_positive_intertwine hS hR hs hf
  have hxx : X * star X = (G * G) * R := by
    rw [hxstar]
    change (B * F) * (F * star B) = _
    rw [hcomm, mul_assoc G, ← mul_assoc B, hcomm, mul_assoc G B, ← mul_assoc]
  have hxxle : X * star X ≤ operatorRpow R (u + u) := by
    have hf2 : Continuous (fun x : ℝ ↦ f x * f x) := hf.mul hf
    have hf3 : Continuous (fun x : ℝ ↦ (f x * f x) * x) := hf2.mul continuous_id
    have hp2 : Continuous (fun x : ℝ ↦ x ^ (u + u)) :=
      continuous_id.rpow_const fun _ ↦ Or.inr (add_nonneg hu hu)
    have hreal : (G * G) * R = positiveCFC R (fun x ↦ (f x * f x) * x) := by
      calc
        (G * G) * R = positiveCFC R (fun x ↦ f x * f x) * positiveCFC R id := by
          rw [positiveCFC_id hR, positiveCFC_mul R hf hf]
        _ = _ := (positiveCFC_mul R hf2 continuous_id).symm
    rw [hxx, hreal]
    exact positiveCFC_mono hR hf3 hp2 (fun x hx ↦ regularizer_diag_le hε hx hu)
  have hyy : Y * star Y = operatorRpow S (u + u) := by
    rw [hystar]
    exact (operatorRpow_add hS hu hu).symm
  have hcross : star X * B * Y = positiveCFC S (fun x ↦ (f x * x) * x ^ u) := by
    rw [hxstar, mul_assoc F (star B) B]
    change (F * S) * Y = _
    conv_lhs => enter [1, 2]; rw [← positiveCFC_id hS]
    rw [← positiveCFC_mul S hf continuous_id]
    have hfi : Continuous (fun x : ℝ ↦ f x * x) := hf.mul continuous_id
    exact (positiveCFC_mul S hfi hp).symm
  refine ⟨traceRe (star X * B * Y), ?_, ?_⟩
  · rw [hcross]
    exact trace_cross_approximation hS hε hu
  have hquad := block_trace_cauchy_schwarz h X Y
  rw [traceRe_sandwich_rotate hX hmA, traceRe_sandwich_rotate hY hmC, hyy] at hquad
  apply hquad.trans
  apply mul_le_mul_of_nonneg_right _ (traceRe_positive_pair_nonneg hC
    (operatorRpow_nonneg hS) hmC (operatorRpow_mem_groupCStar hmS _))
  have hXs : star X ∈ groupCStar n := star_mem hX
  exact traceRe_positive_pair_mono hA hxxle hmA
    ((groupCStar n).mul_mem hX hXs) (operatorRpow_mem_groupCStar hmR _)

/-- The q-moment norm of an off-diagonal entry of a positive block is bounded by the
geometric mean of the q-moment norms of the diagonal entries. -/
theorem block_power_trace_le {n : ℕ} {A B C : Operator n}
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hmA : A ∈ groupCStar n) (hmB : B ∈ groupCStar n) (hmC : C ∈ groupCStar n)
    (h : HermitianBlockNonneg A B C) {q : ℝ} (hq : 1 < q) :
    traceRe (operatorRpow (star B * B) (q / 2)) ^ (2 / q) ≤
      traceRe (operatorRpow A q) ^ (1 / q) * traceRe (operatorRpow C q) ^ (1 / q) := by
  let S := star B * B
  let R := B * star B
  have hS : 0 ≤ S := star_mul_self_nonneg B
  have hR : 0 ≤ R := mul_star_self_nonneg B
  have hmBstar : star B ∈ groupCStar n := star_mem hmB
  have hmS : S ∈ groupCStar n := (groupCStar n).mul_mem hmBstar hmB
  have hmR : R ∈ groupCStar n := (groupCStar n).mul_mem hmB hmBstar
  let u := (q - 1) / 4
  let q' := q / (q - 1)
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := sub_pos.mpr hq
  have hq' : 1 < q' := (lt_div_iff₀ hq1).2 (by linarith)
  have hqq' : 1 / q + 1 / q' = 1 := by dsimp [q']; field_simp; ring
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have huq : (u + u) * q' = q / 2 := by dsimp [u, q']; field_simp; ring
  have huq' : u + u + 1 / 2 = q / 2 := by dsimp [u]; ring
  let μ := traceRe (operatorRpow S (q / 2))
  let ν := μ ^ (1 / q')
  let a := traceRe (operatorRpow A q) ^ (1 / q)
  let c := traceRe (operatorRpow C q) ^ (1 / q)
  let K := a * c * ν ^ 2
  have hμ : 0 ≤ μ := traceRe_nonneg (operatorRpow_nonneg hS)
  have hν : 0 ≤ ν := Real.rpow_nonneg hμ _
  have ha : 0 ≤ a := Real.rpow_nonneg (traceRe_nonneg (operatorRpow_nonneg hA)) _
  have hc : 0 ≤ c := Real.rpow_nonneg (traceRe_nonneg (operatorRpow_nonneg hC)) _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hμR : traceRe (operatorRpow R (q / 2)) = μ := by
    have hpow : Continuous (fun x : ℝ ↦ x ^ (q / 2)) :=
      continuous_id.rpow_const fun _ ↦ Or.inr (by positivity)
    exact (traceRe_cfc_star_mul_eq_traceRe_cfc_mul_star hmB hpow).symm
  have haH := traceRe_positive_pair_holder hA (operatorRpow_nonneg (r := u + u) hR)
    hmA (operatorRpow_mem_groupCStar hmR _) hq hq' hqq'
  have hcH := traceRe_positive_pair_holder hC (operatorRpow_nonneg (r := u + u) hS)
    hmC (operatorRpow_mem_groupCStar hmS _) hq hq' hqq'
  rw [operatorRpow_comp hR (add_nonneg hu hu) (by linarith), huq, hμR] at haH
  rw [operatorRpow_comp hS (add_nonneg hu hu) (by linarith), huq] at hcH
  have hprod : traceRe (A * operatorRpow R (u + u)) *
      traceRe (C * operatorRpow S (u + u)) ≤ K := by
    have hp := mul_le_mul haH hcH
      (traceRe_positive_pair_nonneg hC (operatorRpow_nonneg hS) hmC
        (operatorRpow_mem_groupCStar hmS _)) (mul_nonneg ha hν)
    exact hp.trans_eq (by dsimp [K, a, c, ν, μ]; ring)
  let D := (max ‖S‖ 1) ^ (u + u)
  have he (ε : ℝ) (hε : 0 < ε) : μ ≤ Real.sqrt K + D * Real.sqrt ε := by
    obtain ⟨v, hv, hv2⟩ := block_trace_approximate hA hC hmA hmB hmC h hu hε
    rw [huq'] at hv
    have hvK := hv2.trans hprod
    have hv' : v ≤ Real.sqrt K := by
      have hvK' : v ^ 2 ≤ (Real.sqrt K) ^ 2 := by rwa [Real.sq_sqrt hK]
      by_contra! hgt
      have hvpos : 0 ≤ v := (Real.sqrt_nonneg K).trans hgt.le
      exact (not_le_of_gt ((sq_lt_sq₀ (Real.sqrt_nonneg K) hvpos).mpr hgt)) hvK'
    exact hv.trans (add_le_add_left hv' _)
  have hlim : Filter.Tendsto (fun ε : ℝ ↦ Real.sqrt K + D * Real.sqrt ε)
      (𝓝[>] 0) (𝓝 (Real.sqrt K)) := by
    have hcont : Continuous (fun ε : ℝ ↦ Real.sqrt K + D * Real.sqrt ε) := by fun_prop
    simpa [ContinuousWithinAt] using hcont.continuousWithinAt (s := Set.Ioi 0) (x := 0)
  have hμK : μ ≤ Real.sqrt K := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
    exact he ε hε
  have hμK2 : μ ^ 2 ≤ K := by
    simpa only [Real.sq_sqrt hK] using (sq_le_sq₀ hμ (Real.sqrt_nonneg K)).mpr hμK
  change μ ^ (2 / q) ≤ a * c
  by_cases hm0 : μ = 0
  · rw [hm0, Real.zero_rpow (by positivity : 2 / q ≠ 0)]
    exact mul_nonneg ha hc
  have hmpos := lt_of_le_of_ne hμ (Ne.symm hm0)
  have hνpos : 0 < ν := Real.rpow_pos_of_pos hmpos _
  have hν2 : ν ^ 2 = μ ^ (2 / q') := by
    dsimp [ν]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμ]
    congr 1
    norm_num
    ring
  have heq : 2 / q + 2 / q' = 2 := by
    calc
      2 / q + 2 / q' = 2 * (1 / q + 1 / q') := by ring
      _ = 2 := by rw [hqq', mul_one]
  have hh : μ ^ (2 / q) * ν ^ 2 = μ ^ 2 := by
    rw [hν2, ← Real.rpow_add hmpos, heq, Real.rpow_two]
  exact le_of_mul_le_mul_right (hh ▸ hμK2) (sq_pos_of_pos hνpos)

end FreeGroupHypercontractivity
