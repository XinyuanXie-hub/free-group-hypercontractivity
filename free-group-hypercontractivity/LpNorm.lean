module

public import «free-group-hypercontractivity».AbsoluteValueBlock
import all «free-group-hypercontractivity».Model

public section

namespace FreeGroupHypercontractivity

open scoped ComplexOrder ENNReal

private theorem tracialNorm_nonneg {n : ℕ} (p : ℝ) (A : Operator n) :
    0 ≤ operatorLpNorm p A := by
  change 0 ≤ traceRe (operatorRpow (star A * A) (p / 2)) ^ (1 / p)
  exact Real.rpow_nonneg (traceRe_nonneg (operatorRpow_nonneg (star_mul_self_nonneg A))) _

private theorem tracialNorm_sq {n : ℕ} (p : ℝ) (A : Operator n) :
    operatorLpNorm p A ^ 2 = traceRe (operatorRpow (star A * A) (p / 2)) ^ (2 / p) := by
  change (traceRe (operatorRpow (star A * A) (p / 2)) ^ (1 / p)) ^ 2 = _
  have h := traceRe_nonneg (operatorRpow_nonneg (r := p / 2) (star_mul_self_nonneg A))
  rw [← Real.rpow_natCast, ← Real.rpow_mul h]
  congr 1
  push_cast
  ring

private theorem tracialNorm_add_positive {n : ℕ} {A B : Operator n}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hmA : A ∈ groupCStar n) (hmB : B ∈ groupCStar n)
    {p : ℝ} (hp : 1 < p) :
    operatorLpNorm p (A + B) ≤ operatorLpNorm p A + operatorLpNorm p B := by
  let S := A + B
  let q := p / (p - 1)
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp1 := sub_pos.mpr hp
  have hq : 1 < q := (lt_div_iff₀ hp1).2 (by linarith)
  have hpq : 1 / p + 1 / q = 1 := by dsimp [q]; field_simp; ring
  have hqexp : (p - 1) * q = p := by dsimp [q]; field_simp
  have hS : 0 ≤ S := add_nonneg hA hB
  have hmS : S ∈ groupCStar n := (groupCStar n).add_mem hmA hmB
  let V := operatorRpow S (p - 1)
  have hV : 0 ≤ V := operatorRpow_nonneg hS
  have hmV : V ∈ groupCStar n := operatorRpow_mem_groupCStar hmS _
  have hpow : operatorRpow S p = S * V := by
    conv_lhs => rw [show p = 1 + (p - 1) by ring, operatorRpow_add hS zero_le_one hp1.le,
      operatorRpow_one hS]
  let μ := traceRe (operatorRpow S p)
  have hμ : 0 ≤ μ := traceRe_nonneg (operatorRpow_nonneg hS)
  have hmoment : μ ≤ (operatorLpNorm p A + operatorLpNorm p B) * μ ^ (1 / q) := by
    have ha := traceRe_positive_pair_holder hA hV hmA hmV hp hq hpq
    have hb := traceRe_positive_pair_holder hB hV hmB hmV hp hq hpq
    have hvq : operatorRpow V q = operatorRpow S p := by
      change operatorRpow (operatorRpow S (p - 1)) q = _
      rw [operatorRpow_comp hS hp1.le (by linarith), hqexp]
    rw [hvq, ← operatorLpNorm_of_nonneg_eq_trace_rpow hp0.le hA] at ha
    rw [hvq, ← operatorLpNorm_of_nonneg_eq_trace_rpow hp0.le hB] at hb
    have hμ' : μ = traceRe (A * V) + traceRe (B * V) := by
      dsimp only [μ]
      rw [hpow]
      change traceRe ((A + B) * V) = _
      rw [add_mul, traceRe_add]
    calc
      μ = traceRe (A * V) + traceRe (B * V) := hμ'
      _ ≤ (operatorLpNorm p A + operatorLpNorm p B) * μ ^ (1 / q) := by
        rw [add_mul]
        exact add_le_add ha hb
  change operatorLpNorm p S ≤ _
  rw [operatorLpNorm_of_nonneg_eq_trace_rpow hp0.le hS]
  change μ ^ (1 / p) ≤ _
  by_cases hzero : μ = 0
  · rw [hzero, Real.zero_rpow (by positivity : 1 / p ≠ 0)]
    exact add_nonneg (tracialNorm_nonneg _ _) (tracialNorm_nonneg _ _)
  have hμpos : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hzero)
  have hμprod : μ ^ (1 / p) * μ ^ (1 / q) = μ := by
    rw [← Real.rpow_add hμpos, hpq, Real.rpow_one]
  have hcomparison : μ ^ (1 / p) * μ ^ (1 / q) ≤
      (operatorLpNorm p A + operatorLpNorm p B) * μ ^ (1 / q) := by
    rwa [hμprod]
  exact le_of_mul_le_mul_right hcomparison (Real.rpow_pos_of_pos hμpos _)

private theorem tracialNorm_add {n : ℕ} {A B : Operator n}
    (hmA : A ∈ groupCStar n) (hmB : B ∈ groupCStar n) {p : ℝ} (hp : 1 < p) :
    operatorLpNorm p (A + B) ≤ operatorLpNorm p A + operatorLpNorm p B := by
  let L := absoluteValueOperator (star A) + absoluteValueOperator (star B)
  let R := absoluteValueOperator A + absoluteValueOperator B
  have habs (U : Operator n) : 0 ≤ absoluteValueOperator U :=
    operatorRpow_nonneg (star_mul_self_nonneg U)
  have hmabs {U : Operator n} (hU : U ∈ groupCStar n) :
      absoluteValueOperator U ∈ groupCStar n := by
    have hUs : star U ∈ groupCStar n := star_mem hU
    exact operatorRpow_mem_groupCStar ((groupCStar n).mul_mem hUs hU) _
  have hmAs : star A ∈ groupCStar n := star_mem hmA
  have hmBs : star B ∈ groupCStar n := star_mem hmB
  have hL : 0 ≤ L := add_nonneg (habs _) (habs _)
  have hR : 0 ≤ R := add_nonneg (habs _) (habs _)
  have hmL : L ∈ groupCStar n := (groupCStar n).add_mem (hmabs hmAs) (hmabs hmBs)
  have hmR : R ∈ groupCStar n := (groupCStar n).add_mem (hmabs hmA) (hmabs hmB)
  have hblock : HermitianBlockNonneg L (A + B) R := by
    intro v w
    have ha := absolute_value_block_nonneg A v w
    have hb := absolute_value_block_nonneg B v w
    change 0 ≤ (inner ℂ v (L v)).re + 2 * (inner ℂ v ((A + B) w)).re + (inner ℂ w (R w)).re
    simp only [L, R, add_apply, inner_add_right, Complex.add_re]
    linarith only [ha, hb]
  have hp0 := (zero_lt_one.trans hp).le
  have hbound := block_power_trace_le hL hR hmL ((groupCStar n).add_mem hmA hmB) hmR hblock hp
  rw [← tracialNorm_sq p, ← operatorLpNorm_of_nonneg_eq_trace_rpow hp0 hL,
    ← operatorLpNorm_of_nonneg_eq_trace_rpow hp0 hR] at hbound
  have ha (U : Operator n) : operatorLpNorm p (absoluteValueOperator U) = operatorLpNorm p U :=
    operatorLpNorm_absoluteValue_eq hp0 U
  have hleft : operatorLpNorm p L ≤ operatorLpNorm p A + operatorLpNorm p B := by
    have h := tracialNorm_add_positive (habs (star A)) (habs (star B))
      (hmabs hmAs) (hmabs hmBs) hp
    rw [ha, ha, operatorLpNorm_star_eq hp0 hmA, operatorLpNorm_star_eq hp0 hmB] at h
    exact h
  have hright : operatorLpNorm p R ≤ operatorLpNorm p A + operatorLpNorm p B := by
    have h := tracialNorm_add_positive (habs A) (habs B) (hmabs hmA) (hmabs hmB) hp
    rw [ha, ha] at h
    exact h
  apply (sq_le_sq₀ (tracialNorm_nonneg _ _)
    (add_nonneg (tracialNorm_nonneg _ _) (tracialNorm_nonneg _ _))).mp
  simpa only [pow_two] using hbound.trans
    (mul_le_mul hleft hright (tracialNorm_nonneg _ _)
      (add_nonneg (tracialNorm_nonneg _ _) (tracialNorm_nonneg _ _)))

private theorem tracialNorm_smul {n : ℕ} {p : ℝ} (hp : 0 < p)
    (c : ℂ) (A : Operator n) : operatorLpNorm p (c • A) = ‖c‖ * operatorLpNorm p A := by
  have hscalar : star c * c = Complex.ofReal (‖c‖ ^ 2) := by
    rw [Complex.ofReal_pow]
    exact Complex.conj_mul' c
  have hstar : star (c • A) = star c • star A := star_smul _ _
  have hprod : star (c • A) * (c • A) =
      Complex.ofReal (‖c‖ ^ 2) • (star A * A) := by
    rw [hstar, smul_mul_smul_comm, hscalar]
  change traceRe (operatorRpow (star (c • A) * (c • A)) (p / 2)) ^ (1 / p) =
    ‖c‖ * traceRe (operatorRpow (star A * A) (p / 2)) ^ (1 / p)
  rw [hprod, operatorRpow_smul (star_mul_self_nonneg A) (sq_nonneg _) (by positivity),
    traceRe_ofReal_smul, Real.mul_rpow (Real.rpow_nonneg (sq_nonneg ‖c‖) _)
      (traceRe_nonneg (operatorRpow_nonneg (star_mul_self_nonneg A)))]
  have hnorm : ((‖c‖ ^ 2) ^ (p / 2)) ^ (1 / p) = ‖c‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (norm_nonneg _)]
    rw [show (↑(2 : ℕ) * (p / 2)) * (1 / p) = 1 by push_cast; field_simp, Real.rpow_one]
  rw [hnorm]

private theorem tracialNorm_zero {n : ℕ} {p : ℝ} (hp : 0 < p) :
    operatorLpNorm p (0 : Operator n) = 0 := by
  unfold operatorLpNorm
  rw [mul_zero, cfc_apply_zero]
  simp [Real.zero_rpow (show p / 2 ≠ 0 by positivity),
    traceRe, Real.zero_rpow (inv_ne_zero hp.ne')]

private theorem tracialPower_faithful {n : ℕ} {S : Operator n} (hS : 0 ≤ S)
    {r : ℝ} (hr : 0 < r) (h : traceRe (operatorRpow S r) = 0) :
    traceRe S = 0 := by
  let _ : Nontrivial (Hilbert n) := by
    refine ⟨⟨lp.single 2 1 1, 0, ?_⟩⟩
    intro hh
    have := congrArg (fun v : Hilbert n ↦ v 1) hh
    simp at this
  have hSn : IsStarNormal S :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hS).isSelfAdjoint.isStarNormal
  have hb (ε : ℝ) (hε : 0 < ε) : traceRe S ≤ ε := by
    let c := ‖S‖ / ε ^ r
    have hc : 0 ≤ c := div_nonneg (norm_nonneg _) (Real.rpow_nonneg hε.le _)
    let f := fun z : ℂ ↦ Complex.ofReal (z.re ^ r)
    let g := fun z : ℂ ↦ (ε : ℂ) + (c : ℂ) * f z
    have hf : Continuous f := continuous_operatorRpowSymbol hr.le
    have hg : Continuous g := continuous_const.add (continuous_const.mul hf)
    have hle (z : ℂ) (hz : z ∈ spectrum ℂ S) : z ≤ g z := by
      obtain ⟨x, hx, rfl⟩ := exists_ofReal_of_spectrum_nonneg hS hz
      have hxS : x ≤ ‖S‖ := by
        simpa [Complex.norm_real, Real.norm_of_nonneg hx] using spectrum.norm_le_norm_of_mem hz
      unfold g f
      simp only [Complex.ofReal_re, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.real_le_real]
      by_cases he : x ≤ ε
      · exact he.trans (le_add_of_nonneg_right (mul_nonneg hc (Real.rpow_nonneg hx _)))
      · have hh := Real.rpow_le_rpow hε.le (le_of_not_ge he) hr.le
        have hεp := Real.rpow_pos_of_pos hε r
        have hbound : ‖S‖ ≤ c * x ^ r := by
          calc
            ‖S‖ = c * ε ^ r := (div_mul_cancel₀ _ hεp.ne').symm
            _ ≤ c * x ^ r := mul_le_mul_of_nonneg_left hh hc
        exact hxS.trans (hbound.trans (le_add_of_nonneg_left hε.le))
    have hop := cfc_mono (a := S) (f := id) hle continuous_id.continuousOn hg.continuousOn
    have hgCfc : cfc g S = (ε : ℂ) • (1 : Operator n) + (c : ℂ) • operatorRpow S r := by
      unfold g
      rw [cfc_const_add (ε : ℂ) (fun z : ℂ ↦ (c : ℂ) * f z) S
        (continuous_const.mul hf).continuousOn hSn,
        cfc_const_mul (c : ℂ) f S hf.continuousOn, Algebra.algebraMap_eq_smul_one]
      rfl
    rw [cfc_id ℂ S hSn, hgCfc] at hop
    have htrace := traceRe_mono hop
    simpa only [traceRe_add, traceRe_ofReal_smul, traceRe_one, h, mul_zero, mul_one, add_zero]
      using htrace
  refine le_antisymm ?_ (traceRe_nonneg hS)
  by_contra! hh
  linarith only [hh, hb (traceRe S / 2) (half_pos hh)]

private theorem tracialNorm_separates {n : ℕ} {p : ℝ} (hp : 0 < p) (x : GroupAlgebra n)
    (hx : lpNorm p x = 0) : x = 0 := by
  let T := regularImage x
  let S := star T * T
  have hS : 0 ≤ S := star_mul_self_nonneg T
  have h0 : traceRe (operatorRpow S (p / 2)) = 0 := by
    have hpos := traceRe_nonneg (operatorRpow_nonneg (r := p / 2) hS)
    by_contra hh
    have h := Real.rpow_pos_of_pos (lt_of_le_of_ne hpos (Ne.symm hh)) (1 / p)
    change traceRe (operatorRpow S (p / 2)) ^ (1 / p) = 0 at hx
    exact h.ne' hx
  have hτ := tracialPower_faithful hS (by positivity) h0
  change traceRe (star T * T) = 0 at hτ
  rw [traceRe_star_mul_self] at hτ
  have hδ : T (lp.single 2 1 1) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hτ)
  apply MonoidAlgebra.coeff_injective
  ext g
  have hg := congrArg (fun v : Hilbert n ↦ v g) hδ
  simpa only [T, regularImage_delta, lp.coeFn_zero, Pi.zero_apply,
    MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hg

/-- The trace formula defines a norm on Fourier polynomials for every finite exponent
strictly greater than one. -/
noncomputable def fourierLpNorm (n : ℕ) (p : ℝ) (hp : 1 < p) : FourierLpNorm n p where
  coreNorm :=
    { toFun := lpNorm p
      map_zero' := by
        simpa only [lpNorm_eq_operatorLpNorm, regularImage_zero] using
          (tracialNorm_zero (n := n) (zero_lt_one.trans hp))
      add_le' := fun x y ↦ by
        simp only [lpNorm_eq_operatorLpNorm, regularImage_add]
        exact tracialNorm_add (regularImage_mem_groupCStar x) (regularImage_mem_groupCStar y) hp
      neg' := fun x ↦ by
        have h : regularImage (-x) = (-1 : ℂ) • regularImage x := by
          rw [← regularHom_apply, map_neg, regularHom_apply]
          exact (neg_one_smul ℂ (regularImage x)).symm
        simp only [lpNorm_eq_operatorLpNorm, h, tracialNorm_smul (zero_lt_one.trans hp),
          norm_neg, norm_one, one_mul]
      eq_zero_of_map_eq_zero' := tracialNorm_separates (zero_lt_one.trans hp) }
  norm_eq := fun _ ↦ rfl
  norm_smul_le := fun c x ↦ by
    change lpNorm p (c • x) ≤ ‖c‖ * lpNorm p x
    simp only [lpNorm_eq_operatorLpNorm, regularImage_smul, tracialNorm_smul (zero_lt_one.trans hp), le_rfl]

end FreeGroupHypercontractivity
