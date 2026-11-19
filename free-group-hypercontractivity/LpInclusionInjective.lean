module

public import «free-group-hypercontractivity».LpPositivePart
public import «free-group-hypercontractivity».LpPositiveTests
import all «free-group-hypercontractivity».Model

public section

namespace FreeGroupHypercontractivity

open scoped ComplexOrder InnerProductSpace

private theorem traceRe_star_invariant {n : ℕ} (A : Operator n) :
    traceRe (star A) = traceRe A := by
  rw [traceRe_as_inner, traceRe_as_inner, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  simpa only [RCLike.re_to_complex] using
    (inner_re_symm (𝕜 := ℂ) (A (lp.single 2 1 1)) (lp.single 2 1 1))

private theorem realPart_mem_groupCStar {n : ℕ} {A : Operator n}
    (hmA : A ∈ groupCStar n) : (realPart A : Operator n) ∈ groupCStar n := by
  rw [realPart_apply_coe, ← Complex.coe_smul]
  have hmAs : star A ∈ groupCStar n := star_mem hmA
  exact (groupCStar n).smul_mem ((groupCStar n).add_mem hmA hmAs) _

private theorem realPart_neg_I_smul_eq_imaginaryPart {n : ℕ} (A : Operator n) :
    realPart ((-Complex.I) • A) = imaginaryPart A := calc
  _ = realPart (-(Complex.I • A)) :=
    congrArg (fun T : Operator n ↦ realPart T) (neg_smul Complex.I A)
  _ = -realPart (Complex.I • A) := map_neg realPart _
  _ = -(-imaginaryPart A) := congrArg Neg.neg (realPart_I_smul A)
  _ = _ := neg_neg _

private theorem traceRe_realPart_mul {n : ℕ} {A B : Operator n} (hmA : A ∈ groupCStar n)
    (hmB : B ∈ groupCStar n) (hB : IsSelfAdjoint B) :
    traceRe ((realPart A : Operator n) * B) = traceRe (A * B) := by
  have hstar : traceRe (star A * B) = traceRe (A * B) := by
    rw [← traceRe_star_invariant (star A * B), star_mul, star_star, hB.star_eq,
      traceRe_mul_comm_closure (mem_groupCStar_iff.mp hmB) (mem_groupCStar_iff.mp hmA)]
  rw [realPart_apply_coe, ← Complex.coe_smul, smul_mul_assoc, traceRe_ofReal_smul,
    add_mul, traceRe_add, hstar]
  ring

private theorem signedPositivePart_norm_le_of_tests {n : ℕ} {q d : ℝ} (hq : 1 < q)
    (hd : 0 ≤ d) {A : Operator n} (hmA : A ∈ groupCStar n) (hA : IsSelfAdjoint A)
    (hTest : ∀ {B : Operator n}, B ∈ groupCStar n → 0 ≤ B →
      |traceRe (A * B)| ≤ d * operatorLpNorm (lpConjugate q) B)
    {s : ℝ} (hs : s = 1 ∨ s = -1) :
    operatorLpNorm q (signedPositivePart s A) ≤ d := by
  let U := signedPositivePart s A
  let B := operatorRpow U (q - 1)
  have hU : 0 ≤ U := signedPositivePart_nonneg s A
  have hmU : U ∈ groupCStar n := signedPositivePart_mem hmA s
  have hB : 0 ≤ B := operatorRpow_nonneg hU
  have hmB : B ∈ groupCStar n := operatorRpow_mem_groupCStar hmU _
  let μ := traceRe (operatorRpow U q)
  have hμ : 0 ≤ μ := traceRe_nonneg (operatorRpow_nonneg hU)
  have hpow : operatorRpow B (lpConjugate q) = operatorRpow U q := by
    change operatorRpow (operatorRpow U (q - 1)) (lpConjugate q) = operatorRpow U q
    rw [operatorRpow_comp hU (by linarith) (le_trans zero_le_one (one_lt_lpConjugate hq).le),
      lpConjugate_mul_sub_one hq]
  have hBnorm : operatorLpNorm (lpConjugate q) B = μ ^ (1 / lpConjugate q) := by
    rw [operatorLpNorm_of_nonneg_eq_trace_rpow (le_trans zero_le_one (one_lt_lpConjugate hq).le)
      hB, hpow]
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hmoment := hTest hmB hB
  change |traceRe (A * operatorRpow (signedPositivePart s A) (q - 1))| ≤ _ at hmoment
  rw [traceRe_signedPositivePart_test hA hs (sub_pos.mpr hq),
    show q - 1 + 1 = q by ring, abs_mul, hsabs, one_mul, hBnorm] at hmoment
  change |μ| ≤ d * μ ^ (1 / lpConjugate q) at hmoment
  rw [abs_of_nonneg hμ] at hmoment
  change operatorLpNorm q U ≤ d
  rw [operatorLpNorm_of_nonneg_eq_trace_rpow (by linarith) hU]
  change μ ^ (1 / q) ≤ d
  by_cases hzero : μ = 0
  · rw [hzero, Real.zero_rpow (by positivity : 1 / q ≠ 0)]
    exact hd
  have hμpos := lt_of_le_of_ne hμ (Ne.symm hzero)
  have hprod : μ ^ (1 / q) * μ ^ (1 / lpConjugate q) = μ := by
    rw [← Real.rpow_add hμpos, lpConjugate_reciprocals hq, Real.rpow_one]
  have hcomparison : μ ^ (1 / q) * μ ^ (1 / lpConjugate q) ≤
      d * μ ^ (1 / lpConjugate q) := by rwa [hprod]
  exact le_of_mul_le_mul_right hcomparison (Real.rpow_pos_of_pos hμpos _)

private theorem selfAdjoint_norm_le_two_of_tests {n : ℕ} {q d : ℝ} (hq : 1 < q)
    (hd : 0 ≤ d) {A : Operator n} (hmA : A ∈ groupCStar n) (hA : IsSelfAdjoint A)
    (hTest : ∀ {B : Operator n}, B ∈ groupCStar n → 0 ≤ B →
      |traceRe (A * B)| ≤ d * operatorLpNorm (lpConjugate q) B) :
    operatorLpNorm q A ≤ 2 * d := by
  let U := signedPositivePart 1 A
  let V := signedPositivePart (-1) A
  have hU := signedPositivePart_norm_le_of_tests hq hd hmA hA hTest (s := 1) (Or.inl rfl)
  have hV := signedPositivePart_norm_le_of_tests hq hd hmA hA hTest (s := -1) (Or.inr rfl)
  have hmU : U ∈ groupCStar n := signedPositivePart_mem hmA 1
  have hmV : V ∈ groupCStar n := signedPositivePart_mem hmA (-1)
  have hdec : U + (-1 : ℂ) • V = A := calc
    _ = U + -V := congrArg (U + ·) (neg_one_smul ℂ V)
    _ = U - V := (sub_eq_add_neg U V).symm
    _ = A := signedPositivePart_sub hA
  have he := tracialNorm_add hmU ((groupCStar n).smul_mem hmV (-1 : ℂ)) hq
  rw [hdec, tracialNorm_smul (zero_lt_one.trans hq), norm_neg, norm_one, one_mul] at he
  exact he.trans ((add_le_add hU hV).trans_eq (two_mul d).symm)

private theorem operatorLpNorm_le_four_of_tests {n : ℕ} {q d : ℝ} (hq : 1 < q)
    (hd : 0 ≤ d) {A : Operator n} (hmA : A ∈ groupCStar n)
    (hTest : ∀ {B : Operator n}, B ∈ groupCStar n → 0 ≤ B →
      ∀ c : ℂ, ‖c‖ = 1 → |traceRe ((c • A) * B)| ≤ d * operatorLpNorm (lpConjugate q) B) :
    operatorLpNorm q A ≤ 4 * d := by
  have hmRe := realPart_mem_groupCStar hmA
  have hmAI : (-Complex.I) • A ∈ groupCStar n := (groupCStar n).smul_mem hmA _
  have hmIm : (imaginaryPart A : Operator n) ∈ groupCStar n := by
    rw [← realPart_neg_I_smul_eq_imaginaryPart A]
    exact realPart_mem_groupCStar hmAI
  have hRe := selfAdjoint_norm_le_two_of_tests hq hd hmRe (realPart A).property (by
    intro B hmB hB
    rw [traceRe_realPart_mul hmA hmB (ContinuousLinearMap.nonneg_iff_isPositive.mp hB).isSelfAdjoint]
    simpa only [one_smul] using hTest hmB hB 1 norm_one)
  have hIm := selfAdjoint_norm_le_two_of_tests hq hd hmIm (imaginaryPart A).property (by
    intro B hmB hB
    rw [← realPart_neg_I_smul_eq_imaginaryPart A,
      traceRe_realPart_mul hmAI hmB (ContinuousLinearMap.nonneg_iff_isPositive.mp hB).isSelfAdjoint]
    exact hTest hmB hB (-Complex.I) (by simp))
  have he := tracialNorm_add hmRe ((groupCStar n).smul_mem hmIm Complex.I) hq
  rw [realPart_add_I_smul_imaginaryPart, tracialNorm_smul (zero_lt_one.trans hq), Complex.norm_I,
    one_mul] at he
  exact he.trans ((add_le_add hRe hIm).trans_eq (by ring))

private theorem eq_zero_of_lpInclusion_eq_zero {n : ℕ} {p q : ℝ}
    (hp : 1 < p) (hpq : p ≤ q) {x : Lp n q} (hx : lpInclusion n p q x = 0) : x = 0 := by
  have hq := hp.trans_le hpq
  have hnorm (y : GroupAlgebra n) : ‖lpEmbed n q y‖ ≤ 4 * ‖lpEmbed n q y - x‖ := by
    rw [norm_lpEmbed hq y, lpNorm_eq_operatorLpNorm]
    refine operatorLpNorm_le_four_of_tests hq (norm_nonneg _) (regularImage_mem_groupCStar y) ?_
    intro B hmB hB c hc
    have hvanish : positiveTraceTest hq c hmB hB x = 0 := by
      rw [← positiveTraceTest_lpInclusion hp hpq, hx, map_zero]
    have ht := positiveTraceTest_abs_le hq c hmB hB (lpEmbed n q y - x)
    rw [map_sub, hvanish, sub_zero, positiveTraceTest_lpEmbed, hc, one_mul, mul_comm] at ht
    exact ht
  by_contra hne
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hne
  let ε := ‖x‖ / 6
  have hε : 0 < ε := by positivity
  have hcl : x ∈ closure (Set.range (fun y : LpCore n q ↦ (y : Lp n q))) :=
    UniformSpace.Completion.denseRange_coe x
  obtain ⟨_, ⟨y, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp hcl ε hε
  change dist x (lpEmbed n q y) < ε at hdist
  rw [dist_comm, dist_eq_norm] at hdist
  have htriangle : ‖x‖ ≤ ‖lpEmbed n q y - x‖ + ‖lpEmbed n q y‖ := by
    have he := norm_add_le (x - lpEmbed n q y) (lpEmbed n q y)
    rwa [sub_add_cancel, norm_sub_rev] at he
  have hbound := hnorm y
  dsimp only [ε] at hdist
  linarith

/-- The canonical inclusion of the tracial q-completion into the
p-completion has trivial kernel. -/
theorem lpInclusion_injective {n : ℕ} {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) :
    Function.Injective (lpInclusion n p q) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply eq_zero_of_lpInclusion_eq_zero hp hpq
  have h := lpInclusion_add hp hpq (x - y) y
  rw [sub_add_cancel, hxy] at h
  exact add_right_cancel (by simpa only [zero_add] using h.symm)

end FreeGroupHypercontractivity
