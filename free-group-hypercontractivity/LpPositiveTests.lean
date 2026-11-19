module

public import «free-group-hypercontractivity».AbsoluteValueBlock
public import «free-group-hypercontractivity».LpPointwise
public import Mathlib.Analysis.Normed.Group.HomCompletion
import all «free-group-hypercontractivity».Model

public section

namespace FreeGroupHypercontractivity

open scoped ComplexOrder

/-- Hölder's bound for the real trace pairing against a positive operator. -/
theorem abs_traceRe_mul_le_tracialNorm {n : ℕ} {A B : Operator n}
    (hmA : A ∈ groupCStar n) (hmB : B ∈ groupCStar n) (hB : 0 ≤ B)
    {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1) :
    |traceRe (A * B)| ≤ operatorLpNorm p A * operatorLpNorm q B := by
  let C := operatorRpow B (1 / 2)
  let L := absoluteValueOperator (star A)
  let R := absoluteValueOperator A
  have hmC : C ∈ groupCStar n := operatorRpow_mem_groupCStar hmB _
  have hC : 0 ≤ C := operatorRpow_nonneg hB
  have hCs : star C = C :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hC).isSelfAdjoint.star_eq
  have hCsq : C * C = B := by
    have h := (operatorRpow_add hB (r := 1 / 2) (s := 1 / 2) (by norm_num) (by norm_num)).symm
    rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, operatorRpow_one hB] at h
    exact h
  have hrotate (X : Operator n) (hmX : X ∈ groupCStar n) :
      traceRe (star C * X * C) = traceRe (X * B) := by
    rw [mul_assoc, traceRe_mul_comm_closure (mem_groupCStar_iff.mp (star_mem hmC))
      (mem_groupCStar_iff.mp ((groupCStar n).mul_mem hmX hmC)), mul_assoc, hCs, hCsq]
  have habs (X : Operator n) : 0 ≤ absoluteValueOperator X :=
    operatorRpow_nonneg (star_mul_self_nonneg X)
  have hmabs {X : Operator n} (hmX : X ∈ groupCStar n) :
      absoluteValueOperator X ∈ groupCStar n :=
    by
      have hmXs : star X ∈ groupCStar n := star_mem hmX
      exact operatorRpow_mem_groupCStar ((groupCStar n).mul_mem hmXs hmX) _
  have hmL : L ∈ groupCStar n := hmabs (star_mem hmA)
  have hmR : R ∈ groupCStar n := hmabs hmA
  have hL : 0 ≤ L := habs _
  have hR : 0 ≤ R := habs _
  have hp0 : 0 ≤ p := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hblock := block_trace_cauchy_schwarz (absolute_value_block_nonneg A) C C
  change traceRe (star C * A * C) ^ 2 ≤
    traceRe (star C * L * C) * traceRe (star C * R * C) at hblock
  rw [hrotate A hmA, hrotate L hmL, hrotate R hmR] at hblock
  have hleft := traceRe_positive_pair_holder hL hB hmL hmB hp hq hpq
  have hright := traceRe_positive_pair_holder hR hB hmR hmB hp hq hpq
  rw [← operatorLpNorm_of_nonneg_eq_trace_rpow hp0 hL,
    ← operatorLpNorm_of_nonneg_eq_trace_rpow hq0 hB] at hleft
  rw [← operatorLpNorm_of_nonneg_eq_trace_rpow hp0 hR,
    ← operatorLpNorm_of_nonneg_eq_trace_rpow hq0 hB] at hright
  have hLp : operatorLpNorm p L = operatorLpNorm p A := by
    change operatorLpNorm p (operatorRpow (star (star A) * star A) (1 / 2)) =
      operatorLpNorm p A
    rw [operatorLpNorm_absoluteValue_eq hp0, operatorLpNorm_star_eq hp0 hmA]
  have hRp : operatorLpNorm p R = operatorLpNorm p A :=
    operatorLpNorm_absoluteValue_eq hp0 A
  rw [hLp] at hleft
  rw [hRp] at hright
  have hright0 := traceRe_positive_pair_nonneg hR hB hmR hmB
  have hbound0 : 0 ≤ operatorLpNorm p A * operatorLpNorm q B :=
    (traceRe_positive_pair_nonneg hL hB hmL hmB).trans hleft
  apply abs_le_of_sq_le_sq _ hbound0
  exact hblock.trans ((mul_le_mul hleft hright hright0 hbound0).trans_eq (pow_two _).symm)


/-- The conjugate exponent of an exponent strictly greater than one. -/
@[expose]
noncomputable def lpConjugate (p : ℝ) : ℝ := p / (p - 1)

theorem one_lt_lpConjugate {p : ℝ} (hp : 1 < p) : 1 < lpConjugate p :=
  (lt_div_iff₀ (sub_pos.mpr hp)).2 (by linarith)

theorem lpConjugate_reciprocals {p : ℝ} (hp : 1 < p) :
    1 / p + 1 / lpConjugate p = 1 := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hp1 : p - 1 ≠ 0 := (sub_pos.mpr hp).ne'
  unfold lpConjugate
  field_simp
  ring

theorem lpConjugate_mul_sub_one {p : ℝ} (hp : 1 < p) :
    (p - 1) * lpConjugate p = p := by
  have hp1 : p - 1 ≠ 0 := (sub_pos.mpr hp).ne'
  unfold lpConjugate
  field_simp

private theorem positiveTraceTest_core_bound {n : ℕ} {p : ℝ} (hp : 1 < p)
    (c : ℂ) {B : Operator n} (hmB : B ∈ groupCStar n) (hB : 0 ≤ B) (x : LpCore n p) :
    |traceRe ((c • regularImage x) * B)| ≤
      (‖c‖ * operatorLpNorm (lpConjugate p) B) * ‖x‖ := by
  have hmA : c • regularImage x ∈ groupCStar n :=
    (groupCStar n).smul_mem (regularImage_mem_groupCStar x) c
  have h := abs_traceRe_mul_le_tracialNorm hmA hmB hB hp (one_lt_lpConjugate hp)
    (lpConjugate_reciprocals hp)
  calc
    _ ≤ operatorLpNorm p (c • regularImage x) * operatorLpNorm (lpConjugate p) B := h
    _ = _ := by
      rw [tracialNorm_smul (zero_lt_one.trans hp) c, ← norm_lpCore_eq_operatorLpNorm hp x]
      ring

private theorem traceRe_regularImage_smul_mul_add {n : ℕ} (c : ℂ) (B : Operator n)
    (x y : GroupAlgebra n) :
    traceRe ((c • regularImage (x + y)) * B) =
      traceRe ((c • regularImage x) * B) + traceRe ((c • regularImage y) * B) := by
  simp only [regularImage_add, smul_add, add_mul, traceRe_add]

private noncomputable def positiveTraceTestCore {n : ℕ} {p : ℝ} (hp : 1 < p)
    (c : ℂ) {B : Operator n} (hmB : B ∈ groupCStar n) (hB : 0 ≤ B) :
    NormedAddGroupHom (LpCore n p) ℝ where
  toFun x := traceRe ((c • regularImage x) * B)
  map_add' x y := traceRe_regularImage_smul_mul_add c B x y
  bound' := ⟨‖c‖ * operatorLpNorm (lpConjugate p) B, fun x ↦ by
    simpa only [Real.norm_eq_abs] using positiveTraceTest_core_bound hp c hmB hB x⟩

/-- Continuous real trace test on a tracial completion. The scalar parameter
allows the real and imaginary components to be tested using the same bound. -/
noncomputable def positiveTraceTest {n : ℕ} {p : ℝ} (hp : 1 < p)
    (c : ℂ) {B : Operator n} (hmB : B ∈ groupCStar n) (hB : 0 ≤ B) :
    NormedAddGroupHom (Lp n p) ℝ :=
  (positiveTraceTestCore hp c hmB hB).extension

@[simp] theorem positiveTraceTest_lpEmbed {n : ℕ} {p : ℝ} (hp : 1 < p)
    (c : ℂ) {B : Operator n} (hmB : B ∈ groupCStar n) (hB : 0 ≤ B) (y : GroupAlgebra n) :
    positiveTraceTest hp c hmB hB (lpEmbed n p y) = traceRe ((c • regularImage y) * B) :=
  (positiveTraceTestCore hp c hmB hB).extension_coe (show LpCore n p from y)

theorem positiveTraceTest_abs_le {n : ℕ} {p : ℝ} (hp : 1 < p)
    (c : ℂ) {B : Operator n} (hmB : B ∈ groupCStar n) (hB : 0 ≤ B) (x : Lp n p) :
    |positiveTraceTest hp c hmB hB x| ≤
      (‖c‖ * operatorLpNorm (lpConjugate p) B) * ‖x‖ := by
  rw [← Real.norm_eq_abs]
  refine UniformSpace.Completion.induction_on x
    (isClosed_le ((positiveTraceTest hp c hmB hB).continuous.norm)
      (continuous_const.mul continuous_norm)) ?_
  intro y
  have he := positiveTraceTest_lpEmbed hp c hmB hB (show GroupAlgebra n from y)
  calc
    ‖positiveTraceTest hp c hmB hB (y : Lp n p)‖ =
        |traceRe ((c • regularImage y) * B)| :=
      (congrArg norm he).trans (Real.norm_eq_abs _)
    _ ≤ (‖c‖ * operatorLpNorm (lpConjugate p) B) * ‖y‖ :=
      positiveTraceTest_core_bound hp c hmB hB y
    _ = (‖c‖ * operatorLpNorm (lpConjugate p) B) * ‖(y : Lp n p)‖ :=
      congrArg _ (UniformSpace.Completion.norm_coe y).symm

theorem positiveTraceTest_lpInclusion {n : ℕ} {p q : ℝ}
    (hp : 1 < p) (hpq : p ≤ q) (c : ℂ)
    {B : Operator n} (hmB : B ∈ groupCStar n) (hB : 0 ≤ B) (x : Lp n q) :
    positiveTraceTest hp c hmB hB (lpInclusion n p q x) =
      positiveTraceTest (hp.trans_le hpq) c hmB hB x := by
  apply congrFun (g := positiveTraceTest (hp.trans_le hpq) c hmB hB) _ x
  apply UniformSpace.Completion.ext
    ((positiveTraceTest hp c hmB hB).continuous.comp (lpInclusion_continuous n p q))
    (positiveTraceTest (hp.trans_le hpq) c hmB hB).continuous
  intro y
  let a : GroupAlgebra n := y
  exact (congrArg (positiveTraceTest hp c hmB hB) (lpInclusion_coe hp hpq a)).trans
    ((positiveTraceTest_lpEmbed hp c hmB hB a).trans
      (positiveTraceTest_lpEmbed (hp.trans_le hpq) c hmB hB a).symm)

end FreeGroupHypercontractivity
