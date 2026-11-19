module

import all «free-group-hypercontractivity».Model
public import «free-group-hypercontractivity».LpNorm
public import «free-group-hypercontractivity».PoissonExtension

public section

namespace FreeGroupHypercontractivity

open UniformSpace

theorem norm_lpCore {n : ℕ} {p : ℝ} (hp : 1 < p) (x : LpCore n p) :
    ‖x‖ = lpNorm p x := by
  classical
  let N := fourierLpNorm n p hp
  have h : ∃ f : AddGroupSeminorm (GroupAlgebra n), ∀ a, f a = lpNorm p a :=
    ⟨N.coreNorm.toAddGroupSeminorm, N.norm_eq⟩
  change coreLpSeminorm n p x = _
  unfold coreLpSeminorm
  rw [dite_eq_left h]
  exact Classical.choose_spec h x

/-- Embed a Fourier polynomial into the canonical tracial completion. -/
@[expose] noncomputable def lpEmbed (n : ℕ) (p : ℝ) (x : GroupAlgebra n) : Lp n p :=
  ((show LpCore n p from x) : Lp n p)

theorem norm_lpEmbed {n : ℕ} {p : ℝ} (hp : 1 < p) (x : GroupAlgebra n) :
    ‖lpEmbed n p x‖ = lpNorm p x :=
  (Completion.norm_coe (show LpCore n p from x)).trans (norm_lpCore hp x)

theorem norm_lpCore_eq_operatorLpNorm {n : ℕ} {p : ℝ} (hp : 1 < p) (x : LpCore n p) :
    ‖x‖ = operatorLpNorm p (regularImage x) :=
  (norm_lpCore hp x).trans (lpNorm_eq_operatorLpNorm p x)

/-- Monotonicity of tracial norms uses Hölder against the identity. -/
theorem lpNorm_mono {n : ℕ} {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (x : GroupAlgebra n) :
    lpNorm p x ≤ lpNorm q x := by
  rcases hpq.eq_or_lt with rfl | hpq
  · exact le_rfl
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq0 : 0 < q := hp0.trans hpq
  let A := regularImage x
  let S := star A * A
  let U := operatorRpow S (p / 2)
  let r := q / p
  let r' := r / (r - 1)
  have hr : 1 < r := (lt_div_iff₀ hp0).mpr (by simpa)
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hrm : 0 < r - 1 := sub_pos.mpr hr
  have hr' : 1 < r' := (lt_div_iff₀ hrm).mpr (by linarith)
  have hconj : 1 / r + 1 / r' = 1 := by
    dsimp only [r']
    field_simp [hr0.ne', hrm.ne']
    ring
  have hS : 0 ≤ S := star_mul_self_nonneg A
  have hA : A ∈ groupCStar n := regularImage_mem_groupCStar x
  have hmS : S ∈ groupCStar n := mul_mem (star_mem hA) hA
  have hmU : U ∈ groupCStar n := operatorRpow_mem_groupCStar hmS _
  have hU : 0 ≤ U := operatorRpow_nonneg hS
  have h := traceRe_positive_pair_holder hU (show 0 ≤ (1 : Operator n) from zero_le_one)
    hmU (one_mem (groupCStar n)) hr hr' hconj
  have hUq : operatorRpow U r = operatorRpow S (q / 2) := by
    dsimp only [U]
    rw [operatorRpow_comp hS (by positivity) (zero_le_one.trans hr.le)]
    congr 1
    dsimp only [r]
    field_simp [hp0.ne']
  have hone : operatorRpow (1 : Operator n) r' = 1 := by
    rw [operatorRpow, cfc_apply_one]
    simp
  rw [mul_one, hUq, hone, traceRe_one, Real.one_rpow, mul_one] at h
  have hnU : 0 ≤ traceRe U := traceRe_nonneg hU
  have hnS : 0 ≤ traceRe (operatorRpow S (q / 2)) :=
    traceRe_nonneg (operatorRpow_nonneg hS)
  have hpow := Real.rpow_le_rpow hnU h (show 0 ≤ 1 / p by positivity)
  rw [← Real.rpow_mul hnS] at hpow
  have hexp : (1 / r) * (1 / p) = 1 / q := by
    dsimp only [r]
    field_simp [hp0.ne', hq0.ne']
  rw [hexp] at hpow
  exact hpow

private noncomputable def lpCoreInclusion (n : ℕ) (p q : ℝ) : LpCore n q →+ LpCore n p :=
  AddMonoidHom.id (GroupAlgebra n)

theorem lpInclusion_uniformContinuous_core {n : ℕ} {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) :
    UniformContinuous (α := LpCore n q) (β := LpCore n p) id := by
  change UniformContinuous (lpCoreInclusion n p q)
  apply AddMonoidHomClass.uniformContinuous_of_bound _ 1
  intro x
  rw [one_mul, norm_lpCore hp, norm_lpCore (hp.trans_le hpq)]
  exact lpNorm_mono hp hpq x

theorem lpInclusion_continuous (n : ℕ) (p q : ℝ) : Continuous (lpInclusion n p q) :=
  Completion.continuous_map

theorem lpInclusion_coe {n : ℕ} {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q)
    (x : GroupAlgebra n) :
    lpInclusion n p q (lpEmbed n q x) = lpEmbed n p x :=
  Completion.map_coe (α := LpCore n q) (β := LpCore n p)
    (lpInclusion_uniformContinuous_core (n := n) hp hpq) (show LpCore n q from x)

theorem lpInclusion_add {n : ℕ} {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (x y : Lp n q) :
    lpInclusion n p q (x + y) = lpInclusion n p q x + lpInclusion n p q y := by
  let f := lpCoreInclusion n p q
  have h : Continuous (f : LpCore n q → LpCore n p) :=
    (lpInclusion_uniformContinuous_core (n := n) hp hpq).continuous
  exact map_add (f.completion h) x y

@[simp] theorem lpInclusion_self (n : ℕ) (p : ℝ) (x : Lp n p) :
    lpInclusion n p p x = x :=
  congrFun Completion.map_id x

theorem extendedLpNorm_le_of_inclusion {n : ℕ} {p q : ℝ} {x : Lp n p} {y : Lp n q}
    (hy : lpInclusion n p q y = x) : extendedLpNorm q x ≤ ‖y‖ₑ :=
  iInf_le (fun z : {y : Lp n q // lpInclusion n p q y = x} ↦ ‖z.val‖ₑ) ⟨y, hy⟩

theorem extendedLpNorm_of_inclusion {n : ℕ} {p q : ℝ}
    (hinj : Function.Injective (lpInclusion n p q)) (y : Lp n q) :
    extendedLpNorm q (lpInclusion n p q y) = ‖y‖ₑ := by
  refine le_antisymm (extendedLpNorm_le_of_inclusion rfl) (le_iInf fun z ↦ ?_)
  rw [hinj z.property]

@[simp] theorem extendedLpNorm_self {n : ℕ} {p : ℝ} (x : Lp n p) :
    extendedLpNorm p x = ‖x‖ₑ := by
  have hinj : Function.Injective (lpInclusion n p p) := by
    intro y z h
    simpa only [lpInclusion_self] using h
  simpa only [lpInclusion_self] using extendedLpNorm_of_inclusion hinj x

private noncomputable def poissonCore (n : ℕ) (p q t : ℝ) : LpCore n p →+ LpCore n q :=
  (poissonLinear n t).toAddMonoidHom

private theorem poissonCore_uniformContinuous {n : ℕ} {p q t : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hc : ∀ x : GroupAlgebra n, lpNorm q (poisson t x) ≤ lpNorm p x) :
    UniformContinuous (α := LpCore n p) (β := LpCore n q) (poisson t) := by
  have h : UniformContinuous (poissonCore n p q t) := by
    apply AddMonoidHomClass.uniformContinuous_of_bound _ 1
    intro x
    rw [one_mul, norm_lpCore hq, norm_lpCore hp]
    exact (congrArg (lpNorm q) (poissonLinear_apply n t x)).le.trans (hc x)
  have hfun : (poisson t : LpCore n p → LpCore n q) = (poissonCore n p q t) := by
    funext x
    exact (poissonLinear_apply n t x).symm
  rwa [hfun]

theorem poissonLp_continuous {n : ℕ} {p : ℝ} (t : ℝ) :
    Continuous (poissonLp (n := n) (p := p) t) :=
  Completion.continuous_map

theorem poissonLp_coe {n : ℕ} {p t : ℝ} (hp : 1 < p)
    (hc : ∀ x : GroupAlgebra n, lpNorm p (poisson t x) ≤ lpNorm p x) (x : GroupAlgebra n) :
    poissonLp t (lpEmbed n p x) = lpEmbed n p (poisson t x) :=
  Completion.map_coe (poissonCore_uniformContinuous hp hp hc) (show LpCore n p from x)

/-- Extend the Fourier multiplier directly into the q-completion. Its values on
the Fourier core agree with the multiplier whenever the core inequality holds. -/
@[expose] noncomputable def poissonLpTo (n : ℕ) (p q t : ℝ) : Lp n p → Lp n q :=
  Completion.map (fun x : LpCore n p ↦ (poisson t x : LpCore n q))

theorem poissonLpTo_coe {n : ℕ} {p q t : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hc : ∀ x : GroupAlgebra n, lpNorm q (poisson t x) ≤ lpNorm p x) (x : GroupAlgebra n) :
    poissonLpTo n p q t (lpEmbed n p x) = lpEmbed n q (poisson t x) :=
  Completion.map_coe (poissonCore_uniformContinuous hp hq hc) (show LpCore n p from x)

theorem poissonLpTo_norm_le {n : ℕ} {p q t : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hc : ∀ x : GroupAlgebra n, lpNorm q (poisson t x) ≤ lpNorm p x) (x : Lp n p) :
    ‖poissonLpTo n p q t x‖ ≤ ‖x‖ := by
  refine Completion.induction_on x
    (isClosed_le (continuous_norm.comp Completion.continuous_map) continuous_norm) ?_
  intro x
  change ‖poissonLpTo n p q t (lpEmbed n p x)‖ ≤ ‖lpEmbed n p x‖
  exact (congrArg norm (poissonLpTo_coe hp hq hc x)).le.trans
    ((norm_lpEmbed hq (poisson t x)).le.trans ((hc x).trans_eq (norm_lpEmbed hp x).symm))

theorem lpInclusion_poissonLpTo {n : ℕ} {p q t : ℝ} (hp : 1 < p) (hpq : p ≤ q)
    (hc : ∀ x : GroupAlgebra n, lpNorm q (poisson t x) ≤ lpNorm p x) (x : Lp n p) :
    lpInclusion n p q (poissonLpTo n p q t x) = poissonLp t x := by
  have hq : 1 < q := hp.trans_le hpq
  have hself (a : GroupAlgebra n) : lpNorm p (poisson t a) ≤ lpNorm p a :=
    (lpNorm_mono hp hpq (poisson t a)).trans (hc a)
  apply Completion.ext' ((lpInclusion_continuous n p q).comp Completion.continuous_map)
    (poissonLp_continuous t) _ x
  intro a
  change lpInclusion n p q (poissonLpTo n p q t (lpEmbed n p a)) =
    poissonLp t (lpEmbed n p a)
  exact (congrArg (lpInclusion n p q) (poissonLpTo_coe hp hq hc a)).trans
    ((lpInclusion_coe hp hpq (poisson t a)).trans (poissonLp_coe hp hself a).symm)

end FreeGroupHypercontractivity
