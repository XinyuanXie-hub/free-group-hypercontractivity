module

meta import Lean.Elab.Command

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Sharp hypercontractivity for free group von Neumann algebras

Definitions for the independent solution of Xie and Zhang, arXiv:2606.03423v3.
-/

-- Comparator checks definition bodies by name, including generated private proofs.
-- Reproduce the names of the generated proofs when elaborating the independent model.
open Lean Elab Command in
elab "#with_challenge_auxiliary_names " declarations:command*
    "#end_challenge_auxiliary_names" : command => do
  let mainModule := (← getEnv).mainModule
  modifyEnv (·.setMainModule `Challenge)
  try
    for declaration in declarations do
      elabCommand declaration
  finally
    modifyEnv (·.setMainModule mainModule)

public section

namespace FreeGroupHypercontractivity

open scoped ENNReal

#with_challenge_auxiliary_names
/-! ## Fourier polynomials and the trace -/

abbrev Group (n : ℕ) := FreeGroup (Fin n)
abbrev GroupAlgebra (n : ℕ) := MonoidAlgebra ℂ (Group n)
noncomputable abbrev Hilbert (n : ℕ) := lp (fun _ : Group n ↦ ℂ) 2
noncomputable abbrev Operator (n : ℕ) := Hilbert n →L[ℂ] Hilbert n

/-- The left regular representation, acting by translation by the inverse on functions. -/
noncomputable def leftRegular {n : ℕ} (g : Group n) : Operator n :=
  let e : Group n ≃ Group n := Equiv.mulLeft g⁻¹
  let translate (v : Hilbert n) : Hilbert n :=
    ⟨fun h ↦ v (e h), memℓp_gen (e.summable_iff.mpr ((lp.memℓp v).summable (by norm_num)))⟩
  LinearMap.mkContinuous
    { toFun := translate
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
    1 (by
      intro v
      simp only [one_mul]
      change ‖translate v‖ ≤ ‖v‖
      rw [lp.norm_eq_tsum_rpow (by norm_num) (translate v),
        lp.norm_eq_tsum_rpow (by norm_num) v]
      change (∑' h, ‖v (e h)‖ ^ (2 : ℝ≥0∞).toReal) ^ _ ≤
        (∑' h, ‖v h‖ ^ (2 : ℝ≥0∞).toReal) ^ _
      have hsum := e.tsum_eq (fun h : Group n ↦ ‖v h‖ ^ (2 : ℝ≥0∞).toReal)
      exact le_of_eq (congrArg (fun x : ℝ ↦ x ^ (1 / (2 : ℝ≥0∞).toReal)) hsum))

/-- Represent a finite Fourier sum as a bounded operator. -/
noncomputable def regularImage {n : ℕ} (x : GroupAlgebra n) : Operator n :=
  x.coeff.sum fun g c ↦ c • leftRegular g

/-- Real part of the canonical trace, given by the identity coefficient of `T δ₁`. -/
noncomputable def traceRe {n : ℕ} (T : Operator n) : ℝ :=
  (T (lp.single 2 1 1) 1).re

/-- A Fourier multiplier with scalar symbol `m`. -/
noncomputable def multiplier {n : ℕ} (m : Group n → ℂ) (x : GroupAlgebra n) :
    GroupAlgebra n :=
  MonoidAlgebra.ofCoeff <| Finsupp.onFinset x.coeff.support
    (fun g ↦ m g * x.coeff g) (by
      intro g hg
      exact Finsupp.mem_support_iff.mpr (fun h ↦ hg (by rw [h, mul_zero])))

/-! ## Sharp hypercontractivity (Theorem 1.1) -/

/-- The Poisson semigroup on Fourier polynomials. -/
noncomputable def poisson {n : ℕ} (t : ℝ) (x : GroupAlgebra n) : GroupAlgebra n :=
  multiplier (fun g ↦ (Real.exp (-t * (FreeGroup.norm g : ℝ)) : ℂ)) x

/-- The tracial p-norm on Fourier polynomials, computed using |T|ᵖ = (T* T)ᵖᐟ². -/
noncomputable def lpNorm {n : ℕ} (p : ℝ) (x : GroupAlgebra n) : ℝ :=
  let T := regularImage x
  let Tpow := cfc (p := IsStarNormal) (fun s : ℂ ↦ Complex.ofReal (s.re ^ (p / 2)))
    (star T * T)
  traceRe Tpow ^ (1 / p)

/-- A copy of the Fourier algebra carrying the tracial p-norm. -/
@[expose] def LpCore (n : ℕ) (_p : ℝ) := GroupAlgebra n

/-- The trace formula determines a seminorm for the exponents in Theorem 1.1.
Use zero when the formula admits no seminorm. -/
@[expose] noncomputable def coreLpSeminorm (n : ℕ) (p : ℝ) :
    AddGroupSeminorm (GroupAlgebra n) := by
  classical
  exact if h : ∃ N : AddGroupSeminorm (GroupAlgebra n), ∀ x, N x = lpNorm p x
    then Classical.choose h else 0

noncomputable instance (n : ℕ) (p : ℝ) : SeminormedAddCommGroup (LpCore n p) :=
  (coreLpSeminorm n p).toSeminormedAddCommGroup

/-- Tracial Lp, the completion of Fourier polynomials in the tracial p-norm. -/
noncomputable abbrev Lp (n : ℕ) (p : ℝ) :=
  UniformSpace.Completion (LpCore n p)

/-- The Poisson semigroup on tracial Lp, extended from Fourier polynomials. -/
@[expose] noncomputable def poissonLp {n : ℕ} {p : ℝ} (t : ℝ) : Lp n p → Lp n p :=
  UniformSpace.Completion.map (fun x : LpCore n p ↦ (poisson t x : LpCore n p))

/-- The canonical inclusion of tracial Lq into tracial Lp when p ≤ q. -/
@[expose] noncomputable def lpInclusion (n : ℕ) (p q : ℝ) : Lp n q → Lp n p :=
  UniformSpace.Completion.map (id : LpCore n q → LpCore n p)

/-- The norm of an Lq preimage under the canonical inclusion, with the empty
infimum giving infinity for elements outside Lq. -/
@[expose] noncomputable def extendedLpNorm {n : ℕ} {p : ℝ} (q : ℝ) (x : Lp n p) :
    ℝ≥0∞ :=
  ⨅ y : {y : Lp n q // lpInclusion n p q y = x}, ‖y.val‖ₑ


/-! ## The log-Sobolev inequality (Theorem 1.2) -/

/-- The word-length generator of the Poisson semigroup. -/
noncomputable def generator {n : ℕ} (x : GroupAlgebra n) : GroupAlgebra n :=
  multiplier (fun g ↦ (FreeGroup.norm g : ℂ)) x

/-- Entropy of a positive bounded operator, using the continuous value at zero. -/
noncomputable def entropy {n : ℕ} (T : Operator n) : ℝ :=
  let mass := traceRe T
  traceRe (cfc (p := IsStarNormal) (fun s : ℂ ↦ Complex.ofReal (s.re * Real.log s.re)) T) -
    mass * Real.log mass

/-- The group von Neumann algebra, given by the bicommutant of the left
regular representation. -/
def groupVonNeumann (n : ℕ) : Set (Operator n) :=
  Set.centralizer (Set.centralizer (Set.range (leftRegular (n := n))))

/-- A positive affiliated operator X in tracial L², represented by its bounded
transform B = X(1 + X)⁻¹ and its Fourier vector Xδ₁. -/
structure PositiveAffiliatedL2 (n : ℕ) where
  boundedTransform : Operator n
  fourierVector : Hilbert n
  transform_mem : boundedTransform ∈ groupVonNeumann n
  transform_nonneg : 0 ≤ boundedTransform
  transform_le_one : boundedTransform ≤ 1
  one_sub_injective : Function.Injective (⇑(1 - boundedTransform : Operator n))
  resolvent_eq : (1 - boundedTransform : Operator n) fourierVector =
    boundedTransform (lp.single 2 1 1)

/-- The domain of the square root of the word-length generator on L². -/
def inFormDomain {n : ℕ} (v : Hilbert n) : Prop :=
  Summable (fun g : Group n ↦ (FreeGroup.norm g : ℝ) * ‖v g‖ ^ 2)

/-- The energy ‖L¹ᐟ²v‖₂² of a vector in the form domain. -/
noncomputable def formEnergy {n : ℕ} (v : Hilbert n) : ℝ :=
  ∑' g : Group n, (FreeGroup.norm g : ℝ) * ‖v g‖ ^ 2

/-- Inverse bounded transform after clipping at the image of k + 1. -/
noncomputable def boundedTransformTruncation (k : ℕ) (s : ℝ) : ℝ :=
  let cutoff : ℝ := (k : ℝ) + 1
  let clipped := min (max 0 s) (cutoff / (1 + cutoff))
  clipped / (1 - clipped)

/-- Ent(X²) for a positive affiliated L² element, using spectral truncation.
All cutoffs are at least one, so the negative part of X² log(X²) is unchanged. -/
noncomputable def PositiveAffiliatedL2.entropySq {n : ℕ} (x : PositiveAffiliatedL2 n) : EReal :=
  let mass := ‖x.fourierVector‖ ^ 2
  let truncatedMoment (k : ℕ) : ℝ :=
    traceRe (cfc (p := IsStarNormal) (fun z : ℂ ↦
      let square := boundedTransformTruncation k z.re ^ 2
      Complex.ofReal (square * Real.log square)) x.boundedTransform)
  (⨆ k, (truncatedMoment k : EReal)) - ↑(mass * Real.log mass)
#end_challenge_auxiliary_names

/-- A realization of the tracial norm on finite Fourier sums. The scalar bound
makes its metric completion a complex normed space. -/
structure FourierLpNorm (n : ℕ) (p : ℝ) where
  coreNorm : AddGroupNorm (GroupAlgebra n)
  norm_eq : ∀ x, coreNorm x = lpNorm p x
  norm_smul_le : ∀ (c : ℂ) (x : GroupAlgebra n),
    coreNorm (c • x) ≤ ‖c‖ * coreNorm x

/-- A copy of the Fourier algebra endowed with a specified tracial norm. -/
@[expose] def FourierLpCore {n : ℕ} {p : ℝ} (_ : FourierLpNorm n p) := GroupAlgebra n

noncomputable instance {n : ℕ} {p : ℝ} (N : FourierLpNorm n p) :
    NormedAddCommGroup (FourierLpCore N) := N.coreNorm.toNormedAddCommGroup

noncomputable instance {n : ℕ} {p : ℝ} (N : FourierLpNorm n p) :
    NormedSpace ℂ (FourierLpCore N) where
  toModule := inferInstanceAs (Module ℂ (GroupAlgebra n))
  norm_smul_le := N.norm_smul_le

/-- The finite-exponent tracial Lp space in its Fourier completion model. The
Fourier polynomials are dense in the tracial Lp space of the group von Neumann
algebra, so their metric completion gives the same space. -/
noncomputable abbrev FourierLp {n : ℕ} {p : ℝ} (N : FourierLpNorm n p) :=
  UniformSpace.Completion (FourierLpCore N)

/-- The canonical embedding of a Fourier polynomial into the completed space. -/
@[expose] noncomputable def fourierLpEmbed {n : ℕ} {p : ℝ} (N : FourierLpNorm n p)
    (x : GroupAlgebra n) : FourierLp N :=
  ((show FourierLpCore N from x) : FourierLp N)

@[simp]
theorem leftRegular_apply {n : ℕ} (g h : Group n) (v : Hilbert n) :
    leftRegular g v h = v (g⁻¹ * h) := by
  rfl

@[simp]
theorem multiplier_coeff {n : ℕ} (m : Group n → ℂ) (x : GroupAlgebra n) (g : Group n) :
    (multiplier m x).coeff g = m g * x.coeff g := by
  simp [multiplier, MonoidAlgebra.coeff_ofCoeff]

end FreeGroupHypercontractivity
