module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Sharp hypercontractivity for free group von Neumann algebras

Challenge for Xie and Zhang, arXiv:2606.03423v3, Theorems 1.1 and 1.2.
-/

public section

namespace FreeGroupHypercontractivity

open scoped ENNReal

/-! ## Fourier polynomials and the trace -/

abbrev Group (n : ℕ) := FreeGroup (Fin n)
abbrev GroupAlgebra (n : ℕ) := MonoidAlgebra ℂ (Group n)
noncomputable abbrev Hilbert (n : ℕ) := lp (fun _ : Group n ↦ ℂ) 2
noncomputable abbrev Operator (n : ℕ) := Hilbert n →L[ℂ] Hilbert n

local notation "δ₁" => lp.single 2 1 1

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
  (T δ₁ 1).re

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

local notation "P[" t "]" => poissonLp t
local notation "‖" x "‖[" q "]" => extendedLpNorm q x

/-- Theorem 1.1. The sharp hypercontractive inequality on tracial Lp. -/
theorem theorem_1_1 (n : ℕ) (hn : 2 ≤ n) (p q t : ℝ)
    (hp : 1 < p) (hpq : p ≤ q) (ht : 0 ≤ t) :
    (∀ x : Lp n p, ‖P[t] x‖[q] ≤ ‖x‖[p]) ↔
      (1 / 2 : ℝ) * Real.log ((q - 1) / (p - 1)) ≤ t := by
  sorry

/-! ## The log-Sobolev inequality (Theorem 1.2) -/

/-- The word-length generator of the Poisson semigroup. -/
noncomputable def generator {n : ℕ} (x : GroupAlgebra n) : GroupAlgebra n :=
  multiplier (fun g ↦ (FreeGroup.norm g : ℂ)) x

/-- Entropy of a positive bounded operator, using the continuous value at zero. -/
noncomputable def entropy {n : ℕ} (T : Operator n) : ℝ :=
  let mass := traceRe T
  traceRe (cfc (p := IsStarNormal) (fun s : ℂ ↦ Complex.ofReal (s.re * Real.log s.re)) T) -
    mass * Real.log mass

local notation "L" => generator
local notation "τ(" x ")" => traceRe (regularImage x)
local notation "Ent(" x ")" => entropy (regularImage x)

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
  resolvent_eq : (1 - boundedTransform : Operator n) fourierVector = boundedTransform δ₁

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

/-- Theorem 1.2, equation (1.1) and its extension by closure to the natural
form domain of the square-root generator. -/
theorem theorem_1_2 (n : ℕ) (hn : 2 ≤ n) :
    (∀ x : GroupAlgebra n, 0 ≤ regularImage x → Ent(x ^ 2) ≤ 2 * τ(x * L x)) ∧
    (∀ x : PositiveAffiliatedL2 n, inFormDomain x.fourierVector →
      x.entropySq ≤ ↑(2 * formEnergy x.fourierVector)) := by
  sorry

end FreeGroupHypercontractivity
