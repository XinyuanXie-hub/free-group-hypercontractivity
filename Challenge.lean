module

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

Challenge for Xie and Zhang, arXiv:2606.03423v3, Theorems 1.1 and 1.2.
-/

public section

namespace FreeGroupHypercontractivity

open scoped ENNReal

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

/-- The noncommutative Lp norm on Fourier polynomials, using |T|ᵖ = (T* T)ᵖᐟ². -/
noncomputable def lpNorm {n : ℕ} (p : ℝ) (x : GroupAlgebra n) : ℝ :=
  let T := regularImage x
  let Tpow := cfc (p := IsStarNormal) (fun s : ℂ ↦ Complex.ofReal (s.re ^ (p / 2)))
    (star T * T)
  traceRe Tpow ^ (1 / p)

/-- A Fourier multiplier with scalar symbol `m`. -/
noncomputable def multiplier {n : ℕ} (m : Group n → ℂ) (x : GroupAlgebra n) :
    GroupAlgebra n :=
  MonoidAlgebra.ofCoeff <| Finsupp.onFinset x.coeff.support
    (fun g ↦ m g * x.coeff g) (by
      intro g hg
      exact Finsupp.mem_support_iff.mpr (fun h ↦ hg (by rw [h, mul_zero])))

/-- The Poisson semigroup on Fourier polynomials. -/
noncomputable def poisson {n : ℕ} (t : ℝ) (x : GroupAlgebra n) : GroupAlgebra n :=
  multiplier (fun g ↦ (Real.exp (-t * (FreeGroup.norm g : ℝ)) : ℂ)) x

/-- The word-length generator of the Poisson semigroup. -/
noncomputable def generator {n : ℕ} (x : GroupAlgebra n) : GroupAlgebra n :=
  multiplier (fun g ↦ (FreeGroup.norm g : ℂ)) x

/-- Entropy for a positive bounded operator, with the continuous convention at zero. -/
noncomputable def entropy {n : ℕ} (T : Operator n) : ℝ :=
  traceRe (cfc (p := IsStarNormal) (fun s : ℂ ↦ Complex.ofReal (s.re * Real.log s.re)) T) -
    traceRe T * Real.log (traceRe T)

/-- The real part of the canonical trace on the group algebra. -/
def τ {n : ℕ} (x : GroupAlgebra n) : ℝ :=
  (x.coeff 1).re

/-- Entropy of a positive group-algebra element in the left regular representation. -/
noncomputable def Ent {n : ℕ} (x : GroupAlgebra n) : ℝ :=
  entropy (regularImage x)

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

/-- Theorem 1.1. The Poisson Fourier multiplier has a contractive complex
linear extension between the tracial Lp and Lq completions exactly at the
stated times. -/
theorem theorem_1_1 (n : ℕ) (hn : 2 ≤ n) (p q t : ℝ)
    (hp : 1 < p) (hpq : p ≤ q) (ht : 0 ≤ t) :
    ∃ (Np : FourierLpNorm n p) (Nq : FourierLpNorm n q),
      ((∃ P : FourierLp Np →L[ℂ] FourierLp Nq,
          (∀ x : GroupAlgebra n, P (fourierLpEmbed Np x) = fourierLpEmbed Nq (poisson t x)) ∧
          ∀ x : FourierLp Np, ‖P x‖ ≤ ‖x‖) ↔
        (1 / 2 : ℝ) * Real.log ((q - 1) / (p - 1)) ≤ t) := by
  sorry

local notation "L" => generator

/-- Theorem 1.2, equation (1.1). Positivity is in the left regular representation. -/
theorem theorem_1_2 (n : ℕ) (hn : 2 ≤ n) (x : GroupAlgebra n)
    (hx : 0 ≤ regularImage x) :
    Ent (x ^ 2) ≤ 2 * τ (x * L x) := by
  sorry

end FreeGroupHypercontractivity
