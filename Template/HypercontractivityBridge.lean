module

import all Template.Model

public import Template.EntropyDissipation
public import Template.HypercontractivityPositive
public import Template.PositiveDensity

public section

namespace FreeGroupHypercontractivity

open Set
open scoped ComplexOrder

set_option maxHeartbeats 1200000 in
/-- The entropy-dissipation estimates required by the Gross evolution follow
from the log-Sobolev inequality on positive Fourier polynomials. -/
theorem poissonEntropyDissipation_of_logSobolev {n : ℕ}
    (hLSI : ∀ y : GroupAlgebra n, 0 ≤ regularImage y →
      entropy (regularImage y ^ 2) ≤ 2 * traceRe (regularImage y * regularImage (generator y))) :
    PoissonEntropyDissipation n := by
  intro x hx r hr
  obtain ⟨a, ha, hax⟩ := hx
  let T := regularImage x
  let X := polynomialInclusion n x
  have hX : (X : Operator n) = T := polynomialInclusion_coe n x
  have hpos : 0 ≤ T := nonneg_of_nonneg_scalar_le ha.le hax
  have hTsa : IsSelfAdjoint T :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hpos).isSelfAdjoint
  have hXsa : IsSelfAdjoint X := by
    apply Subtype.ext
    change star (X : Operator n) = (X : Operator n)
    rw [hX]
    exact hTsa.star_eq
  let : Nontrivial (Hilbert n) := ⟨⟨lp.single 2 1 1, 0, by
    intro h
    have he := congrArg (fun v : Hilbert n ↦ v (1 : Group n)) h
    simp at he⟩⟩
  let b := max a ‖T‖
  have hspec (z : ℂ) (hz : z ∈ spectrum ℂ T) : z.re ∈ Icc a b := by
    refine ⟨le_re_spectrum_of_scalar_le ha.le hax hz, ?_⟩
    exact (le_abs_self z.re).trans ((Complex.abs_re_le_norm z).trans
      ((spectrum.norm_le_norm_of_mem hz).trans (le_max_right _ _)))
  have h := entropy_of_rpow_half_le_dissipation x hpos ha (le_max_left a ‖T‖) hspec hr hLSI
  let f (z : ℝ) := z ^ (r / 2)
  let g (z : ℝ) := z ^ (r - 1)
  have hf : Continuous f := Real.continuous_rpow_const (by linarith)
  have hg : Continuous g := Real.continuous_rpow_const (by linarith)
  have hpow (F : ℝ → ℝ) (hF : Continuous F) :
      ((cfc (p := IsSelfAdjoint) F X : GroupCStar n) : Operator n) = realCfcAt F T := by
    rw [groupCStar_coe_real_cfc F hF X hXsa, hX, realCfcAt]
  have hEntropy := entropy_sq_cfc_half_rpow X (hX ▸ hpos) (zero_lt_one.trans hr)
  dsimp only [PoissonEntropyDissipation]
  change 0 ≤ groupTraceReCLM n (cfc (p := IsSelfAdjoint) g X * polynomialInclusion n (generator x)) ∧ _
  have hD :
      groupTraceReCLM n (cfc (p := IsSelfAdjoint) g X * polynomialInclusion n (generator x)) =
        traceRe (realCfcAt g T * regularImage (generator x)) := by
    rw [groupTraceReCLM_apply]
    change traceRe (((cfc (p := IsSelfAdjoint) g X : GroupCStar n) : Operator n) *
      (polynomialInclusion n (generator x) : Operator n)) = _
    rw [hpow g hg, polynomialInclusion_coe]
  change 0 ≤ traceRe (realCfcAt g T * regularImage (generator x)) ∧
    2 * (r - 1) * entropy (realCfcAt f T ^ 2) ≤
      r ^ 2 * traceRe (realCfcAt g T * regularImage (generator x)) at h
  rw [hD]
  rw [← hpow f hf] at h
  exact ⟨h.1, by simpa only [f, hEntropy] using h.2⟩


/-- Sharp Poisson contractivity on the positive cone of the reduced group
C*-algebra, deduced from log-Sobolev on its positive Fourier polynomials. -/
theorem positive_groupCStar_contractivity_of_logSobolev {n : ℕ}
    (hLSI : ∀ y : GroupAlgebra n, 0 ≤ regularImage y →
      entropy (regularImage y ^ 2) ≤ 2 * traceRe (regularImage y * regularImage (generator y)))
    {p q t : ℝ} (hp : 1 < p) (hpq : p ≤ q) (ht : 0 < t)
    (hthreshold : (1 / 2 : ℝ) * Real.log ((q - 1) / (p - 1)) ≤ t)
    (x : GroupCStar n) (hx : 0 ≤ (x : Operator n)) :
    operatorLpNorm q (poissonCStar n t x : Operator n) ≤ operatorLpNorm p (x : Operator n) := by
  have hp₀ : 0 < p := by linarith
  have hq₀ : 0 < q := by linarith
  apply positive_groupCStar_contractivity_of_fourier hp₀ hq₀ ht.le _ x hx
  apply positive_fourier_contractivity_of_strict hp₀ hq₀
  exact fun y hy ↦ lpNorm_poisson_le_of_entropy_dissipation
    (poissonEntropyDissipation_of_logSobolev hLSI) hp hpq ht hthreshold hy

end FreeGroupHypercontractivity
