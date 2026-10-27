module

public import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# A uniform scalar threshold for native Coulomb perturbations

The one positive threshold controls both the inverse-function amplitude
and the original quadratic critical-energy allowance.
-/

public section

open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Positive source constants determine one threshold for every admissible
connection amplitude, with the exact extended-real critical-bound transfer. -/
theorem exists_uniform_coulomb_perturbation_threshold
    (δ εIFT C : ℝ) (hδ : 0<δ) (hεIFT : 0<εIFT) (hC : 0<C) :
    ∃η0 : ℝ,0<η0 ∧ ∀η : ℝ,0≤η → η≤η0 →
      0≤(1+C)*η ∧ (1+C)*η≤εIFT ∧
      2*C*η^2+2*(δ/4)^2≤δ^2 ∧
      C*η^2≤((1+C)*η)^2 ∧
      ∀E : ℝ≥0∞,E≤ENNReal.ofReal (C*η^2) → E≤ENNReal.ofReal (((1+C)*η)^2) := by
  have hOneC : 0<1+C := by linarith
  let η0 : ℝ := min (εIFT/(1+C)) ((δ/4)/(1+C))
  have hη0 : 0<η0 := lt_min (div_pos hεIFT hOneC)
    (div_pos (div_pos hδ (by norm_num)) hOneC)
  refine ⟨η0,hη0,?_⟩
  intro η hη hSmall
  have hIFT : (1+C)*η≤εIFT := by
    have H := (le_div_iff₀ hOneC).mp (hSmall.trans (min_le_left _ _))
    simpa only [mul_comm] using H
  have hDelta : (1+C)*η≤δ/4 := by
    have H := (le_div_iff₀ hOneC).mp (hSmall.trans (min_le_right _ _))
    simpa only [mul_comm] using H
  have hNonneg : 0≤(1+C)*η := mul_nonneg hOneC.le hη
  have hCoeff : C≤(1+C)^2 := by nlinarith [sq_nonneg C]
  have hScale : C*η^2≤((1+C)*η)^2 :=
    (mul_le_mul_of_nonneg_right hCoeff (sq_nonneg η)).trans_eq (by ring)
  have hSquare : ((1+C)*η)^2≤(δ/4)^2 :=
    (sq_le_sq₀ hNonneg (div_nonneg hδ.le (by norm_num))).mpr hDelta
  have hEnergy : 2*C*η^2+2*(δ/4)^2≤δ^2 := by
    have H := hScale.trans hSquare
    nlinarith [sq_nonneg δ]
  refine ⟨hNonneg,hIFT,hEnergy,hScale,?_⟩
  intro E hE
  exact hE.trans (ENNReal.ofReal_le_ofReal hScale)

end StationaryHarmonicMaps.Analysis
