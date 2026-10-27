module

public import StationaryHarmonicMaps.Analysis.AtomMeanOscillationPairing

/-! # Genuine L1 normalization from an atom's actual support and AE bound -/

public section

open MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

/-- Original finite positive support mass and the actual AE normalized bound produce genuine global L1 membership and norm at most one. -/
theorem normalized_supported_atom_integrable_abs_le_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (hS0 : μ S≠0) (hSFin : μ S≠⊤)
    (a : X → ℝ) (ha : AEStronglyMeasurable a (μ.restrict S))
    (hSupp : Function.support a⊆S)
    (hBound : ∀ᵐ x ∂μ.restrict S,|a x|≤(μ.real S)⁻¹) :
    Integrable a μ ∧ (∫ x,|a x| ∂μ)≤1 := by
  letI : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hSFin
  have hNorm : ∀ᵐ x ∂μ.restrict S,‖a x‖≤(μ.real S)⁻¹ := by
    simpa only [Real.norm_eq_abs] using hBound
  have hLp : MemLp a 1 (μ.restrict S) := MemLp.of_bound ha (μ.real S)⁻¹ hNorm
  have hI : Integrable a μ := (integrableOn_iff_integrable_of_support_subset hSupp).mp
    (hLp.integrable (by norm_num))
  have hOutside (x : X) (hx : x∉S) : |a x|=0 := by
    have hz : a x=0 := by
      by_contra hn
      exact hx (hSupp hn)
    rw [hz,abs_zero]
  refine ⟨hI,?_⟩
  calc
    _ = ∫ x in S,|a x| ∂μ := (setIntegral_eq_integral_of_forall_compl_eq_zero hOutside).symm
    _ ≤ ∫ _x in S,(μ.real S)⁻¹ ∂μ := integral_mono_ae hI.abs.integrableOn
      (integrable_const _) hBound
    _ = 1 := by
      rw [integral_const,smul_eq_mul,measureReal_restrict_apply_univ]
      exact mul_inv_cancel₀ (ENNReal.toReal_pos hS0 hSFin).ne'

end StationaryHarmonicMaps.Analysis

end
