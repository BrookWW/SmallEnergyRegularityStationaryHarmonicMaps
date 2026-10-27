module

public import HarmonicMaps.Analysis.SphereSurfaceChart
public import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Open neighborhoods furnished by central sphere coordinates

The explicit inverse to central normalization identifies a positive-normal
sphere neighborhood with a tangent ball. The neighborhood is open in the
actual unit-sphere subtype and contains its prescribed center.
-/

public section

open Set
open scoped RealInnerProductSpace

namespace HarmonicMaps

/-- The inverse central formula belongs to the tangent hyperplane and its
normalization is exactly the original unit vector. -/
theorem sphereSurface_chart_inverse {n : ℕ} (e : Domain n) (he : ‖e‖ = 1)
    (θ : Domain n) (hθ : ‖θ‖ = 1) (hp : 0 < inner ℝ e θ) :
    (inner ℝ e θ)⁻¹ • θ - e ∈ (ℝ ∙ e)ᗮ ∧
      ‖e + ((inner ℝ e θ)⁻¹ • θ - e)‖⁻¹ •
        (e + ((inner ℝ e θ)⁻¹ • θ - e)) = θ := by
  constructor
  · rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
      inner_smul_right, real_inner_self_eq_norm_sq, he, one_pow,
      inv_mul_cancel₀ hp.ne', sub_self]
  · have hadd : e + ((inner ℝ e θ)⁻¹ • θ - e) = (inner ℝ e θ)⁻¹ • θ := by abel
    rw [hadd, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le), hθ, mul_one,
      inv_inv, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

/-- Every positive tangent-ball radius gives an explicit open sphere
neighborhood of the center, with every point represented by the actual chart. -/
theorem sphereSurface_chart_neighborhood {n : ℕ} (e : Domain n) (he : ‖e‖ = 1)
    (ε : ℝ) (hε : 0 < ε) :
    let U : Set (Metric.sphere (0 : Domain n) 1) :=
      {θ | 0 < inner ℝ e θ.val ∧ ‖(inner ℝ e θ.val)⁻¹ • θ.val - e‖ < ε}
    IsOpen U ∧
      (⟨e, by simpa only [Metric.mem_sphere, dist_zero_right] using he⟩ :
        Metric.sphere (0 : Domain n) 1) ∈ U ∧
      (∀ θ ∈ U, ∃ u : (ℝ ∙ e)ᗮ,
        ‖u‖ < ε ∧ ‖e + (u : Domain n)‖⁻¹ • (e + u) = θ.val) ∧
      ∀ u : (ℝ ∙ e)ᗮ, ‖u‖ < ε →
        (⟨‖e + (u : Domain n)‖⁻¹ • (e + u), by
          simpa only [Metric.mem_sphere, dist_zero_right] using
            (sphereSurface_chart_geometry e he u).2.1⟩ : Metric.sphere (0 : Domain n) 1) ∈ U := by
  let S := Metric.sphere (0 : Domain n) 1
  let P : S → ℝ := fun θ => inner ℝ e θ.val
  let Q : S → Domain n := fun θ => (P θ)⁻¹ • θ.val - e
  have hP : Continuous P := continuous_const.inner continuous_subtype_val
  have hQ : ContinuousOn Q {θ | 0 < P θ} :=
    ((hP.continuousOn.inv₀ (fun θ hθ => hθ.ne')).smul
      continuous_subtype_val.continuousOn).sub continuousOn_const
  have hU : IsOpen ({θ : S | 0 < P θ} ∩ (fun θ : S => ‖Q θ‖) ⁻¹' Iio ε) :=
    hQ.norm.isOpen_inter_preimage (isOpen_lt continuous_const hP) isOpen_Iio
  refine ⟨hU, ?_, ?_, ?_⟩
  · change 0 < inner ℝ e e ∧ ‖(inner ℝ e e)⁻¹ • e - e‖ < ε
    rw [real_inner_self_eq_norm_sq, he, one_pow, inv_one, one_smul, sub_self, norm_zero]
    exact ⟨zero_lt_one, hε⟩
  · intro θ hθ
    have hnorm : ‖θ.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    obtain ⟨htan, hinv⟩ := sphereSurface_chart_inverse e he θ.val hnorm hθ.1
    exact ⟨⟨(inner ℝ e θ.val)⁻¹ • θ.val - e, htan⟩, hθ.2, hinv⟩
  · intro u hu
    have hg := sphereSurface_chart_geometry e he u
    change 0 < inner ℝ e (‖e + (u : Domain n)‖⁻¹ • (e + u)) ∧
      ‖(inner ℝ e (‖e + (u : Domain n)‖⁻¹ • (e + u)))⁻¹ •
        (‖e + (u : Domain n)‖⁻¹ • (e + u)) - e‖ < ε
    rw [hg.2.2.2]
    refine ⟨?_, hu⟩
    rw [hg.2.2.1]
    exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one hg.1)

end HarmonicMaps
end
