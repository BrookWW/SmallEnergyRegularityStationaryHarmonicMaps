module

public import HarmonicMaps.Sobolev
public import Mathlib.Geometry.Euclidean.Inversion.Calculus
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Determinant

/-!
# Actual unit inversion and the Piola energy weight

The derivative is the true radial reflection multiplied by the inverse
squared radius. Its actual determinant and the exact outside-to-inside
Piola energy factor are computed from that reflection. The image of the
punctured unit ball is the strict exterior of the unit sphere.
-/

public section

open HarmonicMaps EuclideanGeometry Set
open scoped RealInnerProductSpace

namespace StationaryHarmonicMaps.Geometry

/-- The actual unit inversion has the reciprocal norm, including the origin convention. -/
theorem norm_unit_inversion {n : ℕ} (x : Domain n) :
    ‖inversion (0 : Domain n) 1 x‖=‖x‖⁻¹ := by
  simpa only [dist_zero_right,one_pow,one_div] using dist_inversion_center (0 : Domain n) x (1 : ℝ)

/-- The actual punctured-space derivative is inverse squared radius times radial reflection. -/
theorem hasFDerivAt_unit_inversion {n : ℕ} (x : Domain n) (hx : x≠0) :
    HasFDerivAt (inversion (0 : Domain n) 1)
      ((‖x‖^2)⁻¹ • ((ℝ ∙ x)ᗮ.reflection : Domain n →L[ℝ] Domain n)) x := by
  simpa only [dist_zero_right,sub_zero,one_div,inv_pow] using
    hasFDerivAt_inversion (R := (1 : ℝ)) hx

/-- The actual Jacobian determinant has the full dimension exponent. -/
theorem abs_det_fderiv_unit_inversion {n : ℕ} (x : Domain n) (hx : x≠0) :
    |(fderiv ℝ (inversion (0 : Domain n) 1) x).det|=(‖x‖^(2*n))⁻¹ := by
  have hDet : LinearMap.det ((ℝ ∙ x)ᗮ.reflection.toLinearMap)=-1 := by
    rw [Submodule.det_reflection]
    change (-1 : ℝ)^Module.finrank ℝ ((ℝ ∙ x)ᗮᗮ)=-1
    rw [(ℝ ∙ x).orthogonal_orthogonal,finrank_span_singleton hx,pow_one]
  rw [(hasFDerivAt_unit_inversion x hx).fderiv]
  change |LinearMap.det ((‖x‖^2)⁻¹ • ((ℝ ∙ x)ᗮ.reflection.toLinearMap))|=(‖x‖^(2*n))⁻¹
  rw [LinearMap.det_smul,hDet]
  simp only [Domain,finrank_euclideanSpace,Fintype.card_fin,mul_neg_one,abs_neg,← inv_pow,← pow_mul]
  exact abs_of_nonneg (by positivity)

/-- Unit inversion maps exactly the punctured interior to the strict exterior. -/
theorem unit_inversion_image_punctured_ball {n : ℕ} :
    inversion (0 : Domain n) 1 '' (Metric.ball (0 : Domain n) 1\{0})={x : Domain n | 1<‖x‖} := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    have hy0 : y≠0 := by simpa only [mem_singleton_iff] using hy.2
    have hyPos : 0<‖y‖ := norm_pos_iff.mpr hy0
    rw [mem_setOf_eq,norm_unit_inversion]
    exact (one_lt_inv₀ hyPos).mpr (by simpa only [Metric.mem_ball,dist_zero_right] using hy.1)
  · intro hx
    refine ⟨inversion (0 : Domain n) 1 x,⟨?_,?_⟩,inversion_inversion _ (by norm_num) _⟩
    · rw [Metric.mem_ball,dist_zero_right,norm_unit_inversion]
      exact (inv_lt_one₀ (lt_trans zero_lt_one hx)).mpr hx
    · rw [mem_singleton_iff]
      exact (inversion_eq_center (by norm_num : (1 : ℝ)≠0)).not.mpr (norm_pos_iff.mp (lt_trans zero_lt_one hx))

/-- The real change-of-variables density of the actual Piola reflection is the correct interior weight. -/
theorem unit_inversion_piola_energy_density {n : ℕ} (hn : 2≤n)
    (x z : Domain n) (hx : x≠0) :
    |(fderiv ℝ (inversion (0 : Domain n) 1) x).det| *
      ‖-((‖inversion (0 : Domain n) 1 x‖^(2*n-2))⁻¹) •
        (ℝ ∙ inversion (0 : Domain n) 1 x)ᗮ.reflection z‖^2 =
      ‖x‖^(2*n-4)*‖z‖^2 := by
  have hxNorm : ‖x‖≠0 := norm_ne_zero_iff.mpr hx
  rw [abs_det_fderiv_unit_inversion x hx,norm_smul,
    (ℝ ∙ inversion (0 : Domain n) 1 x)ᗮ.reflection.norm_map,
    Real.norm_eq_abs,abs_neg,abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _)),
    norm_unit_inversion,inv_pow,inv_inv,mul_pow,← pow_mul]
  have hExponent : (2*n-2)*2=2*n+(2*n-4) := by omega
  rw [hExponent,pow_add]
  field_simp

end StationaryHarmonicMaps.Geometry

end
