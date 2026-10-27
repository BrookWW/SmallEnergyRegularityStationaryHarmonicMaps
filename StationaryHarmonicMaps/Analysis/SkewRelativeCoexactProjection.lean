/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Geometry.OrientationRightCorrection

/-!
# The actual skew projection in full operator coefficients

Taking one half of an operator minus its real adjoint is a self-adjoint
contraction in the complete Hilbert--Schmidt coefficient space. The same
linear map fixes every original skew operator and has skew range.
-/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps.Analysis

/-- Full coefficient skew projection has its literal formula, actual skew range,
self-adjoint pairing, coefficient-one norm control, and fixes every skew input. -/
theorem exists_full_coefficient_skew_projection {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀ T,R (E T)=T) (hER : ∀ z,E (R z)=z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖^2=∑ j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) :
    ∃ S : Ambient (q*q) →L[ℝ] Ambient (q*q),
      (∀ z,S z=E ((1/2:ℝ) • (R z-star (R z)))) ∧
      (∀ z,star (R (S z))= -R (S z)) ∧
      (∀ z w,inner ℝ (S z) w=inner ℝ z (S w)) ∧
      (∀ z,‖S z‖≤‖z‖) ∧
      ∀ z,star (R z)= -R z → S z=z := by
  let Jlin : Ambient (q*q) →ₗ[ℝ] Ambient (q*q) :=
    { toFun := fun z=>E (star (R z))
      map_add' := by
        intro z w
        rw [map_add]
        change E (ContinuousLinearMap.adjoint (R z+R w))=E (star (R z))+E (star (R w))
        rw [map_add,map_add]
        rfl
      map_smul' := by intro c z;rw [map_smul,star_smul,star_trivial,map_smul];rfl }
  let J := Jlin.toContinuousLinearMap
  let S : Ambient (q*q) →L[ℝ] Ambient (q*q) :=
    (1/2:ℝ) • (ContinuousLinearMap.id ℝ (Ambient (q*q))-J)
  have hS (z : Ambient (q*q)) : S z=(1/2:ℝ) • (z-E (star (R z))) := rfl
  have hFormula (z : Ambient (q*q)) : S z=E ((1/2:ℝ) • (R z-star (R z))) := by
    rw [hS,map_smul,map_sub,hER]
  have hSkew (z : Ambient (q*q)) : star (R (S z))= -R (S z) := by
    have hSub : star (R z-star (R z))=star (R z)-R z := by
      change ContinuousLinearMap.adjoint (R z-star (R z))=star (R z)-R z
      rw [map_sub]
      change star (R z)-star (star (R z))=star (R z)-R z
      rw [star_star]
    rw [hFormula,hRE,star_smul,hSub]
    simp only [star_trivial]
    module
  have hInner (z w : Ambient (q*q)) : inner ℝ (S z) w=inner ℝ z (S w) := by
    have hJ : inner ℝ (E (star (R z))) w=inner ℝ z (E (star (R w))) := by
      have H := encoded_inner_star_right_eq_star_left E hE (R z) (R w)
      rw [hER,hER] at H
      exact H.symm
    rw [hS,hS,real_inner_smul_left,real_inner_smul_right,inner_sub_left,inner_sub_right,hJ]
  have hNorm (z : Ambient (q*q)) : ‖S z‖≤‖z‖ := by
    have hStar : ‖E (star (R z))‖=‖z‖ := by
      have hSq := encoded_norm_sq_star E hE (R z)
      rw [hER] at hSq
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hSq
    rw [hS,norm_smul,Real.norm_of_nonneg (by norm_num : 0≤(1/2:ℝ))]
    calc
      _≤(1/2:ℝ)*(‖z‖+‖E (star (R z))‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
      _=‖z‖ := by rw [hStar];ring
  refine ⟨S,hFormula,hSkew,hInner,hNorm,?_⟩
  intro z hz
  rw [hS,hz,map_neg,hER]
  module

end StationaryHarmonicMaps.Analysis

end
