module

public import StationaryHarmonicMaps.Analysis.VariationalVectorEquation
public import StationaryHarmonicMaps.Geometry.ProjectionCommutator

/-!
# The actual normal-projection antisymmetric system

The same C¹ normal extension and weak gradient produce the commutator field.
Skew-adjointness, the forcing identity and operator-column L² bounds are
proved from actual target geometry. Coefficient Hilbert--Schmidt bounds
require a separate finite-dimensional estimate.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The actual commutator field is skew and acts on the same gradient columns as the forcing. -/
theorem normal_projection_commutator_properties {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    {G : Ambient q → Ambient q →L[ℝ] Ambient q}
    (hG : ContDiff ℝ 1 G) (hcG : HasCompactSupport G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (_hL : 0 ≤ L) (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L) :
    ∀ᵐ x ∂volume.restrict Ω.val, ∀ i : Fin n,
      projectionCommutator (G (u x)) (fderiv ℝ G (u x) (Du x i)) ∈
        skewAdjoint (Ambient q →L[ℝ] Ambient q) ∧
      projectionCommutator (G (u x)) (fderiv ℝ G (u x) (Du x i)) (Du x i) =
        fderiv ℝ G (u x) (Du x i) (Du x i) ∧
      ‖projectionCommutator (G (u x)) (fderiv ℝ G (u x) (Du x i))‖ ≤
        (2 * L) * ‖Du x i‖ := by
  filter_upwards [hN, memW12Loc_ae_tangent N hu hN,
    ae_operatorField_derivative_selfAdjoint N hu hN hG hcG hGN,
    ae_operatorField_differentiated_idempotence N hu hN hG hcG hGN]
    with x hxN ht hself hidem
  intro i
  have hQ : IsSelfAdjoint (G (u x)) := by
    rw [hGN ⟨u x, hxN⟩]
    exact N.normalProjection_isSelfAdjoint _
  have hQv : G (u x) (Du x i) = 0 := by
    rw [hGN ⟨u x, hxN⟩]
    exact (N.normalProjection_apply_eq_zero_iff _ _).2 (ht hxN i)
  have hQnorm : ‖G (u x)‖ ≤ 1 := by
    rw [hGN ⟨u x, hxN⟩]
    exact N.normalProjection_norm_le_one _
  have hDnorm : ‖fderiv ℝ G (u x) (Du x i)‖ ≤ L * ‖Du x i‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hDG (u x)) (norm_nonneg _))
  refine ⟨projectionCommutator_mem_skewAdjoint _ _ hQ (hself i),
    projectionCommutator_apply_of_kernel _ _ (hidem i) _ hQv, ?_⟩
  calc
    _ ≤ 2 * ‖G (u x)‖ * ‖fderiv ℝ G (u x) (Du x i)‖ :=
      norm_projectionCommutator_le _ _
    _ ≤ 2 * 1 * (L * ‖Du x i‖) := by gcongr
    _ = _ := by ring

/-- Each operator column of the actual commutator field is locally L². -/
theorem locallyMemL2_projectionCommutator {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    {G : Ambient q → Ambient q →L[ℝ] Ambient q}
    (hG : ContDiff ℝ 1 G) (hcG : HasCompactSupport G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L) (i : Fin n) :
    LocallyMemL2 Ω (fun x => projectionCommutator (G (u x))
      (fderiv ℝ G (u x) (Du x i))) := by
  intro K hK hs
  have hm := (hu.2.1 K hK hs).aestronglyMeasurable
  have hmD := (hu.2.2 i K hK hs).aestronglyMeasurable
  have hS := hG.continuous.comp_aestronglyMeasurable hm
  have hD := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (((hG.continuous_fderiv (by simp)).comp_aestronglyMeasurable hm).prodMk hmD)
  have hA : AEStronglyMeasurable (fun x => projectionCommutator (G (u x))
      (fderiv ℝ G (u x) (Du x i))) (volume.restrict K) :=
    (hS.mul hD).sub (hD.mul hS)
  apply (hu.2.2 i K hK hs).of_le_mul hA
  exact (ae_restrict_of_ae_restrict_of_subset hs
    (normal_projection_commutator_properties N hu hN hG hcG hGN hL hDG)).mono
      (fun x hx => (hx i).2.2)

/-- The original variational hypothesis gives the actual skew commutator system. -/
theorem variational_antisymmetric_system {n q : ℕ} (N : CompactC2EmbeddedTarget q)
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    (hweak : IsWeaklyHarmonicByTangentVariations N Ω u Du)
    (G : Ambient q → Ambient q →L[ℝ] Ambient q) (hG : ContDiff ℝ 1 G)
    (hcG : HasCompactSupport G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L)
    (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ Ω.val) (v : Ambient q) :
    IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) Ω.val volume ∧
    IntegrableOn (fun x => η x * inner ℝ (∑ i : Fin n,
      projectionCommutator (G (u x)) (fderiv ℝ G (u x) (Du x i)) (Du x i)) v)
      Ω.val volume ∧
    (∫ x in Ω.val, ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) =
      ∫ x in Ω.val, η x * inner ℝ (∑ i : Fin n,
        projectionCommutator (G (u x)) (fderiv ℝ G (u x) (Du x i)) (Du x i)) v := by
  have H := variational_weak_vector_equation N hu hN hweak G hG hcG hGN η hη hcη hsη v
  have hforcing : (fun x => η x * inner ℝ
      (∑ i : Fin n, fderiv ℝ G (u x) (Du x i) (Du x i)) v) =ᵐ[volume.restrict Ω.val]
      (fun x => η x * inner ℝ (∑ i : Fin n,
        projectionCommutator (G (u x)) (fderiv ℝ G (u x) (Du x i)) (Du x i)) v) := by
    filter_upwards [normal_projection_commutator_properties N hu hN hG hcG hGN hL hDG]
      with x hx
    congr 2
    exact Finset.sum_congr rfl (fun i _ => (hx i).2.1.symm)
  exact ⟨H.1, H.2.1.congr hforcing, H.2.2.trans (integral_congr_ae hforcing)⟩

end StationaryHarmonicMaps.Analysis

end
