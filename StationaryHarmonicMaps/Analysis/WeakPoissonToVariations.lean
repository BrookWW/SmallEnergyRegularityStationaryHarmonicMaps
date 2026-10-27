module

public import StationaryHarmonicMaps.Analysis.VariationComposition
public import StationaryHarmonicMaps.Analysis.VariationLocalization
public import StationaryHarmonicMaps.Analysis.WeakPoissonBoundedTest
public import StationaryHarmonicMaps.Analysis.VariationalWeakPoisson
public import StationaryHarmonicMaps.Analysis.VariationIntegrability
public import HolderToCK.Analysis.WeakPoissonLocality
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# From the actual signed Poisson equation to tangent variations

Bounded mixed Sobolev compositions give genuine zero-boundary tests on
interior balls. The actual forcing is normal along the given weak gradient,
so its pairing with a tangent variation vanishes. Finite localization then
recovers every original compact C¹ product variation on an arbitrary open
domain.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The actual normal-extension forcing is orthogonal to every tangent field along the map. -/
theorem ae_normal_extension_forcing_inner_tangent_zero {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    (G : Ambient q → Ambient q →L[ℝ] Ambient q) (hG : ContDiff ℝ 1 G)
    (hcG : HasCompactSupport G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    (V : Domain n × Ambient q → Ambient q)
    (hVT : ∀ (x : Domain n) (p : N.Carrier), V (x, p.val) ∈ N.tangentImage p) :
    ∀ᵐ x ∂volume.restrict Ω.val, inner ℝ
      (∑ i : Fin n, fderiv ℝ G (u x) (Du x i) (Du x i)) (V (x, u x)) = 0 := by
  filter_upwards [hN, memW12Loc_ae_tangent N hu hN,
    ae_operatorField_differentiated_idempotence N hu hN hG hcG hGN]
    with x hx ht hidem
  have hQv (i : Fin n) : G (u x) (Du x i) = 0 := by
    rw [hGN ⟨u x, hx⟩]
    exact (N.normalProjection_apply_eq_zero_iff _ _).2 (ht hx i)
  have hB : G (u x) (∑ i : Fin n, fderiv ℝ G (u x) (Du x i) (Du x i)) =
      ∑ i : Fin n, fderiv ℝ G (u x) (Du x i) (Du x i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      projection_derivative_apply_of_kernel _ _ (hidem i) _ (hQv i)
  have hQV : G (u x) (V (x, u x)) = 0 := by
    rw [hGN ⟨u x, hx⟩]
    exact (N.normalProjection_apply_eq_zero_iff _ _).2 (hVT x ⟨u x, hx⟩)
  have hself : IsSelfAdjoint (G (u x)) := by
    rw [hGN ⟨u x, hx⟩]
    exact N.normalProjection_isSelfAdjoint _
  have H := hself.isSymmetric
    (∑ i : Fin n, fderiv ℝ G (u x) (Du x i) (Du x i)) (V (x, u x))
  simp only [ContinuousLinearMap.coe_coe] at H
  rw [hB, hQV, inner_zero_right] at H
  exact H

private theorem outerVariation_density_zero_off_projection {n q : ℕ}
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (V : Domain n × Ambient q → Ambient q) {x : Domain n}
    (hx : x ∉ Prod.fst '' tsupport V) :
    (∑ i : Fin n, inner ℝ (Du x i)
      (fderiv ℝ V (x, u x) (EuclideanSpace.single i 1, Du x i))) = 0 := by
  have hz : (x, u x) ∉ tsupport V := fun h => hx ⟨(x, u x), h, rfl⟩
  simp only [fderiv_of_notMem_tsupport (𝕜 := ℝ) hz, zero_apply,
    inner_zero_right, Finset.sum_const_zero]

/-- Every compact tangent variation supported over one interior ball has zero first variation. -/
theorem integral_outerVariation_eq_zero_of_projected_support_ball {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    (G : Ambient q → Ambient q →L[ℝ] Ambient q) (hG : ContDiff ℝ 1 G)
    (hcG : HasCompactSupport G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L)
    (hP : HolderToCK.WeakPoissonOn Ω Du (fun x => -(∑ i : Fin n,
      fderiv ℝ G (u x) (Du x i) (Du x i))))
    {a : Domain n} {r : ℝ} (hr : 0 < r) (hclosed : Metric.closedBall a r ⊆ Ω.val)
    (V : Domain n × Ambient q → Ambient q) (hV : ContDiff ℝ 1 V)
    (hcV : HasCompactSupport V) (hsV : Prod.fst '' tsupport V ⊆ Metric.ball a r)
    (hVT : ∀ (x : Domain n) (p : N.Carrier), V (x, p.val) ∈ N.tangentImage p) :
    (∫ x, ∑ i : Fin n, inner ℝ (Du x i)
      (fderiv ℝ V (x, u x) (EuclideanSpace.single i 1, Du x i))) = 0 := by
  have hball : Metric.ball a r ⊆ Ω.val := Metric.ball_subset_closedBall.trans hclosed
  obtain ⟨hw, M, _hM, hbound⟩ :=
    variationComposition_zeroBoundary_ball hu hr hclosed V hV hcV hsV
  have hforce := (locallyIntegrableOn_normal_extension_forcing hu G hG hDG).integrableOn_compact_subset
    hclosed (isCompact_closedBall a r)
  have hFneg : IntegrableOn (fun x => -(∑ i : Fin n,
      fderiv ℝ G (u x) (Du x i) (Du x i))) (Metric.ball a r) volume :=
    (hforce.mono_set Metric.ball_subset_closedBall).neg
  have H := weakPoissonOn_bounded_zeroBoundary_test (hP.mono hball)
    (hu.memW12_ball hclosed).2.2 hFneg hw (Eventually.of_forall hbound)
  have horth := ae_restrict_of_ae_restrict_of_subset hball
    (ae_normal_extension_forcing_inner_tangent_zero N hu hN G hG hcG hGN V hVT)
  have hz : (∫ x in Metric.ball a r, inner ℝ
      (-(∑ i : Fin n, fderiv ℝ G (u x) (Du x i) (Du x i))) (V (x, u x))) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [horth] with x hx
    change inner ℝ (-(∑ i : Fin n, fderiv ℝ G (u x) (Du x i) (Du x i))) (V (x, u x)) = 0
    rw [inner_neg_left, hx, neg_zero]
  have heq : (∫ x in Metric.ball a r, ∑ i : Fin n, inner ℝ (Du x i)
      (fderiv ℝ V (x, u x) (EuclideanSpace.single i 1, Du x i))) = 0 := by
    have HH : (∫ x in Metric.ball a r, ∑ i : Fin n, inner ℝ (Du x i)
        (fderiv ℝ V (x, u x) (EuclideanSpace.single i 1, Du x i))) =
        -(∫ x in Metric.ball a r, inner ℝ
          (-(∑ i : Fin n, fderiv ℝ G (u x) (Du x i) (Du x i))) (V (x, u x))) := H.2.2
    rw [hz, neg_zero] at HH
    exact HH
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
    outerVariation_density_zero_off_projection u Du V (fun h => hx (hsV h)))] at heq
  exact heq

/-- The actual signed Poisson equation implies the original full C¹ tangent-variation predicate. -/
theorem weakPoissonOn_implies_tangentVariations {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    (G : Ambient q → Ambient q →L[ℝ] Ambient q) (hG : ContDiff ℝ 1 G)
    (hcG : HasCompactSupport G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L)
    (hP : HolderToCK.WeakPoissonOn Ω Du (fun x => -(∑ i : Fin n,
      fderiv ℝ G (u x) (Du x i) (Du x i)))) :
    IsWeaklyHarmonicByTangentVariations N Ω u Du := by
  intro V hV hcV hsV hVT
  obtain ⟨r, t, W, hballs, hW, hsum⟩ :=
    exists_finite_ball_variation_localization Ω V hV hcV hsV
  have hWT (j : t) (x : Domain n) (p : N.Carrier) : W j (x, p.val) ∈ N.tangentImage p := by
    obtain ⟨c, hc⟩ := (hW j).2.2.2 (x, p.val)
    rw [hc]
    exact (N.tangentImage p).smul_mem c (hVT x p)
  have hWΩ (j : t) : tsupport (W j) ⊆ Ω.val ×ˢ (Set.univ : Set (Ambient q)) := by
    intro z hz
    exact ⟨Metric.ball_subset_closedBall.trans (hballs j.val).2
      ((hW j).2.2.1 ⟨z, hz, rfl⟩), mem_univ _⟩
  have hWI (j : t) := integrable_outerVariation_density hu (hW j).1 (hW j).2.1 (hWΩ j)
  have hzero (j : t) := integral_outerVariation_eq_zero_of_projected_support_ball N hu hN
    G hG hcG hGN hDG hP (hballs j.val).1 (hballs j.val).2
      (W j) (hW j).1 (hW j).2.1 (hW j).2.2.1 (hWT j)
  have hDsum (z : Domain n × Ambient q) :
      fderiv ℝ V z = ∑ j : t, fderiv ℝ (W j) z := by
    have H := fderiv_sum (u := Finset.univ) (A := W) (x := z)
      (fun j _ => ((hW j).1.differentiable (by simp) z))
    exact (congrArg (fun f : Domain n × Ambient q → Ambient q => fderiv ℝ f z) hsum).symm.trans H
  have hdensity (x : Domain n) : (∑ i : Fin n, inner ℝ (Du x i)
      (fderiv ℝ V (x, u x) (EuclideanSpace.single i 1, Du x i))) =
      ∑ j : t, ∑ i : Fin n, inner ℝ (Du x i)
        (fderiv ℝ (W j) (x, u x) (EuclideanSpace.single i 1, Du x i)) := by
    simp only [hDsum, sum_apply, inner_sum]
    exact Finset.sum_comm
  refine ⟨integrableOn_outerVariation_density hu hV hcV hsV, ?_⟩
  have hwhole : (∫ x, ∑ i : Fin n, inner ℝ (Du x i)
      (fderiv ℝ V (x, u x) (EuclideanSpace.single i 1, Du x i))) = 0 := by
    simp_rw [hdensity]
    rw [integral_finsetSum _ (fun j _ => hWI j)]
    simp only [hzero, Finset.sum_const_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
    outerVariation_density_zero_off_projection u Du V (by
      rintro ⟨z, hz, rfl⟩
      exact hx (hsV hz).1))]
  exact hwhole

/-- For the actual normal extension, map criticality and the signed weak PDE are equivalent. -/
theorem tangentVariations_iff_weakPoissonOn {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    (G : Ambient q → Ambient q →L[ℝ] Ambient q) (hG : ContDiff ℝ 1 G)
    (hcG : HasCompactSupport G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L) :
    IsWeaklyHarmonicByTangentVariations N Ω u Du ↔
      HolderToCK.WeakPoissonOn Ω Du (fun x => -(∑ i : Fin n,
        fderiv ℝ G (u x) (Du x i) (Du x i))) :=
  ⟨fun hweak => variational_weakPoissonOn N hu hN hweak G hG hcG hGN hDG,
    weakPoissonOn_implies_tangentVariations N hu hN G hG hcG hGN hDG⟩

/-- One actual target-dependent extension gives the equivalence on every open domain. -/
theorem exists_normal_extension_tangentVariations_iff {q : ℕ} (N : CompactC2EmbeddedTarget q) :
    ∃ (G : Ambient q → Ambient q →L[ℝ] Ambient q) (L : ℝ),
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      (∀ p : N.Carrier, G p.val = N.normalProjection p) ∧ 0 ≤ L ∧
      (∀ y : Ambient q, ‖fderiv ℝ G y‖ ≤ L) ∧
      ∀ {n : ℕ} {Ω : OpenDomain n} {u : Domain n → Ambient q}
        {Du : Domain n → Gradient n q}, MemW12Loc Ω u Du →
        (∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet) →
        (IsWeaklyHarmonicByTangentVariations N Ω u Du ↔
          HolderToCK.WeakPoissonOn Ω Du (fun x => -(∑ i : Fin n,
            fderiv ℝ G (u x) (Du x i) (Du x i)))) := by
  obtain ⟨G, L, hG, hcG, hraw, hL, hDG⟩ :=
    N.exists_global_ambient_normal_projection_extension_bounded_derivative
  have hGN (p : N.Carrier) : G p.val = N.normalProjection p :=
    (hraw p).trans (N.normalProjection_eq_starProjection p).symm
  refine ⟨G, L, hG, hcG, hGN, hL, hDG, ?_⟩
  intro n Ω u Du hu hN
  exact tangentVariations_iff_weakPoissonOn N hu hN G hG hcG hGN hDG

end StationaryHarmonicMaps.Analysis

end
