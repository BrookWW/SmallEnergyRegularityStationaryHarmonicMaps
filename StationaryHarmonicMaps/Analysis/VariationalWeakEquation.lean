module

public import StationaryHarmonicMaps.Analysis.TangentVariationTest
public import StationaryHarmonicMaps.Analysis.C2TargetSobolevTangency
public import StationaryHarmonicMaps.Foundation.WeakHarmonicity
public import StationaryHarmonicMaps.Geometry.C2ProjectionGlobalExtension
import HarmonicMaps.SobolevLemmas
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The weak equation from actual tangent variations

The prescribed map-criticality is tested with compact C¹ tangent fields.
Tangency of the same weak gradient removes the normal projection from the
linear term. The derivative of the tangent test gives the positive-sign
normal-projection forcing. All distributional integrals are genuinely
integrable.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem integrableOn_linear_weak_test {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ Ω.val) (v : Ambient q) :
    IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) Ω.val volume := by
  apply integrable_finsetSum
  intro i _hi
  have hDη : ContDiff ℝ ∞ (coordinateDerivative η hη i) :=
    (contDiff_infty_iff_fderiv.mp hη).2.clm_apply contDiff_const
  have hpair := hu.1.integrable_test_gradient i hDη
    (hcη.fderiv_apply ℝ (EuclideanSpace.single i 1))
    ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsη)
  simpa only [coordinateDerivative, real_inner_smul_left, real_inner_smul_right] using
    hpair.inner_const (𝕜 := ℝ) v

/-- The map-variation identity gives the positive-sign scalar weak harmonic-map equation. -/
theorem variational_weak_equation {n q : ℕ} (N : CompactC2EmbeddedTarget q)
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    (hweak : IsWeaklyHarmonicByTangentVariations N Ω u Du)
    (G : Ambient q → Ambient q →L[ℝ] Ambient q) (hG : ContDiff ℝ 1 G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ Ω.val) (v : Ambient q) :
    IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) Ω.val volume ∧
    IntegrableOn (fun x => η x * ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ G (u x) (Du x i) v)) Ω.val volume ∧
    (∫ x in Ω.val, ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) =
    ∫ x in Ω.val, η x * ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ G (u x) (Du x i) v) := by
  obtain ⟨Y, hY, hcY, hYN, hYtangent, hDY⟩ := exists_compact_tangent_field N G hG hGN v
  have hη1 : ContDiff ℝ 1 η := hη.of_le ENat.LEInfty.out
  have htest := tangent_product_variation N Ω η hη1 hcη hsη Y hY hcY hYtangent
  let V : Domain n × Ambient q → Ambient q := fun z => η z.1 • Y z.2
  have hcrit := hweak V htest.1 htest.2.1 htest.2.2.1 htest.2.2.2
  let L : Domain n → ℝ := fun x => ∑ i : Fin n,
    inner ℝ (Du x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)
  let R : Domain n → ℝ := fun x => η x * ∑ i : Fin n,
    inner ℝ (Du x i) (fderiv ℝ G (u x) (Du x i) v)
  let T : Domain n → ℝ := fun x => ∑ i : Fin n,
    inner ℝ (Du x i) (fderiv ℝ V (x, u x) (EuclideanSpace.single i 1, Du x i))
  have hTLR : T =ᵐ[volume.restrict Ω.val] (fun x => L x - R x) := by
    filter_upwards [hN, memW12Loc_ae_tangent N hu hN] with x hxN hxt
    let p : N.Carrier := ⟨u x, hxN⟩
    change (∑ i : Fin n, inner ℝ (Du x i)
      (fderiv ℝ V (x, u x) (EuclideanSpace.single i 1, Du x i))) =
      (∑ i : Fin n, inner ℝ (Du x i)
        (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) -
      η x * ∑ i : Fin n, inner ℝ (Du x i) (fderiv ℝ G (u x) (Du x i) v)
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    have hQi : N.normalProjection p (Du x i) = 0 :=
      (N.normalProjection_apply_eq_zero_iff p (Du x i)).mpr (hxt hxN i)
    have hinner : inner ℝ (Du x i) (G (u x) v) = 0 := by
      rw [hGN p]
      have hs : inner ℝ (N.normalProjection p (Du x i)) v =
          inner ℝ (Du x i) (N.normalProjection p v) :=
        (N.normalProjection_isSelfAdjoint p).isSymmetric (Du x i) v
      rw [← hs, hQi, inner_zero_left]
    have hYinner : inner ℝ (Du x i) (Y (u x)) = inner ℝ (Du x i) v := by
      rw [hYN p, inner_sub_right, hinner, sub_zero]
    rw [fderiv_tangent_product_variation η hη1 Y hY x (u x)
      (EuclideanSpace.single i 1) (Du x i), hDY p (Du x i),
      inner_add_right, real_inner_smul_right, inner_neg_right,
      real_inner_smul_right, hYinner]
    simp only [p, real_inner_smul_right]
    ring
  have hL : IntegrableOn L Ω.val volume :=
    integrableOn_linear_weak_test hu η hη hcη hsη v
  have hLR : IntegrableOn (fun x => L x - R x) Ω.val volume := hcrit.1.congr hTLR
  have hR : IntegrableOn R Ω.val volume := by
    apply (hL.sub hLR).congr
    filter_upwards [] with x
    change L x - (L x - R x) = R x
    ring
  have hzero : (∫ x in Ω.val, L x - R x) = 0 :=
    (integral_congr_ae hTLR).symm.trans hcrit.2
  rw [integral_sub hL hR] at hzero
  exact ⟨hL, hR, sub_eq_zero.mp hzero⟩

/-- One target-dependent extension works for every Sobolev map and every admissible test. -/
theorem exists_normal_extension_variational_weak_equation {q : ℕ}
    (N : CompactC2EmbeddedTarget q) :
    ∃ (G : Ambient q → Ambient q →L[ℝ] Ambient q) (C : ℝ),
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      (∀ p : N.Carrier, G p.val = N.normalProjection p) ∧ 0 ≤ C ∧
      (∀ z : Ambient q, ‖fderiv ℝ G z‖ ≤ C) ∧
      ∀ {n : ℕ} {Ω : OpenDomain n} {u : Domain n → Ambient q}
        {Du : Domain n → Gradient n q}, MemW12Loc Ω u Du →
        (∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet) →
        IsWeaklyHarmonicByTangentVariations N Ω u Du →
        ∀ (η : Domain n → ℝ) (_hη : ContDiff ℝ ∞ η),
          HasCompactSupport η → tsupport η ⊆ Ω.val → ∀ v : Ambient q,
          IntegrableOn (fun x => ∑ i : Fin n,
            inner ℝ (Du x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) Ω.val volume ∧
          IntegrableOn (fun x => η x * ∑ i : Fin n,
            inner ℝ (Du x i) (fderiv ℝ G (u x) (Du x i) v)) Ω.val volume ∧
          (∫ x in Ω.val, ∑ i : Fin n,
            inner ℝ (Du x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) =
          ∫ x in Ω.val, η x * ∑ i : Fin n,
            inner ℝ (Du x i) (fderiv ℝ G (u x) (Du x i) v) := by
  obtain ⟨G, C, hG, hcG, hraw, hC, hbound⟩ :=
    N.exists_global_ambient_normal_projection_extension_bounded_derivative
  have hGN (p : N.Carrier) : G p.val = N.normalProjection p :=
    (hraw p).trans (N.normalProjection_eq_starProjection p).symm
  refine ⟨G, C, hG, hcG, hGN, hC, hbound, ?_⟩
  intro n Ω u Du hu hN hweak η hη hcη hsη v
  exact variational_weak_equation N hu hN hweak G hG hGN η hη hcη hsη v

end StationaryHarmonicMaps.Analysis

end
