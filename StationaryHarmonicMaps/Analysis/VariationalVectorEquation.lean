module

public import StationaryHarmonicMaps.Analysis.VariationalWeakEquation
public import StationaryHarmonicMaps.Analysis.SobolevProjectionDifferential

/-!
# The vector forcing in the variational weak equation

Actual self-adjointness of the differentiated projection along the displayed
Sobolev columns moves the operator across the inner product. This identifies
the positive-sign vector forcing without a projection identity away from the
target.
-/

public section

open HarmonicMaps MeasureTheory
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The original map-criticality gives the actual positive-sign vector forcing. -/
theorem variational_weak_vector_equation {n q : ℕ} (N : CompactC2EmbeddedTarget q)
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    (hweak : IsWeaklyHarmonicByTangentVariations N Ω u Du)
    (G : Ambient q → Ambient q →L[ℝ] Ambient q) (hG : ContDiff ℝ 1 G)
    (hcG : HasCompactSupport G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ Ω.val) (v : Ambient q) :
    IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) Ω.val volume ∧
    IntegrableOn (fun x => η x * inner ℝ
      (∑ i : Fin n, fderiv ℝ G (u x) (Du x i) (Du x i)) v) Ω.val volume ∧
    (∫ x in Ω.val, ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) =
    ∫ x in Ω.val, η x * inner ℝ
      (∑ i : Fin n, fderiv ℝ G (u x) (Du x i) (Du x i)) v := by
  have hscalar := variational_weak_equation N hu hN hweak G hG hGN η hη hcη hsη v
  have hself := ae_operatorField_derivative_selfAdjoint N hu hN hG hcG hGN
  have hswap : (fun x => η x * ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ G (u x) (Du x i) v)) =ᵐ[volume.restrict Ω.val]
      (fun x => η x * inner ℝ
        (∑ i : Fin n, fderiv ℝ G (u x) (Du x i) (Du x i)) v) := by
    filter_upwards [hself] with x hx
    apply congrArg (fun z : ℝ => η x * z)
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _hi
    have hs : inner ℝ (fderiv ℝ G (u x) (Du x i) (Du x i)) v =
        inner ℝ (Du x i) (fderiv ℝ G (u x) (Du x i) v) :=
      (hx i).isSymmetric (Du x i) v
    exact hs.symm
  exact ⟨hscalar.1, hscalar.2.1.congr hswap,
    hscalar.2.2.trans (integral_congr_ae hswap)⟩

end StationaryHarmonicMaps.Analysis

end
