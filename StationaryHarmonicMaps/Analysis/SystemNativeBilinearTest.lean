/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.BoundedNativeOperatorTest
public import StationaryHarmonicMaps.Analysis.ZeroBoundaryLinearMap

/-!
# Bounded native bilinear zero-boundary tests with different dimensions

A genuine finite-dimensional direct-sum encoding turns any continuous
bilinear product into an endomorphism product. Actual linear W0 transport
and the bounded native endomorphism product recover the original literal
graph, without identifying the two input/output dimensions.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

/-- A bounded original native coefficient times a bounded original native
W0 test has its literal bilinear W0 graph in the actual output dimension. -/
theorem zeroBoundary_bounded_native_bilinear_product_ball {n m q k : ℕ}
    (a : Domain n) (r : ℝ) (hr : 0<r)
    (p : Domain n → Ambient m) (Dp : Domain n → Gradient n m)
    (hp : MemW12 (ballDomain a r) p Dp) (M : ℝ)
    (hpBound : ∀ᵐx∂volume.restrict (Metric.ball a r),‖p x‖≤M)
    (B : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient k))
    (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q)
    (hφ : HasZeroBoundaryValues (ballDomain a r) φ Dφ) (H : ℝ)
    (hφBound : ∀ᵐx∂volume.restrict (Metric.ball a r),‖φ x‖≤H) :
    HasZeroBoundaryValues (ballDomain a r) (fun x=>B (p x) (φ x))
      (fun x i=>B (Dp x i) (φ x)+B (p x) (Dφ x i)) := by
  let E : (Ambient q×Ambient k)≃L[ℝ] Ambient (q+k) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let I := E.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Ambient q) (Ambient k))
  let J := E.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Ambient q) (Ambient k))
  let π := (ContinuousLinearMap.fst ℝ (Ambient q) (Ambient k)).comp E.symm.toContinuousLinearMap
  let ρ := (ContinuousLinearMap.snd ℝ (Ambient q) (Ambient k)).comp E.symm.toContinuousLinearMap
  have hπ (y : Ambient q) : π (I y)=y := by
    change (E.symm (E (y,0))).1=y
    rw [E.symm_apply_apply]
  have hρ (z : Ambient k) : ρ (J z)=z := by
    change (E.symm (E (0,z))).2=z
    rw [E.symm_apply_apply]
  let A₀ : Ambient m →ₗ[ℝ] (Ambient (q+k) →L[ℝ] Ambient (q+k)) :=
    { toFun := fun z=>J.comp ((B z).comp π)
      map_add' := by
        intro z w
        apply ContinuousLinearMap.ext
        intro y
        change J (B (z+w) (π y))=J (B z (π y))+J (B w (π y))
        rw [map_add,add_apply,map_add]
      map_smul' := by
        intro c z
        apply ContinuousLinearMap.ext
        intro y
        change J (B (c • z) (π y))=c • J (B z (π y))
        rw [map_smul,smul_apply,map_smul] }
  let A := A₀.toContinuousLinearMap
  have hValue (z : Ambient m) (y : Ambient q) : ρ (A z (I y))=B z y := by
    change ρ (J (B z (π (I y))))=B z y
    rw [hπ,hρ]
  have hLift := zeroBoundary_continuousLinearMap hφ I
  have hLiftBound : ∀ᵐx∂volume.restrict (Metric.ball a r),‖I (φ x)‖≤‖I‖*|H| := by
    filter_upwards [hφBound] with x hx
    exact (I.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hx.trans (le_abs_self H)) (norm_nonneg I))
  have hProduct := zeroBoundary_bounded_native_operator_apply_ball a r hr p Dp hp M hpBound A
    (fun x=>I (φ x)) (fun x i=>I (Dφ x i)) hLift (‖I‖*|H|) hLiftBound
  have hOut := zeroBoundary_continuousLinearMap hProduct ρ
  change HasZeroBoundaryValues (ballDomain a r) (fun x=>ρ (A (p x) (I (φ x))))
    (fun x i=>ρ (A (Dp x i) (I (φ x))+A (p x) (I (Dφ x i)))) at hOut
  simpa only [map_add,hValue] using hOut

end StationaryHarmonicMaps.Analysis

end
