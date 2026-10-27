module

public import StationaryHarmonicMaps.Analysis.BoundedNativeOperatorTest
public import StationaryHarmonicMaps.Analysis.CriticalMorreyMeanOscillation
public import HarmonicMaps.Analysis.SobolevDifference

/-!
# Native frame products on a query ball

A bounded native zero-boundary cutoff on a parent ball gives the literal
frame product there. Restriction and a fixed-vector native linear graph
then give the mean-subtracted product on each query ball.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Fixed-vector evaluation of the encoded operator acts on the same finite
native weak-gradient graph. -/
theorem native_operator_apply_const {n m q : ℕ} {Ω : OpenDomain n}
    {p : Domain n → Ambient m} {Dp : Domain n → Gradient n m}
    (hp : MemW12 Ω p Dp)
    (L : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q)) (c : Ambient q) :
    MemW12 Ω (fun x => L (p x) c) (fun x i => L (Dp x i) c) := by
  let A : Ambient m →L[ℝ] Ambient q := L.flip c
  exact ⟨memW12Loc_continuousLinearMap hp.to_memW12Loc A |>.1,
    A.lipschitz.comp_memLp (map_zero A) hp.2.1,
    fun i => A.lipschitz.comp_memLp (map_zero A) (hp.2.2 i)⟩

/-- A bounded native frame times the original bounded parent-ball W0 cutoff,
minus any constant, has its actual Leibniz graph on every query ball. -/
theorem native_frame_cutoff_sub_constant_test_ball {n m q : ℕ}
    (a : Domain n) (R : ℝ) (hR : 0<R)
    (p : Domain n → Ambient m) (Dp : Domain n → Gradient n m)
    (hp : MemW12 (ballDomain a R) p Dp) (M : ℝ)
    (hpBound : ∀ᵐ x ∂volume.restrict (ball a R),‖p x‖≤M)
    (L : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q)
    (hv : HasZeroBoundaryValues (ballDomain a R) v Dv) (N : ℝ)
    (hvBound : ∀ᵐ x ∂volume.restrict (ball a R),‖v x‖≤N)
    (b : Domain n) (t : ℝ) (hSub : ball b t ⊆ ball a R) (c : Ambient q) :
    MemW12 (ballDomain b t) (fun x => L (p x) (v x-c))
      (fun x i => L (Dp x i) (v x-c)+L (p x) (Dv x i)) := by
  have hProduct := zeroBoundary_bounded_native_operator_apply_ball a R hR
    p Dp hp M hpBound L v Dv hv N hvBound
  have hConst := native_operator_apply_const hp L c
  have hDifference := hProduct.1.sub hConst
  have hWhole : MemW12 (ballDomain a R) (fun x => L (p x) (v x-c))
      (fun x i => L (Dp x i) (v x-c)+L (p x) (Dv x i)) := by
    convert hDifference using 1
    · funext x
      exact map_sub (L (p x)) (v x) c
    · funext x i
      simp only [map_sub]
      abel
  exact memW12_of_openDomain_subset hWhole hSub

end StationaryHarmonicMaps.Analysis
end
