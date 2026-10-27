module

public import StationaryHarmonicMaps.Geometry.SkewExponential
public import StationaryHarmonicMaps.Geometry.OrientationDeterminant
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Orientation of the actual exponential of a skew real operator -/

public section

open HarmonicMaps Set
open scoped Topology

namespace StationaryHarmonicMaps

/-- The continuous exponential path starts at the identity and keeps the
positive determinant sign among actual orthogonal operators. -/
theorem operator_exp_det_eq_one_of_skew {q : ℕ}
    (S : Ambient q→L[ℝ]Ambient q) (hS : star S=-S) (t : ℝ) :
    (NormedSpace.exp (t • S)).det=1 := by
  let f : ℝ→ℝ := fun s=>(NormedSpace.exp (s • S)).det
  have hf : Continuous f := (contDiff_operator_det q).continuous.comp
    ((contDiff_operator_exp q).continuous.comp (continuous_id.smul continuous_const))
  have hRange : MapsTo f univ ({1,-1} : Set ℝ) := by
    intro s _
    have H := operator_det_eq_one_or_neg_one (NormedSpace.exp (s • S))
      (operator_exp_orthogonal_of_skew S hS s).1
    simpa only [mem_insert_iff,mem_singleton_iff,f] using H
  have hEq : f t=f 0 := isPreconnected_univ.constant_of_mapsTo
    (Set.toFinite ({1,-1} : Set ℝ)).isDiscrete hf.continuousOn hRange (mem_univ t) (mem_univ 0)
  have hZero : f 0=1 := by
    change (NormedSpace.exp ((0 : ℝ) • S)).det=1
    have hS0 : (0 : ℝ) • S=(0 : Ambient q→L[ℝ]Ambient q) := by
      apply ContinuousLinearMap.ext
      intro x
      change (0 : ℝ) • S x=0
      exact _root_.zero_smul ℝ (S x)
    rw [hS0,NormedSpace.exp_zero]
    change LinearMap.det (1 : Module.End ℝ (Ambient q))=1
    exact map_one _
  exact hEq.trans hZero

end StationaryHarmonicMaps
