module

public import HarmonicMaps.Minimizer
public import HarmonicMaps.Analysis.FiniteEnergyGradient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Finite Sobolev membership on the unit ball

Compact target membership bounds the map almost everywhere. Together with
the unit ball's finite volume and the existing weak-gradient measurability,
this gives global map L2 control. Finite extended HS energy supplies global
L2 control of the same displayed gradient columns.

The result supplies whole-ball Sobolev membership for convolution smoothing. It does not use local
minimality, stationarity, target projections, or a regularity conclusion.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace HarmonicMaps

/-- A local Sobolev map with a.e. compact-target values is L2 on the unit ball. -/
theorem MemW12Loc.memLp_unitBall_of_targetValues
    {n q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc (ballDomain (0 : Domain n) 1) u Du)
    (hN : TakesValuesIn N (ballDomain (0 : Domain n) 1) u) :
    MemLp u 2 (volume.restrict (Metric.ball (0 : Domain n) 1)) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Domain n) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  obtain ⟨C, _hC, hbound⟩ := N.isCompact.isBounded.exists_pos_norm_le
  have hu_meas : AEStronglyMeasurable u
      (volume.restrict (Metric.ball (0 : Domain n) 1)) :=
    hu.1.1.aestronglyMeasurable
  have hu_bound : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      ‖u x‖ ≤ C := by
    filter_upwards [hN] with x hx
    exact hbound (u x) hx
  exact MemLp.of_bound hu_meas C hu_bound

/-- Local W1,2, compact-target values and finite total HS energy imply finite
W1,2 on the unit ball, using exactly the input weak gradient. -/
theorem MemW12Loc.memW12_unitBall_of_finiteEnergy
    {n q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc (ballDomain (0 : Domain n) 1) u Du)
    (hN : TakesValuesIn N (ballDomain (0 : Domain n) 1) u)
    (hE : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤) :
    MemW12 (ballDomain (0 : Domain n) 1) u Du := by
  refine ⟨hu.1, hu.memLp_unitBall_of_targetValues N hN, ?_⟩
  exact hu.memLp_gradient_columns_unitBall_of_finiteEnergy hE

end HarmonicMaps

end
