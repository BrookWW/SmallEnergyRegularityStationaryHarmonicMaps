module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Genuine L² products with essentially bounded ring factors -/

public section

open MeasureTheory Filter

namespace StationaryHarmonicMaps.Analysis

/-- A measurable essentially bounded left factor preserves actual L² membership. -/
theorem memLp_two_bounded_mul_left {X B : Type*} [MeasurableSpace X] [NormedRing B]
    {μ : Measure X} {P Q : X → B} {C : ℝ}
    (hP : AEStronglyMeasurable P μ) (hb : ∀ᵐ x ∂μ, ‖P x‖ ≤ C)
    (hQ : MemLp Q 2 μ) : MemLp (fun x => P x * Q x) 2 μ := by
  apply hQ.of_le_mul (c := C) (hP.mul hQ.aestronglyMeasurable)
  filter_upwards [hb] with x hx
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

/-- A measurable essentially bounded right factor preserves actual L² membership. -/
theorem memLp_two_bounded_mul_right {X B : Type*} [MeasurableSpace X] [NormedRing B]
    {μ : Measure X} {P Q : X → B} {C : ℝ}
    (hP : AEStronglyMeasurable P μ) (hb : ∀ᵐ x ∂μ, ‖P x‖ ≤ C)
    (hQ : MemLp Q 2 μ) : MemLp (fun x => Q x * P x) 2 μ := by
  apply hQ.of_le_mul (c := C) (hQ.aestronglyMeasurable.mul hP)
  filter_upwards [hb] with x hx
  exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans_eq
    (mul_comm _ _))

/-- Two actual bounded factors control a sum of the connection's L² products. -/
theorem memLp_two_bounded_connection {X B : Type*} [MeasurableSpace X] [NormedRing B]
    {μ : Measure X} {P Q D A : X → B} {C C' : ℝ}
    (hP : AEStronglyMeasurable P μ) (hbP : ∀ᵐ x ∂μ, ‖P x‖ ≤ C)
    (hQ : AEStronglyMeasurable Q μ) (hbQ : ∀ᵐ x ∂μ, ‖Q x‖ ≤ C')
    (hD : MemLp D 2 μ) (hA : MemLp A 2 μ) :
    MemLp (fun x => Q x * D x + Q x * A x * P x) 2 μ :=
  (memLp_two_bounded_mul_left hQ hbQ hD).add
    (memLp_two_bounded_mul_right hP hbP (memLp_two_bounded_mul_left hQ hbQ hA))

end StationaryHarmonicMaps.Analysis

end
