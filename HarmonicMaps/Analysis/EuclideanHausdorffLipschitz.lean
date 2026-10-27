module

public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Euclidean Hausdorff measure bounds for Lipschitz charts

A Lipschitz chart bounds normalized Hausdorff measure of every image set by
source volume. A Lipschitz inverse on the chart carrier gives the reverse
bound. The normalization is the native Euclidean Hausdorff normalization in
the dimension of the source inner product space.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Module
open scoped ENNReal NNReal

namespace HarmonicMaps

private theorem normalizedHausdorff_lipschitz_image_le
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (d : ℕ) {L : ℝ≥0} {f : X → Y} {s : Set X} (hf : LipschitzOnWith L f s) :
    (euclideanHausdorffMeasure d : Measure Y) (f '' s) ≤
      (L : ℝ≥0∞) ^ d * (euclideanHausdorffMeasure d : Measure X) s := by
  have h := hf.hausdorffMeasure_image_le (d := (d : ℝ)) (Nat.cast_nonneg d)
  simp only [ENNReal.rpow_natCast] at h
  simp only [euclideanHausdorffMeasure_def, Measure.smul_apply, nnreal_smul_coe_apply]
  calc
    _ ≤ _ := mul_le_mul_right h _
    _ = _ := mul_left_comm _ _ _

private theorem normalizedHausdorff_le_antilipschitz_image
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (d : ℕ) {K : ℝ≥0} {f : X → Y} (hf : AntilipschitzWith K f) (s : Set X) :
    (euclideanHausdorffMeasure d : Measure X) s ≤
      (K : ℝ≥0∞) ^ d * (euclideanHausdorffMeasure d : Measure Y) (f '' s) := by
  have h := hf.le_hausdorffMeasure_image (d := (d : ℝ)) (Nat.cast_nonneg d) s
  simp only [ENNReal.rpow_natCast] at h
  simp only [euclideanHausdorffMeasure_def, Measure.smul_apply, nnreal_smul_coe_apply]
  calc
    _ ≤ _ := mul_le_mul_right h _
    _ = _ := mul_left_comm _ _ _

/-- A chart Lipschitz on its actual carrier bounds the normalized Hausdorff
measure of every image subset by the actual source volume. -/
theorem euclideanHausdorff_lipschitzOn_image_le_volume
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [EMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {f : H → E} {patch S : Set H} {L : ℝ≥0}
    (hf : LipschitzOnWith L f patch) (hS : S ⊆ patch) :
    (euclideanHausdorffMeasure (finrank ℝ H) : Measure E) (f '' S) ≤
      (L : ℝ≥0∞) ^ (finrank ℝ H) * (volume : Measure H) S := by
  simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
    normalizedHausdorff_lipschitz_image_le (finrank ℝ H) (hf.mono hS)

/-- An antilipschitz chart on its actual subtype carrier gives the reverse
normalized Hausdorff bound for every subset of that carrier. -/
theorem volume_le_euclideanHausdorff_image_of_antilipschitzOn
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [EMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {f : H → E} {patch S : Set H} {K : ℝ≥0}
    (hf : AntilipschitzWith K (fun x : patch => f x.val)) (hS : S ⊆ patch) :
    (volume : Measure H) S ≤ (K : ℝ≥0∞) ^ (finrank ℝ H) *
      (euclideanHausdorffMeasure (finrank ℝ H) : Measure E) (f '' S) := by
  let T : Set patch := Subtype.val ⁻¹' S
  have hT : (Subtype.val : patch → H) '' T = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hS hx⟩, hx, rfl⟩
  have hImage : (fun x : patch => f x.val) '' T = f '' S := by
    rw [← hT, image_image]
  have h := normalizedHausdorff_le_antilipschitz_image (finrank ℝ H) hf T
  rw [hImage] at h
  have hMeasure : (euclideanHausdorffMeasure (finrank ℝ H) : Measure patch) T =
      (volume : Measure H) S := by
    rw [← isometry_subtype_coe.euclideanHausdorffMeasure_image T, hT,
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  rwa [hMeasure] at h

/-- A pointwise inverse distance bound on the chart carrier suffices for the
reverse normalized Hausdorff estimate, with no measurability premise on S. -/
theorem volume_le_euclideanHausdorff_image_of_dist_le
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {f : H → E} {patch S : Set H} {K : ℝ≥0}
    (hf : ∀ x ∈ patch, ∀ y ∈ patch, dist x y ≤ K * dist (f x) (f y))
    (hS : S ⊆ patch) :
    (volume : Measure H) S ≤ (K : ℝ≥0∞) ^ (finrank ℝ H) *
      (euclideanHausdorffMeasure (finrank ℝ H) : Measure E) (f '' S) := by
  apply volume_le_euclideanHausdorff_image_of_antilipschitzOn (K := K) ?_ hS
  exact AntilipschitzWith.of_le_mul_dist (fun x y => hf x.val x.property y.val y.property)

end HarmonicMaps
end
