module

public import HarmonicMaps.Energy
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Orthogonal invariance of the canonical scaled-polar sphere measure

The angular cone formula and preservation of Euclidean volume give equality
on every measurable sphere set. The same polar weight and radial pushforward
then preserve this invariance.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace HarmonicMaps

private theorem sphereCone_preimage {n : ℕ}
    (T : Domain n ≃ₗᵢ[ℝ] Domain n)
    (e : Metric.sphere (0 : Domain n) 1 ≃ₜ Metric.sphere (0 : Domain n) 1)
    (he : ∀ θ, (e θ).val = T θ.val)
    (s : Set (Metric.sphere (0 : Domain n) 1)) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (e ⁻¹' s)) =
      T ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext z
  constructor
  · rintro ⟨r, hr, y, ⟨θ, hθ, rfl⟩, rfl⟩
    refine ⟨r, hr, (e θ).val, ⟨e θ, hθ, rfl⟩, ?_⟩
    rw [he, T.map_smul]
  · rintro ⟨r, hr, y, ⟨θ, hθ, rfl⟩, hz⟩
    refine ⟨r, hr, (e.symm θ).val, ⟨e.symm θ, ?_, rfl⟩, ?_⟩
    · simpa only [mem_preimage, e.apply_symm_apply] using hθ
    · apply T.injective
      rw [T.map_smul, ← he, e.apply_symm_apply]
      exact hz

private theorem canonicalSphere_rotationInvariant {n : ℕ}
    (T : Domain n ≃ₗᵢ[ℝ] Domain n)
    (e : Metric.sphere (0 : Domain n) 1 ≃ₜ Metric.sphere (0 : Domain n) 1)
    (he : ∀ θ, (e θ).val = T θ.val) :
    Measure.map e (volume : Measure (Domain n)).toSphere =
      (volume : Measure (Domain n)).toSphere := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply e.measurable hs,
    (volume : Measure (Domain n)).toSphere_apply' (e.measurable hs),
    (volume : Measure (Domain n)).toSphere_apply' hs,
    sphereCone_preimage T e he s,
    T.measurePreserving.measure_preimage_emb T.toHomeomorph.measurableEmbedding]

/-- Every real linear isometry preserves the literal radius-scaled canonical
polar sphere measure, with its exact polar weight. -/
theorem poisson_scaledPolar_rotationInvariant {n : ℕ}
    (R : PositiveRadius) (T : Domain n ≃ₗᵢ[ℝ] Domain n) :
    Measure.map T
      (Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
        (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) =
      Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
        (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere) := by
  let e : Metric.sphere (0 : Domain n) 1 ≃ₜ Metric.sphere (0 : Domain n) 1 :=
    T.toHomeomorph.subtype (fun z => by
      simp only [Metric.mem_sphere, dist_zero_right]
      change ‖z‖ = 1 ↔ ‖T z‖ = 1
      rw [T.norm_map])
  have he : ∀ θ, (e θ).val = T θ.val := fun _ => rfl
  have hAngular := canonicalSphere_rotationInvariant T e he
  let β : Metric.sphere (0 : Domain n) 1 → Domain n := fun θ => R.val • θ.val
  have hβ : Measurable β :=
    ((continuous_const : Continuous (fun _ : Metric.sphere (0 : Domain n) 1 => R.val)).smul
      continuous_subtype_val).measurable
  have hComp : T ∘ β = β ∘ e := by
    funext θ
    change T (R.val • θ.val) = R.val • (e θ).val
    rw [T.map_smul, he]
  change Measure.map T (Measure.map β _) = Measure.map β _
  rw [Measure.map_map T.continuous.measurable hβ, hComp,
    ← Measure.map_map hβ e.measurable, Measure.map_smul, hAngular]

end HarmonicMaps

end
