module

public import HarmonicMaps.Analysis.MorreyHolder
public import HarmonicMaps.Analysis.ContinuousRepresentativeLocality

/-! # The complete generic Morrey representative theorem

The original finite Sobolev map and HS growth hypothesis supply one
all-radius mean representative. Positive-volume subtype locality proves
full uniqueness and membership in every closed almost-everywhere target.
-/

public section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

namespace HarmonicMaps

/-- The full source Morrey conclusion, with one constant before every map and target parameter. -/
theorem morrey_representative (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ (q : ℕ) (f : Domain n → Ambient q) (Df : Domain n → Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) f Df → ∀ (M : ℝ), 0 ≤ M →
      (∀ (x : Domain n), x ∈ Metric.ball (0 : Domain n) (1 / 2) →
        ∀ (r : PositiveRadius), r.val ≤ (1 / 2 : ℝ) →
          (∫ y in Metric.ball x r.val, hsNormSq (Df y)) ≤
            M * Real.rpow r.val ((n : ℝ) - 2 + 2 * α)) →
      ∃ w : Metric.ball (0 : Domain n) (1 / 2) → Ambient q,
        IsContinuousRepresentative (ballDomain (0 : Domain n) (1 / 2)) f w ∧
        (∀ (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2)),
          Tendsto (fun r : ℝ => (volume (Metric.ball x r)).toReal⁻¹ •
            (∫ y in Metric.ball x r, f y)) (𝓝[>] (0 : ℝ)) (𝓝 (w ⟨x, hx⟩))) ∧
        (∀ x y : Metric.ball (0 : Domain n) (1 / 2),
          ‖w x - w y‖ ≤ (C : ℝ) * Real.sqrt M *
            Real.rpow (dist (x : Domain n) (y : Domain n)) α) ∧
        (∀ v : Metric.ball (0 : Domain n) (1 / 2) → Ambient q,
          IsContinuousRepresentative (ballDomain (0 : Domain n) (1 / 2)) f v → v = w) ∧
        (∀ K : Set (Ambient q), IsClosed K →
          (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), f x ∈ K) →
          ∀ x, w x ∈ K) := by
  obtain ⟨C, hC⟩ := morrey_holder n hn α hα hα1
  refine ⟨C, ?_⟩
  intro q f Df hf M hM hgrowth
  obtain ⟨w, hw, hlimit, hholder⟩ := hC q f Df hf M hM hgrowth
  refine ⟨w, hw, hlimit, hholder, ?_, ?_⟩
  · intro v hv
    exact hv.unique hw
  · intro K hK hfK
    have hinnerK : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) (1 / 2)), f x ∈ K :=
      hfK.filter_mono (ae_mono (Measure.restrict_mono_set volume
        (Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1))))
    exact hw.mem_closed_of_ae K hK hinnerK

end HarmonicMaps
