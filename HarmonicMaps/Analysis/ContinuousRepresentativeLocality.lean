module

public import HarmonicMaps.Representative
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Continuous representatives on actual open-domain subtypes

The induced subtype measure is positive on nonempty open sets. Actual
almost-everywhere agreement therefore gives uniqueness of every continuous
representative and transfers membership in any closed target set.
-/

public section

open MeasureTheory Filter Set

namespace HarmonicMaps

/-- The defining almost-everywhere agreement holds on the actual domain subtype. -/
theorem IsContinuousRepresentative.ae_subtype {n q : ℕ} {Ω : OpenDomain n}
    {f : Domain n → Ambient q} {w : Ω.val → Ambient q}
    (hw : IsContinuousRepresentative Ω f w) :
    ∀ᵐ x : Ω.val ∂volume.comap (Subtype.val : Ω.val → Domain n), w x = f x.val := by
  filter_upwards [(ae_restrict_iff_subtype Ω.property.measurableSet).1 hw.2] with x hx
  exact hx x.property

/-- Every pair of continuous almost-everywhere representatives agrees on its domain. -/
theorem IsContinuousRepresentative.unique {n q : ℕ} {Ω : OpenDomain n}
    {f : Domain n → Ambient q} {w v : Ω.val → Ambient q}
    (hw : IsContinuousRepresentative Ω f w)
    (hv : IsContinuousRepresentative Ω f v) : w = v := by
  let μ : Measure Ω.val := volume.comap (Subtype.val : Ω.val → Domain n)
  letI : μ.IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap volume Ω.property.isOpenEmbedding_subtypeVal
  have heq : w =ᵐ[μ] v := by
    filter_upwards [hw.ae_subtype, hv.ae_subtype] with x hx hvx
    exact hx.trans hvx.symm
  exact Measure.eq_of_ae_eq heq hw.1 hv.1

/-- A continuous representative of an almost-everywhere closed-set-valued map
belongs to that set at every point, without a nonemptiness premise. -/
theorem IsContinuousRepresentative.mem_closed_of_ae {n q : ℕ} {Ω : OpenDomain n}
    {f : Domain n → Ambient q} {w : Ω.val → Ambient q}
    (hw : IsContinuousRepresentative Ω f w) (K : Set (Ambient q))
    (hK : IsClosed K) (hfK : ∀ᵐ x ∂volume.restrict Ω.val, f x ∈ K) :
    ∀ x : Ω.val, w x ∈ K := by
  let μ : Measure Ω.val := volume.comap (Subtype.val : Ω.val → Domain n)
  letI : μ.IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap volume Ω.property.isOpenEmbedding_subtypeVal
  have hwK : ∀ᵐ x : Ω.val ∂μ, w x ∈ K := by
    filter_upwards [hw.ae_subtype,
      (ae_restrict_iff_subtype Ω.property.measurableSet).1 hfK] with x hx hKx
    exact hx.symm ▸ hKx
  have heq : w ⁻¹' K = Set.univ :=
    ((hK.preimage hw.1).ae_eq_univ_iff_eq (μ := μ)).1 (ae_eq_univ.2 hwK)
  intro x
  have hx : x ∈ w ⁻¹' K := by rw [heq]; exact mem_univ x
  exact hx

/-- Positive ball volume produces a target point from the original AE values. -/
theorem set_nonempty_of_ae_mem_ball {n q : ℕ} {a : Domain n} {R : ℝ}
    (hR : 0 < R) (f : Domain n → Ambient q) (K : Set (Ambient q))
    (hfK : ∀ᵐ x ∂volume.restrict (Metric.ball a R), f x ∈ K) : K.Nonempty := by
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (Metric.measure_ball_pos volume a hR).ne' hfK
  exact ⟨f x, hx⟩

end HarmonicMaps
