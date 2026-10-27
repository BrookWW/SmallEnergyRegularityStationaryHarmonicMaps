module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Equality of measures from sharp local comparisons

On a compact space, inequalities between restrictions to an open neighborhood
of every point imply the corresponding global measure inequality. Two measures
are equal if these local comparisons hold in both directions with every real
factor greater than one. No finite-mass hypothesis is required.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace HarmonicMaps

/-- Domination of measures on open neighborhoods patches to global domination
on a compact space. -/
theorem measure_le_of_locally_restrict_le {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ ν : Measure X)
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ μ.restrict U ≤ ν.restrict U) :
    μ ≤ ν := by
  classical
  choose U hU hx hle using h
  have hcover : (univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have htotal : (⋃ x ∈ t, U x) = univ := subset_antisymm (subset_univ _) ht
  have heq (x : X) : (μ ⊓ ν).restrict (U x) = μ.restrict (U x) := by
    rw [← sInf_pair, Measure.restrict_sInf_eq_sInf_restrict (by simp) (hU x).measurableSet]
    simpa only [image_pair, sInf_pair] using inf_eq_left.mpr (hle x)
  have hall : (μ ⊓ ν).restrict (⋃ x ∈ t, U x) = μ.restrict (⋃ x ∈ t, U x) :=
    Measure.restrict_biUnion_finset_congr.mpr (fun x _ => heq x)
  rw [htotal, Measure.restrict_univ, Measure.restrict_univ] at hall
  exact inf_eq_left.mp hall

/-- Arbitrarily sharp local comparison of two measures on a compact space
implies equality of the complete measures. -/
theorem measure_eq_of_locally_arbitrarily_sharp_comparison {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ ν : Measure X)
    (h : ∀ C : ℝ, 1 < C → ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      μ.restrict U ≤ ENNReal.ofReal C • ν.restrict U ∧
      ν.restrict U ≤ ENNReal.ofReal C • μ.restrict U) : μ = ν := by
  have hglobal (C : ℝ) (hC : 1 < C) :
      μ ≤ ENNReal.ofReal C • ν ∧ ν ≤ ENNReal.ofReal C • μ := by
    constructor
    · apply measure_le_of_locally_restrict_le
      intro x
      obtain ⟨U, hU, hx, hμ, _⟩ := h C hC x
      exact ⟨U, hU, hx, by simpa only [Measure.restrict_smul] using hμ⟩
    · apply measure_le_of_locally_restrict_le
      intro x
      obtain ⟨U, hU, hx, _, hν⟩ := h C hC x
      exact ⟨U, hU, hx, by simpa only [Measure.restrict_smul] using hν⟩
  have hbound (ρ σ : Measure X) (hρ : ∀ C : ℝ, 1 < C → ρ ≤ ENNReal.ofReal C • σ) :
      ρ ≤ σ := by
    apply Measure.le_iff'.mpr
    intro s
    have hlim : Tendsto (fun C : ℝ => ENNReal.ofReal C) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ≥0∞)) := by
      simpa only [ENNReal.ofReal_one] using
        (ENNReal.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    have hprod := ENNReal.Tendsto.mul_const hlim (b := σ s) (Or.inl one_ne_zero)
    rw [one_mul] at hprod
    apply ge_of_tendsto hprod
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards with C hC
    exact Measure.le_iff'.mp (hρ C hC) s
  exact le_antisymm (hbound μ ν (fun C hC => (hglobal C hC).1))
    (hbound ν μ (fun C hC => (hglobal C hC).2))

end HarmonicMaps
end
