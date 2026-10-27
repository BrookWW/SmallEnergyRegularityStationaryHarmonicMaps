module

public import StationaryHarmonicMaps.Analysis.C1MixedPostcomposition
public import HarmonicMaps.Analysis.SobolevLocality
public import HarmonicMaps.SobolevRestriction
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual Sobolev compositions of compact variations

A compact C¹ field on the domain-target product has bounded derivative and
bounded values. Its actual composition with a local Sobolev map has the
mixed weak columns. Compact projection of its support gives genuine zero
boundary values on every ball containing that projection.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The actual composed field has compact support in the projection of the field support. -/
theorem variationComposition_tsupport_subset {n q : ℕ}
    (u : Domain n → Ambient q) (V : Domain n × Ambient q → Ambient q)
    (hcV : HasCompactSupport V) :
    tsupport (fun x => V (x, u x)) ⊆ Prod.fst '' tsupport V := by
  apply closure_minimal _ (hcV.image continuous_fst).isClosed
  intro x hx
  exact ⟨(x, u x), subset_tsupport V hx, rfl⟩

/-- Compact C¹ fields give genuine mixed local Sobolev compositions. -/
theorem memW12Loc_variationComposition {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (V : Domain n × Ambient q → Ambient q) (hV : ContDiff ℝ 1 V)
    (hcV : HasCompactSupport V) :
    MemW12Loc Ω (fun x => V (x, u x))
      (fun x i => fderiv ℝ V (x, u x) (EuclideanSpace.single i 1, Du x i)) := by
  obtain ⟨L, hL⟩ := (hcV.fderiv ℝ).exists_bound_of_continuous
    (hV.continuous_fderiv (by simp))
  exact memW12Loc_mixed_postcompose_c1 hu V hV hL

/-- Interior projected support produces actual zero-boundary and bounded test data. -/
theorem variationComposition_zeroBoundary_ball {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {a : Domain n} {r : ℝ} (hr : 0 < r)
    (hclosed : Metric.closedBall a r ⊆ Ω.val)
    (V : Domain n × Ambient q → Ambient q) (hV : ContDiff ℝ 1 V)
    (hcV : HasCompactSupport V) (hsV : Prod.fst '' tsupport V ⊆ Metric.ball a r) :
    HasZeroBoundaryValues (ballDomain a r) (fun x => V (x, u x))
      (fun x i => fderiv ℝ V (x, u x) (EuclideanSpace.single i 1, Du x i)) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖V (x, u x)‖ ≤ M := by
  have hW := (memW12Loc_variationComposition hu V hV hcV).memW12_ball hclosed
  have hts := variationComposition_tsupport_subset u V hcV
  have hc : HasCompactSupport (fun x => V (x, u x)) :=
    (hcV.image continuous_fst).of_isClosed_subset (isClosed_tsupport _) hts
  obtain ⟨M, hM⟩ := hcV.exists_bound_of_continuous hV.continuous
  exact ⟨hW.zeroBoundary_of_compactSupport_ball hr hc (hts.trans hsV),
    M, (norm_nonneg _).trans (hM (0, 0)), fun x => hM (x, u x)⟩

end StationaryHarmonicMaps.Analysis

end
