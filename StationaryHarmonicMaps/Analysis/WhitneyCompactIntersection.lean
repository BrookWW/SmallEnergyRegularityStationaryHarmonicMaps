module

public import StationaryHarmonicMaps.Analysis.WhitneyBallOverlap

/-!
# Actual finite intersections with a compact interior support

Relative local finiteness of the original Whitney balls is applied on
the original compact set. A genuine finite neighborhood subcover shows
that only finitely many original balls meet that set. This controls the
low-index direction of cross-level atomic correction sums.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual disjoint Whitney balls have only finitely many tenfold members meeting a supplied compact subset of the original open set. -/
theorem finite_whitney_balls_intersecting_compact {n : ℕ}
    (S U : Set (Domain n)) (hOpen : IsOpen S) (hComp : Sᶜ.Nonempty)
    (hDisj : U.PairwiseDisjoint (fun a=>Metric.ball a (Metric.infDist a Sᶜ/20)))
    (K : Set (Domain n)) (hK : IsCompact K) (hKS : K⊆S) :
    {a∈U | (Metric.ball a (10*(Metric.infDist a Sᶜ/20))∩K).Nonempty}.Finite := by
  classical
  choose V hV hFin using (fun x : K=>locallyFiniteWithin_whitney_tenfold_balls S U hOpen hComp hDisj x.val (hKS x.property))
  obtain ⟨t,hCover⟩ := hK.elim_nhds_subcover' (fun x hx=>V ⟨x,hx⟩) (fun x hx=>hV ⟨x,hx⟩)
  have hUnion : (⋃ x∈(t : Set K),{a∈U | (Metric.ball a (10*(Metric.infDist a Sᶜ/20))∩V x).Nonempty}).Finite :=
    t.finite_toSet.biUnion (fun x _=>hFin x)
  apply hUnion.subset
  intro a ha
  obtain ⟨z,hzBall,hzK⟩ := ha.2
  obtain ⟨x,hxz⟩ := mem_iUnion.mp (hCover hzK)
  obtain ⟨hxt,hzV⟩ := mem_iUnion.mp hxz
  exact mem_iUnion_of_mem x (mem_iUnion_of_mem hxt ⟨ha.1,z,hzBall,hzV⟩)

end StationaryHarmonicMaps.Analysis

end
