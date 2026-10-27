module

public import HarmonicMaps.Sobolev
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! # Compactness makes uniformly disjoint positive-radius centers finite -/

public section

open HarmonicMaps Set

namespace StationaryHarmonicMaps.Analysis

/-- Actual disjoint balls of one positive radius have only finitely many centers inside a compact set. -/
theorem finite_centers_of_disjoint_uniform_balls {n : ℕ}
    (T K : Set (Domain n)) (hK : IsCompact K) (hTK : T⊆K)
    (ε : ℝ) (hε : 0<ε) (hDisj : T.PairwiseDisjoint (fun a=>Metric.ball a ε)) : T.Finite := by
  obtain ⟨F,_hFK,hFinite,hCover⟩ := hK.finite_cover_balls (half_pos hε)
  have hSingle (z : Domain n) : (T∩Metric.ball z (ε/2)).Subsingleton := by
    intro a ha b hb
    by_contra hne
    have hDist : dist a b<ε := by
      have haDist : dist a z<ε/2 := ha.2
      have hbDist : dist z b<ε/2 := by simpa only [Metric.mem_ball,dist_comm] using hb.2
      have hTri := dist_triangle a z b
      linarith only [haDist,hbDist,hTri]
    exact (Set.disjoint_left.mp (hDisj ha.1 hb.1 hne)) (Metric.mem_ball_self hε) hDist
  have hUnion : (⋃ z∈F,T∩Metric.ball z (ε/2)).Finite :=
    hFinite.biUnion (fun z _=> (hSingle z).finite)
  apply hUnion.subset
  intro a ha
  obtain ⟨z,hz⟩ := mem_iUnion.mp (hCover (hTK ha))
  obtain ⟨hzF,haz⟩ := mem_iUnion.mp hz
  exact mem_iUnion_of_mem z (mem_iUnion_of_mem hzF ⟨ha,haz⟩)

end StationaryHarmonicMaps.Analysis

end
