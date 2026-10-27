module

public import StationaryHarmonicMaps.Analysis.FiniteVolumeBallRadius
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.MeasureTheory.Covering.Vitali

/-!
# A genuine countable Whitney-radius Vitali cover

The original open set and its finite volume produce a nonempty closed
complement. Radii are the actual distances to this complement divided
by twenty. A disjoint countable subfamily covers the original set after
fivefold enlargement; tenfold balls remain inside it, and nearest
complement points give the actual nearby good centers.
-/

public section

open HarmonicMaps MeasureTheory Set Metric
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The actual finite-volume open set produces a countable disjoint distance-radius family, its fivefold cover, tenfold interior balls, genuine nearest complement points and the original total-volume bound. -/
theorem exists_open_whitney_vitali_cover (n : ℕ) (hn : 0<n)
    (S : Set (Domain n)) (hOpen : IsOpen S) (hFinite : volume S≠∞) :
    let r := fun a=>Metric.infDist a Sᶜ/20
    ∃ U : Set (Domain n),U.Countable ∧ U⊆S ∧
      U.PairwiseDisjoint (fun a=>Metric.ball a (r a)) ∧
      S=⋃ a : U,Metric.ball a.val (5*r a.val) ∧
      (∀ a∈U,0<r a ∧ Metric.ball a (10*r a)⊆S ∧
        ∃ y∈Sᶜ,dist y a=20*r a) ∧
      (∑' a : U,volume (Metric.ball a.val (r a.val)))≤volume S := by
  intro r
  obtain ⟨R,_hR,hCap,hComp⟩ := exists_ball_radius_cap_of_finite_volume n hn S hFinite
  have hPos (a : Domain n) (ha : a∈S) : 0<r a := by
    apply div_pos _ (by norm_num)
    exact (hOpen.isClosed_compl.notMem_iff_infDist_pos hComp).mp (not_not_intro ha)
  have hSub10 (a : Domain n) : Metric.ball a (10*r a)⊆S := by
    apply (Metric.ball_subset_ball ?_).trans Metric.ball_infDist_compl_subset
    dsimp only [r]
    linarith only [Metric.infDist_nonneg (x := a) (s := Sᶜ)]
  have hSub (a : Domain n) (ha : a∈S) : Metric.ball a (r a)⊆S :=
    (Metric.ball_subset_ball (by linarith only [hPos a ha])).trans (hSub10 a)
  obtain ⟨U,hUS,hDisj,hCover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    S id r R (fun a ha=>hCap a (r a) (hPos a ha) (hSub a ha)) 5 (by norm_num)
  have hCount : U.Countable := hDisj.countable_of_isOpen (fun _ _=>Metric.isOpen_ball)
    (fun a ha=>⟨a,Metric.mem_ball_self (hPos a (hUS ha))⟩)
  letI : Countable U := hCount.to_subtype
  have hEq : S=⋃ a : U,Metric.ball a.val (5*r a.val) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨a,ha,hsa⟩ := hCover x hx
      exact mem_iUnion_of_mem (⟨a,ha⟩ : U) (hsa (Metric.mem_ball_self (hPos x hx)))
    · apply iUnion_subset
      intro a
      exact (Metric.ball_subset_ball (by linarith only [hPos a.val (hUS a.property)])).trans (hSub10 a.val)
  have hGood (a : Domain n) (ha : a∈U) : 0<r a ∧ Metric.ball a (10*r a)⊆S ∧
      ∃ y∈Sᶜ,dist y a=20*r a := by
    obtain ⟨y,hy,hDist⟩ := hOpen.isClosed_compl.exists_infDist_eq_dist hComp a
    refine ⟨hPos a (hUS ha),hSub10 a,y,hy,?_⟩
    rw [dist_comm,← hDist]
    dsimp only [r]
    ring
  have hSmallDisj : Pairwise (fun a b : U=>Disjoint
      (Metric.ball a.val (r a.val)) (Metric.ball b.val (r b.val))) := hDisj.subtype
  have hSum : (∑' a : U,volume (Metric.ball a.val (r a.val)))≤volume S := by
    rw [← measure_iUnion hSmallDisj (fun _=>measurableSet_ball)]
    apply measure_mono
    exact iUnion_subset (fun a=>hSub a.val (hUS a.property))
  exact ⟨U,hCount,hUS,hDisj,hEq,hGood,hSum⟩

end StationaryHarmonicMaps.Analysis

end
