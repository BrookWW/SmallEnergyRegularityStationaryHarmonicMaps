module

public import StationaryHarmonicMaps.Analysis.OpenWhitneyVitaliCover
public import StationaryHarmonicMaps.Analysis.UniformBallPacking

/-!
# Actual finite overlap and relative local finiteness of Whitney balls

The literal radius is distance to the complement divided by twenty.
Whenever a twelvefold ball contains a fixed interior point, the original
radii are uniformly positive and the original centers lie in a fixed
compact ball. The genuinely disjoint original balls give finite overlap.
A strict interior neighborhood then gives relative local finiteness of
the tenfold family, without a global boundedness assumption.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual distance radii and disjoint original balls produce finite twelvefold overlap at every original interior point. -/
theorem finite_whitney_twelvefold_overlap {n : ℕ}
    (S U : Set (Domain n)) (hOpen : IsOpen S) (hComp : Sᶜ.Nonempty)
    (hDisj : U.PairwiseDisjoint (fun a=>Metric.ball a (Metric.infDist a Sᶜ/20)))
    (x : Domain n) (hx : x∈S) :
    {a∈U | x∈Metric.ball a (12*(Metric.infDist a Sᶜ/20))}.Finite := by
  let r := fun a=>Metric.infDist a Sᶜ/20
  let δ := Metric.infDist x Sᶜ
  let T := {a∈U | x∈Metric.ball a (12*r a)}
  have hδ : 0<δ := (hOpen.isClosed_compl.notMem_iff_infDist_pos hComp).mp (not_not_intro hx)
  have hBounds (a : Domain n) (ha : a∈T) : δ/40<r a ∧ dist a x≤2*δ := by
    have hDist : dist x a<12*r a := ha.2
    have hInf1 := Metric.infDist_le_infDist_add_dist (x := a) (y := x) (s := Sᶜ)
    have hInf2 := Metric.infDist_le_infDist_add_dist (x := x) (y := a) (s := Sᶜ)
    have hRa : Metric.infDist a Sᶜ=20*r a := by dsimp only [r];ring
    rw [hRa,dist_comm] at hInf1
    rw [hRa] at hInf2
    change 20*r a≤δ+dist x a at hInf1
    change δ≤20*r a+dist x a at hInf2
    constructor
    · linarith only [hInf2,hDist,hδ]
    · rw [dist_comm]
      linarith only [hInf1,hDist,hδ]
  have hSub : T⊆Metric.closedBall x (2*δ) := fun a ha=>(hBounds a ha).2
  have hSmallDisj : T.PairwiseDisjoint (fun a=>Metric.ball a (δ/40)) := by
    intro a ha b hb hne
    exact (hDisj ha.1 hb.1 hne).mono (Metric.ball_subset_ball (hBounds a ha).1.le)
      (Metric.ball_subset_ball (hBounds b hb).1.le)
  exact finite_centers_of_disjoint_uniform_balls T (Metric.closedBall x (2*δ))
    (isCompact_closedBall _ _) hSub (δ/40) (by positivity) hSmallDisj

/-- Original disjoint Whitney balls have a genuinely locally finite tenfold family relative to the original open set. -/
theorem locallyFiniteWithin_whitney_tenfold_balls {n : ℕ}
    (S U : Set (Domain n)) (hOpen : IsOpen S) (hComp : Sᶜ.Nonempty)
    (hDisj : U.PairwiseDisjoint (fun a=>Metric.ball a (Metric.infDist a Sᶜ/20))) :
    ∀ x∈S,∃ V∈𝓝 x,
      {a∈U | (Metric.ball a (10*(Metric.infDist a Sᶜ/20))∩V).Nonempty}.Finite := by
  intro x hx
  let δ := Metric.infDist x Sᶜ
  let r := fun a=>Metric.infDist a Sᶜ/20
  have hδ : 0<δ := (hOpen.isClosed_compl.notMem_iff_infDist_pos hComp).mp (not_not_intro hx)
  refine ⟨Metric.ball x (δ/100),Metric.ball_mem_nhds x (by positivity),?_⟩
  apply (finite_whitney_twelvefold_overlap S U hOpen hComp hDisj x hx).subset
  intro a ha
  refine ⟨ha.1,?_⟩
  obtain ⟨z,hza,hzx⟩ := ha.2
  have hzaDist : dist z a<10*r a := hza
  have hzxDist : dist x z<δ/100 := by simpa only [Metric.mem_ball,dist_comm] using hzx
  have hTri := dist_triangle x z a
  have hBound : dist x a<δ/100+10*r a := lt_of_le_of_lt hTri (add_lt_add hzxDist hzaDist)
  have hInf := Metric.infDist_le_infDist_add_dist (x := x) (y := a) (s := Sᶜ)
  have hRa : Metric.infDist a Sᶜ=20*r a := by dsimp only [r];ring
  rw [hRa] at hInf
  change δ≤20*r a+dist x a at hInf
  change dist x a<12*r a
  have hDist0 : 0≤dist x a := dist_nonneg
  linarith only [hBound,hInf,hDist0]

end StationaryHarmonicMaps.Analysis

end
