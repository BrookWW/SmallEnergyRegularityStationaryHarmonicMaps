module

public import StationaryHarmonicMaps.Analysis.WhitneyBallOverlap

/-!
# A genuine dimension-only bound for Whitney overlap

The actual tenfold overlap has original radii greater than one thirtieth
of the distance of the fixed point to the complement. Disjoint equal
small balls fit in the ball of sixty times that radius. Their actual
Euclidean volumes give the uniform cardinal bound 60 to the dimension.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem uniform_ball_card_bound {n : ℕ} (T : Set (Domain n)) (hT : T.Finite)
    (x : Domain n) (ε : ℝ) (hε : 0<ε)
    (hDisj : T.PairwiseDisjoint (fun a=>Metric.ball a ε))
    (hSub : ∀ a∈T,Metric.ball a ε⊆Metric.ball x (60*ε)) : T.ncard≤60^n := by
  letI : Fintype T := hT.fintype
  have hVolume : (∑' a : T,volume (Metric.ball a.val ε))≤volume (Metric.ball x (60*ε)) := by
    rw [← measure_iUnion hDisj.subtype (fun _=>measurableSet_ball)]
    exact measure_mono (iUnion_subset (fun a=>hSub a.val a.property))
  have hTranslate (a : T) : volume (Metric.ball a.val ε)=volume (Metric.ball (0 : Domain n) ε) := by
    rw [Measure.addHaar_ball_of_pos volume a.val hε,Measure.addHaar_ball_of_pos volume (0 : Domain n) hε]
  have hScale : volume (Metric.ball x (60*ε))=
      (60 : ℝ≥0∞)^n*volume (Metric.ball (0 : Domain n) ε) := by
    rw [Measure.addHaar_ball_of_pos volume x (by positivity),Measure.addHaar_ball_of_pos volume (0 : Domain n) hε]
    simp only [finrank_euclideanSpace,Fintype.card_fin,mul_pow,
      ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ)≤60) n),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ)≤60),ENNReal.ofReal_ofNat,mul_assoc]
  simp_rw [hTranslate] at hVolume
  rw [hScale,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hVolume
  have H : (Fintype.card T : ℝ≥0∞)≤(60 : ℝ≥0∞)^n := by
    apply (ENNReal.mul_le_mul_iff_right (Metric.measure_ball_pos volume (0 : Domain n) hε).ne' measure_ball_ne_top).mp
    simpa only [mul_comm] using hVolume
  have Hnat : Fintype.card T≤60^n := by exact_mod_cast H
  rw [← Nat.card_coe_set_eq T,Nat.card_eq_fintype_card]
  exact Hnat

/-- The original disjoint distance-radius Whitney balls have at most 60^n tenfold overlaps at every actual interior point. -/
theorem whitney_tenfold_overlap_card_le {n : ℕ}
    (S U : Set (Domain n)) (hOpen : IsOpen S) (hComp : Sᶜ.Nonempty)
    (hDisj : U.PairwiseDisjoint (fun a=>Metric.ball a (Metric.infDist a Sᶜ/20)))
    (x : Domain n) (hx : x∈S) :
    let T := {a∈U | x∈Metric.ball a (10*(Metric.infDist a Sᶜ/20))}
    T.Finite ∧ T.ncard≤60^n := by
  intro T
  let r := fun a=>Metric.infDist a Sᶜ/20
  let δ := Metric.infDist x Sᶜ
  have hδ : 0<δ := (hOpen.isClosed_compl.notMem_iff_infDist_pos hComp).mp (not_not_intro hx)
  have hBounds (a : Domain n) (ha : a∈T) : δ/30<r a ∧ dist a x<δ := by
    have hDist : dist x a<10*r a := ha.2
    have hInf1 := Metric.infDist_le_infDist_add_dist (x := a) (y := x) (s := Sᶜ)
    have hInf2 := Metric.infDist_le_infDist_add_dist (x := x) (y := a) (s := Sᶜ)
    have hRa : Metric.infDist a Sᶜ=20*r a := by dsimp only [r];ring
    rw [hRa,dist_comm] at hInf1
    rw [hRa] at hInf2
    change 20*r a≤δ+dist x a at hInf1
    change δ≤20*r a+dist x a at hInf2
    constructor
    · linarith only [hInf2,hDist]
    · rw [dist_comm]
      linarith only [hInf1,hDist]
  have hFinite : T.Finite := (finite_whitney_twelvefold_overlap S U hOpen hComp hDisj x hx).subset (by
    intro a ha
    refine ⟨ha.1,Metric.ball_subset_ball ?_ ha.2⟩
    have H : 0≤r a := div_nonneg Metric.infDist_nonneg (by norm_num)
    change 10*r a≤12*r a
    linarith only [H])
  have hSmallDisj : T.PairwiseDisjoint (fun a=>Metric.ball a (δ/30)) := by
    intro a ha b hb hne
    exact (hDisj ha.1 hb.1 hne).mono (Metric.ball_subset_ball (hBounds a ha).1.le)
      (Metric.ball_subset_ball (hBounds b hb).1.le)
  have hSub (a : Domain n) (ha : a∈T) : Metric.ball a (δ/30)⊆Metric.ball x (60*(δ/30)) := by
    intro z hz
    have hza : dist z a<δ/30 := hz
    have hax := (hBounds a ha).2
    have hTri := dist_triangle z a x
    change dist z x<60*(δ/30)
    linarith only [hza,hax,hTri,hδ]
  exact ⟨hFinite,uniform_ball_card_bound T hFinite x (δ/30) (by positivity) hSmallDisj hSub⟩

end StationaryHarmonicMaps.Analysis

end
