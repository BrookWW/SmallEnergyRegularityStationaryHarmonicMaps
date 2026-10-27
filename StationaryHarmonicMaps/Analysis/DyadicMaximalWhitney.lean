module

public import StationaryHarmonicMaps.Analysis.DyadicMaximalContinuity
public import StationaryHarmonicMaps.Analysis.DyadicMaximalWeakOne
public import StationaryHarmonicMaps.Analysis.OpenWhitneyVitaliCover

/-!
# Actual maximal superlevel Whitney covers and measure aggregation

The original extended L1 density gives an open finite-volume strict
maximal superlevel. Its actual distance-radius Whitney cover supplies
countably many disjoint cores and genuine nearby output good points.
Countable subadditivity and the original core-volume sum aggregate local
measure conclusions. This is a measure aggregation lemma; an operator
application must produce its local estimates from its actual responses.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original extended L1 density produces the actual finite-volume maximal superlevel Whitney cover, its original disjoint cores and nearby maximal good points. -/
theorem exists_dyadic_maximal_whitney_cover (n : ℕ) (hn : 0<n)
    (f : Domain n → ℝ≥0∞) (hf : AEMeasurable f volume) (hFinite : (∫⁻ z,f z)≠∞)
    (L : ℝ) (hL : 0<L) :
    let S := {x | ENNReal.ofReal L<dyadicBallMaximal f x}
    let r := fun a=>Metric.infDist a Sᶜ/20
    ∃ U : Set (Domain n),U.Countable ∧ U⊆S ∧
      U.PairwiseDisjoint (fun a=>Metric.ball a (r a)) ∧
      S=⋃ a : U,Metric.ball a.val (5*r a.val) ∧
      (∀ a∈U,0<r a ∧ Metric.ball a (10*r a)⊆S ∧
        ∃ y,dyadicBallMaximal f y≤ENNReal.ofReal L ∧ dist y a=20*r a) ∧
      (∑' a : U,volume (Metric.ball a.val (r a.val)))≤volume S := by
  intro S r
  have hOpen : IsOpen S := isOpen_dyadicBallMaximal_superlevel_of_lintegral_ne_top f hf hFinite _
  have hWeak := dyadicBallMaximal_weak_one f L hL
  have hSFinite : volume S≠∞ := ne_of_lt (hWeak.trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hFinite)))
  obtain ⟨U,hCount,hUS,hDisj,hCover,hGood,hSum⟩ := exists_open_whitney_vitali_cover n hn S hOpen hSFinite
  refine ⟨U,hCount,hUS,hDisj,hCover,?_,hSum⟩
  intro a ha
  obtain ⟨hr,hSub,y,hy,hDist⟩ := hGood a ha
  refine ⟨hr,hSub,y,?_,hDist⟩
  exact le_of_not_gt hy

/-- Genuine maximal-superlevel Whitney cores aggregate local measure estimates; no decomposition or operator level inequality is asserted by this pure aggregation theorem. -/
theorem dyadic_goodLambda_of_whitney_local_measure (n : ℕ) (hn : 0<n)
    (f k : Domain n → ℝ≥0∞) (hf : AEMeasurable f volume) (hFinite : (∫⁻ z,f z)≠∞)
    (L A δ : ℝ) (hL : 0<L) (hA : 1≤A) (ε : ℝ≥0∞)
    (hLocal : ∀ (a y : Domain n) (r : ℝ),0<r → dist y a≤20*r →
      dyadicBallMaximal f y≤ENNReal.ofReal L →
      (Metric.ball a (5*r)∩{x | ENNReal.ofReal (A*L)<dyadicBallMaximal f x ∧
        dyadicBallMaximal k x≤ENNReal.ofReal (δ*L)}).Nonempty →
      volume (Metric.ball a (5*r)∩{x | ENNReal.ofReal (A*L)<dyadicBallMaximal f x ∧
        dyadicBallMaximal k x≤ENNReal.ofReal (δ*L)})≤ε*volume (Metric.ball a r)) :
    volume {x | ENNReal.ofReal (A*L)<dyadicBallMaximal f x ∧ dyadicBallMaximal k x≤ENNReal.ofReal (δ*L)}≤
      ε*volume {x | ENNReal.ofReal L<dyadicBallMaximal f x} := by
  classical
  let S := {x | ENNReal.ofReal L<dyadicBallMaximal f x}
  let E := {x | ENNReal.ofReal (A*L)<dyadicBallMaximal f x ∧ dyadicBallMaximal k x≤ENNReal.ofReal (δ*L)}
  let r := fun a=>Metric.infDist a Sᶜ/20
  obtain ⟨U,hCount,_hUS,_hDisj,hCover,hGood,hSum⟩ := exists_dyadic_maximal_whitney_cover n hn f hf hFinite L hL
  letI : Countable U := hCount.to_subtype
  change S=⋃ a : U,Metric.ball a.val (5*r a.val) at hCover
  have hES : E⊆S := by
    intro x hx
    have hLevel : ENNReal.ofReal L≤ENNReal.ofReal (A*L) :=
      ENNReal.ofReal_le_ofReal (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hL.le)
    exact hLevel.trans_lt hx.1
  have hLocalU (a : U) : volume (Metric.ball a.val (5*r a.val)∩E)≤ε*volume (Metric.ball a.val (r a.val)) := by
    obtain ⟨hr,_hSub,y,hy,hDist⟩ := hGood a.val a.property
    by_cases hNonempty : (Metric.ball a.val (5*r a.val)∩E).Nonempty
    · exact hLocal a.val y (r a.val) hr hDist.le hy hNonempty
    · rw [Set.not_nonempty_iff_eq_empty.mp hNonempty,measure_empty]
      exact zero_le
  have hCoverE : E⊆⋃ a : U,Metric.ball a.val (5*r a.val)∩E := by
    intro x hx
    have hxS := hES hx
    rw [hCover] at hxS
    obtain ⟨a,ha⟩ := mem_iUnion.mp hxS
    exact mem_iUnion_of_mem a ⟨ha,hx⟩
  calc
    _ ≤ volume (⋃ a : U,Metric.ball a.val (5*r a.val)∩E) := measure_mono hCoverE
    _ ≤ ∑' a : U,volume (Metric.ball a.val (5*r a.val)∩E) := measure_iUnion_le _
    _ ≤ ∑' a : U,ε*volume (Metric.ball a.val (r a.val)) := ENNReal.tsum_le_tsum hLocalU
    _ = ε*(∑' a : U,volume (Metric.ball a.val (r a.val))) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hSum zero_le

end StationaryHarmonicMaps.Analysis

end
