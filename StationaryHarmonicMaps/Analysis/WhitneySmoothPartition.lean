module

public import StationaryHarmonicMaps.Analysis.WhitneyBallPackingBound
public import StationaryHarmonicMaps.Analysis.NormalizedSmoothFamily

/-!
# An actual normalized smooth partition on the original Whitney cover

The original finite-volume open set supplies its disjoint distance-radius
cover. Actual scaled cutoffs equal one on the covering fivefold balls.
Their genuine sum lies between one and 60 to the dimension on the open
set, and is pointwise a finite sum everywhere. Dividing the same cutoffs
by this sum produces globally smooth compact functions with the exact
partition identity and the original support localization.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original open finite-volume data produce the actual Whitney cutoffs, their positive uniformly bounded genuine sum, and the same normalized smooth compact partition. -/
theorem exists_whitney_normalized_smooth_partition (n : ℕ) (hn : 0<n) :
    ∃ C : ℝ,0<C ∧ ∀ S : Set (Domain n),IsOpen S → volume S≠(∞ : ℝ≥0∞) →
      let r := fun a=>Metric.infDist a Sᶜ/20
      ∃ U : Set (Domain n),U.Countable ∧ U⊆S ∧
        U.PairwiseDisjoint (fun a=>Metric.ball a (r a)) ∧
        S=⋃ a : U,Metric.ball a.val (5*r a.val) ∧
        ∃ η : U → Domain n → ℝ,
          (∀ a,ContDiff ℝ ∞ (η a) ∧ HasCompactSupport (η a) ∧
            tsupport (η a)⊆Metric.ball a.val (10*r a.val) ∧ tsupport (η a)⊆S ∧
            (∀ x∈Metric.closedBall a.val (5*r a.val),η a x=1) ∧
            (∀ x,0≤η a x ∧ η a x≤1) ∧ (∀ x,‖fderiv ℝ (η a) x‖≤C/(5*r a.val))) ∧
          let P := fun x=>∑' a,η a x
          let θ := fun a x=>η a x/P x
          (∀ x,Function.HasFiniteSupport (fun a=>η a x)) ∧
            (∀ x∈S,1≤P x ∧ P x≤(60 : ℝ)^n) ∧
            (∀ x,Function.HasFiniteSupport (fun a=>θ a x)) ∧
            (∀ a,ContDiff ℝ ∞ (θ a) ∧ HasCompactSupport (θ a) ∧
              tsupport (θ a)⊆Metric.ball a.val (10*r a.val) ∧ tsupport (θ a)⊆S) ∧
            (∀ a x,0≤θ a x ∧ θ a x≤1) ∧ (∀ x∈S,∑' a,θ a x=1) := by
  classical
  obtain ⟨C,hC,Hcut⟩ := exists_scaled_ball_cutoff n
  refine ⟨C,hC,?_⟩
  intro S hOpen hFinite r
  obtain ⟨U,hCount,hUS,hDisj,hCover,hGood,_hVolume⟩ := exists_open_whitney_vitali_cover n hn S hOpen hFinite
  obtain ⟨_R,_hR,_hCap,hComp⟩ := exists_ball_radius_cap_of_finite_volume n hn S hFinite
  have hRpos (a : U) : 0<r a.val := (hGood a.val a.property).1
  choose η hη hcη hsη hOne hBounds hDη using (fun a : U=>Hcut a.val (5*r a.val) (mul_pos (by norm_num) (hRpos a)))
  have hSuppBall (a : U) : tsupport (η a)⊆Metric.ball a.val (10*r a.val) := by
    simpa only [show 2*(5*r a.val)=10*r a.val by ring] using hsη a
  have hSuppS (a : U) : tsupport (η a)⊆S :=
    (hSuppBall a).trans (hGood a.val a.property).2.1
  have hLocal : ∀ x∈S,∃ V∈𝓝 x,{a : U | (Function.support (η a)∩V).Nonempty}.Finite := by
    intro x hx
    obtain ⟨V,hV,hFin⟩ := locallyFiniteWithin_whitney_tenfold_balls S U hOpen hComp hDisj x hx
    refine ⟨V,hV,?_⟩
    have hPre : {a : U | a.val∈{a∈U | (Metric.ball a (10*r a)∩V).Nonempty}}.Finite :=
      hFin.preimage Subtype.val_injective.injOn
    apply hPre.subset
    intro a ha
    obtain ⟨z,hz,hzV⟩ := ha
    exact ⟨a.property,z,hSuppBall a (subset_tsupport (η a) hz),hzV⟩
  obtain ⟨hFiniteη,_hPSmooth⟩ := finite_support_contDiffOn_tsum_of_locallyFinite S η hη
    (fun a=>(subset_tsupport (η a)).trans (hSuppS a)) hLocal
  let P := fun x=>∑' a,η a x
  have hPLower (x : Domain n) (hx : x∈S) : 1≤P x := by
    have hCoverX := hx
    rw [hCover] at hCoverX
    obtain ⟨a,ha⟩ := mem_iUnion.mp hCoverX
    have hOneX : η a x=1 := hOne a x (Metric.ball_subset_closedBall ha)
    have hSummable : Summable (fun a=>η a x) := summable_of_hasFiniteSupport (hFiniteη x)
    have H := hSummable.sum_le_tsum ({a} : Finset U) (fun b _=>(hBounds b x).1)
    simpa only [Finset.sum_singleton,hOneX] using H
  have hPUpper (x : Domain n) (hx : x∈S) : P x≤(60 : ℝ)^n := by
    let F := (hFiniteη x).toFinset
    let T := {a∈U | x∈Metric.ball a (10*r a)}
    obtain ⟨hTFin,hTCard⟩ := whitney_tenfold_overlap_card_le S U hOpen hComp hDisj x hx
    have hImage : F.image Subtype.val⊆hTFin.toFinset := by
      intro a ha
      obtain ⟨b,hb,hba⟩ := Finset.mem_image.mp ha
      subst a
      apply hTFin.mem_toFinset.mpr
      exact ⟨b.property,hSuppBall b (subset_tsupport (η b) ((hFiniteη x).mem_toFinset.mp hb))⟩
    have hCard : F.card≤60^n := by
      have H := Finset.card_le_card hImage
      rw [Finset.card_image_of_injective F Subtype.val_injective,
        ← Set.ncard_eq_toFinset_card T hTFin] at H
      exact H.trans hTCard
    have hSumEq : P x=∑ a∈F,η a x := tsum_eq_sum (fun a ha=>by
      by_contra hnot
      exact ha ((hFiniteη x).mem_toFinset.mpr hnot))
    rw [hSumEq]
    calc
      _ ≤ ∑ _a∈F,(1 : ℝ) := Finset.sum_le_sum (fun a _=>(hBounds a x).2)
      _ = (F.card : ℝ) := by simp
      _ ≤ (60 : ℝ)^n := by exact_mod_cast hCard
  obtain ⟨_hFiniteη,hFiniteθ,hθ,hθBounds,hPartition⟩ := normalized_smooth_supported_family S hOpen η
    hη hcη hSuppS (fun a x=>(hBounds a x).1) hLocal (fun x hx=>(zero_lt_one.trans_le (hPLower x hx)))
  refine ⟨U,hCount,hUS,hDisj,hCover,η,?_,hFiniteη,fun x hx=>⟨hPLower x hx,hPUpper x hx⟩,
    hFiniteθ,?_,hθBounds,hPartition⟩
  · intro a
    exact ⟨hη a,hcη a,hSuppBall a,hSuppS a,hOne a,hBounds a,hDη a⟩
  · intro a
    exact ⟨(hθ a).1,(hθ a).2.1,(hθ a).2.2.trans (hSuppBall a),(hθ a).2.2.trans (hSuppS a)⟩

end StationaryHarmonicMaps.Analysis

end
