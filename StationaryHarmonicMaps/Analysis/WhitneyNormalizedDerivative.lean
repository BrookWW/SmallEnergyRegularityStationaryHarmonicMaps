module

public import StationaryHarmonicMaps.Analysis.WhitneySmoothPartition
public import StationaryHarmonicMaps.Analysis.NormalizedDerivativeBound

/-!
# Genuine derivative control after Whitney normalization

At a point in an original cutoff support, all active Whitney radii are
within a factor three of that original radius. The proved finite overlap
bounds the genuine derivative of the original sum. Differentiating the
actual quotient then gives the uniform normalized cutoff bound.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual smooth Whitney cutoffs and the positive original sum give the genuine uniform derivative bound for the same normalized quotient. -/
theorem norm_fderiv_whitney_normalized_cutoff_le {n : ℕ}
    (S U : Set (Domain n)) (hOpen : IsOpen S) (hComp : Sᶜ.Nonempty) (hUS : U⊆S)
    (hDisj : U.PairwiseDisjoint (fun a=>Metric.ball a (Metric.infDist a Sᶜ/20)))
    (η : U → Domain n → ℝ) (hη : ∀ a,ContDiff ℝ ∞ (η a)) (hcη : ∀ a,HasCompactSupport (η a))
    (hSupp : ∀ a,tsupport (η a)⊆Metric.ball a.val (10*(Metric.infDist a.val Sᶜ/20)))
    (hBounds : ∀ a x,0≤η a x ∧ η a x≤1)
    (C : ℝ) (hC : 0<C)
    (hDη : ∀ a x,‖fderiv ℝ (η a) x‖≤C/(5*(Metric.infDist a.val Sᶜ/20)))
    (hPLower : ∀ x∈S,1≤∑' a,η a x) :
    ∀ (a : U) (x : Domain n),
      ‖fderiv ℝ (fun y=>η a y/(∑' b,η b y)) x‖≤
        ((1+3*(60 : ℝ)^n)*C)/(5*(Metric.infDist a.val Sᶜ/20)) := by
  classical
  let r := fun a=>Metric.infDist a Sᶜ/20
  let N : ℝ := (60 : ℝ)^n
  let P := fun x=>∑' a,η a x
  have hRpos (a : U) : 0<r a.val := div_pos
    ((hOpen.isClosed_compl.notMem_iff_infDist_pos hComp).mp (not_not_intro (hUS a.property))) (by norm_num)
  have hSuppS (a : U) : tsupport (η a)⊆S := by
    apply (hSupp a).trans
    apply (Metric.ball_subset_ball ?_).trans Metric.ball_infDist_compl_subset
    linarith only [Metric.infDist_nonneg (x := a.val) (s := Sᶜ)]
  have hLocal : ∀ x∈S,∃ V∈𝓝 x,{a : U | (Function.support (η a)∩V).Nonempty}.Finite := by
    intro x hx
    obtain ⟨V,hV,hFin⟩ := locallyFiniteWithin_whitney_tenfold_balls S U hOpen hComp hDisj x hx
    refine ⟨V,hV,?_⟩
    have hPre : {a : U | a.val∈{a∈U | (Metric.ball a (10*r a)∩V).Nonempty}}.Finite :=
      hFin.preimage Subtype.val_injective.injOn
    apply hPre.subset
    intro a ha
    obtain ⟨z,hz,hzV⟩ := ha
    exact ⟨a.property,z,hSupp a (subset_tsupport (η a) hz),hzV⟩
  obtain ⟨_hFin,hPSmooth⟩ := finite_support_contDiffOn_tsum_of_locallyFinite S η hη
    (fun a=>(subset_tsupport (η a)).trans (hSuppS a)) hLocal
  obtain ⟨_hFinη,_hFinθ,hθ,_hθBounds,_hPart⟩ := normalized_smooth_supported_family S hOpen η hη hcη hSuppS
    (fun a x=>(hBounds a x).1) hLocal (fun x hx=>zero_lt_one.trans_le (hPLower x hx))
  intro a x
  have haPos := hRpos a
  by_cases hxSupp : x∈tsupport (fun y=>η a y/P y)
  · have hxS : x∈S := hSuppS a ((hθ a).2.2 hxSupp)
    have hxa : dist x a.val<10*r a.val := hSupp a ((hθ a).2.2 hxSupp)
    let T := {b∈U | x∈Metric.ball b (10*r b)}
    obtain ⟨hTFin,hTCard⟩ := whitney_tenfold_overlap_card_le S U hOpen hComp hDisj x hxS
    have hASet : {b : U | x∈Metric.ball b.val (10*r b.val)}.Finite := by
      have H : {b : U | b.val∈T}.Finite := hTFin.preimage Subtype.val_injective.injOn
      exact H.subset (fun b hb=>⟨b.property,hb⟩)
    let A := hASet.toFinset
    have hCardA : A.card≤60^n := by
      have hImage : A.image Subtype.val⊆hTFin.toFinset := by
        intro b hb
        obtain ⟨c,hc,hcb⟩ := Finset.mem_image.mp hb
        subst b
        exact hTFin.mem_toFinset.mpr ⟨c.property,hASet.mem_toFinset.mp hc⟩
      have H := Finset.card_le_card hImage
      rw [Finset.card_image_of_injective A Subtype.val_injective,← Set.ncard_eq_toFinset_card T hTFin] at H
      exact H.trans hTCard
    have hOutside (b : U) (hb : b∉A) : x∉tsupport (η b) := by
      intro hxb
      exact hb (hASet.mem_toFinset.mpr (hSupp b hxb))
    have hActiveBound (b : U) (hb : b∈A) : ‖fderiv ℝ (η b) x‖≤3*C/(5*r a.val) := by
      have hxb : dist x b.val<10*r b.val := hASet.mem_toFinset.mp hb
      have hInf := Metric.infDist_le_infDist_add_dist (x := a.val) (y := b.val) (s := Sᶜ)
      have hTri := dist_triangle a.val x b.val
      have hax : dist a.val x<10*r a.val := by simpa only [dist_comm] using hxa
      have hRa : Metric.infDist a.val Sᶜ=20*r a.val := by dsimp only [r];ring
      have hRb : Metric.infDist b.val Sᶜ=20*r b.val := by dsimp only [r];ring
      rw [hRa,hRb] at hInf
      have hRatio : r a.val≤3*r b.val := by linarith only [hInf,hTri,hax,hxb]
      apply (hDη b x).trans
      apply (div_le_div_iff₀ (mul_pos (by norm_num) (hRpos b)) (mul_pos (by norm_num) (hRpos a))).mpr
      have H := mul_le_mul_of_nonneg_left hRatio hC.le
      nlinarith only [H]
    have hDP : ‖fderiv ℝ P x‖≤N*(3*C/(5*r a.val)) := by
      have H := norm_fderiv_locallyFinite_tsum_le η hη x (hLocal x hxS) A hOutside
        (3*C/(5*r a.val)) hActiveBound
      have hCardReal : (A.card : ℝ)≤N := by dsimp only [N];exact_mod_cast hCardA
      exact H.trans (mul_le_mul_of_nonneg_right hCardReal (by positivity))
    have H := norm_fderiv_normalized_scalar_le (η a) P x ((hη a).differentiable (by simp) x)
      ((hPSmooth.contDiffAt (hOpen.mem_nhds hxS)).differentiableAt (by simp)) (hPLower x hxS)
      (hBounds a x).1 (hBounds a x).2 (C/(5*r a.val)) (N*(3*C/(5*r a.val))) (hDη a x) hDP
    exact H.trans_eq (by dsimp only [N];ring)
  · rw [fderiv_of_notMem_tsupport ℝ hxSupp,norm_zero]
    change 0≤((1+3*N)*C)/(5*r a.val)
    dsimp only [N]
    positivity

end StationaryHarmonicMaps.Analysis

end
