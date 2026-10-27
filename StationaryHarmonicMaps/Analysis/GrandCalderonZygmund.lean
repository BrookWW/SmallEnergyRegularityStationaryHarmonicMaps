module

public import StationaryHarmonicMaps.Analysis.NormalizedGrandCutoffPieces
public import StationaryHarmonicMaps.Analysis.PartitionCancellationSum
public import StationaryHarmonicMaps.Analysis.GrandMaximalLebesgueDomination

/-!
# Actual Calderon--Zygmund reconstruction from the original grand field

The original integrable function and its finite literal grand integral
produce the bad set, its normalized partition and newly computed cutoff
averages. The original cancellation pieces are genuinely summable under
an integrable dominator, preserving the original integral. The same good
function has its actual small-level cap bound and the original error has
its actual large-level tail bound. No decomposition or pointwise value
certificate is an input.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original finite grand data produce an actual integrable Calderon--Zygmund good part, original cancellation reconstruction and genuine cap/tail bounds. -/
theorem exists_grand_calderon_zygmund_reconstruction (n : ℕ) (hn : 0<n) :
    ∃ A : ℝ,0<A ∧ ∀ (f : Domain n → ℝ),Integrable f volume →
      let J := fun a => ⨆ r : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a r.val),
        ⨆ (_ : ∀ x∈Metric.ball a r.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤r.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      (∫⁻ x,J x)<(∞ : ℝ≥0∞) → ∀ L : ℝ,0<L →
        let S := {x | ENNReal.ofReal L<J x}
        ∃ U : Set (Domain n),U.Countable ∧ ∃ θ : U → Domain n → ℝ,
          (∀ a,ContDiff ℝ ∞ (θ a) ∧ HasCompactSupport (θ a) ∧ tsupport (θ a)⊆S) ∧
          (∀ x,Function.HasFiniteSupport (fun a=>θ a x)) ∧
          (∀ a x,0≤θ a x ∧ θ a x≤1) ∧ (∀ x∈S,∑' a,θ a x=1) ∧
          let c := fun a=>(∫ x,θ a x*f x)/(∫ x,θ a x)
          let b := fun a x=>θ a x*(f x-c a)
          let g := fun x=>f x-∑' a,b a x
          (∀ a,|c a|≤A*L ∧ Integrable (b a) volume ∧ (∫ x,b a x)=0) ∧
          Integrable (fun x=>∑' a,|b a x|) volume ∧
          Integrable (fun x=>∑' a,b a x) volume ∧ (∫ x,(∑' a,b a x))=0 ∧
          Integrable g volume ∧ (∫ x,g x)=(∫ x,f x) ∧
          (∀ x∈S,g x=∑' a,θ a x*c a) ∧ (∀ x∉S,g x=f x) ∧
          (∀ x,f x=g x+∑' a,b a x) ∧
          (∀ᵐ x ∂volume,ENNReal.ofReal |g x|≤ENNReal.ofReal A*min (J x) (ENNReal.ofReal L)) ∧
          (∀ᵐ x ∂volume,ENNReal.ofReal |f x-g x|≤ENNReal.ofReal (2*A)*(S.indicator J x)) := by
  classical
  obtain ⟨D,hD,Hpieces⟩ := exists_normalized_grand_superlevel_pieces n hn
  obtain ⟨C,hC,Hvalue⟩ := exists_ae_value_le_smooth_grand_kernel n
  let A := max C D
  have hA : 0<A := hC.trans_le (le_max_left _ _)
  refine ⟨A,hA,?_⟩
  intro f hf J hJ L hL S
  obtain ⟨U,hCount,_hUS,_hDisj,_hCover,θ,hFinite,hPart,hData⟩ := Hpieces f hf hJ L hL
  letI : Countable U := hCount.to_subtype
  let c := fun a=>(∫ x,θ a x*f x)/(∫ x,θ a x)
  let b := fun a x=>θ a x*(f x-c a)
  let g := fun x=>f x-∑' a,b a x
  have hθSmooth (a : U) : ContDiff ℝ ∞ (θ a) := (hData a).1
  have hθCompact (a : U) : HasCompactSupport (θ a) := (hData a).2.1
  have hθSupp (a : U) : tsupport (θ a)⊆S := (hData a).2.2.2.1
  have hθBounds (a : U) (x : Domain n) : 0≤θ a x ∧ θ a x≤1 := (hData a).2.2.2.2.1 x
  have hc (a : U) : |c a|≤D*L := (hData a).2.2.2.2.2.2.1
  have hMean (a : U) : (∫ x,b a x)=0 := (hData a).2.2.2.2.2.2.2.2.1
  obtain ⟨hLS,hMeas⟩ := lowerSemicontinuous_measurable_smooth_grand_kernel f
  have hOpen : IsOpen S := hLS.isOpen_preimage (ENNReal.ofReal L)
  have hSubset : S⊆{x | ENNReal.ofReal L≤J x} := by intro x hx;change ENNReal.ofReal L<J x at hx;exact hx.le
  have hFiniteS : volume S≠(∞ : ℝ≥0∞) := by
    have H : volume S≤(∫⁻ x,J x)/ENNReal.ofReal L := (measure_mono hSubset).trans
      (meas_ge_le_lintegral_div hMeas.aemeasurable (ENNReal.ofReal_pos.mpr hL).ne' ENNReal.ofReal_ne_top)
    apply (H.trans_lt ?_).ne
    rw [div_eq_mul_inv]
    exact ENNReal.mul_lt_top hJ (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hL))
  obtain ⟨_hBadFinite,hBI,hAbsI,hSumI,hSumZero,hgI,hgMean,hInside,hBound,hOutside,hRecon⟩ :=
    integrable_partition_cancellation_sum volume S hOpen.measurableSet hFiniteS f hf θ
      (fun a=>(hθSmooth a).continuous.aestronglyMeasurable) hFinite
      (fun a=>(subset_tsupport (θ a)).trans (hθSupp a)) (fun a x=>(hθBounds a x).1) hPart c (D*L) hc hMean
  have hAEValue : ∀ᵐ x ∂volume,ENNReal.ofReal |f x|≤ENNReal.ofReal C*J x := Hvalue f hf
  have hCap : ∀ᵐ x ∂volume,ENNReal.ofReal |g x|≤ENNReal.ofReal A*min (J x) (ENNReal.ofReal L) := by
    filter_upwards [hAEValue] with x hxValue
    by_cases hx : x∈S
    · have hLarge : ENNReal.ofReal L≤J x := (show ENNReal.ofReal L<J x from hx).le
      rw [min_eq_right hLarge]
      calc
        _ ≤ ENNReal.ofReal (D*L) := ENNReal.ofReal_le_ofReal (hBound x hx)
        _ ≤ ENNReal.ofReal (A*L) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hL.le)
        _ = _ := ENNReal.ofReal_mul hA.le
    · have hSmall : J x≤ENNReal.ofReal L := le_of_not_gt hx
      have hOut : g x=f x := hOutside x hx
      rw [min_eq_left hSmall,hOut]
      exact hxValue.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) zero_le)
  have hError : ∀ᵐ x ∂volume,ENNReal.ofReal |f x-g x|≤ENNReal.ofReal (2*A)*(S.indicator J x) := by
    filter_upwards [hAEValue,hCap] with x hxValue hxCap
    by_cases hx : x∈S
    · rw [indicator_of_mem hx]
      have hAValue : ENNReal.ofReal |f x|≤ENNReal.ofReal A*J x := hxValue.trans
        (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) zero_le)
      have hAGood : ENNReal.ofReal |g x|≤ENNReal.ofReal A*J x := hxCap.trans
        (mul_le_mul_of_nonneg_left (min_le_left _ _) zero_le)
      calc
        _ ≤ ENNReal.ofReal (|f x|+|g x|) := ENNReal.ofReal_le_ofReal (abs_sub _ _)
        _ = ENNReal.ofReal |f x|+ENNReal.ofReal |g x| := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ ENNReal.ofReal A*J x+ENNReal.ofReal A*J x := add_le_add hAValue hAGood
        _ = ENNReal.ofReal (2*A)*J x := by rw [show 2*A=A+A by ring,ENNReal.ofReal_add hA.le hA.le,add_mul]
    · have hOut : g x=f x := hOutside x hx
      rw [hOut,sub_self,abs_zero,ENNReal.ofReal_zero,indicator_of_notMem hx,mul_zero]
  refine ⟨U,hCount,θ,fun a=>⟨hθSmooth a,hθCompact a,hθSupp a⟩,hFinite,hθBounds,hPart,?_,
    hAbsI,hSumI,hSumZero,hgI,hgMean,hInside,hOutside,hRecon,hCap,hError⟩
  intro a
  exact ⟨(hc a).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hL.le),hBI a,hMean a⟩

end StationaryHarmonicMaps.Analysis

end
