module

public import StationaryHarmonicMaps.Analysis.WhitneyPartitionQuantitative
public import StationaryHarmonicMaps.Analysis.WhitneyNormalizedKernel
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Joint actual quantitative partitions of original grand superlevels

The original scalar function and its finite literal grand integral
produce the open bad set and one actual normalized Whitney partition.
The same functions retain the true derivative and mass bounds, their
actual nearby good points, and their newly computed original averages
and cancellation pieces. These joint witnesses supply cross-level
atomic corrections without changing the chosen partition.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original finite grand data produce one quantitative normalized partition retaining all actual supports, masses, derivatives, good points and newly computed cancellation averages. -/

@[expose] noncomputable def strongGrandPartitionKernelMajorant (n : ℕ) : ℝ :=
  whitneyMassNormalizedKernelMajorant n (whitneyPartitionDerivativeConstant n)

theorem exists_strong_grand_superlevel_partition_explicit (n : ℕ) (hn : 0<n) :
    ∃ B D : ℝ,0<B ∧ 0<D ∧ B = whitneyPartitionDerivativeConstant n ∧
      D = strongGrandPartitionKernelMajorant n ∧ ∀ (f : Domain n → ℝ),Integrable f volume →
      let J := fun a => ⨆ s : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a s.val),
        ⨆ (_ : ∀ x∈Metric.ball a s.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤s.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      (∫⁻ x,J x)<(∞ : ℝ≥0∞) → ∀ L : ℝ,0<L →
        let S := {x | ENNReal.ofReal L<J x}
        let r := fun a=>Metric.infDist a Sᶜ/20
        IsOpen S ∧ volume S≠(∞ : ℝ≥0∞) ∧ Sᶜ.Nonempty ∧
        ∃ U : Set (Domain n),U.Countable ∧ U⊆S ∧
          U.PairwiseDisjoint (fun a=>Metric.ball a (r a)) ∧ S=⋃ a : U,Metric.ball a.val (5*r a.val) ∧
          (∑' a : U,volume (Metric.ball a.val (r a.val)))≤volume S ∧
          ∃ θ : U → Domain n → ℝ,(∀ x,Function.HasFiniteSupport (fun a=>θ a x)) ∧
            (∀ x∈S,∑' a,θ a x=1) ∧ ∀ a,
              0<r a.val ∧ ContDiff ℝ ∞ (θ a) ∧ HasCompactSupport (θ a) ∧
              tsupport (θ a)⊆Metric.ball a.val (10*r a.val) ∧ tsupport (θ a)⊆S ∧
              (∀ x,0≤θ a x ∧ θ a x≤1) ∧ (∀ x,‖fderiv ℝ (θ a) x‖≤B/r a.val) ∧
              volume.real (Metric.ball a.val (5*r a.val))/(60 : ℝ)^n≤∫ x,θ a x ∧
              (∃ y∈Sᶜ,dist y a.val=20*r a.val ∧ J y≤ENNReal.ofReal L) ∧
              0<(∫ x,θ a x) ∧
              let c := (∫ x,θ a x*f x)/(∫ x,θ a x)
              |c|≤D*L ∧ Integrable (fun x=>θ a x*(f x-c)) volume ∧
                (∫ x,θ a x*(f x-c))=0 := by
  classical
  obtain ⟨B,hB,hBFormula,Hpartition⟩ := exists_quantitative_whitney_smooth_partition_explicit n hn
  obtain ⟨D,hD,hDFormula,Hkernel⟩ := exists_whitney_mass_normalized_kernel_bound_majorant n B hB
  refine ⟨B,D,hB,hD,hBFormula,?_,?_⟩
  · rw [hDFormula, hBFormula]
    rfl
  intro f hf J hJ L hL S r
  obtain ⟨hLS,hMeas⟩ := lowerSemicontinuous_measurable_smooth_grand_kernel f
  have hOpen : IsOpen S := hLS.isOpen_preimage (ENNReal.ofReal L)
  have hSubset : S⊆{x | ENNReal.ofReal L≤J x} := by intro x hx;change ENNReal.ofReal L<J x at hx;exact hx.le
  have hMeasure : volume S≤(∫⁻ x,J x)/ENNReal.ofReal L := (measure_mono hSubset).trans
    (meas_ge_le_lintegral_div hMeas.aemeasurable (ENNReal.ofReal_pos.mpr hL).ne' ENNReal.ofReal_ne_top)
  have hFinite : volume S≠(∞ : ℝ≥0∞) := (hMeasure.trans_lt (by
    rw [div_eq_mul_inv]
    exact ENNReal.mul_lt_top hJ (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hL)))).ne
  obtain ⟨_R,_hR,_hCap,hComp⟩ := exists_ball_radius_cap_of_finite_volume n hn S hFinite
  obtain ⟨U,hCount,hUS,hDisj,hCover,θ,hFiniteθ,hθData,hPart⟩ := Hpartition S hOpen hFinite
  letI : Countable U := hCount.to_subtype
  have hRpos (a : U) : 0<r a.val := div_pos
    ((hOpen.isClosed_compl.notMem_iff_infDist_pos hComp).mp (not_not_intro (hUS a.property))) (by norm_num)
  have hVolume : (∑' a : U,volume (Metric.ball a.val (r a.val)))≤volume S := by
    rw [← measure_iUnion hDisj.subtype (fun _=>measurableSet_ball)]
    apply measure_mono
    apply iUnion_subset
    intro a
    apply (Metric.ball_subset_ball ?_).trans Metric.ball_infDist_compl_subset
    dsimp only [r]
    linarith only [Metric.infDist_nonneg (x := a.val) (s := Sᶜ)]
  refine ⟨hOpen,hFinite,hComp,U,hCount,hUS,hDisj,hCover,hVolume,θ,hFiniteθ,hPart,?_⟩
  intro a
  have hra := hRpos a
  obtain ⟨y,hy,hDist⟩ := hOpen.isClosed_compl.exists_infDist_eq_dist hComp a.val
  have hNear : dist y a.val=20*r a.val := by rw [dist_comm,← hDist];dsimp only [r];ring
  have hGood : J y≤ENNReal.ofReal L := le_of_not_gt hy
  have hGood2 : J y≤ENNReal.ofReal (2*L) := hGood.trans (ENNReal.ofReal_le_ofReal (by linarith only [hL]))
  have hMass := (hθData a).2.2.2.2.2.2
  obtain ⟨hMassPos,hθfI,hRaw⟩ := Hkernel f hf a.val y (r a.val) L (∫ x,θ a x) hra hL.le hNear.le hGood2 hMass
    (θ a) (hθData a).1 (hθData a).2.1 (hθData a).2.2.1 (hθData a).2.2.2.2.2.1
  have hAverage : |(∫ x,θ a x*f x)/(∫ x,θ a x)|≤D*L := by
    rw [abs_div,abs_of_pos hMassPos]
    exact hRaw
  have hθI : Integrable (θ a) volume := (hθData a).1.continuous.integrable_of_hasCompactSupport (hθData a).2.1
  obtain ⟨hBadI,hZero⟩ := integrable_zero_mean_cutoff_piece volume f (θ a) hθI hθfI hMassPos.ne'
  exact ⟨hra,(hθData a).1,(hθData a).2.1,(hθData a).2.2.1,(hθData a).2.2.2.1,
    (hθData a).2.2.2.2.1,(hθData a).2.2.2.2.2.1,hMass,⟨y,hy,hNear,hGood⟩,
    hMassPos,hAverage,hBadI,hZero⟩

theorem exists_strong_grand_superlevel_partition (n : ℕ) (hn : 0<n) :
    ∃ B D : ℝ,0<B ∧ 0<D ∧ ∀ (f : Domain n → ℝ),Integrable f volume →
      let J := fun a => ⨆ s : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a s.val),
        ⨆ (_ : ∀ x∈Metric.ball a s.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤s.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      (∫⁻ x,J x)<(∞ : ℝ≥0∞) → ∀ L : ℝ,0<L →
        let S := {x | ENNReal.ofReal L<J x}
        let r := fun a=>Metric.infDist a Sᶜ/20
        IsOpen S ∧ volume S≠(∞ : ℝ≥0∞) ∧ Sᶜ.Nonempty ∧
        ∃ U : Set (Domain n),U.Countable ∧ U⊆S ∧
          U.PairwiseDisjoint (fun a=>Metric.ball a (r a)) ∧ S=⋃ a : U,Metric.ball a.val (5*r a.val) ∧
          (∑' a : U,volume (Metric.ball a.val (r a.val)))≤volume S ∧
          ∃ θ : U → Domain n → ℝ,(∀ x,Function.HasFiniteSupport (fun a=>θ a x)) ∧
            (∀ x∈S,∑' a,θ a x=1) ∧ ∀ a,
              0<r a.val ∧ ContDiff ℝ ∞ (θ a) ∧ HasCompactSupport (θ a) ∧
              tsupport (θ a)⊆Metric.ball a.val (10*r a.val) ∧ tsupport (θ a)⊆S ∧
              (∀ x,0≤θ a x ∧ θ a x≤1) ∧ (∀ x,‖fderiv ℝ (θ a) x‖≤B/r a.val) ∧
              volume.real (Metric.ball a.val (5*r a.val))/(60 : ℝ)^n≤∫ x,θ a x ∧
              (∃ y∈Sᶜ,dist y a.val=20*r a.val ∧ J y≤ENNReal.ofReal L) ∧
              0<(∫ x,θ a x) ∧
              let c := (∫ x,θ a x*f x)/(∫ x,θ a x)
              |c|≤D*L ∧ Integrable (fun x=>θ a x*(f x-c)) volume ∧
                (∫ x,θ a x*(f x-c))=0 := by
  obtain ⟨B, D, hB, hD, _hBFormula, _hDFormula, H⟩ :=
    exists_strong_grand_superlevel_partition_explicit n hn
  exact ⟨B, D, hB, hD, H⟩

end StationaryHarmonicMaps.Analysis

end
