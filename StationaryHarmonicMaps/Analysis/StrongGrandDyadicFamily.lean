module

public import StationaryHarmonicMaps.Analysis.StrongGrandPartition
public import StationaryHarmonicMaps.Analysis.PartitionCancellationSum
public import StationaryHarmonicMaps.Analysis.GoodPartGrandBounds
public import StationaryHarmonicMaps.Analysis.GoodDyadicL1Limits
public import StationaryHarmonicMaps.Analysis.GrandMaximalLebesgueDomination

/-!
# One actual quantitative Whitney family at all integer grand levels

Every positive and negative integer level uses the same original
function and literal grand field. Actual quantitative partitions are
chosen once, retaining their original averages, masses, derivatives and
good points. The good functions are reconstructed from those same
pieces, and their original cap/tail bounds give the true two-ended L1
limits of that same family.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original finite grand data produce one joint quantitative all-integer family and the genuine two-ended L1 limits of its same reconstructed good functions. -/

@[expose] noncomputable def grandDyadicCapConstant (n : ℕ) : ℝ :=
  max (grandGoodPointCutoffMajorant n) (strongGrandPartitionKernelMajorant n)

theorem exists_strong_grand_dyadic_family_explicit (n : ℕ) (hn : 0<n) :
    ∃ B D A : ℝ,0<B ∧ 0<D ∧ 0<A ∧
      B = whitneyPartitionDerivativeConstant n ∧ D = strongGrandPartitionKernelMajorant n ∧
      A = grandDyadicCapConstant n ∧ ∀ (f : Domain n → ℝ),Integrable f volume →
      let J := fun a => ⨆ s : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a s.val),
        ⨆ (_ : ∀ x∈Metric.ball a s.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤s.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      (∫⁻ x,J x)<(∞ : ℝ≥0∞) →
        let S := fun j : ℤ=>{x | ENNReal.ofReal ((2 : ℝ)^j)<J x}
        let r := fun j a=>Metric.infDist a (S j)ᶜ/20
        ∃ U : ℤ → Set (Domain n),∃ θ : (j : ℤ) → U j → Domain n → ℝ,
          (∀ j,IsOpen (S j) ∧ volume (S j)≠(∞ : ℝ≥0∞) ∧ (S j)ᶜ.Nonempty ∧
            (U j).Countable ∧ U j⊆S j ∧
            (U j).PairwiseDisjoint (fun a=>Metric.ball a (r j a)) ∧
            S j=⋃ a : U j,Metric.ball a.val (5*r j a.val) ∧
            (∑' a : U j,volume (Metric.ball a.val (r j a.val)))≤volume (S j) ∧
            (∀ x,Function.HasFiniteSupport (fun a=>θ j a x)) ∧ (∀ x∈S j,∑' a,θ j a x=1) ∧
            ∀ a,0<r j a.val ∧ ContDiff ℝ ∞ (θ j a) ∧ HasCompactSupport (θ j a) ∧
              tsupport (θ j a)⊆Metric.ball a.val (10*r j a.val) ∧ tsupport (θ j a)⊆S j ∧
              (∀ x,0≤θ j a x ∧ θ j a x≤1) ∧ (∀ x,‖fderiv ℝ (θ j a) x‖≤B/r j a.val) ∧
              volume.real (Metric.ball a.val (5*r j a.val))/(60 : ℝ)^n≤∫ x,θ j a x ∧
              (∃ y∈(S j)ᶜ,dist y a.val=20*r j a.val ∧ J y≤ENNReal.ofReal ((2 : ℝ)^j)) ∧
              0<(∫ x,θ j a x) ∧
              let c := (∫ x,θ j a x*f x)/(∫ x,θ j a x)
              |c|≤D*(2 : ℝ)^j ∧ Integrable (fun x=>θ j a x*(f x-c)) volume ∧
                (∫ x,θ j a x*(f x-c))=0) ∧
          let c := fun j (a : U j)=>(∫ x,θ j a x*f x)/(∫ x,θ j a x)
          let b := fun j a x=>θ j a x*(f x-c j a)
          let g := fun j x=>f x-∑' a,b j a x
          (∀ j,(∀ x,Function.HasFiniteSupport (fun a=>b j a x)) ∧
            Integrable (fun x=>∑' a,|b j a x|) volume ∧ Integrable (fun x=>∑' a,b j a x) volume ∧
            (∫ x,(∑' a,b j a x))=0 ∧ Integrable (g j) volume ∧ (∫ x,g j x)=(∫ x,f x) ∧
            (∀ x,J x≤ENNReal.ofReal ((2 : ℝ)^j) → g j x=f x) ∧
            (∀ᵐ x ∂volume,ENNReal.ofReal |g j x|≤ENNReal.ofReal A*min (J x) (ENNReal.ofReal ((2 : ℝ)^j))) ∧
            (∀ᵐ x ∂volume,ENNReal.ofReal |f x-g j x|≤ENNReal.ofReal (2*A)*(S j).indicator J x)) ∧
          Tendsto (fun N : ℕ=>∫ x,|g (-(N : ℤ)) x|) atTop (𝓝 (0 : ℝ)) ∧
          Tendsto (fun N : ℕ=>∫ x,|f x-g ((N : ℤ)+1) x|) atTop (𝓝 (0 : ℝ)) := by
  classical
  obtain ⟨B,D,hB,hD,hBFormula,hDFormula,Hstrong⟩ :=
    exists_strong_grand_superlevel_partition_explicit n hn
  obtain ⟨C,hC,hCFormula,Hvalue⟩ := exists_ae_value_le_smooth_grand_kernel_explicit n
  let A := max C D
  have hA : 0<A := hC.trans_le (le_max_left _ _)
  refine ⟨B,D,A,hB,hD,hA,hBFormula,hDFormula,?_,?_⟩
  · dsimp only [A, grandDyadicCapConstant]
    rw [hCFormula, hDFormula]
  intro f hf J hJ S r
  have hSelect (j : ℤ) := Hstrong f hf hJ ((2 : ℝ)^j) (zpow_pos (by norm_num) j)
  choose U hCount hUS hDisj hCover hVolume θ hFinite hPart hData using (fun j=>(hSelect j).2.2.2)
  letI (j : ℤ) : Countable (U j) := (hCount j).to_subtype
  let c := fun j (a : U j)=>(∫ x,θ j a x*f x)/(∫ x,θ j a x)
  let b := fun j a x=>θ j a x*(f x-c j a)
  let g := fun j x=>f x-∑' a,b j a x
  have hSmooth (j : ℤ) (a : U j) : ContDiff ℝ ∞ (θ j a) := (hData j a).2.1
  have hSupp (j : ℤ) (a : U j) : tsupport (θ j a)⊆S j := (hData j a).2.2.2.2.1
  have hBounds (j : ℤ) (a : U j) (x : Domain n) : 0≤θ j a x ∧ θ j a x≤1 := (hData j a).2.2.2.2.2.1 x
  have hc (j : ℤ) (a : U j) : |c j a|≤D*(2 : ℝ)^j := by
    obtain ⟨_hr,_hs,_hcompact,_hBall,_hS,_hb,_hd,_hm,_hGood,_hMass,hc,_hI,_hZero⟩ := hData j a
    exact hc
  have hMean (j : ℤ) (a : U j) : (∫ x,b j a x)=0 := by
    obtain ⟨_hr,_hs,_hcompact,_hBall,_hS,_hb,_hd,_hm,_hGood,_hMass,_hc,_hI,hZero⟩ := hData j a
    exact hZero
  have hValue : ∀ᵐ x ∂volume,ENNReal.ofReal |f x|≤ENNReal.ofReal C*J x := Hvalue f hf
  have hStats (j : ℤ) : (∀ x,Function.HasFiniteSupport (fun a=>b j a x)) ∧
      Integrable (fun x=>∑' a,|b j a x|) volume ∧ Integrable (fun x=>∑' a,b j a x) volume ∧
      (∫ x,(∑' a,b j a x))=0 ∧ Integrable (g j) volume ∧ (∫ x,g j x)=(∫ x,f x) ∧
      (∀ x,J x≤ENNReal.ofReal ((2 : ℝ)^j) → g j x=f x) ∧
      (∀ᵐ x ∂volume,ENNReal.ofReal |g j x|≤ENNReal.ofReal A*min (J x) (ENNReal.ofReal ((2 : ℝ)^j))) ∧
      (∀ᵐ x ∂volume,ENNReal.ofReal |f x-g j x|≤ENNReal.ofReal (2*A)*(S j).indicator J x) := by
    obtain ⟨hBadFin,_hBI,hAbsI,hSumI,hSumZero,hgI,hgMean,_hInside,hBound,hOutside,_hRecon⟩ :=
      integrable_partition_cancellation_sum volume (S j) (hSelect j).1.measurableSet (hSelect j).2.1 f hf (θ j)
        (fun a=>(hSmooth j a).continuous.aestronglyMeasurable) (hFinite j)
        (fun a=>(subset_tsupport (θ j a)).trans (hSupp j a)) (fun a x=>(hBounds j a x).1) (hPart j) (c j)
        (D*(2 : ℝ)^j) (hc j) (hMean j)
    have hOut (x : Domain n) (hx : J x≤ENNReal.ofReal ((2 : ℝ)^j)) : g j x=f x := hOutside x (not_lt.mpr hx)
    obtain ⟨hCap,hError⟩ := ae_good_part_cap_and_error_bound volume J f (g j) C D ((2 : ℝ)^j)
      hC.le (zpow_pos (by norm_num) j).le hValue (fun x hx=>hBound x hx) hOut
    exact ⟨hBadFin,hAbsI,hSumI,hSumZero,hgI,hgMean,hOut,hCap,hError⟩
  have hMeas : Measurable J := (lowerSemicontinuous_measurable_smooth_grand_kernel f).2
  obtain ⟨hLow,hHigh⟩ := dyadic_good_family_strong_L1_limits volume J hMeas hJ.ne f hf g
    (fun j=>(hStats j).2.2.2.2.1) A (fun j=>(hStats j).2.2.2.2.2.2.2.1)
    (fun j=>(hStats j).2.2.2.2.2.2.2.2)
  refine ⟨U,θ,?_,hStats,hLow,hHigh⟩
  intro j
  exact ⟨(hSelect j).1,(hSelect j).2.1,(hSelect j).2.2.1,hCount j,hUS j,hDisj j,hCover j,hVolume j,hFinite j,hPart j,hData j⟩

theorem exists_strong_grand_dyadic_family (n : ℕ) (hn : 0<n) :
    ∃ B D A : ℝ,0<B ∧ 0<D ∧ 0<A ∧ ∀ (f : Domain n → ℝ),Integrable f volume →
      let J := fun a => ⨆ s : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a s.val),
        ⨆ (_ : ∀ x∈Metric.ball a s.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤s.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      (∫⁻ x,J x)<(∞ : ℝ≥0∞) →
        let S := fun j : ℤ=>{x | ENNReal.ofReal ((2 : ℝ)^j)<J x}
        let r := fun j a=>Metric.infDist a (S j)ᶜ/20
        ∃ U : ℤ → Set (Domain n),∃ θ : (j : ℤ) → U j → Domain n → ℝ,
          (∀ j,IsOpen (S j) ∧ volume (S j)≠(∞ : ℝ≥0∞) ∧ (S j)ᶜ.Nonempty ∧
            (U j).Countable ∧ U j⊆S j ∧
            (U j).PairwiseDisjoint (fun a=>Metric.ball a (r j a)) ∧
            S j=⋃ a : U j,Metric.ball a.val (5*r j a.val) ∧
            (∑' a : U j,volume (Metric.ball a.val (r j a.val)))≤volume (S j) ∧
            (∀ x,Function.HasFiniteSupport (fun a=>θ j a x)) ∧ (∀ x∈S j,∑' a,θ j a x=1) ∧
            ∀ a,0<r j a.val ∧ ContDiff ℝ ∞ (θ j a) ∧ HasCompactSupport (θ j a) ∧
              tsupport (θ j a)⊆Metric.ball a.val (10*r j a.val) ∧ tsupport (θ j a)⊆S j ∧
              (∀ x,0≤θ j a x ∧ θ j a x≤1) ∧ (∀ x,‖fderiv ℝ (θ j a) x‖≤B/r j a.val) ∧
              volume.real (Metric.ball a.val (5*r j a.val))/(60 : ℝ)^n≤∫ x,θ j a x ∧
              (∃ y∈(S j)ᶜ,dist y a.val=20*r j a.val ∧ J y≤ENNReal.ofReal ((2 : ℝ)^j)) ∧
              0<(∫ x,θ j a x) ∧
              let c := (∫ x,θ j a x*f x)/(∫ x,θ j a x)
              |c|≤D*(2 : ℝ)^j ∧ Integrable (fun x=>θ j a x*(f x-c)) volume ∧
                (∫ x,θ j a x*(f x-c))=0) ∧
          let c := fun j (a : U j)=>(∫ x,θ j a x*f x)/(∫ x,θ j a x)
          let b := fun j a x=>θ j a x*(f x-c j a)
          let g := fun j x=>f x-∑' a,b j a x
          (∀ j,(∀ x,Function.HasFiniteSupport (fun a=>b j a x)) ∧
            Integrable (fun x=>∑' a,|b j a x|) volume ∧ Integrable (fun x=>∑' a,b j a x) volume ∧
            (∫ x,(∑' a,b j a x))=0 ∧ Integrable (g j) volume ∧ (∫ x,g j x)=(∫ x,f x) ∧
            (∀ x,J x≤ENNReal.ofReal ((2 : ℝ)^j) → g j x=f x) ∧
            (∀ᵐ x ∂volume,ENNReal.ofReal |g j x|≤ENNReal.ofReal A*min (J x) (ENNReal.ofReal ((2 : ℝ)^j))) ∧
            (∀ᵐ x ∂volume,ENNReal.ofReal |f x-g j x|≤ENNReal.ofReal (2*A)*(S j).indicator J x)) ∧
          Tendsto (fun N : ℕ=>∫ x,|g (-(N : ℤ)) x|) atTop (𝓝 (0 : ℝ)) ∧
          Tendsto (fun N : ℕ=>∫ x,|f x-g ((N : ℤ)+1) x|) atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨B,D,A,hB,hD,hA,_hBFormula,_hDFormula,_hAFormula,H⟩ :=
    exists_strong_grand_dyadic_family_explicit n hn
  exact ⟨B,D,A,hB,hD,hA,H⟩

end StationaryHarmonicMaps.Analysis

end
