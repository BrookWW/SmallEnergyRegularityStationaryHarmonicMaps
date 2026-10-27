module

public import StationaryHarmonicMaps.Analysis.NormalizedGrandAtoms
public import StationaryHarmonicMaps.Analysis.AtomicMeanOscillationLimit

/-!
# Actual continuous Hardy pairing from the original grand integral

The original integrable function and its finite literal smooth grand
integral produce their own normalized atoms and summable coefficients.
Original all-ball mean oscillation then controls a uniquely determined
limit of actual symmetric-truncation integrals. Actual integrable
products have their ordinary integral as that same limit.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original finite smooth grand data and original all-ball mean oscillation produce the unique actual continuous pairing, with no atomic-decomposition or duality premise. -/
theorem existsUnique_continuous_pairing_of_finite_smooth_grand_kernel (n : ℕ) (hn : 0<n) :
    ∃ C : ℝ,0<C ∧ ∀ (f : Domain n → ℝ),Integrable f volume →
      let J := fun a => ⨆ s : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a s.val),
        ⨆ (_ : ∀ x∈Metric.ball a s.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤s.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      (∫⁻ x,J x)<(∞ : ℝ≥0∞) →
        ∀ (b : Domain n → ℝ) (B : ℝ),AEStronglyMeasurable b volume → 0≤B →
          (∀ (x : Domain n) (r : ℝ),0<r → IntegrableOn b (Metric.ball x r) volume ∧
            (⨍ y in Metric.ball x r,|b y-(⨍ z in Metric.ball x r,b z)|)≤B) →
          ∃! s : ℝ,
            (∀ k : ℕ,Integrable (fun x=>f x*min (k : ℝ) (max (-(k : ℝ)) (b x))) volume) ∧
            Tendsto (fun k : ℕ=>∫ x,f x*min (k : ℝ) (max (-(k : ℝ)) (b x))) atTop (𝓝 s) ∧
            |s|≤C*B*(∫⁻ x,J x).toReal ∧
            (Integrable (fun x=>f x*b x) volume → s=(∫ x,f x*b x)) := by
  classical
  obtain ⟨D,hD,Hatom⟩ := exists_normalized_atoms_of_finite_grand_kernel n hn
  let C := 2*D
  have hC : 0<C := mul_pos (by norm_num) hD
  refine ⟨C,hC,?_⟩
  intro f hf J hJ b B hb hB hBMO
  obtain ⟨U,hU,w,a,hAtoms,hw,hCost,_hAbs,hRecon⟩ := Hatom f hf hJ
  letI (j : ℤ) : Countable (U j) := (hU j).1.to_subtype
  let S := fun p : Σ j,U j=>Metric.ball p.2.val
    (70*(Metric.infDist p.2.val {x | ENNReal.ofReal ((2 : ℝ)^p.1)<J x}ᶜ/20))
  have hRadius (p : Σ j,U j) : 0<70*(Metric.infDist p.2.val
      {x | ENNReal.ofReal ((2 : ℝ)^p.1)<J x}ᶜ/20) := mul_pos (by norm_num) ((hU p.1).2 p.2)
  have hS0 (p : Σ j,U j) : volume (S p)≠0 :=
    (Metric.measure_ball_pos volume p.2.val (hRadius p)).ne'
  have ha (p : Σ j,U j) : AEStronglyMeasurable (a p) (volume.restrict (S p)) :=
    (hAtoms p).2.1.aestronglyMeasurable.restrict
  have hAEBound (p : Σ j,U j) : ∀ᵐ x ∂volume.restrict (S p),|a p x|≤(volume.real (S p))⁻¹ :=
    ((hAtoms p).2.2.2.2.1).filter_mono (ae_mono Measure.restrict_le_self)
  have hAbs (p : Σ j,U j) : |w p|=w p := abs_of_pos (hAtoms p).1
  have hwAbs : Summable (fun p=>|w p|) := by simpa only [hAbs] using hw
  obtain ⟨s,hAllI,hLimit,hEstimate,hAgree⟩ := exists_atomic_mean_oscillation_pairing_limit
    volume S (fun _=>measurableSet_ball) hS0 (fun _=>measure_ball_ne_top) a ha
    (fun p=>(hAtoms p).2.2.2.1) hAEBound (fun p=>(hAtoms p).2.2.1)
    w hwAbs f b hRecon hb
    (fun p=>(hBMO p.2.val _ (hRadius p)).1) B
    (fun p=>(hBMO p.2.val _ (hRadius p)).2)
  have hBound : |s|≤C*B*(∫⁻ x,J x).toReal := by
    simp only [hAbs] at hEstimate
    exact hEstimate.trans ((mul_le_mul_of_nonneg_left hCost (mul_nonneg (by norm_num) hB)).trans_eq
      (by dsimp only [C];ring))
  refine ⟨s,⟨hAllI,hLimit,hBound,hAgree⟩,?_⟩
  intro t ht
  exact tendsto_nhds_unique ht.2.1 hLimit

end StationaryHarmonicMaps.Analysis

end
