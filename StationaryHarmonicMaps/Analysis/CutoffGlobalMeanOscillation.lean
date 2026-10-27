module

public import StationaryHarmonicMaps.Analysis.GlobalCriticalMeanOscillation
public import StationaryHarmonicMaps.Analysis.CutoffCriticalMorrey

/-!
# Genuine global mean oscillation of the original Sobolev cutoff

The original local critical graph produces its actual full-space cutoff
graph and complete critical bound. Every scalar observable of the same
cutoff is globally measurable, locally integrable on all positive balls
and has a uniform original mean-oscillation estimate.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Original local critical data produce all-ball scalar mean-oscillation bounds for the same literal full-space cutoff. -/
theorem exists_cutoff_global_scalar_mean_oscillation_bound (n : ℕ) (hn : 2≤n)
    (A B : ℝ) (hA : 0≤A) (hB : 0≤B) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
      (η : ℝ),MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀ (χ : Domain n → ℝ),ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ⊆Metric.closedBall (0 : Domain n) (3/4 : ℝ) →
        (∀ x,|χ x|≤A) →
        (∀ (x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) →
        ∀ L : Ambient q →L[ℝ] ℝ,
          let c := ⨍ y in Metric.ball (0 : Domain n) 1,u y
          let b := fun x=>L (χ x • (u x-c))
          AEStronglyMeasurable b volume ∧
            (∀ x,χ x=1 → b x=L (u x-c)) ∧
            ∀ (x : Domain n) (r : ℝ),0<r →
              IntegrableOn b (Metric.ball x r) volume ∧
              (⨍ y in Metric.ball x r,|b y-(⨍ z in Metric.ball x r,b z)|)≤C*‖L‖*η := by
  obtain ⟨K,hK,Hcut⟩ := exists_cutoff_criticalMorrey_bound n hn A B hA hB
  obtain ⟨D,hD,Hmean⟩ := exists_global_scalar_mean_oscillation_bound_of_criticalMorrey n
  let C := D*Real.sqrt K
  have hC : 0<C := mul_pos hD (Real.sqrt_pos.mpr hK)
  refine ⟨C,hC,?_⟩
  intro q u Du η hu hη hMorrey χ hχ hcχ hsχ hχBound hDχ L c b
  let v := fun x=>χ x • (u x-c)
  let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
  obtain ⟨hv,hVBound⟩ := Hcut q u Du η hu hη hMorrey χ hχ hcχ hsχ hχBound hDχ
  change MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv at hv
  have hVLp : MemLp v 2 volume := by
    have H := hv.2.1
    change MemLp v 2 (volume.restrict univ) at H
    rwa [Measure.restrict_univ] at H
  have hbMeas : AEStronglyMeasurable b volume := L.continuous.comp_aestronglyMeasurable hVLp.aestronglyMeasurable
  have hSqrt : Real.sqrt (K*η^2)=Real.sqrt K*η := by
    rw [Real.sqrt_mul hK.le,Real.sqrt_sq hη]
  refine ⟨hbMeas,?_,?_⟩
  · intro x hx
    change L (χ x • (u x-c))=L (u x-c)
    rw [hx,one_smul]
  · intro x r hr
    obtain ⟨hI,hOsc⟩ := Hmean q v Dv (K*η^2) hv (by positivity) hVBound L x r hr
    refine ⟨hI,?_⟩
    exact hOsc.trans_eq (by rw [hSqrt];dsimp only [C];ring)

end StationaryHarmonicMaps.Analysis

end
