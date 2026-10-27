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

@[expose] noncomputable def cutoffGlobalMeanOscillationConstant (n : ℕ) (A B : ℝ) : ℝ :=
  (effectiveGlobalCriticalMeanOscillationConstant n : ℝ) *
    Real.sqrt (cutoffCriticalConstant n A B)

@[expose] def effectiveCutoffGlobalMeanConstant (n A B : ℕ) : ℕ :=
  effectiveGlobalCriticalMeanOscillationConstant n * (1 + effectiveCutoffCriticalConstant n A B)

theorem cutoffGlobalMeanOscillationConstant_pos (n : ℕ) (A B : ℝ) :
    0 < cutoffGlobalMeanOscillationConstant n A B := by
  have HD : 0 < (effectiveGlobalCriticalMeanOscillationConstant n : ℝ) := by
    simp only [effectiveGlobalCriticalMeanOscillationConstant, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    positivity
  exact mul_pos HD (Real.sqrt_pos.mpr (cutoffCriticalConstant_pos n A B))

theorem effectiveCutoffGlobalMeanConstant_pos (n A B : ℕ) :
    0 < (effectiveCutoffGlobalMeanConstant n A B : ℝ) := by
  have HD : 0 < (effectiveGlobalCriticalMeanOscillationConstant n : ℝ) := by
    simp only [effectiveGlobalCriticalMeanOscillationConstant, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    positivity
  simp only [effectiveCutoffGlobalMeanConstant, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  positivity

theorem cutoffGlobalMeanOscillationConstant_natCast_le (n A B : ℕ) :
    cutoffGlobalMeanOscillationConstant n (A : ℝ) (B : ℝ) ≤
      (effectiveCutoffGlobalMeanConstant n A B : ℝ) := by
  have hK := effectiveCutoffCriticalConstant_pos n A B
  have hroot := Real.sq_sqrt hK.le
  have hsqrt : Real.sqrt (effectiveCutoffCriticalConstant n A B : ℝ) ≤
      1 + (effectiveCutoffCriticalConstant n A B : ℝ) := by
    nlinarith only [hroot, Real.sqrt_nonneg (effectiveCutoffCriticalConstant n A B : ℝ),
      sq_nonneg (effectiveCutoffCriticalConstant n A B : ℝ), hK]
  simpa only [cutoffGlobalMeanOscillationConstant, cutoffCriticalConstant_natCast,
    effectiveCutoffGlobalMeanConstant, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg (effectiveGlobalCriticalMeanOscillationConstant n))

/-- Original local critical data produce all-ball scalar mean-oscillation bounds for the same literal full-space cutoff. -/
theorem cutoff_global_scalar_mean_oscillation_bound (n : ℕ) (hn : 2≤n)
    (A B : ℝ) (hA : 0≤A) (hB : 0≤B) :
    ∀ (q : ℕ) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
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
              (⨍ y in Metric.ball x r,|b y-(⨍ z in Metric.ball x r,b z)|)≤cutoffGlobalMeanOscillationConstant n A B*‖L‖*η := by
  let K := cutoffCriticalConstant n A B
  have hK : 0 < K := cutoffCriticalConstant_pos n A B
  have Hcut := cutoff_criticalMorrey_bound n hn A B hA hB
  let D : ℝ := effectiveGlobalCriticalMeanOscillationConstant n
  have Hmean := effective_global_scalar_mean_oscillation_bound_of_criticalMorrey n
  let C := D * Real.sqrt K
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
    exact hOsc.trans_eq (by rw [hSqrt];dsimp only [C, D, K, cutoffGlobalMeanOscillationConstant];ring)

/-- Original local critical data produce all-ball scalar mean-oscillation bounds for the same literal full-space cutoff. -/
theorem effective_cutoff_global_scalar_mean_oscillation_bound (n : ℕ) (hn : 2≤n)
    (A B : ℕ) :
    ∀ (q : ℕ) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
      (η : ℝ),MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀ (χ : Domain n → ℝ),ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ⊆Metric.closedBall (0 : Domain n) (3/4 : ℝ) →
        (∀ x,|χ x|≤(A : ℝ)) →
        (∀ (x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤(B : ℝ)) →
        ∀ L : Ambient q →L[ℝ] ℝ,
          let c := ⨍ y in Metric.ball (0 : Domain n) 1,u y
          let b := fun x=>L (χ x • (u x-c))
          AEStronglyMeasurable b volume ∧
            (∀ x,χ x=1 → b x=L (u x-c)) ∧
            ∀ (x : Domain n) (r : ℝ),0<r →
              IntegrableOn b (Metric.ball x r) volume ∧
              (⨍ y in Metric.ball x r,|b y-(⨍ z in Metric.ball x r,b z)|)≤(effectiveCutoffGlobalMeanConstant n A B : ℝ)*‖L‖*η := by
  intro q u Du η hu hη hMorrey χ hχ hcχ hsχ hχBound hDχ L c b
  obtain ⟨hMeas, hEq, hBall⟩ := cutoff_global_scalar_mean_oscillation_bound n hn
    (A : ℝ) (B : ℝ) (Nat.cast_nonneg A) (Nat.cast_nonneg B)
    q u Du η hu hη hMorrey χ hχ hcχ hsχ hχBound hDχ L
  refine ⟨hMeas, hEq, ?_⟩
  intro x r hr
  obtain ⟨hI, hOsc⟩ := hBall x r hr
  refine ⟨hI, hOsc.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (cutoffGlobalMeanOscillationConstant_natCast_le n A B)
      (norm_nonneg L)) hη

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
  exact ⟨cutoffGlobalMeanOscillationConstant n A B,
    cutoffGlobalMeanOscillationConstant_pos n A B,
    cutoff_global_scalar_mean_oscillation_bound n hn A B hA hB⟩

end StationaryHarmonicMaps.Analysis

end
