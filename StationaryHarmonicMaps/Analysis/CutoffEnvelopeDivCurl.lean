module

public import StationaryHarmonicMaps.Analysis.CutoffCappedEnvelope
public import StationaryHarmonicMaps.Analysis.LocalLpCriticalCutoff
public import StationaryHarmonicMaps.Analysis.LocalDivCurlContinuousPairing
public import StationaryHarmonicMaps.Analysis.NeumannGradientSpace
public import HarmonicMaps.Analysis.SobolevLocality

/-!
# Actual capped-envelope gradient growth

The bounded, nonempty original capped supremum controls every original
ball term. Positive-radius power cancellation yields the actual critical
Lp amplitude from its same value at eight times the reference radius.

-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The actual finite cutoff envelope produces the same native graph and genuine all-center gradient growth with amplitude Ψ(8t)^(1/p), including zero amplitude. -/
theorem cutoff_capped_envelope_lp_growth (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hp₁ : 1≤p) (hp₂ : p≤2) (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (m : ℕ) (u : Domain n → Ambient m) (Du : Domain n → Gradient n m) (η : ℝ)
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du) (hη : 0≤η)
    (hCritical : criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2))
    (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ⊆Metric.closedBall (0 : Domain n) (3/4 : ℝ))
    (hχA : ∀ x,|χ x|≤A) (hDχB : ∀ (x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B)
    (t : ℝ) (ht : 0<t) (htCap : t≤(1/128 : ℝ)) :
    let c := ⨍ y in Metric.ball (0 : Domain n) 1,u y
    let v := fun x=>χ x • (u x-c)
    let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
    let Φ := fun (x : Domain n) (r : ℝ)=>r^(p-(n : ℝ))*∫ y in Metric.ball x r,(Real.sqrt (hsNormSq (Dv y)))^p
    let Ψ := fun s : ℝ=>sSup {z : ℝ | ∃ x r,0<r ∧ r≤s ∧ z=Φ x r}
    MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv ∧ 0≤Ψ (8*t) ∧
      ∀ (x : Domain n) (r : ℝ),0<r → r≤8*t →
        (∫ y in Metric.ball x r,(Real.sqrt (hsNormSq (Dv y)))^p)≤
          ((Ψ (8*t))^(1/p))^p*r^((n : ℝ)-p) := by
  intro c v Dv Φ Ψ
  have hp : 0<p := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) hp₁
  obtain ⟨E,_hE,H⟩ := exists_cutoff_capped_envelope n hn p hp₁ hp₂ A B hA hB
  obtain ⟨hW,Henv⟩ := H m u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχB
  obtain ⟨hNonneg,_hUpper,hTerm,_hMono,_hMean⟩ := Henv (8*t) (by positivity) (by linarith only [htCap])
  refine ⟨hW,hNonneg,?_⟩
  intro x r hr hrCap
  have hCancel : r^((n : ℝ)-p)*r^(p-(n : ℝ))=1 := by
    rw [← Real.rpow_add hr]
    have hExp : (n : ℝ)-p+(p-(n : ℝ))=0 := by ring
    rw [hExp,Real.rpow_zero]
  have hGrowth := mul_le_mul_of_nonneg_left (hTerm x r hr hrCap) (Real.rpow_nonneg hr.le ((n : ℝ)-p))
  change r^((n : ℝ)-p)*(r^(p-(n : ℝ))*∫ y in Metric.ball x r,(Real.sqrt (hsNormSq (Dv y)))^p)≤
    r^((n : ℝ)-p)*Ψ (8*t) at hGrowth
  rw [← mul_assoc,hCancel,one_mul] at hGrowth
  rw [one_div,Real.rpow_inv_rpow hNonneg hp.ne']
  exact hGrowth.trans_eq (mul_comm _ _)


end StationaryHarmonicMaps.Analysis

end
