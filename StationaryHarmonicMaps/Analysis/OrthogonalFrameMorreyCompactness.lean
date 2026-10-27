module

public import StationaryHarmonicMaps.Analysis.OrthogonalFrameL2Compactness
public import StationaryHarmonicMaps.Analysis.WeakHSMorreyClosure

/-!
# Actual native orthogonal frame limits in the complete critical Morrey class

The original complete critical bound controls total gradient energy on B1.
The native whole-ball frame limit has weak convergence of the same original
columns. Actual indicator tests preserve the complete truncated-ball
supremum, including every center and every positive radius.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original complete Morrey bounds produce a native orthogonal frame limit in the same class. -/
theorem exists_criticalMorrey_orthogonal_frame_L2_limit_unitBall {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q))
    (R : Ambient (q * q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀ z, E (R z) = z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (p : ℕ → Domain n → Ambient (q * q)) (Dp : ℕ → Domain n → Gradient n (q * q))
    (hp : ∀ k, MemW12 (ballDomain (0 : Domain n) 1) (p k) (Dp k))
    (horth : ∀ k, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      star (R (p k x)) * R (p k x) = 1)
    (M : ℝ) (hM : 0 ≤ M)
    (hcritical : ∀ k, criticalGradientMorreySquare (Dp k) (Metric.ball (0 : Domain n) 1) ≤
      ENNReal.ofReal M) :
    ∃ (v : Domain n → Ambient (q * q)) (Dv : Domain n → Gradient n (q * q)),
      MemW12 (ballDomain (0 : Domain n) 1) v Dv ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), star (R (v x)) * R (v x) = 1) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), ‖v x‖ = Real.sqrt (q : ℝ)) ∧
      (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Dv x)) ≤ M ∧
      criticalGradientMorreySquare Dv (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal M ∧
      MemW12 (ballDomain (0 : Domain n) 1) (fun x => E (R (v x)))
        (fun x i => E (R (Dv x i))) ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun k => eLpNorm (p (σ k) - v) 2
          (volume.restrict (Metric.ball (0 : Domain n) 1))) atTop (𝓝 0) ∧
        ∀ (i : Fin n) (g : Domain n → Ambient (q * q)),
          MemLp g 2 (volume.restrict (Metric.ball (0 : Domain n) 1)) →
          Tendsto (fun k => ∫ x in Metric.ball (0 : Domain n) 1,
            inner ℝ (Dp (σ k) x i) (g x)) atTop
            (𝓝 (∫ x in Metric.ball (0 : Domain n) 1, inner ℝ (Dv x i) (g x))) := by
  have henergy (k : ℕ) : (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Dp k x)) ≤ M := by
    have H := integral_hsNormSq_le_of_criticalMorrey (Dp k)
      (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)) (by norm_num : (0 : ℝ) < 1) hM
      (subset_inter (Subset.refl _) (Subset.refl _)) (hp k).2.2 (hcritical k)
    simpa only [Real.one_rpow, mul_one] using H
  obtain ⟨v, Dv, hW, hlimitorth, hnorm, hEDv, hNative, σ, hσ, hstrong, hweak⟩ :=
    exists_strong_weak_orthogonal_frame_L2_limit_unitBall E R hER hE p Dp hp horth M hM henergy
  have hlimitCritical := criticalMorrey_bound_of_weak_L2_limit (Metric.ball (0 : Domain n) 1)
    measurableSet_ball (fun k => Dp (σ k)) Dv (fun k i => (hp (σ k)).2.2 i) hW.2.2
      hweak hM (fun k => hcritical (σ k))
  exact ⟨v, Dv, hW, hlimitorth, hnorm, hEDv, hlimitCritical, hNative, σ, hσ, hstrong, hweak⟩

end StationaryHarmonicMaps.Analysis

end
