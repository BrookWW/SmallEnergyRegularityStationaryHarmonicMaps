module

public import StationaryHarmonicMaps.Analysis.BoundedWeakSobolevL2Compactness
public import StationaryHarmonicMaps.Analysis.OrthogonalCoefficientBounds

/-!
# Actual whole-ball native limits of orthogonal Sobolev frames

Faithful complete HS coordinates turn actual orthogonality into the uniform
value bound sqrt(q). The original native Sobolev graphs therefore have one
whole-ball strong/weak limit. Closedness of the genuine decoded adjoint
equation produces orthogonality of that same limit.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual orthogonal Sobolev frames have one native whole-ball limit in the same coordinates. -/
theorem exists_strong_weak_orthogonal_frame_L2_limit_unitBall {n q : ℕ}
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
    (henergy : ∀ k, (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Dp k x)) ≤ M) :
    ∃ (v : Domain n → Ambient (q * q)) (Dv : Domain n → Gradient n (q * q)),
      MemW12 (ballDomain (0 : Domain n) 1) v Dv ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), star (R (v x)) * R (v x) = 1) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), ‖v x‖ = Real.sqrt (q : ℝ)) ∧
      (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Dv x)) ≤ M ∧
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
  have hbound (k : ℕ) : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      ‖p k x‖ ≤ Real.sqrt (q : ℝ) :=
    ae_orthogonal_coordinates_bound (Ω := ballDomain (0 : Domain n) 1) E R hER hE (p k) (horth k)
  obtain ⟨v, Dv, hW, _hVbound, hEDv, σ, hσ, hstrong, hweak⟩ :=
    exists_bounded_strong_weak_sobolev_L2_limit_unitBall p Dp hp (Real.sqrt (q : ℝ)) M
      (Real.sqrt_nonneg _) hM hbound henergy
  have hlimitorth : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      star (R (v x)) * R (v x) = 1 :=
    ae_decoded_orthogonal_of_L2_limit _ R (fun k => p (σ k)) v
      (fun k => (hp (σ k)).2.1) hW.2.1 hstrong (fun k => horth (σ k))
  have hnorm : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), ‖v x‖ = Real.sqrt (q : ℝ) := by
    filter_upwards [hlimitorth] with x hx
    calc
      _ = ‖E (R (v x))‖ := by rw [hER]
      _ = _ := encoded_orthogonal_frame_norm E hE (R (v x)) hx
  have hNative : MemW12 (ballDomain (0 : Domain n) 1) (fun x => E (R (v x)))
      (fun x i => E (R (Dv x i))) := by
    simpa only [hER] using hW
  exact ⟨v, Dv, hW, hlimitorth, hnorm, hEDv, hNative, σ, hσ, hstrong, hweak⟩

end StationaryHarmonicMaps.Analysis

end
