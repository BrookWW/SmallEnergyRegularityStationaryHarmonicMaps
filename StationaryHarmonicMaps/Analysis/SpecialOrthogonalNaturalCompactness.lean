module

public import StationaryHarmonicMaps.Analysis.NaturalCoulombMorreyCompactness
public import StationaryHarmonicMaps.Analysis.L2ClosedRange
public import StationaryHarmonicMaps.Geometry.OrientationDeterminant

/-!
# Actual special orthogonal natural critical limits

The true determinant is continuous on the full operator carrier. Its
closed value-one fiber passes through actual strong L2 convergence.
The same native critical Coulomb subsequence therefore retains its
original special orthogonal constraint and every natural test.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual strong L2 limits preserve the original decoded determinant-one equation. -/
theorem ae_decoded_det_one_of_L2_limit {X : Type*} [MeasurableSpace X] {m q : ℕ}
    (μ : Measure X) (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (p : ℕ → X → Ambient m) (v : X → Ambient m)
    (hp : ∀ k, MemLp (p k) 2 μ) (hv : MemLp v 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (p k-v) 2 μ) atTop (𝓝 0))
    (hdet : ∀ k, ∀ᵐ x ∂μ, (R (p k x)).det = 1) :
    ∀ᵐ x ∂μ, (R (v x)).det = 1 := by
  have hclosed : IsClosed {z : Ambient m | (R z).det = 1} :=
    isClosed_eq (((contDiff_operator_det q).continuous).comp R.continuous) continuous_const
  exact ae_mem_closed_of_L2_limit μ p v hp hv hconv _ hclosed hdet

/-- Original special orthogonal frames retain their determinant, complete critical bounds and all natural tests on the same actual native limit subsequence. -/
theorem exists_special_orthogonal_natural_critical_limit_unitBall {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀ T, R (E T) = T) (hER : ∀ z, E (R z) = z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (p : ℕ → Domain n → Ambient (q*q)) (Dp : ℕ → Domain n → Gradient n (q*q))
    (hp : ∀ k, MemW12 (ballDomain (0 : Domain n) 1) (p k) (Dp k))
    (horth : ∀ k, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      star (R (p k x)) * R (p k x) = 1)
    (hdet : ∀ k, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), (R (p k x)).det = 1)
    (A : ℕ → Domain n → Gradient n (q*q)) (a : Domain n → Gradient n (q*q))
    (hA : ∀ k i, MemLp (fun x => A k x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (ha : ∀ i, MemLp (fun x => a x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (hStrongA : ∀ i, Tendsto (fun k => eLpNorm (fun x => A k x i-a x i) 2
      (volume.restrict (Metric.ball (0 : Domain n) 1))) atTop (𝓝 0))
    {MD MA MZ : ℝ} (hMD : 0 ≤ MD) (hMA : 0 ≤ MA) (hMZ : 0 ≤ MZ)
    (hCriticalD : ∀ k, criticalGradientMorreySquare (Dp k) (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal MD)
    (hCriticalA : ∀ k, criticalGradientMorreySquare (A k) (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal MA)
    (hCriticalZ : ∀ k, criticalGradientMorreySquare
      (fun x i => E (star (R (p k x)) * R (Dp k x i) +
        star (R (p k x)) * R (A k x i) * R (p k x))) (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal MZ)
    (hNatural : ∀ k (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
      MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
      (∫ x in Metric.ball (0 : Domain n) 1, ∑ i : Fin n, inner ℝ
        (E (star (R (p k x)) * R (Dp k x i) +
          star (R (p k x)) * R (A k x i) * R (p k x))) (Dψ x i)) = 0) :
    ∃ (σ : ℕ → ℕ) (v : Domain n → Ambient (q*q)) (Dv : Domain n → Gradient n (q*q)),
      StrictMono σ ∧ MemW12 (ballDomain (0 : Domain n) 1) v Dv ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), star (R (v x)) * R (v x) = 1) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), (R (v x)).det = 1) ∧
      criticalGradientMorreySquare Dv (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal MD ∧
      Tendsto (fun k => eLpNorm (p (σ k)-v) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) atTop (𝓝 0) ∧
      (∀ (i : Fin n) (b : Domain n → Ambient (q*q)),
        MemLp b 2 (volume.restrict (Metric.ball (0 : Domain n) 1)) →
        Tendsto (fun k => ∫ x in Metric.ball (0 : Domain n) 1, inner ℝ (Dp (σ k) x i) (b x)) atTop
          (𝓝 (∫ x in Metric.ball (0 : Domain n) 1, inner ℝ (Dv x i) (b x)))) ∧
      let Z := fun x i => E (star (R (v x)) * R (Dv x i) + star (R (v x)) * R (a x i) * R (v x))
      (∀ i, MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) ∧
      criticalGradientMorreySquare Z (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal MZ ∧
      ∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (Z x i) (Dψ x i))
          (Metric.ball (0 : Domain n) 1) volume ∧
        (∫ x in Metric.ball (0 : Domain n) 1, ∑ i : Fin n, inner ℝ (Z x i) (Dψ x i)) = 0 := by
  obtain ⟨σ,v,Dv,hσ,hv,hvo,hCrit,hStrong,hWeak,hZ,hMZLimit,hTests⟩ :=
    exists_natural_coulomb_critical_limit_unitBall E R hRE hER hE p Dp hp horth
      A a hA ha hStrongA hMD hMA hMZ hCriticalD hCriticalA hCriticalZ hNatural
  have hdetv := ae_decoded_det_one_of_L2_limit
    (volume.restrict (Metric.ball (0 : Domain n) 1)) R (fun k => p (σ k)) v
    (fun k => (hp (σ k)).2.1) hv.2.1 hStrong (fun k => hdet (σ k))
  exact ⟨σ,v,Dv,hσ,hv,hvo,hdetv,hCrit,hStrong,hWeak,hZ,hMZLimit,hTests⟩

end StationaryHarmonicMaps.Analysis

end
