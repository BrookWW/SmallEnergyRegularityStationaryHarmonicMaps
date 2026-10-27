module

public import StationaryHarmonicMaps.Analysis.WeakNaturalCoulombClosure
public import StationaryHarmonicMaps.Analysis.OrthogonalFrameMorreyCompactness

/-!
# Actual compactness of natural Coulomb frames in the complete critical class

Original native orthogonal frames with complete critical gradient bounds
have a genuine same-map strong L2 and same-gradient weak L2 subsequence.
Strong L2 convergence of the original coefficient fields and actual weak
matrix products retain the literal connection, its complete critical bound
and every native natural boundary test. This is a closure theorem for
actual given frames, and does not construct a Morrey gauge from a potential.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

private theorem column_energy_le_critical_unitBall {n m : ℕ}
    (F : Domain n → Gradient n m)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    {M : ℝ} (hM : 0 ≤ M)
    (hcritical : criticalGradientMorreySquare F (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal M)
    (i : Fin n) : (∫ x in Metric.ball (0 : Domain n) 1, ‖F x i‖ ^ 2) ≤ M := by
  have hTotal := integral_hsNormSq_le_of_criticalMorrey F
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)) (by norm_num : (0 : ℝ) < 1) hM
    (subset_inter (Subset.refl _) (Subset.refl _)) hF hcritical
  have hCol : (∫ x in Metric.ball (0 : Domain n) 1, ‖F x i‖ ^ 2) ≤
      ∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (F x) := by
    apply integral_mono ((hF i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
      (integrable_hsNormSq_of_columns F hF)
    intro x
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖F x j‖) (Finset.mem_univ i)
  exact hCol.trans (by simpa only [Real.one_rpow,mul_one] using hTotal)

/-- The original complete class and natural tests produce a genuine native orthogonal subsequential limit with the same literal connection. -/
theorem exists_natural_coulomb_critical_limit_unitBall {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀ T, R (E T) = T) (hER : ∀ z, E (R z) = z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (p : ℕ → Domain n → Ambient (q*q)) (Dp : ℕ → Domain n → Gradient n (q*q))
    (hp : ∀ k, MemW12 (ballDomain (0 : Domain n) 1) (p k) (Dp k))
    (horth : ∀ k, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      star (R (p k x)) * R (p k x) = 1)
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
  obtain ⟨v,Dv,hv,hvorth,_hNorm,_hEDv,hDvCritical,_hNative,σ,hσ,hStrong,hWeak⟩ :=
    exists_criticalMorrey_orthogonal_frame_L2_limit_unitBall E R hER hE p Dp hp horth MD hMD hCriticalD
  let Ω := ballDomain (0 : Domain n) 1
  let μ := volume.restrict Ω.val
  have hBound (k : ℕ) : ∀ᵐ x ∂μ, ‖p (σ k) x‖ ≤ Real.sqrt (q : ℝ) :=
    ae_orthogonal_coordinates_bound E R hER hE (p (σ k)) (horth (σ k))
  have hWeakA (i : Fin n) (b : Domain n → Ambient (q*q)) (hb : MemLp b 2 μ) :
      Tendsto (fun k => ∫ x in Ω.val, inner ℝ (A (σ k) x i) (b x)) atTop
        (𝓝 (∫ x in Ω.val, inner ℝ (a x i) (b x))) := by
    have H := (HolderToCK.tendsto_integral_inner_of_L2 (fun k => hA k i) (ha i) hb (hStrongA i)).comp hσ.tendsto_atTop
    change Tendsto (fun k => ∫ x in Metric.ball (0 : Domain n) 1, inner ℝ (b x) (A (σ k) x i)) atTop
      (𝓝 (∫ x in Metric.ball (0 : Domain n) 1, inner ℝ (b x) (a x i))) at H
    change Tendsto (fun k => ∫ x in Metric.ball (0 : Domain n) 1, inner ℝ (A (σ k) x i) (b x)) atTop
      (𝓝 (∫ x in Metric.ball (0 : Domain n) 1, inner ℝ (a x i) (b x)))
    simpa only [real_inner_comm] using H
  have hED (k : ℕ) (i : Fin n) : (∫ x in Ω.val, ‖Dp (σ k) x i‖ ^ 2) ≤ MD :=
    column_energy_le_critical_unitBall (Dp (σ k)) (hp (σ k)).2.2 hMD (hCriticalD (σ k)) i
  have hEA (k : ℕ) (i : Fin n) : (∫ x in Ω.val, ‖A (σ k) x i‖ ^ 2) ≤ MA :=
    column_energy_le_critical_unitBall (A (σ k)) (hA (σ k)) hMA (hCriticalA (σ k)) i
  have H (i : Fin n) := weak_L2_limit_matrix_connection_encoding μ E R hRE
    (fun k => p (σ k)) v (fun k => (hp (σ k)).2.1) hv.2.1 hStrong hBound
    (fun k x => Dp (σ k) x i) (fun k x => A (σ k) x i)
    (fun x => Dv x i) (fun x => a x i)
    (fun k => (hp (σ k)).2.2 i) (hv.2.2 i) (fun k => hA (σ k) i) (ha i)
    (hWeak i) (hWeakA i) (fun k => hED k i) (fun k => hEA k i)
  have hNat := native_gradient_tests_of_weak_L2_limit Ω
    (fun k x i => E (star (R (p (σ k) x)) * R (Dp (σ k) x i) +
      star (R (p (σ k) x)) * R (A (σ k) x i) * R (p (σ k) x)))
    (fun x i => E (star (R (v x)) * R (Dv x i) + star (R (v x)) * R (a x i) * R (v x)))
    (fun k i => (H i).2.1 k) (fun i => (H i).1) (fun i => (H i).2.2)
    (fun k => hNatural (σ k))
  have hMZLimit := criticalMorrey_bound_of_weak_L2_limit Ω.val Ω.property.measurableSet
    (fun k x i => E (star (R (p (σ k) x)) * R (Dp (σ k) x i) +
      star (R (p (σ k) x)) * R (A (σ k) x i) * R (p (σ k) x)))
    (fun x i => E (star (R (v x)) * R (Dv x i) + star (R (v x)) * R (a x i) * R (v x)))
    (fun k i => (H i).2.1 k) (fun i => (H i).1) (fun i => (H i).2.2)
    hMZ (fun k => hCriticalZ (σ k))
  exact ⟨σ,v,Dv,hσ,hv,hvorth,hDvCritical,hStrong,hWeak,fun i => (H i).1,hMZLimit,hNat⟩

end StationaryHarmonicMaps.Analysis

end
