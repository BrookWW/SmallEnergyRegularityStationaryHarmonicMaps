module

public import StationaryHarmonicMaps.Analysis.SpecialOrthogonalNaturalCompactness
public import StationaryHarmonicMaps.Analysis.WeakHSPowerGrowthClosure

/-!
# Stronger power growth on the same natural special orthogonal subsequence

The original joint compactness theorem supplies one native map, its actual
weak derivative and the literal natural connection. Indicator localization
of the same weak limits preserves the additional original power bounds.
No further subsequence is selected and no critical bound is inferred from
an unnormalized total-energy estimate.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

private theorem column_energy_le_complete_critical {n m : ℕ}
    (F : Domain n → Gradient n m)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    {M : ℝ} (hM : 0 ≤ M)
    (hCritical : criticalGradientMorreySquare F (ball (0 : Domain n) 1) ≤ ENNReal.ofReal M)
    (i : Fin n) : (∫ x in ball (0 : Domain n) 1, ‖F x i‖ ^ 2) ≤ M := by
  have hTotal := integral_hsNormSq_le_of_criticalMorrey F
    (mem_ball_self (by norm_num : (0 : ℝ) < 1)) (by norm_num : (0 : ℝ) < 1) hM
    (subset_inter (Subset.refl _) (Subset.refl _)) hF hCritical
  have hColumn : (∫ x in ball (0 : Domain n) 1, ‖F x i‖ ^ 2) ≤
      ∫ x in ball (0 : Domain n) 1, hsNormSq (F x) := by
    apply integral_mono ((hF i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
      (integrable_hsNormSq_of_columns F hF)
    intro x
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖F x j‖) (Finset.mem_univ i)
  exact hColumn.trans (by simpa only [Real.one_rpow, mul_one] using hTotal)

/-- The same actual joint native special orthogonal limit preserves the
original uniform real-power growth of both its derivative and its literal
natural connection, together with all original critical bounds and tests. -/
theorem exists_special_orthogonal_natural_power_growth_limit_unitBall {n q : ℕ}
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
          star (R (p k x)) * R (A k x i) * R (p k x))) (Dψ x i)) = 0)
    (ν KD KZ : ℝ) (hKD : 0 ≤ KD) (hKZ : 0 ≤ KZ)
    (hGrowthD : ∀ k x, x ∈ ball (0 : Domain n) 1 → ∀ r : ℝ, 0 < r →
      (∫ y in ball x r ∩ ball (0 : Domain n) 1, hsNormSq (Dp k y)) ≤ KD * r ^ ν)
    (hGrowthZ : ∀ k x, x ∈ ball (0 : Domain n) 1 → ∀ r : ℝ, 0 < r →
      (∫ y in ball x r ∩ ball (0 : Domain n) 1, hsNormSq (fun i =>
        E (star (R (p k y)) * R (Dp k y i) +
          star (R (p k y)) * R (A k y i) * R (p k y)))) ≤ KZ * r ^ ν) :
    ∃ (σ : ℕ → ℕ) (v : Domain n → Ambient (q*q)) (Dv : Domain n → Gradient n (q*q)),
      StrictMono σ ∧ MemW12 (ballDomain (0 : Domain n) 1) v Dv ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), star (R (v x)) * R (v x) = 1) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), (R (v x)).det = 1) ∧
      criticalGradientMorreySquare Dv (ball (0 : Domain n) 1) ≤ ENNReal.ofReal MD ∧
      Tendsto (fun k => eLpNorm (p (σ k)-v) 2 (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0) ∧
      (∀ (i : Fin n) (g : Domain n → Ambient (q*q)),
        MemLp g 2 (volume.restrict (ball (0 : Domain n) 1)) →
        Tendsto (fun k => ∫ x in ball (0 : Domain n) 1, inner ℝ (Dp (σ k) x i) (g x)) atTop
          (𝓝 (∫ x in ball (0 : Domain n) 1, inner ℝ (Dv x i) (g x)))) ∧
      (∀ x, x ∈ ball (0 : Domain n) 1 → ∀ r : ℝ, 0 < r →
        IntegrableOn (fun y => hsNormSq (Dv y)) (ball x r ∩ ball (0 : Domain n) 1) volume ∧
        (∫ y in ball x r ∩ ball (0 : Domain n) 1, hsNormSq (Dv y)) ≤ KD * r ^ ν) ∧
      let Z := fun x i => E (star (R (v x)) * R (Dv x i) + star (R (v x)) * R (a x i) * R (v x))
      (∀ i, MemLp (fun x => Z x i) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
      criticalGradientMorreySquare Z (ball (0 : Domain n) 1) ≤ ENNReal.ofReal MZ ∧
      (∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (Z x i) (Dψ x i))
          (ball (0 : Domain n) 1) volume ∧
        (∫ x in ball (0 : Domain n) 1, ∑ i : Fin n, inner ℝ (Z x i) (Dψ x i)) = 0) ∧
      ∀ x, x ∈ ball (0 : Domain n) 1 → ∀ r : ℝ, 0 < r →
        IntegrableOn (fun y => hsNormSq (Z y)) (ball x r ∩ ball (0 : Domain n) 1) volume ∧
        (∫ y in ball x r ∩ ball (0 : Domain n) 1, hsNormSq (Z y)) ≤ KZ * r ^ ν := by
  obtain ⟨σ,v,Dv,hσ,hv,hOrth,hDet,hCritical,hStrong,hWeak,hZ,hCriticalZLimit,hTests⟩ :=
    exists_special_orthogonal_natural_critical_limit_unitBall E R hRE hER hE p Dp hp horth hdet
      A a hA ha hStrongA hMD hMA hMZ hCriticalD hCriticalA hCriticalZ hNatural
  have hDvGrowth := power_growth_bound_of_weak_L2_limit (ball (0 : Domain n) 1)
    measurableSet_ball (fun k => Dp (σ k)) Dv (fun k => (hp (σ k)).2.2) hv.2.2 hWeak
    ν KD hKD (fun k => hGrowthD (σ k))
  let μ := volume.restrict (ball (0 : Domain n) 1)
  have hFrameBound (k : ℕ) : ∀ᵐ x ∂μ, ‖p (σ k) x‖ ≤ Real.sqrt (q : ℝ) :=
    ae_orthogonal_coordinates_bound (Ω := ballDomain (0 : Domain n) 1)
      E R hER hE (p (σ k)) (horth (σ k))
  have hWeakA (i : Fin n) (g : Domain n → Ambient (q*q)) (hg : MemLp g 2 μ) :
      Tendsto (fun k => ∫ x in ball (0 : Domain n) 1, inner ℝ (A (σ k) x i) (g x)) atTop
        (𝓝 (∫ x in ball (0 : Domain n) 1, inner ℝ (a x i) (g x))) := by
    have H := (HolderToCK.tendsto_integral_inner_of_L2 (fun k => hA k i) (ha i) hg
      (hStrongA i)).comp hσ.tendsto_atTop
    change Tendsto (fun k => ∫ x in ball (0 : Domain n) 1, inner ℝ (g x) (A (σ k) x i)) atTop
      (𝓝 (∫ x in ball (0 : Domain n) 1, inner ℝ (g x) (a x i))) at H
    change Tendsto (fun k => ∫ x in ball (0 : Domain n) 1, inner ℝ (A (σ k) x i) (g x)) atTop
      (𝓝 (∫ x in ball (0 : Domain n) 1, inner ℝ (a x i) (g x)))
    simpa only [real_inner_comm] using H
  have hEnergyD (k : ℕ) (i : Fin n) :
      (∫ x in ball (0 : Domain n) 1, ‖Dp (σ k) x i‖ ^ 2) ≤ MD :=
    column_energy_le_complete_critical (Dp (σ k)) (hp (σ k)).2.2 hMD (hCriticalD (σ k)) i
  have hEnergyA (k : ℕ) (i : Fin n) :
      (∫ x in ball (0 : Domain n) 1, ‖A (σ k) x i‖ ^ 2) ≤ MA :=
    column_energy_le_complete_critical (A (σ k)) (hA (σ k)) hMA (hCriticalA (σ k)) i
  have hConnection (i : Fin n) := weak_L2_limit_matrix_connection_encoding μ E R hRE
    (fun k => p (σ k)) v (fun k => (hp (σ k)).2.1) hv.2.1 hStrong hFrameBound
    (fun k x => Dp (σ k) x i) (fun k x => A (σ k) x i)
    (fun x => Dv x i) (fun x => a x i)
    (fun k => (hp (σ k)).2.2 i) (hv.2.2 i) (fun k => hA (σ k) i) (ha i)
    (hWeak i) (hWeakA i) (fun k => hEnergyD k i) (fun k => hEnergyA k i)
  have hZGrowth := power_growth_bound_of_weak_L2_limit (ball (0 : Domain n) 1)
    measurableSet_ball
    (fun k x i => E (star (R (p (σ k) x)) * R (Dp (σ k) x i) +
      star (R (p (σ k) x)) * R (A (σ k) x i) * R (p (σ k) x)))
    (fun x i => E (star (R (v x)) * R (Dv x i) + star (R (v x)) * R (a x i) * R (v x)))
    (fun k i => (hConnection i).2.1 k) (fun i => (hConnection i).1)
    (fun i => (hConnection i).2.2) ν KZ hKZ (fun k => hGrowthZ (σ k))
  exact ⟨σ,v,Dv,hσ,hv,hOrth,hDet,hCritical,hStrong,hWeak,hDvGrowth,hZ,hCriticalZLimit,hTests,hZGrowth⟩

end StationaryHarmonicMaps.Analysis

end
