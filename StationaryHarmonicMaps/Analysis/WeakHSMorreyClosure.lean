module

public import StationaryHarmonicMaps.Analysis.HSProductIntegrals
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtEncoding
public import StationaryHarmonicMaps.Analysis.HSWeakL2Subsequence
public import HolderToCK.Analysis.L2PairingContinuity

/-!
# The complete critical Morrey bound under actual weak L2 limits

Testing the true weak limit against itself bounds its HS energy. Indicator
tests localize this argument to every truncated ball. The original literal
double supremum therefore retains the same bound, including all centers
and all positive radii.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual columnwise weak L2 convergence preserves a common full HS energy bound. -/
theorem integral_hsNormSq_weak_limit_le {d n q : ℕ}
    (μ : Measure (Domain d)) (F : ℕ → Domain d → Gradient n q) (G : Domain d → Gradient n q)
    (hF : ∀ k i, MemLp (fun x => F k x i) 2 μ)
    (hG : ∀ i, MemLp (fun x => G x i) 2 μ)
    (hweak : ∀ (i : Fin n) (g : Domain d → Ambient q), MemLp g 2 μ →
      Tendsto (fun k => ∫ x, inner ℝ (F k x i) (g x) ∂μ) atTop
        (𝓝 (∫ x, inner ℝ (G x i) (g x) ∂μ)))
    {B : ℝ} (hB : 0 ≤ B) (henergy : ∀ k, (∫ x, hsNormSq (F k x) ∂μ) ≤ B) :
    (∫ x, hsNormSq (G x) ∂μ) ≤ B := by
  let E : Gradient n q → Ambient (n * q) := fun A => WithLp.toLp 2
    (fun j => A (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
  have hencG : MemLp (fun x => E (G x)) 2 μ := memLp_hs_flatten G hG
  have hnorm (A : Gradient n q) : ‖E A‖ = Real.sqrt (hsNormSq A) := by
    calc
      _ = Real.sqrt (‖E A‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = _ := congrArg Real.sqrt (hs_flatten_norm_sq A)
  have hpair (k : ℕ) :
      (∫ x, ∑ i : Fin n, inner ℝ (F k x i) (G x i) ∂μ) =
        ∑ i : Fin n, ∫ x, inner ℝ (F k x i) (G x i) ∂μ :=
    integral_finsetSum _ (fun i _ => HolderToCK.integrable_inner_of_memLp_two (hF k i) (hG i))
  have hself : (∑ i : Fin n, ∫ x, inner ℝ (G x i) (G x i) ∂μ) =
      ∫ x, hsNormSq (G x) ∂μ := by
    simp only [real_inner_self_eq_norm_sq]
    exact (integral_finsetSum _ (fun i _ => (hG i).integrable_norm_pow (by decide))).symm
  have hlim : Tendsto (fun k => ∫ x, ∑ i : Fin n, inner ℝ (F k x i) (G x i) ∂μ)
      atTop (𝓝 (∫ x, hsNormSq (G x) ∂μ)) := by
    have H := tendsto_finsetSum Finset.univ (fun i _ => hweak i (fun x => G x i) (hG i))
    simpa only [← hpair, hself] using H
  have hbound (k : ℕ) :
      (∫ x, ∑ i : Fin n, inner ℝ (F k x i) (G x i) ∂μ) ≤
        Real.sqrt B * Real.sqrt (∫ x, hsNormSq (G x) ∂μ) := by
    obtain ⟨hprod, hcs⟩ := integral_hs_mul_norm_le (F k) (fun x => E (G x)) (hF k) hencG
    have hI : Integrable (fun x => ∑ i : Fin n, inner ℝ (F k x i) (G x i)) μ :=
      integrable_finsetSum _ (fun i _ => HolderToCK.integrable_inner_of_memLp_two (hF k i) (hG i))
    have hpoint (x : Domain d) : (∑ i : Fin n, inner ℝ (F k x i) (G x i)) ≤
        Real.sqrt (hsNormSq (F k x)) * ‖E (G x)‖ := by
      rw [← hs_flatten_inner (F k x) (G x)]
      exact (real_inner_le_norm _ _).trans_eq (by rw [hnorm])
    have hnormSq : (∫ x, ‖E (G x)‖ ^ 2 ∂μ) = ∫ x, hsNormSq (G x) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => hs_flatten_norm_sq (G x))
    calc
      _ ≤ ∫ x, Real.sqrt (hsNormSq (F k x)) * ‖E (G x)‖ ∂μ := integral_mono hI hprod hpoint
      _ ≤ Real.sqrt (∫ x, hsNormSq (F k x) ∂μ) * Real.sqrt (∫ x, hsNormSq (G x) ∂μ) := by
        simpa only [hnormSq] using hcs
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (henergy k)) (Real.sqrt_nonneg _)
  have hlimit := le_of_tendsto hlim (Eventually.of_forall hbound)
  by_contra hnot
  have hlt : B < ∫ x, hsNormSq (G x) ∂μ := lt_of_not_ge hnot
  have hE : 0 ≤ ∫ x, hsNormSq (G x) ∂μ := integral_nonneg fun x => hsNormSq_nonneg (G x)
  have H := mul_lt_mul_of_pos_right (Real.sqrt_lt_sqrt hB hlt)
    (Real.sqrt_pos.mpr (lt_of_le_of_lt hB hlt))
  rw [← pow_two, Real.sq_sqrt hE] at H
  exact (not_lt_of_ge hlimit) H

private theorem integral_inner_indicator_eq_restrict {n q : ℕ}
    (D S : Set (Domain n)) (hS : MeasurableSet S) (hsub : S ⊆ D)
    (f g : Domain n → Ambient q) :
    (∫ x in D, inner ℝ (f x) (S.indicator g x)) = ∫ x in S, inner ℝ (f x) (g x) := by
  have hpoint : (fun x => inner ℝ (f x) (S.indicator g x)) =
      S.indicator (fun x => inner ℝ (f x) (g x)) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, inner_zero_right]
  rw [hpoint, integral_indicator hS, Measure.restrict_restrict hS,
    inter_eq_left.mpr hsub]

/-- The literal complete critical Morrey square retains its bound under actual weak L2 convergence. -/
theorem criticalMorrey_bound_of_weak_L2_limit {n q : ℕ}
    (D : Set (Domain n)) (hD : MeasurableSet D)
    (F : ℕ → Domain n → Gradient n q) (G : Domain n → Gradient n q)
    (hF : ∀ k i, MemLp (fun x => F k x i) 2 (volume.restrict D))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict D))
    (hweak : ∀ (i : Fin n) (g : Domain n → Ambient q), MemLp g 2 (volume.restrict D) →
      Tendsto (fun k => ∫ x in D, inner ℝ (F k x i) (g x)) atTop
        (𝓝 (∫ x in D, inner ℝ (G x i) (g x))))
    {M : ℝ} (hM : 0 ≤ M)
    (hcritical : ∀ k, criticalGradientMorreySquare (F k) D ≤ ENNReal.ofReal M) :
    criticalGradientMorreySquare G D ≤ ENNReal.ofReal M := by
  unfold criticalGradientMorreySquare
  refine iSup_le fun x => iSup_le fun r => ?_
  let S := Metric.ball x.val r.val ∩ D
  have hS : MeasurableSet S := measurableSet_ball.inter hD
  have hsub : S ⊆ D := inter_subset_right
  have hFs (k : ℕ) (i : Fin n) : MemLp (fun y => F k y i) 2 (volume.restrict S) :=
    (hF k i).mono_measure (Measure.restrict_mono_set volume hsub)
  have hGs (i : Fin n) : MemLp (fun y => G y i) 2 (volume.restrict S) :=
    (hG i).mono_measure (Measure.restrict_mono_set volume hsub)
  have hlocal (i : Fin n) (g : Domain n → Ambient q)
      (hg : MemLp g 2 (volume.restrict S)) :
      Tendsto (fun k => ∫ y in S, inner ℝ (F k y i) (g y)) atTop
        (𝓝 (∫ y in S, inner ℝ (G y i) (g y))) := by
    have hgIndicator : MemLp (S.indicator g) 2 (volume.restrict D) := by
      apply (memLp_indicator_iff_restrict hS).mpr
      simpa only [Measure.restrict_restrict hS, inter_eq_left.mpr hsub] using hg
    have H := hweak i (S.indicator g) hgIndicator
    simpa only [integral_inner_indicator_eq_restrict D S hS hsub] using H
  have hInt : (∫ y in S, hsNormSq (G y)) ≤ M * r.val ^ ((n : ℝ) - 2) :=
    integral_hsNormSq_weak_limit_le (volume.restrict S) F G hFs hGs hlocal
      (mul_nonneg hM (Real.rpow_nonneg r.property.le _))
      (fun k => integral_hsNormSq_le_of_criticalMorrey (F k) x.property r.property hM
        (Subset.refl _) (hFs k) (hcritical k))
  have hcancel : r.val ^ ((n : ℝ) - 2) * r.val ^ (2 - (n : ℤ)) = 1 := by
    rw [← Real.rpow_intCast, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
      ← Real.rpow_add r.property]
    norm_num
  rw [dirichletEnergy_eq_ofReal_integral (integrable_hsNormSq_of_columns G hGs)]
  calc
    _ ≤ ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) *
        ENNReal.ofReal (M * r.val ^ ((n : ℝ) - 2)) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal hInt) _
    _ = ENNReal.ofReal M := by
      rw [← ENNReal.ofReal_mul (zpow_nonneg r.property.le _)]
      congr 1
      calc
        _ = M * (r.val ^ ((n : ℝ) - 2) * r.val ^ (2 - (n : ℤ))) := by ring
        _ = _ := by rw [hcancel, mul_one]

/-- Actual L2 fields with one uniform complete critical bound have a weak subsequence in the same class. -/
theorem exists_weak_criticalMorrey_subsequence {n q : ℕ}
    (F : ℕ → Domain n → Gradient n q)
    (hF : ∀ k i, MemLp (fun x => F k x i) 2
      (volume.restrict (Metric.ball (0 : Domain n) 1)))
    {M : ℝ} (hM : 0 ≤ M)
    (hcritical : ∀ k, criticalGradientMorreySquare (F k) (Metric.ball (0 : Domain n) 1) ≤
      ENNReal.ofReal M) :
    ∃ G : Domain n → Gradient n q,
      (∀ i, MemLp (fun x => G x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) ∧
      (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (G x)) ≤ M ∧
      criticalGradientMorreySquare G (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal M ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∀ (i : Fin n) (g : Domain n → Ambient q),
          MemLp g 2 (volume.restrict (Metric.ball (0 : Domain n) 1)) →
          Tendsto (fun k => ∫ x in Metric.ball (0 : Domain n) 1, inner ℝ (F (σ k) x i) (g x)) atTop
            (𝓝 (∫ x in Metric.ball (0 : Domain n) 1, inner ℝ (G x i) (g x))) := by
  have henergy (k : ℕ) : (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (F k x)) ≤ M := by
    have H := integral_hsNormSq_le_of_criticalMorrey (F k)
      (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)) (by norm_num : (0 : ℝ) < 1) hM
      (subset_inter (Subset.refl _) (Subset.refl _)) (hF k) (hcritical k)
    simpa only [Real.one_rpow, mul_one] using H
  obtain ⟨G, hG, hEG, σ, hσ, hweak⟩ :=
    exists_weak_HS_L2_subsequence (volume.restrict (Metric.ball (0 : Domain n) 1)) F hF hM henergy
  have hlimit := criticalMorrey_bound_of_weak_L2_limit (Metric.ball (0 : Domain n) 1)
    measurableSet_ball (fun k => F (σ k)) G (fun k => hF (σ k)) hG hweak hM
      (fun k => hcritical (σ k))
  exact ⟨G, hG, hEG, hlimit, σ, hσ, hweak⟩

end StationaryHarmonicMaps.Analysis

end
