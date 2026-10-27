module

public import StationaryHarmonicMaps.Analysis.SmoothLpPoincare
public import StationaryHarmonicMaps.Analysis.LpSobolevLimit
public import StationaryHarmonicMaps.Analysis.ZeroBoundaryPoincare
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtEncoding
public import HarmonicMaps.Analysis.SobolevSmoothDensity

/-!
# Actual weak ball Poincare with the same lower exponent

The complete HS encoding transfers columnwise L2 approximation to its
actual norm. The lower norm-power integral limit and smooth segment
inequality therefore give Poincare for the original weak columns, with
the same exponent p on both sides.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Strong convergence of every actual column gives strong L2 convergence of the full HS norm. -/
theorem tendsto_hsNorm_eLpNorm_of_columns_L2 {n q : ℕ} {μ : Measure (Domain n)}
    (F : ℕ → Domain n → Gradient n q) (G : Domain n → Gradient n q)
    (hF : ∀ k i, MemLp (fun x => F k x i) 2 μ)
    (hG : ∀ i, MemLp (fun x => G x i) 2 μ)
    (hconv : ∀ i, Tendsto (fun k => eLpNorm (fun x => F k x i-G x i) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm
      ((fun x => Real.sqrt (hsNormSq (F k x)))-(fun x => Real.sqrt (hsNormSq (G x)))) 2 μ)
      atTop (𝓝 0) := by
  let E := fun A : Gradient n q => WithLp.toLp 2 (fun j : Fin (n*q) =>
    A (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
  have hE (A : Gradient n q) : ‖E A‖^2=hsNormSq A := hs_flatten_norm_sq A
  have hEn (A : Gradient n q) : Real.sqrt (hsNormSq A)=‖E A‖ := by
    rw [← hE, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hD (k : ℕ) (i : Fin n) : MemLp (fun x => F k x i-G x i) 2 μ :=
    (hF k i).sub (hG i)
  have hzero := tendsto_integral_hsNormSq_of_columns_L2 (Du := fun _ _ => (0 : Ambient q)) hD (fun _ => MemLp.zero)
    (fun i => by simpa only [Pi.zero_apply, sub_zero] using hconv i)
  have hzero' : Tendsto (fun k => ∫ x, hsNormSq (fun i => F k x i-G x i) ∂μ) atTop (𝓝 0) := by
    simpa only [hsNormSq, Pi.zero_apply, norm_zero, zero_pow (by decide : (2 : ℕ)≠0), Finset.sum_const_zero,
      integral_zero] using hzero
  have hED (k : ℕ) : MemLp (fun x => E (F k x)-E (G x)) 2 μ :=
    (memLp_hs_flatten (F k) (hF k)).sub (memLp_hs_flatten G hG)
  have hEq (k : ℕ) (x : Domain n) : E (F k x)-E (G x)=E (fun i => F k x i-G x i) := by
    ext j
    rfl
  have hNorm (k : ℕ) : eLpNorm (fun x => E (F k x)-E (G x)) 2 μ =
      ENNReal.ofReal (Real.sqrt (∫ x, hsNormSq (fun i => F k x i-G x i) ∂μ)) := by
    rw [(hED k).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, hEq, hE, Real.sqrt_eq_rpow, one_div]
  have hLim := ENNReal.tendsto_ofReal (Real.continuous_sqrt.continuousAt.tendsto.comp hzero')
  have hLim' : Tendsto (fun k => eLpNorm (fun x => E (F k x)-E (G x)) 2 μ) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ← hNorm, Real.sqrt_zero, ENNReal.ofReal_zero] using hLim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLim' (fun _ => zero_le)
  intro k
  apply eLpNorm_mono_ae
  exact Eventually.of_forall fun x => by
    change ‖Real.sqrt (hsNormSq (F k x))-Real.sqrt (hsNormSq (G x))‖ ≤ ‖E (F k x)-E (G x)‖
    rw [hEn, hEn]
    simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (E (F k x)) (E (G x))

/-- The actual native W12 map satisfies ball Poincare at each exponent between one and two. -/
theorem sobolev_poincare_lp_ball {n q : ℕ} (a : Domain n) {r p : ℝ}
    (hr : 0 < r) (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a r) u Du) :
    (∫ x in Metric.ball a r, ‖u x-(⨍ y in Metric.ball a r, u y)‖^p) ≤
      (2*r*Real.sqrt (n : ℝ))^p * (2 : ℝ)^n *
        ∫ x in Metric.ball a r, (Real.sqrt (hsNormSq (Du x)))^p := by
  let μ : Measure (Domain n) := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (ballDomain a r).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  obtain ⟨m,hm,hmW,hconv,hDconv⟩ := hu.smoothDensity_memW12_ball hr
  have hleft := tendsto_integral_centered_rpow_of_L2 (fun k => (hmW k).2.1) hu.2.1 hconv hp hp₂
  have hHSconv := tendsto_hsNorm_eLpNorm_of_columns_L2
    (fun k x i => fderiv ℝ (m k) x (EuclideanSpace.single i 1)) Du
    (fun k => (hmW k).2.2) hu.2.2 hDconv
  have hHSm (k : ℕ) : MemLp (fun x => Real.sqrt (hsNormSq
      (fun i => fderiv ℝ (m k) x (EuclideanSpace.single i 1)))) 2 μ :=
    memLp_sqrt_sum_norm_sq _ (hmW k).2.2
  have hHSu : MemLp (fun x => Real.sqrt (hsNormSq (Du x))) 2 μ :=
    memLp_sqrt_sum_norm_sq Du hu.2.2
  have hright := tendsto_integral_norm_rpow_of_L2 hHSm hHSu hHSconv hp hp₂
  have hright' : Tendsto (fun k => ∫ x in Metric.ball a r, (Real.sqrt (hsNormSq
      (fun i => fderiv ℝ (m k) x (EuclideanSpace.single i 1))))^p) atTop
      (𝓝 (∫ x in Metric.ball a r, (Real.sqrt (hsNormSq (Du x)))^p)) := by
    simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hright
  exact le_of_tendsto_of_tendsto hleft
    (hright'.const_mul ((2*r*Real.sqrt (n : ℝ))^p*(2 : ℝ)^n))
    (Eventually.of_forall fun k => smooth_poincare_lp_ball a hr hp hp₂ (hm k).contDiffOn
      (hmW k).2.1 (hmW k).2.2)

end StationaryHarmonicMaps.Analysis

end
