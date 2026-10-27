module

public import HarmonicMaps.Analysis.SobolevPoincare
public import HarmonicMaps.Analysis.SmoothWeakGradient
public import HarmonicMaps.Analysis.MorreyBallEstimates
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Coercive Poincaré estimates from support in an interior ball

A zero region with at least half the surrounding measure controls the
constant component of any L² map. Applying the ordinary ball Poincaré
estimate on a doubled ball then controls a compact smooth map by its
actual gradient without subtracting its mean.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- A half-mass zero region controls the full square norm by oscillation about any constant. -/
theorem integral_norm_sq_le_six_oscillation_of_zero_on_half
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : X → E) (hf : MemLp f 2 μ) (m : E) {K : Set X}
    (hzero : ∀ᵐ x ∂μ.restrict Kᶜ, f x = 0)
    (hhalf : μ.real Set.univ ≤ 2 * μ.real Kᶜ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) ≤ 6 * ∫ x, ‖f x - m‖ ^ 2 ∂μ := by
  have hfi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hgi : Integrable (fun x => ‖f x - m‖ ^ 2) μ :=
    (hf.sub (memLp_const m)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hAnn : (∫ x in Kᶜ, ‖f x - m‖ ^ 2 ∂μ) = μ.real Kᶜ * ‖m‖ ^ 2 := by
    calc
      _ = ∫ _x in Kᶜ, ‖m‖ ^ 2 ∂μ := integral_congr_ae
        (hzero.mono (fun x hx => by rw [hx, zero_sub, norm_neg]))
      _ = _ := by
        rw [integral_const]
        simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  have hmean : μ.real Set.univ * ‖m‖ ^ 2 ≤
      2 * ∫ x, ‖f x - m‖ ^ 2 ∂μ := by
    calc
      _ ≤ 2 * (μ.real Kᶜ * ‖m‖ ^ 2) := by
        nlinarith only [mul_le_mul_of_nonneg_right hhalf (sq_nonneg ‖m‖)]
      _ = 2 * ∫ x in Kᶜ, ‖f x - m‖ ^ 2 ∂μ := by rw [hAnn]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hgi (Eventually.of_forall (fun x => sq_nonneg ‖f x - m‖)))
        (by norm_num)
  have hpoint (x : X) : ‖f x‖ ^ 2 ≤ 2 * ‖f x - m‖ ^ 2 + 2 * ‖m‖ ^ 2 := by
    have hs := pow_le_pow_left₀ (norm_nonneg (f x)) (norm_le_norm_sub_add (f x) m) 2
    nlinarith only [hs, sq_nonneg (‖f x - m‖ - ‖m‖)]
  have hbound := integral_mono hfi ((hgi.const_mul 2).add (integrable_const (2 * ‖m‖ ^ 2)))
    hpoint
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hgi.const_mul 2) (integrable_const (2 * ‖m‖ ^ 2)),
    integral_const_mul, integral_const, smul_eq_mul] at hbound
  change (∫ x, ‖f x‖ ^ 2 ∂μ) ≤
    2 * (∫ x, ‖f x - m‖ ^ 2 ∂μ) + μ.real Set.univ * (2 * ‖m‖ ^ 2) at hbound
  nlinarith only [hbound, hmean]


/-- A doubled ball has at least twice the inner mass in every positive dimension. -/
theorem doubled_ball_half_mass {n : ℕ} (hn : 1 ≤ n) (a : Domain n)
    {R : ℝ} (hR : 0 < R) :
    (volume.restrict (Metric.ball a (2 * R))).real Set.univ ≤
      2 * (volume.restrict (Metric.ball a (2 * R))).real (Metric.ball a R)ᶜ := by
  have hsub : Metric.ball a R ⊆ Metric.ball a (2 * R) :=
    Metric.ball_subset_ball (by linarith only [hR])
  have hvol : volume.real (Metric.ball a (2 * R)) =
      (2 : ℝ) ^ n * volume.real (Metric.ball a R) := by
    rw [morrey_ball_volume a (by positivity : 0 < 2 * R), morrey_ball_volume a hR,
      mul_pow]
    ring
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hn
  have hmass : 2 * volume.real (Metric.ball a R) ≤ volume.real (Metric.ball a (2 * R)) := by
    rw [hvol]
    exact mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg
  have hAnn := measureReal_sdiff (μ := (volume : Measure (Domain n))) hsub
    measurableSet_ball measure_ball_ne_top
  have hset : (Metric.ball a R)ᶜ ∩ Metric.ball a (2 * R) =
      Metric.ball a (2 * R) \ Metric.ball a R := by
    ext x
    exact and_comm
  have hcomp : (volume.restrict (Metric.ball a (2 * R))).real (Metric.ball a R)ᶜ =
      volume.real (Metric.ball a (2 * R)) - volume.real (Metric.ball a R) := by
    simp only [measureReal_def, Measure.restrict_apply measurableSet_ball.compl, hset]
    exact hAnn
  have huniv : (volume.restrict (Metric.ball a (2 * R))).real Set.univ =
      volume.real (Metric.ball a (2 * R)) := by
    simp only [measureReal_def, Measure.restrict_apply_univ]
  rw [huniv, hcomp]
  linarith only [hmass]

/-- Ball Poincaré becomes coercive when the map vanishes outside the inner half ball. -/
theorem memW12_supported_doubled_ball_poincare {n q : ℕ} (hn : 1 ≤ n)
    (a : Domain n) {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a (2 * R)) u Du)
    (hzero : ∀ x : Domain n, x ∉ Metric.ball a R → u x = 0) :
    (∫ x in Metric.ball a (2 * R), ‖u x‖ ^ 2) ≤
      (24 * (2 : ℝ) ^ (n + 1)) * R ^ 2 *
        ∫ x in Metric.ball a (2 * R), hsNormSq (Du x) := by
  let μ : Measure (Domain n) := volume.restrict (Metric.ball a (2 * R))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (ballDomain a (2 * R)).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hz : ∀ᵐ x ∂μ.restrict (Metric.ball a R)ᶜ, u x = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
    exact hzero x hx
  have hosc := integral_norm_sq_le_six_oscillation_of_zero_on_half u hu.2.1
    (⨍ x in Metric.ball a (2 * R), u x) hz (doubled_ball_half_mass hn a hR)
  have hp := hu.poincare_ball (by positivity : 0 < 2 * R)
  calc
    _ ≤ 6 * ∫ x in Metric.ball a (2 * R),
        ‖u x - (⨍ y in Metric.ball a (2 * R), u y)‖ ^ 2 := hosc
    _ ≤ 6 * ((2 : ℝ) ^ (n + 1) * (2 * R) ^ 2 *
        ∫ x in Metric.ball a (2 * R), hsNormSq (Du x)) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring



/-- A genuine compact smooth zero-boundary test satisfies a coercive HS Poincaré bound. -/
theorem compactSmooth_zeroBoundary_poincare {n q : ℕ} (hn : 1 ≤ n)
    (a : Domain n) {R : ℝ} (hR : 0 < R)
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Metric.ball a R) :
    (∫ x in Metric.ball a R, ‖ψ x‖ ^ 2) ≤
      (24 * (2 : ℝ) ^ (n + 1)) * R ^ 2 * ∫ x in Metric.ball a R,
        hsNormSq (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
  have hmap : MemLp ψ 2 (volume.restrict (ballDomain a (2 * R)).val) :=
    (hψ.continuous.memLp_of_hasCompactSupport (μ := volume) hcψ).restrict _
  have hcol (i : Fin n) : MemLp (coordinateDerivative ψ hψ i) 2
      (volume.restrict (ballDomain a (2 * R)).val) :=
    (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (μ := volume) (hcψ.fderiv_apply ℝ (EuclideanSpace.single i 1))).restrict _
  have hu := memW12_of_contDiff (ballDomain a (2 * R)) hψ hmap hcol
  have hz (x : Domain n) (hx : x ∉ Metric.ball a R) : ψ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hsψ h))
  have hco := memW12_supported_doubled_ball_poincare hn a hR hu hz
  have hzD (x : Domain n) (hx : x ∉ Metric.ball a R) (i : Fin n) :
      coordinateDerivative ψ hψ i x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx
      (hsψ (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) h)))
  have hzE (x : Domain n) (hx : x ∉ Metric.ball a R) :
      hsNormSq (fun i => coordinateDerivative ψ hψ i x) = 0 := by
    simp only [hsNormSq, hzD x hx, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero]
  have hsub : Metric.ball a R ⊆ Metric.ball a (2 * R) :=
    Metric.ball_subset_ball (by linarith only [hR])
  have heqInt (f : Domain n → ℝ) (hf : ∀ x, x ∉ Metric.ball a R → f x = 0) :
      (∫ x in Metric.ball a (2 * R), f x) = ∫ x in Metric.ball a R, f x := by
    calc
      _ = ∫ x, f x := setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hf x (fun h => hx (hsub h)))
      _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm
  have hmapI := heqInt (fun x => ‖ψ x‖ ^ 2)
    (fun x hx => by rw [hz x hx]; simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
  have henergyI := heqInt (fun x => hsNormSq (fun i => coordinateDerivative ψ hψ i x)) hzE
  rw [hmapI, henergyI] at hco
  simpa only [coordinateDerivative] using hco


end StationaryHarmonicMaps.Analysis

end
