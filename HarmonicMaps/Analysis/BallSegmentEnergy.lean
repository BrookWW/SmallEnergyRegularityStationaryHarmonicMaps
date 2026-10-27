module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Energy along a segment in an open ball

The derivative density is the sum of squared coordinate-column norms. Local
smoothness on the ball supplies continuity and differentiability at every point
of a segment with endpoints in the ball.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped BigOperators ContDiff

namespace HarmonicMaps

noncomputable section

/-- Coordinate-column energy controls every value of a continuous linear map. -/
theorem norm_apply_sq_le_hsNormSq {n q : ℕ}
    (A : Domain n →L[ℝ] Ambient q) (v : Domain n) :
    ‖A v‖ ^ 2 ≤ ‖v‖ ^ 2 * hsNormSq (fun i => A (EuclideanSpace.single i 1)) := by
  have hrepr : (∑ i : Fin n, v i • EuclideanSpace.single i 1) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  have hnorm : ‖A v‖ ≤ ∑ i : Fin n, |v i| * ‖A (EuclideanSpace.single i 1)‖ := by
    calc
      ‖A v‖ = ‖A (∑ i : Fin n, v i • EuclideanSpace.single i 1)‖ :=
        congrArg (fun w => ‖A w‖) hrepr.symm
      _ = ‖∑ i : Fin n, v i • A (EuclideanSpace.single i 1)‖ := by
        rw [map_sum]
        simp only [map_smul]
      _ ≤ ∑ i : Fin n, ‖v i • A (EuclideanSpace.single i 1)‖ :=
        norm_sum_le _ _
      _ = ∑ i : Fin n, |v i| * ‖A (EuclideanSpace.single i 1)‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
  have hnormsq := pow_le_pow_left₀ (norm_nonneg (A v)) hnorm 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin n => |v i|) (fun i => ‖A (EuclideanSpace.single i 1)‖)
  have hcoord : (∑ i : Fin n, |v i| ^ 2) = ‖v‖ ^ 2 := by
    simpa only [sq_abs] using (EuclideanSpace.real_norm_sq_eq v).symm
  exact hnormsq.trans (by simpa only [hcoord, hsNormSq] using hcs)

/-- The derivative-column density is continuous on the open ball. -/
theorem continuousOn_hsNormSq_fderiv {n q : ℕ}
    {f : Domain n → Ambient q} {a : Domain n} {r : ℝ}
    (hsmooth : ContDiffOn ℝ ∞ f (Metric.ball a r)) :
    ContinuousOn (fun z => hsNormSq (fun i =>
      fderiv ℝ f z (EuclideanSpace.single i 1))) (Metric.ball a r) := by
  have hderiv := hsmooth.continuousOn_fderiv_of_isOpen Metric.isOpen_ball
    (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  unfold hsNormSq
  exact continuousOn_finsetSum Finset.univ fun i _ =>
    (hderiv.clm_apply continuousOn_const).norm.pow 2

/-- Every point of the closed parameter interval lies in the ball. -/
theorem segmentPoint_mem_ball {n : ℕ} {a x y : Domain n} {r t : ℝ}
    (hx : x ∈ Metric.ball a r) (hy : y ∈ Metric.ball a r) (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) • x + t • y ∈ Metric.ball a r := by
  exact (convex_ball a r) hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)

/-- The ball-local density is integrable along each segment in the ball. -/
theorem intervalIntegrable_segment_hsNormSq_fderiv {n q : ℕ}
    {f : Domain n → Ambient q} {a x y : Domain n} {r : ℝ}
    (hsmooth : ContDiffOn ℝ ∞ f (Metric.ball a r))
    (hx : x ∈ Metric.ball a r) (hy : y ∈ Metric.ball a r) :
    IntervalIntegrable (fun t : ℝ => hsNormSq (fun i =>
      fderiv ℝ f ((1 - t) • x + t • y) (EuclideanSpace.single i 1))) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (continuousOn_hsNormSq_fderiv hsmooth).comp
    (by fun_prop) (fun t ht => segmentPoint_mem_ball hx hy ht)

private theorem sq_intervalIntegral_le_intervalIntegral_sq
    {h : ℝ → ℝ} (hcont : ContinuousOn h (Icc (0 : ℝ) 1)) :
    (∫ t in (0 : ℝ)..1, h t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (h t) ^ 2 := by
  let c := ∫ t in (0 : ℝ)..1, h t
  have hi : IntervalIntegrable h volume 0 1 :=
    hcont.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hsq : IntervalIntegrable (fun t => (h t) ^ 2) volume 0 1 :=
    (hcont.pow 2).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hexpand : (fun t => (h t - c) ^ 2) =
      (fun t => (h t) ^ 2 - (2 * c) * h t + c ^ 2) := by
    funext t
    ring
  have hvariance : (∫ t in (0 : ℝ)..1, (h t - c) ^ 2) =
      (∫ t in (0 : ℝ)..1, (h t) ^ 2) - c ^ 2 := by
    rw [hexpand, intervalIntegral.integral_add (hsq.sub (hi.const_mul _))
      intervalIntegrable_const,
      intervalIntegral.integral_sub hsq (hi.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [sub_zero, one_smul]
    dsimp [c]
    ring
  have hnonneg := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (fun t => sq_nonneg (h t - c))
  rw [hvariance] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- The squared endpoint difference is bounded by derivative energy along the segment. -/
theorem segment_energy_bound {n q : ℕ}
    {f : Domain n → Ambient q} {a x y : Domain n} {r : ℝ}
    (hsmooth : ContDiffOn ℝ ∞ f (Metric.ball a r))
    (hx : x ∈ Metric.ball a r) (hy : y ∈ Metric.ball a r) :
    ‖f x - f y‖ ^ 2 ≤ ‖y - x‖ ^ 2 * ∫ t in (0 : ℝ)..1,
      hsNormSq (fun i => fderiv ℝ f ((1 - t) • x + t • y)
        (EuclideanSpace.single i 1)) := by
  let γ : ℝ → Domain n := fun t => (1 - t) • x + t • y
  let d : ℝ → Ambient q := fun t => fderiv ℝ f (γ t) (y - x)
  let g : ℝ → ℝ := fun t => hsNormSq (fun i =>
    fderiv ℝ f (γ t) (EuclideanSpace.single i 1))
  have hγcont : Continuous γ := by dsimp [γ]; fun_prop
  have hγball : MapsTo γ (Icc (0 : ℝ) 1) (Metric.ball a r) :=
    fun t ht => segmentPoint_mem_ball hx hy ht
  have hfdcont := (hsmooth.continuousOn_fderiv_of_isOpen Metric.isOpen_ball
    (by norm_num : (1 : ℕ∞ω) ≤ ∞)).comp hγcont.continuousOn hγball
  have hdcont : ContinuousOn d (Icc (0 : ℝ) 1) :=
    hfdcont.clm_apply continuousOn_const
  have hdi : IntervalIntegrable d volume 0 1 :=
    hdcont.intervalIntegrable_of_Icc (by norm_num)
  have hgi : IntervalIntegrable g volume 0 1 :=
    intervalIntegrable_segment_hsNormSq_fderiv hsmooth hx hy
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (f ∘ γ) (d t) t := by
    intro t ht
    have hf : DifferentiableAt ℝ f (γ t) :=
      (hsmooth.differentiableOn (by norm_num)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (hγball ht))
    have hγderiv : HasDerivAt γ (y - x) t := by
      convert
        (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const x).add
          ((hasDerivAt_id t).smul_const y) using 1
      all_goals first | rfl | simp [sub_eq_add_neg, add_comm]
    exact hf.hasFDerivAt.comp_hasDerivAt t hγderiv
  have hftc : (∫ t in (0 : ℝ)..1, d t) = f y - f x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv t (by simpa only [uIcc_of_le zero_le_one] using ht)) hdi
    simpa only [Function.comp_apply, γ, sub_self, zero_smul, one_smul,
      zero_add, sub_zero, add_zero] using h
  have hnorm : ‖f x - f y‖ ≤ ∫ t in (0 : ℝ)..1, ‖d t‖ := by
    have h := intervalIntegral.norm_integral_le_integral_norm
      (f := d) (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [hftc, norm_sub_rev] using h
  have hnormsq := pow_le_pow_left₀ (norm_nonneg (f x - f y)) hnorm 2
  have hcs := sq_intervalIntegral_le_intervalIntegral_sq hdcont.norm
  have hdi2 : IntervalIntegrable (fun t => ‖d t‖ ^ 2) volume 0 1 :=
    (hdcont.norm.pow 2).intervalIntegrable_of_Icc (by norm_num)
  have hbound := intervalIntegral.integral_mono_on
    (by norm_num : (0 : ℝ) ≤ 1) hdi2 (hgi.const_mul (‖y - x‖ ^ 2))
    (fun t _ => norm_apply_sq_le_hsNormSq (fderiv ℝ f (γ t)) (y - x))
  rw [intervalIntegral.integral_const_mul] at hbound
  exact (hnormsq.trans hcs).trans hbound

/-- The diameter of the ball yields the source segment estimate. -/
theorem ball_segment_energy_bound {n q : ℕ}
    {f : Domain n → Ambient q} {a x y : Domain n} {r : ℝ}
    (hsmooth : ContDiffOn ℝ ∞ f (Metric.ball a r))
    (hx : x ∈ Metric.ball a r) (hy : y ∈ Metric.ball a r) (hr : 0 < r) :
    ‖f x - f y‖ ^ 2 ≤ 4 * r ^ 2 * ∫ t in (0 : ℝ)..1,
      hsNormSq (fun i => fderiv ℝ f ((1 - t) • x + t • y)
        (EuclideanSpace.single i 1)) := by
  have hdist : ‖y - x‖ ≤ 2 * r := by
    have h := dist_triangle y a x
    have hy' : dist y a < r := hy
    have hx' : dist a x < r := by simpa only [Metric.mem_ball, dist_comm] using hx
    rw [dist_eq_norm] at h
    linarith
  have hdist2 : ‖y - x‖ ^ 2 ≤ 4 * r ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg (y - x)) (by positivity : 0 ≤ 2 * r)).mpr hdist
    nlinarith
  have hg : 0 ≤ ∫ t in (0 : ℝ)..1, hsNormSq (fun i =>
      fderiv ℝ f ((1 - t) • x + t • y) (EuclideanSpace.single i 1)) :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) fun _ => hsNormSq_nonneg _
  exact (segment_energy_bound hsmooth hx hy).trans (mul_le_mul_of_nonneg_right hdist2 hg)

/-- The segment estimate with a set integral over the closed unit interval. -/
theorem ball_segment_energy_bound_Icc {n q : ℕ}
    {f : Domain n → Ambient q} {a x y : Domain n} {r : ℝ}
    (hsmooth : ContDiffOn ℝ ∞ f (Metric.ball a r))
    (hx : x ∈ Metric.ball a r) (hy : y ∈ Metric.ball a r) (hr : 0 < r) :
    ‖f x - f y‖ ^ 2 ≤ 4 * r ^ 2 * ∫ t in Icc (0 : ℝ) 1,
      hsNormSq (fun i => fderiv ℝ f ((1 - t) • x + t • y)
        (EuclideanSpace.single i 1)) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact ball_segment_energy_bound hsmooth hx hy hr

end
end HarmonicMaps

end
