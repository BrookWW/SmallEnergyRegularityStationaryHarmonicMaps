module

public import HarmonicMaps.Analysis.DirichletSmoothData
public import HarmonicMaps.Analysis.SobolevPostcompositionBasic
public import HarmonicMaps.Analysis.QuantitativeRadialCutoff
public import HarmonicMaps.Analysis.SobolevAECongruence
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Smooth zero sphere values give the existing zero boundary closure

The input is smooth on an open neighborhood of the closed source ball.
Vanishing on its sphere gives a boundary-distance bound. The accepted
quantitative radial cutoff supplies compact smooth graph approximants with
the actual coordinate derivative columns.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace HarmonicMaps

private theorem smooth_ballCutoff {n : ℕ} (R : PositiveRadius)
    (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioo 0 1) (hv : ∀ t, 0 ≤ b t ∧ b t ≤ 2)
    (hm : (∫ t, b t) = 1) (δ : ℝ) (hδ : 0 < δ) (hsmall : 4 * δ < R.val) :
    ∃ χ : Domain n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Metric.closedBall 0 (R.val - 2 * δ) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ Metric.ball (0 : Domain n) (R.val - 3 * δ), χ x = 1) ∧
      ∀ x, ‖fderiv ℝ χ x‖ ≤ 2 / δ := by
  let scale : ℝ := (4 * R.val)⁻¹
  let d : ℝ := scale * δ
  let t : ℝ := scale * (R.val - 3 * δ)
  have hscale : 0 < scale := inv_pos.mpr (mul_pos (by norm_num) R.property)
  have hd : 0 < d := mul_pos hscale hδ
  have hdt : d < t := by
    dsimp only [d, t]
    apply mul_lt_mul_of_pos_left _ hscale
    linarith only [hsmall]
  have hhalf : t + 2 * d < 1 / 2 := by
    have heq : t + 2 * d = (R.val - δ) / (4 * R.val) := by
      dsimp only [t, d, scale]
      ring
    rw [heq]
    apply (div_lt_iff₀ (mul_pos (by norm_num) R.property)).mpr
    nlinarith only [R.property, hδ]
  obtain ⟨hsmooth, _, hsupp, _, hvalues, hplateau, _, _, _, hbound⟩ :=
    quantitativeRadialCutoff_properties b hb hc hs hv hm n t d d hd hdt hhalf hd.le le_rfl
  let s : Domain n → ℝ := fun x => d * (1 - ∫ y in Iic ((‖x‖ - t) / d), b y)
  let χ : Domain n → ℝ := fun x => d⁻¹ • s (scale • x)
  have hsmooth' : ContDiff ℝ ∞ s := hsmooth
  have hTdiff : ContDiff ℝ ∞ (fun x : Domain n => scale • x) :=
    ContDiff.const_smul scale contDiff_id
  have hcomp : ContDiff ℝ ∞ (fun x : Domain n => s (scale • x)) :=
    hsmooth'.comp hTdiff
  have hχ : ContDiff ℝ ∞ χ := ContDiff.const_smul d⁻¹ hcomp
  have hnorm (x : Domain n) : ‖scale • x‖ = scale * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg hscale.le]
  have heq : t + d = scale * (R.val - 2 * δ) := by dsimp only [t, d]; ring
  have hsupport : tsupport χ ⊆ Metric.closedBall 0 (R.val - 2 * δ) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    have hsx : s (scale • x) ≠ 0 := by
      intro hz
      apply hx
      change d⁻¹ • s (scale • x) = 0
      rw [hz, smul_zero]
    have hmem := hsupp (subset_tsupport s hsx)
    rw [Metric.mem_closedBall, dist_zero_right, hnorm, heq] at hmem
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (mul_le_mul_iff_right₀ hscale).mp hmem
  refine ⟨χ, hχ,
    (isCompact_closedBall (0 : Domain n) (R.val - 2 * δ)).of_isClosed_subset
      (isClosed_tsupport χ) hsupport, hsupport, ?_, ?_, ?_⟩
  · intro x
    have hx := hvalues (scale • x)
    change 0 ≤ d⁻¹ • s (scale • x) ∧ d⁻¹ • s (scale • x) ≤ 1
    rw [smul_eq_mul]
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hd.le) hx.1
    · exact (mul_le_mul_of_nonneg_left hx.2 (inv_nonneg.mpr hd.le)).trans_eq
        (inv_mul_cancel₀ hd.ne')
  · intro x hx
    have hxnorm : ‖x‖ < R.val - 3 * δ := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    have hmem : scale • x ∈ Metric.ball (0 : Domain n) t := by
      rw [Metric.mem_ball, dist_zero_right, hnorm]
      exact mul_lt_mul_of_pos_left hxnorm hscale
    change d⁻¹ • s (scale • x) = 1
    have hvalue : s (scale • x) = d := hplateau _ hmem
    rw [hvalue, smul_eq_mul, inv_mul_cancel₀ hd.ne']
  · intro x
    have hT : HasFDerivAt (fun x : Domain n => scale • x)
        (scale • ContinuousLinearMap.id ℝ (Domain n)) x :=
      (hasFDerivAt_id x).const_smul scale
    have hDeriv : HasFDerivAt χ
        (d⁻¹ • (fderiv ℝ s (scale • x)).comp (scale • ContinuousLinearMap.id ℝ (Domain n))) x :=
      ((hsmooth'.differentiable (by simp) (scale • x)).hasFDerivAt.comp x hT).const_smul d⁻¹
    have hId : ‖scale • ContinuousLinearMap.id ℝ (Domain n)‖ ≤ scale := by
      rw [norm_smul, Real.norm_of_nonneg hscale.le]
      exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hscale.le).trans_eq
        (mul_one scale)
    have hsbound : ‖fderiv ℝ s (scale • x)‖ ≤ 2 := by
      have hh := hbound (scale • x)
      simpa only [mul_div_cancel_right₀ _ hd.ne'] using hh
    rw [hDeriv.fderiv, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
    calc
      _ ≤ d⁻¹ * (‖fderiv ℝ s (scale • x)‖ *
          ‖scale • ContinuousLinearMap.id ℝ (Domain n)‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
          (inv_nonneg.mpr hd.le)
      _ ≤ d⁻¹ * (2 * scale) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hsbound hId (norm_nonneg _) (by norm_num))
          (inv_nonneg.mpr hd.le)
      _ = 2 / δ := by dsimp only [d]; field_simp [hscale.ne', hδ.ne']

private theorem smooth_zeroSphere_boundary_bound {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (f : Domain n → Ambient q) (hf : ContDiffOn ℝ ∞ f U)
    (hboundary : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, f x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.closedBall (0 : Domain n) R.val,
      ‖f x‖ ≤ C * (R.val - ‖x‖) := by
  have hfd : ∀ x ∈ Metric.closedBall (0 : Domain n) R.val,
      DifferentiableAt ℝ f x := fun x hx =>
    (hf.contDiffAt (hU.mem_nhds (hclosed hx))).differentiableAt (by simp)
  have hderiv : ContinuousOn (fderiv ℝ f) (Metric.closedBall 0 R.val) :=
    (hf.continuousOn_fderiv_of_isOpen hU (by simp)).mono hclosed
  obtain ⟨C₀, hC₀⟩ :=
    ((isCompact_closedBall (0 : Domain n) R.val).image_of_continuousOn hderiv).isBounded.exists_norm_le
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound : ∀ x ∈ Metric.closedBall (0 : Domain n) R.val, ‖fderiv ℝ f x‖ ≤ C :=
    fun x hx => (hC₀ _ (mem_image_of_mem (fderiv ℝ f) hx)).trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hxnorm : ‖x‖ ≤ R.val := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  obtain ⟨y, hy, hdist⟩ : ∃ y : Domain n, y ∈ Metric.sphere 0 R.val ∧
      ‖x - y‖ = R.val - ‖x‖ := by
    by_cases hxzero : x = 0
    · subst x
      let i : Fin n := ⟨0, by omega⟩
      let y : Domain n := R.val • EuclideanSpace.single i 1
      have hynorm : ‖y‖ = R.val := by
        rw [norm_smul, Real.norm_of_nonneg R.property.le]
        simp only [EuclideanSpace.single, PiLp.norm_single, norm_one, mul_one]
      exact ⟨y, by rwa [Metric.mem_sphere, dist_zero_right],
        by rw [zero_sub, norm_neg, hynorm, norm_zero, sub_zero]⟩
    · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hxzero
      let y : Domain n := (R.val / ‖x‖) • x
      have hscale : 1 ≤ R.val / ‖x‖ := (le_div_iff₀ hxn).mpr (by simpa using hxnorm)
      have hynorm : ‖y‖ = R.val := by
        rw [norm_smul, Real.norm_of_nonneg (div_nonneg R.property.le hxn.le),
          div_mul_cancel₀ _ hxn.ne']
      have hdist : ‖x - y‖ = R.val - ‖x‖ := by
        rw [norm_sub_rev]
        change ‖(R.val / ‖x‖) • x - x‖ = _
        have heq : (R.val / ‖x‖) • x - x = (R.val / ‖x‖ - 1) • x := by
          rw [sub_smul, one_smul]
        rw [heq, norm_smul,
          Real.norm_of_nonneg (sub_nonneg.mpr hscale)]
        field_simp [hxn.ne']
      exact ⟨y, by rwa [Metric.mem_sphere, dist_zero_right], hdist⟩
  have hmean := (convex_closedBall (0 : Domain n) R.val).norm_image_sub_le_of_norm_fderiv_le
    hfd hbound (Metric.sphere_subset_closedBall hy) hx
  simpa only [hboundary y hy, sub_zero, hdist] using hmean

private theorem smooth_compactCutoff_contDiff {n q : ℕ}
    (U : Set (Domain n)) (hU : IsOpen U) (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f U) (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ U) : ContDiff ℝ ∞ (fun x => χ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hsχ hx)))
  · have heq : (fun y => χ y • f y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

private theorem cutoff_fderiv_eq_zero {n : ℕ} (χ : Domain n → ℝ)
    (t : ℝ) (hplateau : ∀ x ∈ Metric.ball (0 : Domain n) t, χ x = 1)
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) t) : fderiv ℝ χ x = 0 := by
  have heq : χ =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact hplateau y hy
  exact ((hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq heq).fderiv

private theorem smooth_product_column {n q : ℕ}
    {f : Domain n → Ambient q} {χ : Domain n → ℝ}
    (hprod : ContDiff ℝ ∞ (fun x => χ x • f x))
    (x : Domain n) (hχ : DifferentiableAt ℝ χ x) (hf : DifferentiableAt ℝ f x)
    (i : Fin n) :
    coordinateDerivative (fun x => χ x • f x) hprod i x =
      fderiv ℝ χ x (EuclideanSpace.single i 1) • f x +
        χ x • fderiv ℝ f x (EuclideanSpace.single i 1) := by
  simp only [coordinateDerivative, fderiv_fun_smul hχ hf, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, add_comm]

private theorem norm_cutoff_error_le {q : ℕ} (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (v : Ambient q) : ‖t • v - v‖ ≤ ‖v‖ := by
  have heq : t • v - v = (t - 1) • v := by rw [sub_smul, one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ht.2)]
  exact (mul_le_mul_of_nonneg_right (by linarith only [ht.1] : -(t - 1) ≤ 1)
    (norm_nonneg v)).trans_eq (one_mul _)

/-- Smooth zero sphere data produce the genuine W1,2_0 graph closure with the
original classical coordinate columns. -/
theorem smooth_zeroBoundary_ball {n q : ℕ} (hn : 2 ≤ n) (R : PositiveRadius)
    (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (f : Domain n → Ambient q) (hf : ContDiffOn ℝ ∞ f U)
    (hboundary : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, f x = 0) :
    HasZeroBoundaryValues (ballDomain (0 : Domain n) R.val) f
      (fun x i => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  let μ := volume.restrict (Metric.ball (0 : Domain n) R.val)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hw := dirichlet_smoothData_memW12 R U hU hclosed f hf
  obtain ⟨C, hC, hfb⟩ := smooth_zeroSphere_boundary_bound hn R U hU hclosed f hf hboundary
  obtain ⟨b, hb, hc, hs, hv, hm⟩ := quantitativeCutoffDensity_exists
  let δ : ℕ → ℝ := fun k => (R.val / 8) * (1 / ((k : ℝ) + 1))
  have hδpos (k : ℕ) : 0 < δ k := by
    exact mul_pos (div_pos R.property (by norm_num))
      (one_div_pos.mpr (by positivity))
  have hδbound (k : ℕ) : δ k ≤ R.val / 8 := by
    have hdiv : 1 / ((k : ℝ) + 1) ≤ 1 := by
      simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (show (1 : ℝ) ≤ (k : ℝ) + 1 by linarith only [Nat.cast_nonneg (α := ℝ) k])
    exact (mul_le_mul_of_nonneg_left hdiv (div_nonneg R.property.le (by norm_num))).trans_eq
      (mul_one _)
  have hδsmall (k : ℕ) : 4 * δ k < R.val := by
    have hh := mul_le_mul_of_nonneg_left (hδbound k) (by norm_num : (0 : ℝ) ≤ 4)
    linarith only [hh, R.property]
  have hδlim : Tendsto δ atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (R.val / 8)
  obtain ⟨χ, hχ, hcχ, hsχ, hvχ, hpχ, hDχ⟩ :
      ∃ χ : ℕ → Domain n → ℝ,
        (∀ k, ContDiff ℝ ∞ (χ k)) ∧
        (∀ k, HasCompactSupport (χ k)) ∧
        (∀ k, tsupport (χ k) ⊆ Metric.closedBall 0 (R.val - 2 * δ k)) ∧
        (∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) ∧
        (∀ k, ∀ x ∈ Metric.ball (0 : Domain n) (R.val - 3 * δ k), χ k x = 1) ∧
        (∀ k x, ‖fderiv ℝ (χ k) x‖ ≤ 2 / δ k) := by
    have hh (k : ℕ) := smooth_ballCutoff (n := n) R b hb hc hs hv hm
      (δ k) (hδpos k) (hδsmall k)
    choose χ hχ hcχ hsχ hvχ hpχ hDχ using hh
    exact ⟨χ, hχ, hcχ, hsχ, hvχ, hpχ, hDχ⟩
  have hsBall (k : ℕ) : tsupport (χ k) ⊆ Metric.ball (0 : Domain n) R.val :=
    (hsχ k).trans (Metric.closedBall_subset_ball (by linarith only [hδpos k]))
  let a : ℕ → Domain n → Ambient q := fun k x => χ k x • f x
  have ha (k : ℕ) : ContDiff ℝ ∞ (a k) :=
    smooth_compactCutoff_contDiff U hU f hf (χ k) (hχ k)
      ((hsBall k).trans (Metric.ball_subset_closedBall.trans hclosed))
  have hfd (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
      DifferentiableAt ℝ f x :=
    (hf.contDiffAt (hU.mem_nhds (hclosed (Metric.ball_subset_closedBall hx)))).differentiableAt
      (by simp)
  have hplateauEvent (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
      ∀ᶠ k : ℕ in atTop, χ k x = 1 ∧ fderiv ℝ (χ k) x = 0 := by
    have hxnorm : ‖x‖ < R.val := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    have hlim : Tendsto (fun k => R.val - 3 * δ k) atTop (𝓝 R.val) := by
      simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hδlim.const_mul 3)
    filter_upwards [hlim.eventually (eventually_gt_nhds hxnorm)] with k hk
    have hmem : x ∈ Metric.ball (0 : Domain n) (R.val - 3 * δ k) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hk
    exact ⟨hpχ k x hmem, cutoff_fderiv_eq_zero (χ k) _ (hpχ k) x hmem⟩
  have hmap : Tendsto (fun k => eLpNorm (a k - f) 2 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_zero_of_dominated
      (fun k => (ha k).continuous.aestronglyMeasurable.sub hw.2.1.aestronglyMeasurable)
      hw.2.1 (C := 1)
    · intro k
      filter_upwards [] with x
      simpa only [Pi.sub_apply, one_mul] using norm_cutoff_error_le (χ k x) (hvχ k x) (f x)
    · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      apply Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [hplateauEvent x hx] with k hk
      simp only [Pi.sub_apply, a, hk.1, one_smul, sub_self]
  refine ⟨hw, a, ha, (fun k => ⟨(hcχ k).smul_right,
    (tsupport_smul_subset_left (χ k) f).trans (hsBall k)⟩), hmap, ?_⟩
  intro i
  let A : ℕ → Domain n → Ambient q := fun k x =>
    fderiv ℝ (χ k) x (EuclideanSpace.single i 1) • f x
  let B : ℕ → Domain n → Ambient q := fun k x =>
    (χ k x - 1) • fderiv ℝ f x (EuclideanSpace.single i 1)
  have hAMeas (k : ℕ) : AEStronglyMeasurable (A k) μ :=
    (((hχ k).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.smul
      hw.2.1.aestronglyMeasurable
  have hBMeas (k : ℕ) : AEStronglyMeasurable (B k) μ :=
    ((hχ k).continuous.sub continuous_const).aestronglyMeasurable.smul
      (hw.2.2 i).aestronglyMeasurable
  have hALim : Tendsto (fun k => eLpNorm (A k) 2 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_zero_of_dominated hAMeas
      (memLp_const (1 : ℝ)) (C := 6 * C)
    · intro k
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      change ‖fderiv ℝ (χ k) x (EuclideanSpace.single i 1) • f x‖ ≤ 6 * C * ‖(1 : ℝ)‖
      rw [norm_one, mul_one]
      by_cases hinner : x ∈ Metric.ball (0 : Domain n) (R.val - 3 * δ k)
      · rw [cutoff_fderiv_eq_zero (χ k) _ (hpχ k) x hinner,
          zero_apply, zero_smul, norm_zero]
        exact mul_nonneg (by norm_num) hC
      · have hnorm : R.val - 3 * δ k ≤ ‖x‖ := by
          exact le_of_not_gt (by simpa only [Metric.mem_ball, dist_zero_right] using hinner)
        have hcolumn : ‖fderiv ℝ (χ k) x (EuclideanSpace.single i 1)‖ ≤ 2 / δ k := by
          have hb := (fderiv ℝ (χ k) x).le_opNorm (EuclideanSpace.single i 1)
          simp only [EuclideanSpace.single, PiLp.norm_single, norm_one, mul_one] at hb
          exact hb.trans (hDχ k x)
        have hfBound : ‖f x‖ ≤ C * (3 * δ k) :=
          (hfb x (Metric.ball_subset_closedBall hx)).trans
            (mul_le_mul_of_nonneg_left (by linarith only [hnorm]) hC)
        rw [norm_smul]
        calc
          _ ≤ (2 / δ k) * (C * (3 * δ k)) :=
            mul_le_mul hcolumn hfBound (norm_nonneg _) (div_nonneg (by norm_num) (hδpos k).le)
          _ = 6 * C := by field_simp [(hδpos k).ne']; ring
    · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      apply Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [hplateauEvent x hx] with k hk
      simp only [A, hk.2, zero_apply, zero_smul]
  have hBLim : Tendsto (fun k => eLpNorm (B k) 2 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_zero_of_dominated hBMeas (hw.2.2 i) (C := 1)
    · intro k
      filter_upwards [] with x
      simpa only [B, one_mul, sub_smul, one_smul] using
        norm_cutoff_error_le (χ k x) (hvχ k x) (fderiv ℝ f x (EuclideanSpace.single i 1))
    · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      apply Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [hplateauEvent x hx] with k hk
      simp only [B, hk.1, sub_self, zero_smul]
  have hsum : Tendsto (fun k => eLpNorm (A k) 2 μ + eLpNorm (B k) 2 μ) atTop (𝓝 0) := by
    simpa only [zero_add] using hALim.add hBLim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
  intro k
  have heq : (fun x => coordinateDerivative (a k) (ha k) i x -
      fderiv ℝ f x (EuclideanSpace.single i 1)) =ᵐ[μ] A k + B k := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    rw [smooth_product_column (ha k) x ((hχ k).differentiable (by simp) x) (hfd x hx)]
    simp only [A, B, Pi.add_apply, sub_smul, one_smul]
    abel
  change eLpNorm (fun x => coordinateDerivative (a k) (ha k) i x -
    fderiv ℝ f x (EuclideanSpace.single i 1)) 2 μ ≤
    eLpNorm (A k) 2 μ + eLpNorm (B k) 2 μ
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_add_le (hAMeas k) (hBMeas k) (by norm_num)

end HarmonicMaps
