module

public import HarmonicMaps.Analysis.DirichletSmoothData
public import HarmonicMaps.Analysis.SobolevPostcompositionBasic
public import HarmonicMaps.Analysis.QuantitativeRadialCutoff
public import HarmonicMaps.Analysis.SobolevAECongruence
import Mathlib.Analysis.Calculus.MeanValue
public import HarmonicMaps.Analysis.DirichletCompactGreen
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Closed-ball smooth boundary data and harmonic uniqueness

Native smoothness within the closed ball supplies finite Sobolev data and
compact smooth approximants with the original interior coordinate columns.
Zero sphere values give the existing W0 graph closure. Harmonic candidates
with equal sphere data agree on the entire closed ball.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology BigOperators

namespace HarmonicMaps

private theorem closedW0_smooth_ballCutoff {n : ℕ} (R : PositiveRadius)
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

private theorem closedW0_smooth_compactCutoff_contDiff {n q : ℕ}
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

private theorem closedW0_cutoff_fderiv_eq_zero {n : ℕ} (χ : Domain n → ℝ)
    (t : ℝ) (hplateau : ∀ x ∈ Metric.ball (0 : Domain n) t, χ x = 1)
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) t) : fderiv ℝ χ x = 0 := by
  have heq : χ =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact hplateau y hy
  exact ((hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq heq).fderiv

private theorem closedW0_smooth_product_column {n q : ℕ}
    {f : Domain n → Ambient q} {χ : Domain n → ℝ}
    (hprod : ContDiff ℝ ∞ (fun x => χ x • f x))
    (x : Domain n) (hχ : DifferentiableAt ℝ χ x) (hf : DifferentiableAt ℝ f x)
    (i : Fin n) :
    coordinateDerivative (fun x => χ x • f x) hprod i x =
      fderiv ℝ χ x (EuclideanSpace.single i 1) • f x +
        χ x • fderiv ℝ f x (EuclideanSpace.single i 1) := by
  simp only [coordinateDerivative, fderiv_fun_smul hχ hf, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, add_comm]

private theorem closedW0_norm_cutoff_error_le {q : ℕ} (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (v : Ambient q) : ‖t • v - v‖ ≤ ‖v‖ := by
  have heq : t • v - v = (t - 1) • v := by rw [sub_smul, one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ht.2)]
  exact (mul_le_mul_of_nonneg_right (by linarith only [ht.1] : -(t - 1) ≤ 1)
    (norm_nonneg v)).trans_eq (one_mul _)

private theorem closedW0_uniqueDiff {n : ℕ} (R : PositiveRadius) :
    UniqueDiffOn ℝ (Metric.closedBall (0 : Domain n) R.val) :=
  uniqueDiffOn_convex (convex_closedBall _ _)
    ⟨0, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self R.property)⟩

private theorem closedW0_continuous_memLp {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {f : Domain n → E} {R : ℝ}
    (hf : ContinuousOn f (Metric.closedBall (0 : Domain n) R)) :
    MemLp f 2 (volume.restrict (Metric.closedBall (0 : Domain n) R)) := by
  let K := Metric.closedBall (0 : Domain n) R
  have hK : IsCompact K := isCompact_closedBall _ _
  letI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hf).isBounded.exists_norm_le
  apply MemLp.of_bound
    (hf.aestronglyMeasurable_of_subset_isCompact hK hK.measurableSet Subset.rfl) C
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC _ (mem_image_of_mem f hx)

private theorem closedW0_memW12 {n q : ℕ} (R : PositiveRadius)
    (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : Domain n) R.val)) :
    MemW12 (ballDomain (0 : Domain n) R.val) f
      (fun x i => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  let K := Metric.closedBall (0 : Domain n) R.val
  let B := Metric.ball (0 : Domain n) R.val
  have hfd : ∀ x ∈ B, DifferentiableAt ℝ f x := fun x hx =>
    ((hf.mono Metric.ball_subset_closedBall).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
  have hWithin : ContinuousOn (fderivWithin ℝ f K) K :=
    hf.continuousOn_fderivWithin (closedW0_uniqueDiff R) (by simp)
  have hm2 : MemLp f 2 (volume.restrict B) :=
    (closedW0_continuous_memLp hf.continuousOn).mono_measure
      (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
  have hcol2 (i : Fin n) : MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
      2 (volume.restrict B) := by
    have hcol : MemLp (fun x => fderivWithin ℝ f K x (EuclideanSpace.single i 1))
        2 (volume.restrict B) :=
      (closedW0_continuous_memLp (hWithin.clm_apply continuousOn_const)).mono_measure
        (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
    apply hcol.ae_eq
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hK : K ∈ nhds x := mem_of_superset
      (Metric.isOpen_ball.mem_nhds hx) Metric.ball_subset_closedBall
    rw [fderivWithin_of_mem_nhds hK]
  exact memW12_ball_of_differentiableAt hfd (fun _ _ _ => rfl) hm2 hcol2

private theorem closedW0_zeroSphere_boundary_bound {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : Domain n) R.val))
    (hboundary : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, f x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.closedBall (0 : Domain n) R.val,
      ‖f x‖ ≤ C * (R.val - ‖x‖) := by
  have hfd : DifferentiableOn ℝ f (Metric.closedBall (0 : Domain n) R.val) :=
    hf.differentiableOn (by simp)
  have hderiv : ContinuousOn (fderivWithin ℝ f (Metric.closedBall 0 R.val))
      (Metric.closedBall 0 R.val) :=
    hf.continuousOn_fderivWithin (closedW0_uniqueDiff R) (by simp)
  obtain ⟨C₀, hC₀⟩ :=
    ((isCompact_closedBall (0 : Domain n) R.val).image_of_continuousOn hderiv).isBounded.exists_norm_le
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound : ∀ x ∈ Metric.closedBall (0 : Domain n) R.val, ‖fderivWithin ℝ f (Metric.closedBall (0 : Domain n) R.val) x‖ ≤ C :=
    fun x hx => (hC₀ _ (mem_image_of_mem (fderivWithin ℝ f (Metric.closedBall (0 : Domain n) R.val)) hx)).trans (le_max_left _ _)
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
  have hmean := (convex_closedBall (0 : Domain n) R.val).norm_image_sub_le_of_norm_fderivWithin_le
    hfd hbound (Metric.sphere_subset_closedBall hy) hx
  simpa only [hboundary y hy, sub_zero, hdist] using hmean

/-- Smooth zero sphere data produce the genuine W1,2_0 graph closure with the
original classical coordinate columns. -/
theorem closed_smooth_zeroBoundary_ball {n q : ℕ} (hn : 2 ≤ n) (R : PositiveRadius)
    (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : Domain n) R.val))
    (hboundary : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, f x = 0) :
    HasZeroBoundaryValues (ballDomain (0 : Domain n) R.val) f
      (fun x i => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  let μ := volume.restrict (Metric.ball (0 : Domain n) R.val)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hw := closedW0_memW12 R f hf
  have hfOpen : ContDiffOn ℝ ∞ f (Metric.ball (0 : Domain n) R.val) :=
    hf.mono Metric.ball_subset_closedBall
  obtain ⟨C, hC, hfb⟩ := closedW0_zeroSphere_boundary_bound hn R f hf hboundary
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
    have hh (k : ℕ) := closedW0_smooth_ballCutoff (n := n) R b hb hc hs hv hm
      (δ k) (hδpos k) (hδsmall k)
    choose χ hχ hcχ hsχ hvχ hpχ hDχ using hh
    exact ⟨χ, hχ, hcχ, hsχ, hvχ, hpχ, hDχ⟩
  have hsBall (k : ℕ) : tsupport (χ k) ⊆ Metric.ball (0 : Domain n) R.val :=
    (hsχ k).trans (Metric.closedBall_subset_ball (by linarith only [hδpos k]))
  let a : ℕ → Domain n → Ambient q := fun k x => χ k x • f x
  have ha (k : ℕ) : ContDiff ℝ ∞ (a k) :=
    closedW0_smooth_compactCutoff_contDiff (Metric.ball (0 : Domain n) R.val) Metric.isOpen_ball
      f hfOpen (χ k) (hχ k) (hsBall k)
  have hfd (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
      DifferentiableAt ℝ f x :=
    (hfOpen.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt
      (by simp)
  have hplateauEvent (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
      ∀ᶠ k : ℕ in atTop, χ k x = 1 ∧ fderiv ℝ (χ k) x = 0 := by
    have hxnorm : ‖x‖ < R.val := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    have hlim : Tendsto (fun k => R.val - 3 * δ k) atTop (𝓝 R.val) := by
      simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hδlim.const_mul 3)
    filter_upwards [hlim.eventually (eventually_gt_nhds hxnorm)] with k hk
    have hmem : x ∈ Metric.ball (0 : Domain n) (R.val - 3 * δ k) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hk
    exact ⟨hpχ k x hmem, closedW0_cutoff_fderiv_eq_zero (χ k) _ (hpχ k) x hmem⟩
  have hmap : Tendsto (fun k => eLpNorm (a k - f) 2 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_zero_of_dominated
      (fun k => (ha k).continuous.aestronglyMeasurable.sub hw.2.1.aestronglyMeasurable)
      hw.2.1 (C := 1)
    · intro k
      filter_upwards [] with x
      simpa only [Pi.sub_apply, one_mul] using closedW0_norm_cutoff_error_le (χ k x) (hvχ k x) (f x)
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
      · rw [closedW0_cutoff_fderiv_eq_zero (χ k) _ (hpχ k) x hinner,
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
        closedW0_norm_cutoff_error_le (χ k x) (hvχ k x) (fderiv ℝ f x (EuclideanSpace.single i 1))
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
    rw [closedW0_smooth_product_column (ha k) x ((hχ k).differentiable (by simp) x) (hfd x hx)]
    simp only [A, B, Pi.add_apply, sub_smul, one_smul]
    abel
  change eLpNorm (fun x => coordinateDerivative (a k) (ha k) i x -
    fderiv ℝ f x (EuclideanSpace.single i 1)) 2 μ ≤
    eLpNorm (A k) 2 μ + eLpNorm (B k) 2 μ
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_add_le (hAMeas k) (hBMeas k) (by norm_num)


private theorem closedW0_smaller_support {n q : ℕ} (R : PositiveRadius)
    (φ : Domain n → Ambient q) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Metric.ball (0 : Domain n) R.val) :
    ∃ r : PositiveRadius, r.val < R.val ∧ tsupport φ ⊆ Metric.ball (0 : Domain n) r.val := by
  by_cases hne : (tsupport φ).Nonempty
  · obtain ⟨y, hy, hmax⟩ := hcφ.exists_isMaxOn hne continuous_norm.continuousOn
    have hyR : ‖y‖ < R.val := by
      simpa only [Metric.mem_ball, dist_zero_right] using hsφ hy
    let r : ℝ := (‖y‖ + R.val) / 2
    have hr : 0 < r := by dsimp only [r]; linarith only [norm_nonneg y, R.property]
    refine ⟨⟨r, hr⟩, ?_, ?_⟩
    · dsimp only [r]
      linarith only [hyR]
    · intro x hx
      rw [Metric.mem_ball, dist_zero_right]
      have hxy : ‖x‖ ≤ ‖y‖ := hmax hx
      dsimp only [r]
      linarith only [hxy, hyR]
  · refine ⟨⟨R.val / 2, half_pos R.property⟩, half_lt_self R.property, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

private theorem closedW0_compactTest_green_zero {n q : ℕ} (R : PositiveRadius)
    (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball (0 : Domain n) R.val))
    (hharmonic : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian f x = 0)
    (φ : Domain n → Ambient q) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ Metric.ball (0 : Domain n) R.val) :
    (∫ x in Metric.ball (0 : Domain n) R.val, ∑ i : Fin n,
      inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1))
        (coordinateDerivative φ hφ i x)) = 0 := by
  obtain ⟨r, hrR, hsr⟩ := closedW0_smaller_support R φ hcφ hsφ
  have hclosed : Metric.closedBall (0 : Domain n) r.val ⊆ Metric.ball (0 : Domain n) R.val :=
    Metric.closedBall_subset_ball hrR
  obtain ⟨_, _, hGreen⟩ := dirichlet_compactTest_green r
    (Metric.ball (0 : Domain n) R.val) Metric.isOpen_ball hclosed f hf φ hφ hcφ hsr
  have hRight : (∫ x in Metric.ball (0 : Domain n) r.val, inner ℝ
      (∑ i : Fin n,
        fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) (φ x)) = 0 := by
    calc
      _ = ∫ x in Metric.ball (0 : Domain n) r.val, (0 : ℝ) :=
        setIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun x hx => by
          rw [← dirichlet_smoothData_laplacian r (Metric.ball (0 : Domain n) R.val)
            Metric.isOpen_ball hclosed f hf x (Metric.ball_subset_closedBall hx),
            hharmonic x (hclosed (Metric.ball_subset_closedBall hx)), inner_zero_left])
      _ = 0 := by simp only [integral_zero]
  have hSmall : (∫ x in Metric.ball (0 : Domain n) r.val, ∑ i : Fin n,
      inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1))
        (coordinateDerivative φ hφ i x)) = 0 := by
    simpa only [hRight, neg_zero] using hGreen
  have hZero (x : Domain n) (hx : x ∉ Metric.ball (0 : Domain n) r.val) (i : Fin n) :
      coordinateDerivative φ hφ i x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hx (hsr (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) hmem))
  have hSmallGlobal : (∫ x in Metric.ball (0 : Domain n) r.val, ∑ i : Fin n,
      inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1))
        (coordinateDerivative φ hφ i x)) =
      ∫ x : Domain n, ∑ i : Fin n, inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1))
        (coordinateDerivative φ hφ i x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      apply Finset.sum_eq_zero
      intro i _
      rw [hZero x hx i, inner_zero_right])
  have hOriginalGlobal : (∫ x in Metric.ball (0 : Domain n) R.val, ∑ i : Fin n,
      inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1))
        (coordinateDerivative φ hφ i x)) =
      ∫ x : Domain n, ∑ i : Fin n, inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1))
        (coordinateDerivative φ hφ i x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      apply Finset.sum_eq_zero
      intro i _
      rw [hZero x (fun hy => hx ((Metric.ball_subset_ball hrR.le) hy)) i, inner_zero_right])
  exact hOriginalGlobal.trans (hSmallGlobal.symm.trans hSmall)

private theorem closedW0_inner_integrable_L2 {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

private theorem closedW0_integral_inner_toLp {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, inner ℝ (f x) (g x) ∂μ) = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

private theorem closedW0_tendsto_integral_inner_L2 {n q : ℕ} {μ : Measure (Domain n)}
    {f : ℕ → Domain n → Ambient q} {u g : Domain n → Ambient q}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, inner ℝ (g x) (f k x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (g x) (u x) ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hlim
  have hconst : Tendsto (fun _ : ℕ => hg.toLp g) atTop (𝓝 (hg.toLp g)) :=
    tendsto_const_nhds
  have hinner := hconst.inner (𝕜 := ℝ) hLp
  simp_rw [closedW0_integral_inner_toLp hg (hf _), closedW0_integral_inner_toLp hg hu]
  exact hinner

private theorem closedW0_harmonic_energy_zero {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : Domain n) R.val))
    (hboundary : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, f x = 0)
    (hharmonic : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian f x = 0) :
    IntegrableOn (fun x => ∑ i : Fin n, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2)
      (Metric.ball (0 : Domain n) R.val) volume ∧
    (∫ x in Metric.ball (0 : Domain n) R.val,
      ∑ i : Fin n, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) = 0 := by
  let μ := volume.restrict (Metric.ball (0 : Domain n) R.val)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hfOpen : ContDiffOn ℝ ∞ f (Metric.ball (0 : Domain n) R.val) :=
    hf.mono Metric.ball_subset_closedBall
  obtain ⟨hw, a, ha, has, _, hgrad⟩ := closed_smooth_zeroBoundary_ball hn R f hf hboundary
  have hCol (i : Fin n) : MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 μ := hw.2.2 i
  have haD (k : ℕ) (i : Fin n) : MemLp (coordinateDerivative (a k) (ha k) i) 2 μ := by
    have hc := (has k).1.fderiv_apply ℝ (EuclideanSpace.single i 1)
    have hcont : Continuous (coordinateDerivative (a k) (ha k) i) :=
      ((ha k).continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hcont.memLp_top_of_hasCompactSupport hc μ).mono_exponent (by simp)
  have hLeftLim : Tendsto (fun k => ∑ i : Fin n,
      ∫ x, inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1))
        (coordinateDerivative (a k) (ha k) i x) ∂μ) atTop
      (nhds (∑ i : Fin n, ∫ x, inner ℝ
        (fderiv ℝ f x (EuclideanSpace.single i 1))
        (fderiv ℝ f x (EuclideanSpace.single i 1)) ∂μ)) :=
    tendsto_finsetSum Finset.univ (fun i _ =>
      closedW0_tendsto_integral_inner_L2 (fun k => haD k i) (hCol i) (hCol i) (hgrad i))
  have hSeq (k : ℕ) : (∑ i : Fin n,
      ∫ x, inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1))
        (coordinateDerivative (a k) (ha k) i x) ∂μ) = 0 := by
    rw [← integral_finsetSum Finset.univ (fun i _ => closedW0_inner_integrable_L2 (hCol i) (haD k i))]
    exact closedW0_compactTest_green_zero R f hfOpen hharmonic (a k) (ha k) (has k).1 (has k).2
  have hEnergy : (∑ i : Fin n, ∫ x, inner ℝ
      (fderiv ℝ f x (EuclideanSpace.single i 1))
      (fderiv ℝ f x (EuclideanSpace.single i 1)) ∂μ) = 0 :=
    tendsto_nhds_unique hLeftLim (tendsto_const_nhds.congr'
      (Eventually.of_forall (fun k => (hSeq k).symm)))
  have hInt (i : Fin n) : Integrable (fun x => inner ℝ
      (fderiv ℝ f x (EuclideanSpace.single i 1))
      (fderiv ℝ f x (EuclideanSpace.single i 1))) μ :=
    closedW0_inner_integrable_L2 (hCol i) (hCol i)
  have hSumInt := integrable_finsetSum Finset.univ (fun i _ => hInt i)
  have hSumEnergy : (∫ x, ∑ i : Fin n, inner ℝ
      (fderiv ℝ f x (EuclideanSpace.single i 1))
      (fderiv ℝ f x (EuclideanSpace.single i 1)) ∂μ) = 0 := by
    rw [integral_finsetSum Finset.univ (fun i _ => hInt i)]
    exact hEnergy
  change Integrable (fun x : Domain n => ∑ i : Fin n,
    ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) μ ∧
    (∫ x : Domain n, ∑ i : Fin n, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2 ∂μ) = 0
  simpa only [real_inner_self_eq_norm_sq] using And.intro hSumInt hSumEnergy

/-- Native within-smooth harmonic data with actual zero sphere values vanish
on the complete closed ball. No smooth neighborhood representative is assumed. -/
theorem closed_dirichlet_harmonic_zero_closedBall {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : Domain n) R.val))
    (hboundary : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, f x = 0)
    (hharmonic : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian f x = 0) :
    ∀ x ∈ Metric.closedBall (0 : Domain n) R.val, f x = 0 := by
  classical
  have hfOpen : ContDiffOn ℝ ∞ f (Metric.ball (0 : Domain n) R.val) :=
    hf.mono Metric.ball_subset_closedBall
  obtain ⟨hInt, hEnergyZero⟩ := closedW0_harmonic_energy_zero hn R f hf hboundary hharmonic
  let e : Domain n → ℝ := fun x => ∑ i : Fin n,
    ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2
  have hNonneg : 0 ≤ e := fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hAE : e =ᵐ[volume.restrict (Metric.ball (0 : Domain n) R.val)] 0 :=
    (integral_eq_zero_iff_of_nonneg hNonneg hInt).mp hEnergyZero
  have hCols (i : Fin n) : ContDiffOn ℝ ∞
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
      (Metric.ball (0 : Domain n) R.val) :=
    (hfOpen.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const
  have hEcont : ContinuousOn e (Metric.ball (0 : Domain n) R.val) := by
    apply continuousOn_finsetSum
    intro i _
    exact (hCols i).continuousOn.norm.pow 2
  have hEvery : EqOn e (fun _ => 0) (Metric.ball (0 : Domain n) R.val) :=
    (volume : Measure (Domain n)).eqOn_open_of_ae_eq hAE Metric.isOpen_ball hEcont continuousOn_const
  have hColumnZero (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val)
      (i : Fin n) : fderiv ℝ f x (EuclideanSpace.single i 1) = 0 := by
    have H := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
      sq_nonneg ‖fderiv ℝ f x (EuclideanSpace.single j 1)‖)).mp (hEvery hx)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (H i (Finset.mem_univ i)))
  have hDerivativeZero (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
      fderiv ℝ f x = 0 := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
    intro i
    simpa [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using hColumnZero x hx i
  have hDiff : DifferentiableOn ℝ f (Metric.ball (0 : Domain n) R.val) :=
    hfOpen.differentiableOn (by simp)
  have hConst : EqOn f (fun _ => f 0) (Metric.ball (0 : Domain n) R.val) := by
    intro x hx
    apply (convex_ball (0 : Domain n) R.val).is_const_of_fderivWithin_eq_zero hDiff
      (fun z hz => by rw [fderivWithin_of_isOpen Metric.isOpen_ball hz, hDerivativeZero z hz])
      hx (Metric.mem_ball_self R.property)
  have hConstClosed : EqOn f (fun _ => f 0) (Metric.closedBall (0 : Domain n) R.val) :=
    hConst.of_subset_closure hf.continuousOn continuousOn_const
      Metric.ball_subset_closedBall (by rw [closure_ball 0 (ne_of_gt R.property)])
  let i : Fin n := ⟨0, by omega⟩
  let p : Domain n := R.val • EuclideanSpace.single i 1
  have hp : p ∈ Metric.sphere (0 : Domain n) R.val := by
    simp only [p, Metric.mem_sphere, dist_zero_right, norm_smul,
      Real.norm_of_nonneg R.property.le, PiLp.norm_single, norm_one, mul_one]
  have hAtZero : f 0 = 0 := (hConstClosed (Metric.sphere_subset_closedBall hp)).symm.trans
    (hboundary p hp)
  intro x hx
  exact (hConstClosed hx).trans hAtZero

/-- All native within-smooth harmonic candidates with the same actual sphere
values agree on the source closed carrier; their outside values are unrestricted. -/
theorem closed_dirichlet_harmonic_unique_closedBall {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (f g : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : Domain n) R.val))
    (hg : ContDiffOn ℝ ∞ g (Metric.closedBall (0 : Domain n) R.val))
    (hboundary : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, f x = g x)
    (hfHarmonic : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian f x = 0)
    (hgHarmonic : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian g x = 0) :
    EqOn f g (Metric.closedBall (0 : Domain n) R.val) := by
  have hfOpen := hf.mono Metric.ball_subset_closedBall
  have hgOpen := hg.mono Metric.ball_subset_closedBall
  have hZero := closed_dirichlet_harmonic_zero_closedBall hn R (f - g) (hf.sub hg)
    (fun x hx => sub_eq_zero.mpr (hboundary x hx)) (fun x hx => by
      rw [((hfOpen.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).laplacian_sub
        ((hgOpen.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).of_le
          (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))),
        hfHarmonic x hx, hgHarmonic x hx, sub_self])
  intro x hx
  exact sub_eq_zero.mp (hZero x hx)

/-- Closed within-smooth maps agreeing on the sphere have the genuine W0
boundary difference with the original native interior coordinate columns. -/
theorem closed_smooth_zeroBoundaryDifference {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (f g : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : Domain n) R.val))
    (hg : ContDiffOn ℝ ∞ g (Metric.closedBall (0 : Domain n) R.val))
    (hboundary : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, f x = g x) :
    HasZeroBoundaryValues (ballDomain (0 : Domain n) R.val) (f - g)
      (fun x i => fderiv ℝ f x (EuclideanSpace.single i 1) -
        fderiv ℝ g x (EuclideanSpace.single i 1)) := by
  have hW := closed_smooth_zeroBoundary_ball hn R (f - g) (hf.sub hg)
    (fun x hx => sub_eq_zero.mpr (hboundary x hx))
  apply hW.congr_ae (EventuallyEq.refl _ _)
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  funext i
  have hfd : DifferentiableAt ℝ f x :=
    ((hf.mono Metric.ball_subset_closedBall).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
  have hgd : DifferentiableAt ℝ g x :=
    ((hg.mono Metric.ball_subset_closedBall).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
  rw [fderiv_sub hfd hgd, sub_apply]

end HarmonicMaps

end
