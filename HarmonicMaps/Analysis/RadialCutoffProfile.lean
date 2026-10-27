module

public import HarmonicMaps.Analysis.RadialTestAdmissibility
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smooth shrinking radial cutoffs

The positive-radius carrier excludes a zero transition width. The profile is
one through the inner radius and zero beyond the outer transition radius.
-/

@[expose] public section

open Set Filter
open scoped ContDiff Topology

namespace HarmonicMaps

/-- A smooth radial cutoff with positive inner radius and transition width. -/
noncomputable def radialCutoffProfile (t δ : PositiveRadius) (r : ℝ) : ℝ :=
  1 - Real.smoothTransition ((r - t.val) / δ.val)

/-- Every shrinking radial profile is smooth. -/
theorem radialCutoffProfile_contDiff (t δ : PositiveRadius) :
    ContDiff ℝ ∞ (radialCutoffProfile t δ) := by
  apply contDiff_const.sub
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ.val)

/-- The cutoff remains between zero and one. -/
theorem radialCutoffProfile_mem_Icc (t δ : PositiveRadius) (r : ℝ) :
    radialCutoffProfile t δ r ∈ Icc (0 : ℝ) 1 := by
  have h0 := Real.smoothTransition.nonneg ((r - t.val) / δ.val)
  have h1 := Real.smoothTransition.le_one ((r - t.val) / δ.val)
  constructor <;> dsimp [radialCutoffProfile] <;> linarith only [h0, h1]

/-- The profile is exactly one up to the inner radius. -/
theorem radialCutoffProfile_eq_one (t δ : PositiveRadius) {r : ℝ} (hr : r ≤ t.val) :
    radialCutoffProfile t δ r = 1 := by
  rw [radialCutoffProfile, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) δ.property.le), sub_zero]

/-- The profile vanishes beyond its transition interval. -/
theorem radialCutoffProfile_eq_zero (t δ : PositiveRadius) {r : ℝ}
    (hr : t.val + δ.val ≤ r) : radialCutoffProfile t δ r = 0 := by
  rw [radialCutoffProfile, Real.smoothTransition.one_of_one_le, sub_self]
  exact (le_div_iff₀ δ.property).mpr (by linarith only [hr])

/-- The actual scalar derivative of the shrinking profile. -/
theorem radialCutoffProfile_hasDerivAt (t δ : PositiveRadius) (r : ℝ) :
    HasDerivAt (radialCutoffProfile t δ)
      (-(deriv Real.smoothTransition ((r - t.val) / δ.val)) / δ.val) r := by
  have h : HasDerivAt (fun r : ℝ => (r - t.val) / δ.val) (1 / δ.val) r :=
    ((hasDerivAt_id r).sub_const t.val).div_const δ.val
  have hs : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff : ContDiff ℝ 1 Real.smoothTransition).differentiable one_ne_zero
  have hc := (hs ((r - t.val) / δ.val)).hasDerivAt.comp r h
  change HasDerivAt (fun z : ℝ => 1 - Real.smoothTransition ((z - t.val) / δ.val)) _ r
  simpa only [Function.comp_def, Pi.sub_def, zero_sub, div_eq_mul_inv,
    one_mul, neg_mul] using (hasDerivAt_const r (1 : ℝ)).sub hc

/-- The displayed derivative formula uses the actual derivative operator. -/
theorem radialCutoffProfile_deriv (t δ : PositiveRadius) (r : ℝ) :
    deriv (radialCutoffProfile t δ) r =
      -(deriv Real.smoothTransition ((r - t.val) / δ.val)) / δ.val :=
  (radialCutoffProfile_hasDerivAt t δ r).deriv

/-- The derivative of the fixed transition vanishes outside its transition interval. -/
theorem smoothTransition_deriv_eq_zero {r : ℝ} (hr : r ∉ Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition r = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at hr
  rcases hr with hr | hr
  · have he : Real.smoothTransition =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hr] with x hx
      exact Real.smoothTransition.zero_of_nonpos hx.le
    exact ((hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq he).deriv
  · have he : Real.smoothTransition =ᶠ[𝓝 r] (fun _ => (1 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      exact Real.smoothTransition.one_of_one_le hx.le
    exact ((hasDerivAt_const r (1 : ℝ)).congr_of_eventuallyEq he).deriv

/-- The smooth fixed transition has a finite uniform derivative bound. -/
theorem smoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |deriv Real.smoothTransition r| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    Real.smoothTransition.contDiff.continuous_deriv (by norm_num : (1 : ℕ∞) ≤ ∞)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨C, hC0, fun r => ?_⟩
  by_cases hr : r ∈ Icc (0 : ℝ) 1
  · simpa only [Real.norm_eq_abs] using hC r hr
  · rw [smoothTransition_deriv_eq_zero hr, abs_zero]
    exact hC0

/-- The derivative bound has one universal constant independent of both radii. -/
theorem radialCutoffProfile_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t δ : PositiveRadius) (r : ℝ),
      |deriv (radialCutoffProfile t δ) r| ≤ C / δ.val := by
  obtain ⟨C, hC, hb⟩ := smoothTransition_deriv_bound
  refine ⟨C, hC, fun t δ r => ?_⟩
  rw [radialCutoffProfile_deriv, abs_div, abs_neg, abs_of_pos δ.property]
  exact div_le_div_of_nonneg_right (hb _) δ.property.le

/-- Positive inner radii give the required nonnegative-radius plateau. -/
theorem radialCutoffProfile_plateau (t δ : PositiveRadius) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ r ∈ Ico (0 : ℝ) epsilon,
      radialCutoffProfile t δ r = radialCutoffProfile t δ 0 := by
  refine ⟨t.val, t.property, fun r hr => ?_⟩
  rw [radialCutoffProfile_eq_one t δ hr.2.le,
    radialCutoffProfile_eq_one t δ t.property.le]

/-- The explicit shrinking cutoff gives a genuine compact smooth vector test. -/
theorem radialCutoffProfile_admissible {n : ℕ} (t δ : PositiveRadius)
    {R : ℝ} (hR : t.val + δ.val < R) (a : Domain n) :
    ContDiff ℝ ∞ (fun x => radialVectorField (radialCutoffProfile t δ) (x - a)) ∧
    HasCompactSupport (fun x => radialVectorField (radialCutoffProfile t δ) (x - a)) ∧
    tsupport (fun x => radialVectorField (radialCutoffProfile t δ) (x - a)) ⊆ Metric.ball a R :=
  radialVectorField_admissible (radialCutoffProfile_contDiff t δ)
    (radialCutoffProfile_plateau t δ) hR (fun _ hr => radialCutoffProfile_eq_zero t δ hr) a

end HarmonicMaps
