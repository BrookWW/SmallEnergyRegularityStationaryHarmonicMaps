module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A smooth unit-mass density bounded by two

Convolving the interval density `2 * 1_[1/4,3/4]` with a nonnegative
unit-mass smooth kernel supported in `[-1/8,1/8]` preserves its mass and
upper bound. Its compact support lies in `[1/8,7/8]`.
-/

public section

open MeasureTheory Set
open scoped ContDiff Convolution Pointwise

namespace HarmonicMaps

/-- The source convolution supplies one density with all required properties. -/
theorem quantitativeCutoffDensity_exists :
    ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      tsupport b ⊆ Ioo 0 1 ∧ (∀ t, 0 ≤ b t ∧ b t ≤ 2) ∧ (∫ t, b t) = 1 := by
  let raw : ℝ → ℝ := fun t => Real.smoothTransition (1 - 64 * t ^ 2)
  have hrawSmooth : ContDiff ℝ ∞ raw :=
    Real.smoothTransition.contDiff.comp
      (contDiff_const.sub (contDiff_const.mul (contDiff_id.pow 2)))
  have hrawNonneg : ∀ t, 0 ≤ raw t := fun t => Real.smoothTransition.nonneg _
  have hrawSupport : Function.support raw ⊆ Icc (-1 / 8) (1 / 8) := by
    intro t ht
    have ht' : 0 < 1 - 64 * t ^ 2 := by
      apply lt_of_not_ge
      intro h
      exact ht (Real.smoothTransition.zero_of_nonpos h)
    constructor <;> nlinarith only [ht', sq_nonneg (t - 1 / 8), sq_nonneg (t + 1 / 8)]
  have hrawTSupport : tsupport raw ⊆ Icc (-1 / 8) (1 / 8) :=
    closure_minimal hrawSupport isClosed_Icc
  have hrawCompact : HasCompactSupport raw :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport raw) hrawTSupport
  have hrawInt : Integrable raw volume :=
    hrawSmooth.continuous.integrable_of_hasCompactSupport hrawCompact
  have hrawPos : 0 < ∫ t, raw t := by
    apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := (0 : ℝ)) hrawSmooth.continuous hrawCompact hrawNonneg
    norm_num [raw]
  let rho : ℝ → ℝ := fun t => raw t / ∫ u, raw u
  have hrhoSmooth : ContDiff ℝ ∞ rho := hrawSmooth.div_const _
  have hrhoNonneg : ∀ t, 0 ≤ rho t := fun t => div_nonneg (hrawNonneg t) hrawPos.le
  have hrhoTSupport : tsupport rho ⊆ Icc (-1 / 8) (1 / 8) := by
    change tsupport ((fun t : ℝ => t / ∫ u, raw u) ∘ raw) ⊆ _
    exact (tsupport_comp_subset (g := fun t : ℝ => t / ∫ u, raw u) (zero_div _) raw).trans hrawTSupport
  have hrhoCompact : HasCompactSupport rho :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport rho) hrhoTSupport
  have hrhoInt : Integrable rho volume := hrawInt.div_const _
  have hrhoMass : (∫ t, rho t) = 1 := by
    dsimp only [rho]
    rw [integral_div, div_self hrawPos.ne']
  let f : ℝ → ℝ := (Icc (1 / 4 : ℝ) (3 / 4)).indicator (fun _ => 2)
  have hfInt : Integrable f volume := by
    exact (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (C := (2 : ℝ))
        (by norm_num : volume (Icc (1 / 4 : ℝ) (3 / 4)) ≠ ⊤))
  have hfSupport : Function.support f ⊆ Icc (1 / 4 : ℝ) (3 / 4) := by
    intro t ht
    by_contra h
    exact ht (indicator_of_notMem h _)
  have hfCompact : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport f)
      (closure_minimal hfSupport isClosed_Icc)
  have hfValues : ∀ t, 0 ≤ f t ∧ f t ≤ 2 := by
    intro t
    by_cases ht : t ∈ Icc (1 / 4 : ℝ) (3 / 4)
    · simp only [f, indicator_of_mem ht]
      norm_num
    · simp only [f, indicator_of_notMem ht]
      norm_num
  have hfMass : (∫ t, f t) = 1 := by
    rw [show f = (Icc (1 / 4 : ℝ) (3 / 4)).indicator (fun _ => 2) from rfl,
      integral_indicator measurableSet_Icc, integral_const]
    norm_num [Real.volume_Icc]
  let b : ℝ → ℝ := rho ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
  have hbSupport : Function.support b ⊆ Icc (1 / 8 : ℝ) (7 / 8) := by
    intro t ht
    obtain ⟨u, hu, v, hv, huv⟩ := support_convolution_subset_swap
      (ContinuousLinearMap.lsmul ℝ ℝ) ht
    have hu' := hfSupport hu
    have hv' := hrhoTSupport (subset_tsupport rho hv)
    constructor <;> linarith only [hu'.1, hu'.2, hv'.1, hv'.2, huv]
  have hbTSupport : tsupport b ⊆ Icc (1 / 8 : ℝ) (7 / 8) :=
    closure_minimal hbSupport isClosed_Icc
  refine ⟨b, hrhoCompact.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    hrhoSmooth hfInt.locallyIntegrable,
    hrhoCompact.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hfCompact,
    ?_, ?_, ?_⟩
  · exact hbTSupport.trans (by intro t ht; constructor <;> linarith only [ht.1, ht.2])
  · intro t
    constructor
    · exact integral_nonneg (fun u => mul_nonneg (hrhoNonneg u) (hfValues (t - u)).1)
    · have hconst : ConvolutionExistsAt rho (fun _ : ℝ => (2 : ℝ)) t
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
          using hrhoInt.mul_const 2
      have hbound := convolution_mono_right_of_nonneg hconst hrhoNonneg
        (fun u => (hfValues u).2) (fun _ => by norm_num)
      have hmass : (rho ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun _ : ℝ => (2 : ℝ))) t = 2 := by
        simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
          integral_mul_const, hrhoMass, one_mul]
      exact hbound.trans_eq hmass
  · dsimp only [b]
    rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hrhoInt hfInt,
      hrhoMass, hfMass]
    norm_num

end HarmonicMaps
