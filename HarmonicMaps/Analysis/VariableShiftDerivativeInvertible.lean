module

public import HarmonicMaps.Analysis.VariableShiftCalculus
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Invertibility of the variable translation differential

The uniform derivative bound makes the rank-one perturbation of the identity
strictly smaller than one in operator norm. Thus the actual differential is
bijective and is represented by a continuous linear equivalence at every point.
-/

public section

open scoped ContDiff

namespace HarmonicMaps

variable {n : ℕ} {s : Domain n → ℝ} {L : ℝ}

/-- The actual differential is bijective under the source derivative bound. -/
theorem variableShift_fderiv_bijective (hs : ContDiff ℝ ∞ s)
    (hDs : ∀ z, ‖fderiv ℝ s z‖ ≤ L) (hL : L ≤ 1 / 4) (y : Domain n)
    (hy : y ∈ Metric.ball 0 1) (x : Domain n) :
    Function.Bijective (fderiv ℝ (variableShift s y) x) := by
  have hyNorm : ‖y‖ ≤ 1 := le_of_lt
    (by simpa only [Metric.mem_ball, dist_zero_right] using hy)
  have hRank : ‖(fderiv ℝ s x).smulRight y‖ ≤ L := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    calc
      ‖fderiv ℝ s x‖ * ‖y‖ ≤ ‖fderiv ℝ s x‖ * 1 :=
        mul_le_mul_of_nonneg_left hyNorm (norm_nonneg _)
      _ = ‖fderiv ℝ s x‖ := mul_one _
      _ ≤ L := hDs x
  have hRankLt : ‖(fderiv ℝ s x).smulRight y‖ < 1 :=
    hRank.trans_lt (by linarith only [hL])
  have hUnit : IsUnit (fderiv ℝ (variableShift s y) x) := by
    rw [fderiv_variableShift (hs.differentiable (by norm_num) x) y]
    change IsUnit (1 - (fderiv ℝ s x).smulRight y)
    exact isUnit_one_sub_of_norm_lt_one hRankLt
  exact ContinuousLinearMap.isUnit_iff_bijective.mp hUnit

/-- Every source differential admits a continuous linear equivalence certificate. -/
theorem variableShift_exists_continuousLinearEquiv_hasFDerivAt (hs : ContDiff ℝ ∞ s)
    (hDs : ∀ z, ‖fderiv ℝ s z‖ ≤ L) (hL : L ≤ 1 / 4) (y : Domain n)
    (hy : y ∈ Metric.ball 0 1) (x : Domain n) :
    ∃ e : Domain n ≃L[ℝ] Domain n,
      HasFDerivAt (variableShift s y) (e : Domain n →L[ℝ] Domain n) x := by
  have hBij := variableShift_fderiv_bijective hs hDs hL y hy x
  have hKer : (fderiv ℝ (variableShift s y) x).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hBij.1
  have hRange : (fderiv ℝ (variableShift s y) x).range = ⊤ :=
    LinearMap.range_eq_top.mpr hBij.2
  refine ⟨ContinuousLinearEquiv.ofBijective (fderiv ℝ (variableShift s y) x)
    hKer hRange, ?_⟩
  rw [ContinuousLinearEquiv.coe_ofBijective]
  exact (contDiff_variableShift hs y).differentiable (by norm_num) x |>.hasFDerivAt

end HarmonicMaps
