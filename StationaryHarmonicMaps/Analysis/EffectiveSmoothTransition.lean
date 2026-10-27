module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! # Explicit derivative bounds for the literal smooth transition -/

public section

namespace StationaryHarmonicMaps.Analysis

open Real Polynomial

noncomputable section

private def glueD1 (x : Real) : Real := x⁻¹ ^ 2 * expNegInvGlue x

private def glueD2 (x : Real) : Real :=
  (x⁻¹ ^ 4 - 2 * x⁻¹ ^ 3) * expNegInvGlue x

private theorem glue_hasDerivAt (x : Real) :
    HasDerivAt expNegInvGlue (glueD1 x) x := by
  simpa [glueD1] using
    expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial Real) x

private theorem glueD1_hasDerivAt (x : Real) :
    HasDerivAt glueD1 (glueD2 x) x := by
  convert expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
    ((Polynomial.X : Polynomial Real) ^ 2) x using 1
  · funext y
    simp only [glueD1, Polynomial.eval_pow, Polynomial.eval_X]
  · simp only [glueD2, Polynomial.derivative_X_pow,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring

private theorem pow_mul_exp_neg_le_factorial {t : Real} (ht : 0 <= t) (k : Nat) :
    t ^ k * Real.exp (-t) <= (Nat.factorial k : Real) := by
  have h := Real.pow_div_factorial_le_exp t ht k
  have hk : (0 : Real) < (Nat.factorial k : Real) := by positivity
  have hp : t ^ k <= Real.exp t * (Nat.factorial k : Real) :=
    (div_le_iff₀ hk).mp h
  calc
    t ^ k * Real.exp (-t) <=
        (Real.exp t * (Nat.factorial k : Real)) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = (Nat.factorial k : Real) := by
      rw [mul_right_comm, <- Real.exp_add]
      simp

private theorem glue_abs_le_one (x : Real) : |expNegInvGlue x| <= 1 := by
  rw [abs_of_nonneg (expNegInvGlue.nonneg x)]
  by_cases hx : x <= 0
  · rw [expNegInvGlue.zero_of_nonpos hx]
    norm_num
  · have hx' : 0 < x := lt_of_not_ge hx
    simp only [expNegInvGlue, if_neg hx]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr hx'.le))

private theorem glueD1_abs_le_two (x : Real) : |glueD1 x| <= 2 := by
  by_cases hx : x <= 0
  · simp [glueD1, expNegInvGlue.zero_of_nonpos hx]
  · have ht : 0 <= x⁻¹ := inv_nonneg.mpr (lt_of_not_ge hx).le
    have h := pow_mul_exp_neg_le_factorial ht 2
    simpa [glueD1, expNegInvGlue, hx, abs_of_nonneg,
      mul_nonneg (sq_nonneg x⁻¹) (Real.exp_pos (-x⁻¹)).le] using h

private theorem glueD2_abs_le_thirtySix (x : Real) : |glueD2 x| <= 36 := by
  by_cases hx : x <= 0
  · simp [glueD2, expNegInvGlue.zero_of_nonpos hx]
  · have ht : 0 <= x⁻¹ := inv_nonneg.mpr (lt_of_not_ge hx).le
    have h3 : x⁻¹ ^ 3 * Real.exp (-x⁻¹) <= 6 := by
      convert pow_mul_exp_neg_le_factorial ht 3 using 1
      norm_num
    have h4 : x⁻¹ ^ 4 * Real.exp (-x⁻¹) <= 24 := by
      convert pow_mul_exp_neg_le_factorial ht 4 using 1
      norm_num
    have hE : 0 <= Real.exp (-x⁻¹) := (Real.exp_pos _).le
    have h3n : 0 <= x⁻¹ ^ 3 := pow_nonneg ht _
    have h4n : 0 <= x⁻¹ ^ 4 := pow_nonneg ht _
    calc
      |glueD2 x| = |x⁻¹ ^ 4 * Real.exp (-x⁻¹) -
          2 * (x⁻¹ ^ 3 * Real.exp (-x⁻¹))| := by
        simp only [glueD2, expNegInvGlue, if_neg hx]
        congr 1
        ring
      _ <= |x⁻¹ ^ 4 * Real.exp (-x⁻¹)| +
          |2 * (x⁻¹ ^ 3 * Real.exp (-x⁻¹))| := abs_sub _ _
      _ <= 36 := by
        rw [abs_of_nonneg (mul_nonneg h4n hE),
          abs_of_nonneg (mul_nonneg (by norm_num) (mul_nonneg h3n hE))]
        linarith only [h3, h4]

private theorem exp_neg_two_ge_sixteenth : (1 : Real) / 16 <= Real.exp (-2) := by
  have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hpos : 0 < Real.exp 1 := Real.exp_pos _
  have h2 : Real.exp 2 < 16 := by
    have heq : Real.exp (2 : Real) = Real.exp 1 * Real.exp 1 := by
      rw [<- Real.exp_add]
      norm_num
    rw [heq]
    nlinarith only [h1, hpos]
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos 2) h2.le

private def transitionDenom (x : Real) : Real :=
  expNegInvGlue x + expNegInvGlue (1 - x)

private theorem transitionDenom_lower (x : Real) :
    (1 : Real) / 16 <= transitionDenom x := by
  have hhalf : expNegInvGlue (1 / 2 : Real) = Real.exp (-2) := by
    norm_num [expNegInvGlue]
  rcases le_total (1 / 2 : Real) x with hx | hx
  · have h := expNegInvGlue.monotone hx
    rw [hhalf] at h
    exact exp_neg_two_ge_sixteenth.trans
      (h.trans (le_add_of_nonneg_right (expNegInvGlue.nonneg _)))
  · have h := expNegInvGlue.monotone (show (1 / 2 : Real) <= 1 - x by linarith only [hx])
    rw [hhalf] at h
    exact exp_neg_two_ge_sixteenth.trans
      (h.trans (le_add_of_nonneg_left (expNegInvGlue.nonneg _)))

private def transitionDenomD1 (x : Real) : Real :=
  glueD1 x - glueD1 (1 - x)

private def transitionDenomD2 (x : Real) : Real :=
  glueD2 x + glueD2 (1 - x)

private theorem transitionDenom_hasDerivAt (x : Real) :
    HasDerivAt transitionDenom (transitionDenomD1 x) x := by
  have h := (glue_hasDerivAt x).add
    ((glue_hasDerivAt (1 - x)).comp x
      ((hasDerivAt_const x (1 : Real)).sub (hasDerivAt_id x)))
  apply h.congr_deriv
  change glueD1 x + glueD1 (1 - x) * (0 - 1) = glueD1 x - glueD1 (1 - x)
  ring

private theorem transitionDenomD1_hasDerivAt (x : Real) :
    HasDerivAt transitionDenomD1 (transitionDenomD2 x) x := by
  have h := (glueD1_hasDerivAt x).sub
    ((glueD1_hasDerivAt (1 - x)).comp x
      ((hasDerivAt_const x (1 : Real)).sub (hasDerivAt_id x)))
  apply h.congr_deriv
  change glueD2 x - glueD2 (1 - x) * (0 - 1) = glueD2 x + glueD2 (1 - x)
  ring

private theorem transitionDenom_abs_le_two (x : Real) :
    |transitionDenom x| <= 2 := by
  exact (abs_add_le _ _).trans (by
    have h := add_le_add (glue_abs_le_one x) (glue_abs_le_one (1 - x))
    norm_num at h
    exact h)

private theorem transitionDenomD1_abs_le_four (x : Real) :
    |transitionDenomD1 x| <= 4 := by
  exact (abs_sub _ _).trans (by
    have h := add_le_add (glueD1_abs_le_two x) (glueD1_abs_le_two (1 - x))
    norm_num at h
    exact h)

private theorem transitionDenomD2_abs_le_seventyTwo (x : Real) :
    |transitionDenomD2 x| <= 72 := by
  exact (abs_add_le _ _).trans (by
    have h := add_le_add (glueD2_abs_le_thirtySix x) (glueD2_abs_le_thirtySix (1 - x))
    norm_num at h
    exact h)

private def transitionD1 (x : Real) : Real :=
  (glueD1 x * transitionDenom x - expNegInvGlue x * transitionDenomD1 x) /
    transitionDenom x ^ 2

private def transitionD2 (x : Real) : Real :=
  ((glueD2 x * transitionDenom x - expNegInvGlue x * transitionDenomD2 x) *
      transitionDenom x ^ 2 -
    (glueD1 x * transitionDenom x - expNegInvGlue x * transitionDenomD1 x) *
      (2 * transitionDenom x * transitionDenomD1 x)) /
    (transitionDenom x ^ 2) ^ 2

private theorem transition_hasDerivAt (x : Real) :
    HasDerivAt Real.smoothTransition (transitionD1 x) x := by
  exact (glue_hasDerivAt x).div (transitionDenom_hasDerivAt x)
    (ne_of_gt (lt_of_lt_of_le (by norm_num) (transitionDenom_lower x)))

private theorem transitionD1_hasDerivAt (x : Real) :
    HasDerivAt transitionD1 (transitionD2 x) x := by
  have hf := glue_hasDerivAt x
  have hf1 := glueD1_hasDerivAt x
  have hb := transitionDenom_hasDerivAt x
  have hb1 := transitionDenomD1_hasDerivAt x
  have hn : HasDerivAt
      (fun y => glueD1 y * transitionDenom y - expNegInvGlue y * transitionDenomD1 y)
      (glueD2 x * transitionDenom x - expNegInvGlue x * transitionDenomD2 x) x :=
    ((hf1.mul hb).sub (hf.mul hb1)).congr_deriv (by ring)
  have hd : HasDerivAt (fun y => transitionDenom y ^ 2)
      (2 * transitionDenom x * transitionDenomD1 x) x :=
    (hb.pow 2).congr_deriv (by ring)
  exact hn.div hd (pow_ne_zero 2
    (ne_of_gt (lt_of_lt_of_le (by norm_num) (transitionDenom_lower x))))

private theorem explicit_quotient_derivative_bounds
    (a a1 a2 b b1 b2 : Real)
    (ha : |a| <= 1) (ha1 : |a1| <= 2) (ha2 : |a2| <= 36)
    (hb0 : (1 : Real) / 16 <= b) (hb : |b| <= 2)
    (hb1 : |b1| <= 4) (hb2 : |b2| <= 72) :
    |(a1 * b - a * b1) / b ^ 2| <= (2 : Real) ^ 20 ∧
    |((a2 * b - a * b2) * b ^ 2 - (a1 * b - a * b1) * (2 * b * b1)) /
        (b ^ 2) ^ 2| <= (2 : Real) ^ 40 := by
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb0
  have hn : |a1 * b - a * b1| <= 8 := by
    calc
      _ <= |a1 * b| + |a * b1| := abs_sub _ _
      _ = |a1| * |b| + |a| * |b1| := by rw [abs_mul, abs_mul]
      _ <= 2 * 2 + 1 * 4 := add_le_add
        (mul_le_mul ha1 hb (abs_nonneg _) (by norm_num))
        (mul_le_mul ha hb1 (abs_nonneg _) (by norm_num))
      _ = 8 := by norm_num
  have hdn : |a2 * b - a * b2| <= 144 := by
    calc
      _ <= |a2 * b| + |a * b2| := abs_sub _ _
      _ = |a2| * |b| + |a| * |b2| := by rw [abs_mul, abs_mul]
      _ <= 36 * 2 + 1 * 72 := add_le_add
        (mul_le_mul ha2 hb (abs_nonneg _) (by norm_num))
        (mul_le_mul ha hb2 (abs_nonneg _) (by norm_num))
      _ = 144 := by norm_num
  have hdd : |2 * b * b1| <= 16 := by
    calc
      _ = 2 * |b| * |b1| := by rw [abs_mul, abs_mul]; norm_num
      _ <= 2 * 2 * 4 := mul_le_mul
        (mul_le_mul_of_nonneg_left hb (by norm_num)) hb1 (abs_nonneg _) (by norm_num)
      _ = 16 := by norm_num
  have hbabs : b <= 2 := (le_abs_self b).trans hb
  have hbSq : b ^ 2 <= 4 := by nlinarith only [hbpos, hbabs]
  have hbSqLower : (1 : Real) / 256 <= b ^ 2 := by
    nlinarith only [hb0, sq_nonneg (b - 1 / 16)]
  have hbFourthLower : (1 : Real) / 65536 <= (b ^ 2) ^ 2 := by
    nlinarith only [hbSqLower, sq_nonneg (b ^ 2 - 1 / 256)]
  have hn2 : |(a2 * b - a * b2) * b ^ 2 - (a1 * b - a * b1) * (2 * b * b1)| <= 704 := by
    calc
      _ <= |(a2 * b - a * b2) * b ^ 2| +
          |(a1 * b - a * b1) * (2 * b * b1)| := abs_sub _ _
      _ = |a2 * b - a * b2| * b ^ 2 + |a1 * b - a * b1| * |2 * b * b1| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg b)]
      _ <= 144 * 4 + 8 * 16 := add_le_add
        (mul_le_mul hdn hbSq (sq_nonneg _) (by norm_num))
        (mul_le_mul hn hdd (abs_nonneg _) (by norm_num))
      _ = 704 := by norm_num
  constructor
  · rw [abs_div, abs_of_nonneg (sq_nonneg b)]
    apply (div_le_iff₀ (pow_pos hbpos 2)).mpr
    norm_num
    nlinarith only [hn, hbSqLower]
  · rw [abs_div, abs_of_nonneg (sq_nonneg (b ^ 2))]
    apply (div_le_iff₀ (pow_pos (pow_pos hbpos 2) 2)).mpr
    norm_num
    nlinarith only [hn2, hbFourthLower]

/-- The literal exponential glue has a uniform explicit first derivative bound. -/
theorem expNegInvGlue_abs_deriv_le (x : Real) :
    |deriv expNegInvGlue x| <= 2 := by
  rw [(glue_hasDerivAt x).deriv]
  exact glueD1_abs_le_two x

/-- The literal exponential glue has a uniform explicit second derivative bound. -/
theorem expNegInvGlue_abs_deriv_deriv_le (x : Real) :
    |deriv (deriv expNegInvGlue) x| <= 36 := by
  have h : deriv expNegInvGlue = glueD1 := funext fun y => (glue_hasDerivAt y).deriv
  rw [h, (glueD1_hasDerivAt x).deriv]
  exact glueD2_abs_le_thirtySix x

/-- A numerical lower bound for the actual smooth-transition denominator. -/
theorem smoothTransition_denom_lower (x : Real) :
    (1 : Real) / 16 <= expNegInvGlue x + expNegInvGlue (1 - x) :=
  transitionDenom_lower x

/-- A completely explicit global bound for the actual transition derivative. -/
theorem smoothTransition_abs_deriv_le (x : Real) :
    |deriv Real.smoothTransition x| <= (2 : Real) ^ 20 := by
  rw [(transition_hasDerivAt x).deriv]
  exact (explicit_quotient_derivative_bounds _ _ _ _ _ _
    (glue_abs_le_one x) (glueD1_abs_le_two x) (glueD2_abs_le_thirtySix x)
    (transitionDenom_lower x) (transitionDenom_abs_le_two x)
    (transitionDenomD1_abs_le_four x) (transitionDenomD2_abs_le_seventyTwo x)).1

/-- A completely explicit global bound for the actual second transition derivative. -/
theorem smoothTransition_abs_deriv_deriv_le (x : Real) :
    |deriv (deriv Real.smoothTransition) x| <= (2 : Real) ^ 40 := by
  have h : deriv Real.smoothTransition = transitionD1 :=
    funext fun y => (transition_hasDerivAt y).deriv
  rw [h, (transitionD1_hasDerivAt x).deriv]
  exact (explicit_quotient_derivative_bounds _ _ _ _ _ _
    (glue_abs_le_one x) (glueD1_abs_le_two x) (glueD2_abs_le_thirtySix x)
    (transitionDenom_lower x) (transitionDenom_abs_le_two x)
    (transitionDenomD1_abs_le_four x) (transitionDenomD2_abs_le_seventyTwo x)).2

/-- The literal transition has zero first derivative on the closed zero plateau. -/
theorem smoothTransition_deriv_eq_zero_of_nonpos {x : Real} (hx : x <= 0) :
    deriv Real.smoothTransition x = 0 := by
  rw [(transition_hasDerivAt x).deriv]
  simp only [transitionD1, glueD1, expNegInvGlue.zero_of_nonpos hx,
    mul_zero, zero_mul, sub_self, zero_div]

/-- The literal transition has zero second derivative on the closed zero plateau. -/
theorem smoothTransition_deriv_deriv_eq_zero_of_nonpos {x : Real} (hx : x <= 0) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have h : deriv Real.smoothTransition = transitionD1 :=
    funext fun y => (transition_hasDerivAt y).deriv
  rw [h, (transitionD1_hasDerivAt x).deriv]
  simp only [transitionD2, glueD1, glueD2, expNegInvGlue.zero_of_nonpos hx,
    mul_zero, zero_mul, sub_self, zero_div]

end

end StationaryHarmonicMaps.Analysis
