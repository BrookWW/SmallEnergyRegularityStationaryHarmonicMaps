module

public import HolderToCK.Analysis.Poisson.HessianHolder
public import HolderToCK.Analysis.Poisson.RadialExteriorIntegral
public import HolderToCK.Analysis.Poisson.PotentialLimitsHessian
public import HolderToCK.Analysis.Poisson.HessianAnnularBounds

/-! # Compensated near and far Hessian translation bounds -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace HolderToCK

theorem integrableOn_subLeft_preimage_iff {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] (x : Domain n)
    (f : Domain n → E) {s : Set (Domain n)} (hs : MeasurableSet s) :
    IntegrableOn (fun z => f (x - z)) ((fun z => x - z) ⁻¹' s) volume ↔
      IntegrableOn f s volume := by
  have heq : ((fun z => x - z) ⁻¹' s).indicator (fun z => f (x - z)) =
      fun z => s.indicator f (x - z) := by
    funext z
    simp only [indicator, mem_preimage]
    rfl
  have hp : MeasurableSet ((fun z : Domain n => x - z) ⁻¹' s) :=
    hs.preimage (show Measurable (fun z : Domain n => x - z) from
      (continuous_const.sub continuous_id).measurable)
  rw [← integrable_indicator_iff hp,
    ← integrable_indicator_iff hs, heq]
  exact integrable_comp_sub_left _ x

theorem integral_subLeft_preimage {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : Domain n) (f : Domain n → E) {s : Set (Domain n)} (hs : MeasurableSet s) :
    (∫ z in ((fun z => x - z) ⁻¹' s), f (x - z)) = ∫ z in s, f z := by
  have heq : ((fun z => x - z) ⁻¹' s).indicator (fun z => f (x - z)) =
      fun z => s.indicator f (x - z) := by
    funext z
    simp only [indicator, mem_preimage]
    rfl
  have hp : MeasurableSet ((fun z : Domain n => x - z) ⁻¹' s) :=
    hs.preimage (show Measurable (fun z : Domain n => x - z) from
      (continuous_const.sub continuous_id).measurable)
  rw [← integral_indicator hp,
    ← integral_indicator hs, heq]
  exact integral_sub_left_eq_self _ volume x

theorem subLeft_preimage_ball {n : ℕ} (x : Domain n) (R : ℝ) :
    (fun z => x - z) ⁻¹' Metric.ball (0 : Domain n) R = Metric.ball x R := by
  ext z
  simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero, norm_sub_rev]

theorem integrableOn_subLeft_ball_iff {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] (x : Domain n) (f : Domain n → E) (R : ℝ) :
    IntegrableOn (fun z => f (x - z)) (Metric.ball x R) volume ↔
      IntegrableOn f (Metric.ball (0 : Domain n) R) volume := by
  rw [← subLeft_preimage_ball x R]
  exact integrableOn_subLeft_preimage_iff x f measurableSet_ball

theorem integral_subLeft_ball {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : Domain n) (f : Domain n → E) (R : ℝ) :
    (∫ z in Metric.ball x R, f (x - z)) = ∫ z in Metric.ball (0 : Domain n) R, f z := by
  rw [← subLeft_preimage_ball x R]
  exact integral_subLeft_preimage x f measurableSet_ball

theorem hessianKernelExpression_shiftedHolderDifference_integrableOn {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H R : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H) (x : Domain n) :
    IntegrableOn (fun z => hessianKernelExpression i j (x - z) • (g z - g x))
      (Metric.ball x R) volume := by
  have hi := (integrableOn_subLeft_ball_iff x
    (fun z => hessianKernelExpression i j z • (g (x - z) - g x)) R).mpr
      (hessianKernelExpression_holderDifference_integrableOn hn i j hη hH hHolder x)
  simpa only [sub_sub_cancel] using hi

theorem hessianKernelExpression_shiftedHolderDifference_integral_norm_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H R : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hR : 0 < R)
    (hHolder : HolderBoundOn univ g η H) (x : Domain n) :
    (∫ z in Metric.ball x R,
      ‖hessianKernelExpression i j (x - z) • (g z - g x)‖) ≤
      ((n : ℝ) + 1) * H * R ^ η / η := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have heq : (∫ z in Metric.ball x R,
      ‖hessianKernelExpression i j (x - z) • (g z - g x)‖) =
      ∫ z in Metric.ball (0 : Domain n) R,
        ‖hessianKernelExpression i j z • (g (x - z) - g x)‖ := by
    simpa only [sub_sub_cancel] using integral_subLeft_ball x
      (fun z => ‖hessianKernelExpression i j z • (g (x - z) - g x)‖) R
  rw [heq]
  have hi := hessianKernelExpression_holderDifference_integrableOn hn i j hη hH hHolder x
    (R := R)
  have hpow := (norm_rpow_locallyIntegrable hn (p := η - (n : ℝ))
    (by linarith only [hη])).integrableOn_isCompact (isCompact_closedBall (0 : Domain n) R)
  calc
    _ ≤ ∫ z in Metric.ball (0 : Domain n) R,
        (((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ * H) * ‖z‖ ^ (η - (n : ℝ)) := by
      apply integral_mono_ae hi.norm ((hpow.mono_set Metric.ball_subset_closedBall).const_mul _)
      filter_upwards [ae_restrict_of_ae ((volume : Measure (Domain n)).ae_ne 0)] with z hz
      exact hessianKernelExpression_holderDifference_bound hn i j hH hHolder x z hz
    _ = _ := by
      rw [integral_const_mul, radialPower_integral_ball hn hη hR]
      have hS : euclideanSphereArea n ≠ 0 := (euclideanSphereArea_pos hn).ne'
      field_simp

theorem ball_twoDist_subset_ball_threeDist {n : ℕ} (x y : Domain n) :
    Metric.ball x (2 * dist x y) ⊆ Metric.ball y (3 * dist x y) := by
  intro z hz
  have hz' : dist z x < 2 * dist x y := hz
  change dist z y < 3 * dist x y
  exact (dist_triangle z x y).trans_lt (by linarith only [hz'])

theorem ball_dist_subset_ball_twoDist {n : ℕ} (x y : Domain n) :
    Metric.ball y (dist x y) ⊆ Metric.ball x (2 * dist x y) := by
  intro z hz
  have hz' : dist z y < dist x y := hz
  change dist z x < 2 * dist x y
  exact (dist_triangle z y x).trans_lt (by rw [dist_comm y x]; linarith only [hz'])

theorem hessianKernelDifference_holderFar_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (x y z : Domain n) (hfar : 2 * dist x y ≤ ‖x - z‖) (hz : x - z ≠ 0) :
    ‖(hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z)) •
        (g z - g x)‖ ≤
      (hessianKernelTranslationConstant n * H * dist x y) *
        ‖x - z‖ ^ (η - (n : ℝ) - 1) := by
  have hg : ‖g z - g x‖ ≤ H * ‖x - z‖ ^ η := by
    simpa only [dist_eq_norm, norm_sub_rev, Real.rpow_eq_pow] using
      hHolder z (mem_univ _) x (mem_univ _)
  rw [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ (hessianKernelTranslationConstant n * dist x y * ‖x - z‖ ^ (-(n : ℝ) - 1)) *
        (H * ‖x - z‖ ^ η) :=
      (mul_le_mul_of_nonneg_left hg (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hessianKernelExpression_shift_difference_bound hn i j x y z hfar)
          (mul_nonneg hH (Real.rpow_nonneg (norm_nonneg _) _)))
    _ = _ := by
      rw [show (hessianKernelTranslationConstant n * dist x y * ‖x - z‖ ^ (-(n : ℝ) - 1)) *
          (H * ‖x - z‖ ^ η) =
          (hessianKernelTranslationConstant n * H * dist x y) *
            (‖x - z‖ ^ (-(n : ℝ) - 1) * ‖x - z‖ ^ η) by ring,
        ← Real.rpow_add (norm_pos_iff.mpr hz)]
      congr 2
      ring

theorem hessianKernelTranslationConstant_nonneg {n : ℕ} (hn : 0 < n) :
    0 ≤ hessianKernelTranslationConstant n := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (by positivity))
    (inv_nonneg.mpr (euclideanSphereArea_pos hn).le)) (Real.rpow_nonneg (by norm_num) _)

theorem radialExteriorPower_shifted_integrableOn {n : ℕ} (hn : 0 < n) {η R : ℝ}
    (hη : η < 1) (hR : 0 < R) (x : Domain n) :
    IntegrableOn (fun z => ‖x - z‖ ^ (η - (n : ℝ) - 1))
      (Metric.ball x R)ᶜ volume := by
  have hi := (integrableOn_subLeft_preimage_iff x
    (fun z => ‖z‖ ^ (η - (n : ℝ) - 1)) measurableSet_ball.compl).mpr
      (radialExteriorPower_integrableOn hn hη hR)
  rwa [preimage_compl, subLeft_preimage_ball] at hi

theorem radialExteriorPower_shifted_integral {n : ℕ} (hn : 0 < n) {η R : ℝ}
    (hη : η < 1) (hR : 0 < R) (x : Domain n) :
    (∫ z in (Metric.ball x R)ᶜ, ‖x - z‖ ^ (η - (n : ℝ) - 1)) =
      euclideanSphereArea n * R ^ (η - 1) / (1 - η) := by
  have heq := integral_subLeft_preimage x (fun z => ‖z‖ ^ (η - (n : ℝ) - 1))
    (s := (Metric.ball (0 : Domain n) R)ᶜ)
    measurableSet_ball.compl
  rw [preimage_compl, subLeft_preimage_ball] at heq
  rw [heq, radialExteriorPower_integral hn hη hR]

theorem hessianKernelDifference_holderFar_integrableOn {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hH : 0 ≤ H)
    (hHolder : HolderBoundOn univ g η H) (x y : Domain n) (hxy : x ≠ y) :
    IntegrableOn (fun z =>
      (hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z)) •
        (g z - g x)) (Metric.ball x (2 * dist x y))ᶜ volume := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hi := (radialExteriorPower_shifted_integrableOn hn hη1 (mul_pos zero_lt_two hd) x).const_mul
    (hessianKernelTranslationConstant n * H * dist x y)
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  apply hi.mono' ?_ ?_
  · exact (((hessianKernelExpression_measurable i j).comp
      (continuous_const.sub continuous_id).measurable).sub
        ((hessianKernelExpression_measurable i j).comp
          (continuous_const.sub continuous_id).measurable)).aestronglyMeasurable.smul
            (hg.sub continuous_const).aestronglyMeasurable |>.restrict
  · filter_upwards [ae_restrict_mem measurableSet_ball.compl] with z hz
    have hfar : 2 * dist x y ≤ ‖x - z‖ := by
      simpa only [mem_compl_iff, Metric.mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hz
    exact hessianKernelDifference_holderFar_bound hn i j hH hHolder x y z hfar
      (norm_pos_iff.mp ((mul_pos zero_lt_two hd).trans_le hfar))

theorem hessianKernelDifference_integrableOn {n : ℕ}
    (hn : 0 < n) (i j : Fin n) (x y : Domain n) (hxy : x ≠ y) :
    IntegrableOn (fun z =>
      hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z))
      (Metric.ball x (2 * dist x y))ᶜ volume := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hi := (radialExteriorPower_shifted_integrableOn hn (η := 0) zero_lt_one
    (mul_pos zero_lt_two hd) x).const_mul (hessianKernelTranslationConstant n * dist x y)
  simp only [zero_sub] at hi
  apply hi.mono' ?_ ?_
  · exact (((hessianKernelExpression_measurable i j).comp
      (continuous_const.sub continuous_id).measurable).sub
        ((hessianKernelExpression_measurable i j).comp
          (continuous_const.sub continuous_id).measurable)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_ball.compl] with z hz
    have hfar : 2 * dist x y ≤ ‖x - z‖ := by
      simpa only [mem_compl_iff, Metric.mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hz
    rw [Real.norm_eq_abs]
    exact hessianKernelExpression_shift_difference_bound hn i j x y z hfar

theorem hessianKernelExpression_shiftedData_integrableOn_exterior {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : Fin n) {g : Domain n → E} (hg : Continuous g) (hcg : HasCompactSupport g)
    {R : ℝ} (hR : 0 < R) (x : Domain n) :
    IntegrableOn (fun z => hessianKernelExpression i j (x - z) • g z)
      (Metric.ball x R)ᶜ volume := by
  have hi := (integrableOn_subLeft_preimage_iff x
    (fun z => hessianKernelExpression i j z • g (x - z)) measurableSet_ball.compl).mpr
      (hessianKernelExpression_smul_testIntegrableOn_exterior i j
        (hg.comp (continuous_const.sub continuous_id))
        (hcg.comp_homeomorph (Homeomorph.subLeft x)) hR)
  rw [preimage_compl, subLeft_preimage_ball] at hi
  simpa only [sub_sub_cancel] using hi

theorem potentialHessianExpression_shifted_splitRadius {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H R : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (hR : 0 < R) (x : Domain n) :
    potentialHessianExpression i j g x =
      (((if i = j then 1 else 0) / (n : ℝ)) • g x +
        ∫ z in Metric.ball x R,
          hessianKernelExpression i j (x - z) • (g z - g x)) +
      ∫ z in (Metric.ball x R)ᶜ, hessianKernelExpression i j (x - z) • g z := by
  rw [potentialHessianExpression_splitRadius_all hn i j hη hH hHolder hcg hR x]
  congr 1
  · congr 1
    symm
    simpa only [sub_sub_cancel] using integral_subLeft_ball x
      (fun z => hessianKernelExpression i j z • (g (x - z) - g x)) R
  · symm
    have heq := integral_subLeft_preimage x (fun z => hessianKernelExpression i j z • g (x - z))
      (s := (Metric.ball (0 : Domain n) R)ᶜ) measurableSet_ball.compl
    rw [preimage_compl, subLeft_preimage_ball] at heq
    simpa only [sub_sub_cancel] using heq

@[expose] noncomputable def hessianFarHolderConstant (n : ℕ) (η : ℝ) : ℝ :=
  hessianKernelTranslationConstant n * euclideanSphereArea n * (2 : ℝ) ^ (η - 1) / (1 - η)

theorem hessianKernelDifference_holderFar_integral_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hH : 0 ≤ H)
    (hHolder : HolderBoundOn univ g η H) (x y : Domain n) (hxy : x ≠ y) :
    ‖∫ z in (Metric.ball x (2 * dist x y))ᶜ,
      (hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z)) •
        (g z - g x)‖ ≤ hessianFarHolderConstant n η * H * dist x y ^ η := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hi := hessianKernelDifference_holderFar_integrableOn hn i j hη hη1 hH hHolder x y hxy
  have hpow := (radialExteriorPower_shifted_integrableOn hn hη1 (mul_pos zero_lt_two hd) x).const_mul
    (hessianKernelTranslationConstant n * H * dist x y)
  calc
    _ ≤ ∫ z in (Metric.ball x (2 * dist x y))ᶜ,
        ‖(hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z)) •
          (g z - g x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in (Metric.ball x (2 * dist x y))ᶜ,
        (hessianKernelTranslationConstant n * H * dist x y) *
          ‖x - z‖ ^ (η - (n : ℝ) - 1) := by
      apply integral_mono_ae hi.norm hpow
      filter_upwards [ae_restrict_mem measurableSet_ball.compl] with z hz
      have hfar : 2 * dist x y ≤ ‖x - z‖ := by
        simpa only [mem_compl_iff, Metric.mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hz
      exact hessianKernelDifference_holderFar_bound hn i j hH hHolder x y z hfar
        (norm_pos_iff.mp ((mul_pos zero_lt_two hd).trans_le hfar))
    _ = _ := by
      rw [integral_const_mul, radialExteriorPower_shifted_integral hn hη1
        (mul_pos zero_lt_two hd), Real.mul_rpow zero_lt_two.le hd.le]
      have hp : dist x y * dist x y ^ (η - 1) = dist x y ^ η := by
        calc
          _ = dist x y ^ (1 : ℝ) * dist x y ^ (η - 1) := by rw [Real.rpow_one]
          _ = dist x y ^ (1 + (η - 1)) := (Real.rpow_add hd _ _).symm
          _ = _ := by congr 1; ring
      rw [show (hessianKernelTranslationConstant n * H * dist x y) *
          (euclideanSphereArea n * ((2 : ℝ) ^ (η - 1) * dist x y ^ (η - 1)) / (1 - η)) =
          (hessianKernelTranslationConstant n * euclideanSphereArea n * (2 : ℝ) ^ (η - 1) /
            (1 - η)) * H * (dist x y * dist x y ^ (η - 1)) by ring, hp]
      rfl

theorem hessianKernelExpression_commonNear_integrableOn {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H) (x y : Domain n) :
    IntegrableOn (fun z => hessianKernelExpression i j (y - z) • (g z - g y))
      (Metric.ball x (2 * dist x y)) volume :=
  (hessianKernelExpression_shiftedHolderDifference_integrableOn hn i j hη hH hHolder y
    (R := 3 * dist x y)).mono_set (ball_twoDist_subset_ball_threeDist x y)

theorem hessianKernelExpression_commonNear_integral_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (x y : Domain n) (hxy : x ≠ y) :
    ‖∫ z in Metric.ball x (2 * dist x y),
      hessianKernelExpression i j (y - z) • (g z - g y)‖ ≤
      ((n : ℝ) + 1) * H * (3 * dist x y) ^ η / η := by
  have hi := hessianKernelExpression_shiftedHolderDifference_integrableOn hn i j hη hH hHolder y
    (R := 3 * dist x y)
  calc
    _ ≤ ∫ z in Metric.ball x (2 * dist x y),
        ‖hessianKernelExpression i j (y - z) • (g z - g y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in Metric.ball y (3 * dist x y),
        ‖hessianKernelExpression i j (y - z) • (g z - g y)‖ :=
      setIntegral_mono_set hi.norm (Eventually.of_forall (fun z => norm_nonneg _))
        (Eventually.of_forall (fun _ hz => ball_twoDist_subset_ball_threeDist x y hz))
    _ ≤ _ := hessianKernelExpression_shiftedHolderDifference_integral_norm_bound hn i j hη hH
      (mul_pos (by norm_num) (dist_pos.mpr hxy)) hHolder y

theorem hessianKernelExpression_shifted_integrableOn_annulus {n : ℕ}
    (i j : Fin n) (x : Domain n) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun z => hessianKernelExpression i j (x - z))
      (Metric.ball x b \ Metric.ball x a) volume := by
  have hi := (integrableOn_subLeft_preimage_iff x (hessianKernelExpression i j)
    (measurableSet_ball.diff measurableSet_ball)).mpr
      (hessianKernelExpression_integrableOn_annulus i j ha (b := b))
  rwa [preimage_sdiff, subLeft_preimage_ball, subLeft_preimage_ball] at hi

theorem hessianKernelExpression_commonAnnulus_integrableOn {n : ℕ}
    (i j : Fin n) (x y : Domain n) (hxy : x ≠ y) :
    IntegrableOn (fun z => hessianKernelExpression i j (y - z))
      (Metric.ball x (2 * dist x y) \ Metric.ball y (dist x y)) volume := by
  apply (hessianKernelExpression_shifted_integrableOn_annulus i j y
    (b := 3 * dist x y) (dist_pos.mpr hxy)).mono_set
  intro z hz
  exact ⟨ball_twoDist_subset_ball_threeDist x y hz.1, hz.2⟩

theorem hessianKernelExpression_commonAnnulus_integral_bound {n : ℕ} (hn : 0 < n)
    (i j : Fin n) (x y : Domain n) (hxy : x ≠ y) :
    |∫ z in Metric.ball x (2 * dist x y) \ Metric.ball y (dist x y),
      hessianKernelExpression i j (y - z)| ≤ ((n : ℝ) + 1) * Real.log 3 := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hi := hessianKernelExpression_shifted_integrableOn_annulus i j y
    (b := 3 * dist x y) hd
  calc
    _ ≤ ∫ z in Metric.ball x (2 * dist x y) \ Metric.ball y (dist x y),
        ‖hessianKernelExpression i j (y - z)‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (f := fun z => hessianKernelExpression i j (y - z))
        (μ := volume.restrict (Metric.ball x (2 * dist x y) \ Metric.ball y (dist x y)))
    _ ≤ ∫ z in Metric.ball y (3 * dist x y) \ Metric.ball y (dist x y),
        ‖hessianKernelExpression i j (y - z)‖ :=
      setIntegral_mono_set hi.norm (Eventually.of_forall (fun z => norm_nonneg _))
        (Eventually.of_forall (fun z hz => ⟨ball_twoDist_subset_ball_threeDist x y hz.1, hz.2⟩))
    _ ≤ _ := by
      have heq := integral_subLeft_preimage y (fun z => ‖hessianKernelExpression i j z‖)
        (s := Metric.ball (0 : Domain n) (3 * dist x y) \ Metric.ball (0 : Domain n) (dist x y))
        (measurableSet_ball.diff measurableSet_ball)
      rw [preimage_sdiff, subLeft_preimage_ball, subLeft_preimage_ball] at heq
      rw [heq]
      have hb := hessianKernelExpression_annulus_norm_integral_bound hn i j hd
        (b := 3 * dist x y) (by linarith only [hd])
      rwa [mul_div_cancel_right₀ 3 hd.ne'] at hb

theorem potentialHessianExpression_common_split {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (x y : Domain n) (hxy : x ≠ y) :
    potentialHessianExpression i j g y =
      (((if i = j then 1 else 0) / (n : ℝ)) • g y +
        ∫ z in Metric.ball x (2 * dist x y),
          hessianKernelExpression i j (y - z) • (g z - g y)) +
      (∫ z in (Metric.ball x (2 * dist x y))ᶜ,
        hessianKernelExpression i j (y - z) • g z) +
      (∫ z in Metric.ball x (2 * dist x y) \ Metric.ball y (dist x y),
        hessianKernelExpression i j (y - z)) • g y := by
  let D := Metric.ball x (2 * dist x y)
  let B := Metric.ball y (dist x y)
  let K : Domain n → ℝ := fun z => hessianKernelExpression i j (y - z)
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hBD : B ⊆ D := ball_dist_subset_ball_twoDist x y
  have hnear := hessianKernelExpression_commonNear_integrableOn hn i j hη hH hHolder x y
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  have hfar := hessianKernelExpression_shiftedData_integrableOn_exterior i j hg hcg hd y
  have hKA := hessianKernelExpression_commonAnnulus_integrableOn i j x y hxy
  have hNA : (∫ z in D \ B, K z • (g z - g y)) =
      (∫ z in D, K z • (g z - g y)) - ∫ z in B, K z • (g z - g y) :=
    setIntegral_sdiff measurableSet_ball hnear hBD
  have hset : Bᶜ \ Dᶜ = D \ B := by ext z; simp only [Set.mem_sdiff, mem_compl_iff, not_not]; tauto
  have hFA : (∫ z in D \ B, K z • g z) =
      (∫ z in Bᶜ, K z • g z) - ∫ z in Dᶜ, K z • g z := by
    rw [← hset]
    exact setIntegral_sdiff measurableSet_ball.compl hfar (compl_subset_compl.mpr hBD)
  have hsplitA : (∫ z in D \ B, K z • (g z - g y)) =
      (∫ z in D \ B, K z • g z) - (∫ z in D \ B, K z) • g y := by
    simp_rw [smul_sub]
    rw [integral_sub (hfar.mono_set (fun _ hz => hz.2)) (hKA.smul_const (g y)), integral_smul_const]
  rw [potentialHessianExpression_shifted_splitRadius hn i j hη hH hHolder hcg hd y]
  dsimp only [D, B, K] at hNA hFA hsplitA
  rw [hFA] at hsplitA
  rw [hNA] at hsplitA
  apply sub_eq_zero.mp
  calc
    _ = -(((∫ z in Metric.ball x (2 * dist x y),
          hessianKernelExpression i j (y - z) • (g z - g y)) -
        (∫ z in Metric.ball y (dist x y),
          hessianKernelExpression i j (y - z) • (g z - g y))) -
        (((∫ z in (Metric.ball y (dist x y))ᶜ, hessianKernelExpression i j (y - z) • g z) -
          (∫ z in (Metric.ball x (2 * dist x y))ᶜ, hessianKernelExpression i j (y - z) • g z)) -
          (∫ z in Metric.ball x (2 * dist x y) \ Metric.ball y (dist x y),
            hessianKernelExpression i j (y - z)) • g y)) := by abel
    _ = 0 := by rw [hsplitA, sub_self, neg_zero]

theorem potentialHessianExpression_translation_decomposition {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (x y : Domain n) (hxy : x ≠ y) :
    potentialHessianExpression i j g x - potentialHessianExpression i j g y =
      (((if i = j then 1 else 0) / (n : ℝ)) • (g x - g y) +
        ((∫ z in Metric.ball x (2 * dist x y),
          hessianKernelExpression i j (x - z) • (g z - g x)) -
        ∫ z in Metric.ball x (2 * dist x y),
          hessianKernelExpression i j (y - z) • (g z - g y))) +
      (∫ z in (Metric.ball x (2 * dist x y))ᶜ,
        (hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z)) •
          (g z - g x)) +
      (∫ z in (Metric.ball x (2 * dist x y))ᶜ,
        hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z)) • g x -
      (∫ z in Metric.ball x (2 * dist x y) \ Metric.ball y (dist x y),
        hessianKernelExpression i j (y - z)) • g y := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  have hFx := hessianKernelExpression_shiftedData_integrableOn_exterior i j hg hcg
    (mul_pos zero_lt_two hd) x
  have hFy := (hessianKernelExpression_shiftedData_integrableOn_exterior i j hg hcg hd y).mono_set
    (compl_subset_compl.mpr (ball_dist_subset_ball_twoDist x y))
  have hJ := hessianKernelDifference_integrableOn hn i j x y hxy
  have hW : (∫ z in (Metric.ball x (2 * dist x y))ᶜ,
        (hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z)) •
          (g z - g x)) =
      ((∫ z in (Metric.ball x (2 * dist x y))ᶜ,
        hessianKernelExpression i j (x - z) • g z) -
      ∫ z in (Metric.ball x (2 * dist x y))ᶜ,
        hessianKernelExpression i j (y - z) • g z) -
      (∫ z in (Metric.ball x (2 * dist x y))ᶜ,
        hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z)) • g x := by
    have hCJ : Integrable (fun z => hessianKernelExpression i j (x - z) • g x -
        hessianKernelExpression i j (y - z) • g x)
        (volume.restrict (Metric.ball x (2 * dist x y))ᶜ) := by
      simpa only [sub_smul] using hJ.smul_const (g x)
    have hF : Integrable (fun z => hessianKernelExpression i j (x - z) • g z -
        hessianKernelExpression i j (y - z) • g z)
        (volume.restrict (Metric.ball x (2 * dist x y))ᶜ) := by
      simpa only [IntegrableOn, Pi.sub_def] using hFx.sub hFy
    simp_rw [smul_sub, sub_smul]
    rw [integral_sub hF hCJ, integral_sub hFx hFy]
    congr 1
    rw [← integral_smul_const]
    apply setIntegral_congr_fun measurableSet_ball.compl
    intro z _
    exact (sub_smul _ _ _).symm
  rw [potentialHessianExpression_shifted_splitRadius hn i j hη hH hHolder hcg
    (mul_pos zero_lt_two hd) x,
    potentialHessianExpression_common_split hn i j hη hH hHolder hcg x y hxy, hW]
  simp only [smul_sub]
  abel

end HolderToCK
end
