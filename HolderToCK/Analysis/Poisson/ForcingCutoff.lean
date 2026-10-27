module

public import HolderToCK.Foundation.HolderContinuity
public import HarmonicMaps.Analysis.RadialCutoffProfile
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Group.Uniform

/-! # Compact Holder forcing on the unit ball

A fixed smooth cutoff equals one on the five-eighths ball and vanishes
outside the three-quarters ball. Multiplication localizes the original
forcing without prescribing any off-domain values for that forcing.
-/

public section

open HarmonicMaps Set
open scoped ContDiff Topology NNReal

namespace HolderToCK

@[expose] noncomputable def schauderCutoff {n : ℕ} (x : Domain n) : ℝ :=
  radialCutoffProfile ⟨5 / 8, by norm_num⟩ ⟨1 / 8, by norm_num⟩ ‖x‖

theorem schauderCutoff_mem_Icc {n : ℕ} (x : Domain n) :
    schauderCutoff x ∈ Icc (0 : ℝ) 1 := radialCutoffProfile_mem_Icc _ _ _

theorem schauderCutoff_eq_one {n : ℕ} {x : Domain n}
    (hx : x ∈ Metric.closedBall (0 : Domain n) (5 / 8)) : schauderCutoff x = 1 := by
  exact radialCutoffProfile_eq_one _ _ (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)

theorem schauderCutoff_eq_zero {n : ℕ} {x : Domain n}
    (hx : 3 / 4 ≤ ‖x‖) : schauderCutoff x = 0 :=
  radialCutoffProfile_eq_zero _ _ (by norm_num; exact hx)

theorem schauderCutoff_contDiff {n : ℕ} : ContDiff ℝ ∞ (schauderCutoff : Domain n → ℝ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : Domain n) (by norm_num : (0 : ℝ) < 5 / 8)] with y hy
    exact schauderCutoff_eq_one (Metric.ball_subset_closedBall hy)
  · exact (radialCutoffProfile_contDiff _ _).contDiffAt.comp x (contDiffAt_norm (𝕜 := ℝ) hx)

theorem schauderCutoff_tsupport_subset {n : ℕ} :
    tsupport (schauderCutoff : Domain n → ℝ) ⊆ Metric.closedBall (0 : Domain n) (3 / 4) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hnot
  apply hx
  apply schauderCutoff_eq_zero
  exact (not_le.mp (by simpa only [Metric.mem_closedBall, dist_zero_right] using hnot)).le

theorem schauderCutoff_hasCompactSupport {n : ℕ} :
    HasCompactSupport (schauderCutoff : Domain n → ℝ) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Domain n) (3 / 4))
    (subset_tsupport _ |>.trans schauderCutoff_tsupport_subset)

theorem schauderCutoff_lipschitz (n : ℕ) :
    ∃ B : ℝ≥0, LipschitzWith B (schauderCutoff : Domain n → ℝ) := by
  obtain ⟨C, hC, hbound⟩ := radialCutoffProfile_deriv_bound
  let B : ℝ≥0 := ⟨C / (1 / 8), div_nonneg hC (by norm_num)⟩
  have hprofile : LipschitzWith B
      (radialCutoffProfile ⟨5 / 8, by norm_num⟩ ⟨1 / 8, by norm_num⟩) := by
    apply lipschitzWith_of_nnnorm_deriv_le ((radialCutoffProfile_contDiff _ _).differentiable (by simp))
    intro r
    exact_mod_cast hbound ⟨5 / 8, by norm_num⟩ ⟨1 / 8, by norm_num⟩ r
  refine ⟨B, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (hprofile.dist_le_mul ‖x‖ ‖y‖).trans
    (mul_le_mul_of_nonneg_left (by
      simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using
        abs_norm_sub_norm_le x y) B.property)

@[expose] noncomputable def schauderForcing {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Domain n → E) (x : Domain n) : E := schauderCutoff x • f x

theorem schauderForcing_eq {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Domain n → E) {x : Domain n}
    (hx : x ∈ Metric.closedBall (0 : Domain n) (5 / 8)) :
    schauderForcing f x = f x := by
  rw [schauderForcing, schauderCutoff_eq_one hx, one_smul]

theorem schauderForcing_eq_zero {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Domain n → E) {x : Domain n} (hx : 3 / 4 ≤ ‖x‖) :
    schauderForcing f x = 0 := by
  rw [schauderForcing, schauderCutoff_eq_zero hx, zero_smul]

theorem schauderForcing_tsupport_subset {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Domain n → E) :
    tsupport (schauderForcing f) ⊆ Metric.closedBall (0 : Domain n) (3 / 4) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hnot
  apply hx
  exact schauderForcing_eq_zero f
    (not_le.mp (by simpa only [Metric.mem_closedBall, dist_zero_right] using hnot)).le

theorem schauderForcing_hasCompactSupport {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Domain n → E) : HasCompactSupport (schauderForcing f) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Domain n) (3 / 4))
    ((subset_tsupport _).trans (schauderForcing_tsupport_subset f))

theorem schauderForcing_norm_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Domain n → E} {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ x ∈ Metric.ball (0 : Domain n) 1, ‖f x‖ ≤ L) (x : Domain n) :
    ‖schauderForcing f x‖ ≤ L := by
  by_cases hx : x ∈ Metric.ball (0 : Domain n) 1
  · rw [schauderForcing, norm_smul,
      Real.norm_of_nonneg (schauderCutoff_mem_Icc x).1]
    exact (mul_le_mul_of_nonneg_left (hbound x hx) (schauderCutoff_mem_Icc x).1).trans
      (mul_le_of_le_one_left hL (schauderCutoff_mem_Icc x).2)
  · rw [schauderForcing_eq_zero f (by
      have hnorm : 1 ≤ ‖x‖ := by
        simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hx
      linarith only [hnorm]), norm_zero]
    exact hL

private theorem small_dist_cutoff_eq_zero {n : ℕ} (x y : Domain n)
    (hx : x ∉ Metric.ball (0 : Domain n) 1) (hxy : dist x y < 1 / 4) :
    schauderCutoff x = 0 ∧ schauderCutoff y = 0 := by
  have hnx : 1 ≤ ‖x‖ := by
    simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hx
  have hny : 3 / 4 ≤ ‖y‖ := by
    have ht : ‖x‖ ≤ dist x y + ‖y‖ := by
      simpa only [dist_zero_right] using dist_triangle x y (0 : Domain n)
    linarith only [hnx, ht, hxy]
  exact ⟨schauderCutoff_eq_zero (by linarith only [hnx]), schauderCutoff_eq_zero hny⟩

theorem schauderForcing_holderBound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Domain n → E} {γ H L : ℝ} {B : ℝ≥0}
    (hγ : 0 < γ) (hγOne : γ ≤ 1) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hbound : ∀ x ∈ Metric.ball (0 : Domain n) 1, ‖f x‖ ≤ L)
    (hHolder : HolderBoundOn (Metric.ball (0 : Domain n) 1) f γ H)
    (hCutoff : LipschitzWith B (schauderCutoff : Domain n → ℝ)) :
    HolderBoundOn univ (schauderForcing f) γ (H + ((B : ℝ) + 8) * L) := by
  intro x _ y _
  have hp : 0 ≤ (dist x y) ^ γ := Real.rpow_nonneg dist_nonneg γ
  have hC : 0 ≤ H + ((B : ℝ) + 8) * L := by positivity
  by_cases hnear : dist x y < 1 / 4
  · by_cases hx : x ∈ Metric.ball (0 : Domain n) 1
    · by_cases hy : y ∈ Metric.ball (0 : Domain n) 1
      · have hd : dist x y ≤ (dist x y) ^ γ :=
          Real.self_le_rpow_of_le_one dist_nonneg (by linarith only [hnear]) hγOne
        have hsplit : schauderForcing f x - schauderForcing f y =
            schauderCutoff x • (f x - f y) +
              (schauderCutoff x - schauderCutoff y) • f y := by
          simp only [schauderForcing, smul_sub, sub_smul]
          abel
        rw [hsplit]
        calc
          _ ≤ ‖schauderCutoff x • (f x - f y)‖ +
              ‖(schauderCutoff x - schauderCutoff y) • f y‖ := norm_add_le _ _
          _ ≤ H * (dist x y) ^ γ + (B : ℝ) * dist x y * L := by
            apply add_le_add
            · rw [norm_smul, Real.norm_of_nonneg (schauderCutoff_mem_Icc x).1]
              exact (mul_le_mul_of_nonneg_left (hHolder x hx y hy)
                (schauderCutoff_mem_Icc x).1).trans
                (mul_le_of_le_one_left (mul_nonneg hH hp) (schauderCutoff_mem_Icc x).2)
            · rw [norm_smul]
              exact mul_le_mul (by simpa only [dist_eq_norm] using hCutoff.dist_le_mul x y)
                (hbound y hy) (norm_nonneg _) (by positivity)
          _ ≤ (H + ((B : ℝ) + 8) * L) * (dist x y) ^ γ := by
            have hBd := mul_le_mul_of_nonneg_left hd B.property
            have hBLd := mul_le_mul_of_nonneg_right hBd hL
            calc
              _ ≤ H * (dist x y) ^ γ + (B : ℝ) * (dist x y) ^ γ * L :=
                add_le_add_right hBLd _
              _ ≤ (H + ((B : ℝ) + 8) * L) * (dist x y) ^ γ := by
                have hnonneg : 0 ≤ 8 * L * (dist x y) ^ γ := by positivity
                nlinarith only [hnonneg]
      · obtain ⟨hy0, hx0⟩ := small_dist_cutoff_eq_zero y x hy (by rwa [dist_comm])
        simp only [schauderForcing, hx0, hy0, zero_smul, sub_self, norm_zero]
        exact mul_nonneg hC hp
    · obtain ⟨hx0, hy0⟩ := small_dist_cutoff_eq_zero x y hx hnear
      simp only [schauderForcing, hx0, hy0, zero_smul, sub_self, norm_zero]
      exact mul_nonneg hC hp
  · have hd : 1 / 4 ≤ dist x y := le_of_not_gt hnear
    have hpLower : 1 / 4 ≤ (dist x y) ^ γ := by
      calc
        (1 / 4 : ℝ) ≤ (1 / 4 : ℝ) ^ γ :=
          Real.self_le_rpow_of_le_one (by norm_num) (by norm_num) hγOne
        _ ≤ _ := Real.rpow_le_rpow (by norm_num) hd hγ.le
    calc
      _ ≤ ‖schauderForcing f x‖ + ‖schauderForcing f y‖ := norm_sub_le _ _
      _ ≤ L + L := add_le_add (schauderForcing_norm_bound hL hbound x)
        (schauderForcing_norm_bound hL hbound y)
      _ ≤ (H + ((B : ℝ) + 8) * L) * (dist x y) ^ γ := by
        have hterm : 0 ≤ (H + (B : ℝ) * L) * (dist x y) ^ γ := by positivity
        have hlarge := mul_le_mul_of_nonneg_left hpLower hL
        nlinarith only [hterm, hlarge]

theorem schauderForcing_continuous {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Domain n → E} {γ H L : ℝ}
    (hγ : 0 < γ) (hγOne : γ ≤ 1) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hbound : ∀ x ∈ Metric.ball (0 : Domain n) 1, ‖f x‖ ≤ L)
    (hHolder : HolderBoundOn (Metric.ball (0 : Domain n) 1) f γ H) :
    Continuous (schauderForcing f) := by
  obtain ⟨B, hB⟩ := schauderCutoff_lipschitz n
  exact continuousOn_univ.mp
    ((schauderForcing_holderBound hγ hγOne hH hL hbound hHolder hB).continuousOn hγ)

end HolderToCK
end
