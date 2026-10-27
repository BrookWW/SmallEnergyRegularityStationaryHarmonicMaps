module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds
public import HolderToCK.Foundation.BallVolume

/-!
# Stronger Morrey growth of actual continuous coefficients on a ball

Continuity bounds the complete HS density on the compact closed unit ball.
Small balls use their actual volume; large balls use the total unit-ball
energy. The resulting stronger bound is finite for each original field.
Its constant need not be uniform along a smooth approximation sequence.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

/-- Actual continuous columns have stronger all-center truncated energy growth on the unit ball. -/
theorem exists_strongerMorrey_growth_of_continuous {n q : ℕ} (hn : 1 ≤ n)
    (F : Domain n → Gradient n q)
    (hF : ∀ i, Continuous (fun x => F x i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Domain n) (r : ℝ), 0 < r →
      (∫ x in Metric.ball a r ∩ Metric.ball (0 : Domain n) 1, hsNormSq (F x)) ≤
        C * r ^ ((n : ℝ)-1) := by
  let G := fun x => hsNormSq (F x)
  have hG : Continuous G := by
    apply continuous_finsetSum
    intro i _
    exact (hF i).norm.pow 2
  let B := Metric.ball (0 : Domain n) 1
  let K := Metric.closedBall (0 : Domain n) 1
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : Domain n) 1).exists_bound_of_continuousOn
    hG.continuousOn
  let L : ℝ := max M 1
  let V : ℝ := volume.real B
  let C : ℝ := L*V+1
  have hL : 0 ≤ L := le_trans zero_le_one (le_max_right _ _)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hC : 0 < C := by dsimp only [C]; positivity
  have hI : IntegrableOn G B volume :=
    (hG.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Domain n) 1)).mono_set
      Metric.ball_subset_closedBall
  have hBound (x : Domain n) (hx : x ∈ B) : G x ≤ L := by
    exact (le_abs_self _).trans ((hM x (Metric.ball_subset_closedBall hx)).trans (le_max_left _ _))
  have hEnergy : (∫ x in B,G x) ≤ L*V := by
    calc
      _ ≤ ∫ _x in B,L := integral_mono_ae hI (integrableOn_const measure_ball_ne_top) (by
          filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
          exact hBound x hx)
      _ = _ := by rw [integral_const]; simp only [Measure.restrict_apply_univ,
          smul_eq_mul,measureReal_def,V,mul_comm]
  refine ⟨C,hC,?_⟩
  intro a r hr
  let S := Metric.ball a r ∩ B
  have hIS : IntegrableOn G S volume := hI.mono_set inter_subset_right
  have hVolume : (∫ x in S,G x) ≤ L*volume.real (Metric.ball a r) := by
    calc
      _ ≤ ∫ _x in S,L := integral_mono_ae hIS (integrableOn_const (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono inter_subset_left))) (by
          filter_upwards [ae_restrict_mem (measurableSet_ball.inter measurableSet_ball)] with x hx
          exact hBound x hx.2)
      _ = L*volume.real S := by rw [integral_const]; simp only [Measure.restrict_apply_univ,
          smul_eq_mul,measureReal_def,mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (measureReal_mono inter_subset_left measure_ball_ne_top) hL
  have hNatReal : r^((n : ℝ)-1)=r^(n-1) := by
    rw [← Real.rpow_natCast r (n-1),Nat.cast_sub hn]
    norm_num
  rw [hNatReal]
  by_cases hrOne : r ≤ 1
  · have hP : r^n ≤ r^(n-1) := by
      calc
        _ = r^(n-1)*r := by rw [← pow_succ]; congr 1; omega
        _ ≤ _ := mul_le_of_le_one_right (pow_nonneg hr.le _) hrOne
    have H : (∫ x in S,G x) ≤ L*V*r^(n-1) := by
      calc
        _ ≤ L*(r^n*V) := by simpa only [HolderToCK.ball_volume_real a hr,V,B] using hVolume
        _ ≤ L*(r^(n-1)*V) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hP hV) hL
        _ = _ := by ring
    exact H.trans (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (pow_nonneg hr.le _))
  · have hrOne' : 1 ≤ r := (not_le.mp hrOne).le
    have hP : 1 ≤ r^(n-1) := one_le_pow₀ hrOne'
    have H : (∫ x in S,G x) ≤ L*V := by
      apply le_trans _ hEnergy
      exact setIntegral_mono_set hI (Eventually.of_forall (fun x => hsNormSq_nonneg (F x)))
        (Eventually.of_forall (fun x hx => hx.2))
    exact H.trans ((by dsimp only [C]; linarith : L*V ≤ C).trans
      (le_mul_of_one_le_right hC.le hP))

end StationaryHarmonicMaps.Analysis

end
