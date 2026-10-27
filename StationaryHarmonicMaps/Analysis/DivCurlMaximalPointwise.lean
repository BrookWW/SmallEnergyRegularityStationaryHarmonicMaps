module

public import StationaryHarmonicMaps.Analysis.DivCurlScaleNormalization
public import StationaryHarmonicMaps.Analysis.DyadicBallMaximal

/-!
# Actual dyadic maximal control of rough div--curl kernels

The original local L2 data and native weak graph produce every ball
estimate. Their actual nonnegative averages lift to extended averages,
and the proved dyadic comparison gives pointwise maximal control. No
maximal value is converted to a real number; infinite values are allowed.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal NNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original rough divergence equation and native graph yield actual whole-space kernel pairings controlled by the two literal maximal fields. -/
theorem exists_divcurl_dyadic_maximal_kernel_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ p : ℝ≥0, (p : ℝ)=2*(n : ℝ)/((n : ℝ)+1) ∧ 1 < p ∧ p < 2 ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (Z : Domain n → Gradient n q),
        (∀ i,LocallyMemL2 (⟨univ,isOpen_univ⟩ : OpenDomain n) (fun x => Z x i)) →
        HolderToCK.WeakPoissonOn (⟨univ,isOpen_univ⟩ : OpenDomain n) Z (fun _ => (0 : Ambient q)) →
        ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
          MemW12Loc (⟨univ,isOpen_univ⟩ : OpenDomain n) w Dw →
          ∀ (a : Domain n) (r : ℝ),0<r → ∀ (κ : Domain n → ℝ),
            ContDiff ℝ ∞ κ → HasCompactSupport κ → tsupport κ ⊆ Metric.ball a r →
            (∀ x ∈ Metric.ball a r,∀ i : Fin n,
              |fderiv ℝ κ x (EuclideanSpace.single i 1)| ≤ r^(-(n : ℝ)-1)) →
            Integrable (fun x => κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i)) volume ∧
            ENNReal.ofReal |∫ x,κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i)| ≤
              ENNReal.ofReal C *
                (dyadicBallMaximal (fun x => ENNReal.ofReal ((Real.sqrt (hsNormSq (Z x)))^(p : ℝ))) a)^(1/(p : ℝ)) *
                (dyadicBallMaximal (fun x => ENNReal.ofReal ((Real.sqrt (hsNormSq (Dw x)))^(p : ℝ))) a)^(1/(p : ℝ)) := by
  obtain ⟨p,hpFormula,hp1,hp2,K,hK,Hkernel⟩ := exists_divcurl_scaled_average_kernel_bound n hn
  let α : ℝ := 1/(p : ℝ)
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (lt_trans zero_lt_one hp1)
  have hα : 0 ≤ α := one_div_nonneg.mpr hpR.le
  let A : ℝ := ((2 : ℝ)^n)^α
  let C : ℝ := K*A*A
  have hA : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨p,hpFormula,hp1,hp2,C,mul_pos (mul_pos hK hA) hA,?_⟩
  intro q Z hZ hdiv w Dw hw a r hr κ hκ hcκ hsκ hDκ
  have hZbig (i : Fin n) : MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball a (2*r))) :=
    (hZ i (Metric.closedBall a (2*r)) (isCompact_closedBall _ _) (subset_univ _)).mono_measure
      (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
  have hwBig : MemW12 (ballDomain a (2*r)) w Dw := by
    refine ⟨hw.1.mono (subset_univ _),?_,?_⟩
    · exact (hw.2.1 (Metric.closedBall a (2*r)) (isCompact_closedBall _ _) (subset_univ _)).mono_measure
        (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
    · intro i
      exact (hw.2.2 i (Metric.closedBall a (2*r)) (isCompact_closedBall _ _) (subset_univ _)).mono_measure
        (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
  obtain ⟨hI,hBound⟩ := Hkernel q a r hr Z hZbig (hdiv.mono (subset_univ _)) w Dw hwBig κ hκ hcκ hsκ
    1 zero_le_one (by simpa only [one_mul] using hDκ)
  have hZero (x : Domain n) (hx : x ∉ Metric.ball a r) :
      κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i)=0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsκ h)),zero_mul]
  have hSupp : Function.support (fun x => κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i)) ⊆ Metric.ball a r := by
    intro x hx
    by_contra hnot
    exact hx (hZero x hnot)
  have hWhole : Integrable (fun x => κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i)) volume :=
    (integrableOn_iff_integrable_of_support_subset hSupp).mp hI
  have hWholeEq : (∫ x in Metric.ball a r,κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i))=
      ∫ x,κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hZero
  rw [hWholeEq,mul_one] at hBound
  let f : Domain n → ℝ := fun x => (Real.sqrt (hsNormSq (Z x)))^(p : ℝ)
  let g : Domain n → ℝ := fun x => (Real.sqrt (hsNormSq (Dw x)))^(p : ℝ)
  have hf0 (x : Domain n) : 0 ≤ f x := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hg0 (x : Domain n) : 0 ≤ g x := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hp₂R : (p : ℝ) ≤ 2 := by exact_mod_cast hp2.le
  have hZr (i : Fin n) : MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball a r)) :=
    (hZbig i).mono_measure (Measure.restrict_mono_set volume (Metric.ball_subset_ball (by linarith)))
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a r)) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (ballDomain a (2*r)).val) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a (2*r))) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hfI : IntegrableOn f (Metric.ball a r) volume :=
    integrable_sqrt_sum_norm_sq_rpow Z hpR.le hp₂R hZr
  have hgI : IntegrableOn g (Metric.ball a (2*r)) volume :=
    integrable_sqrt_sum_norm_sq_rpow Dw hpR.le hp₂R hwBig.2.2
  have hfAvg0 : 0 ≤ ⨍ x in Metric.ball a r,f x := by
    rw [setAverage_eq,smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg hf0)
  have hgAvg0 : 0 ≤ ⨍ x in Metric.ball a (2*r),g x := by
    rw [setAverage_eq,smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg hg0)
  have hfAvg : ENNReal.ofReal (⨍ x in Metric.ball a r,f x)=
      centeredBallAverageENN (fun x => ENNReal.ofReal (f x)) a ⟨r,hr⟩ := by
    rw [ofReal_setAverage hfI (Eventually.of_forall hf0),centeredBallAverageENN,ENNReal.div_eq_inv_mul]
  have hgAvg : ENNReal.ofReal (⨍ x in Metric.ball a (2*r),g x)=
      centeredBallAverageENN (fun x => ENNReal.ofReal (g x)) a ⟨2*r,by positivity⟩ := by
    rw [ofReal_setAverage hgI (Eventually.of_forall hg0),centeredBallAverageENN,ENNReal.div_eq_inv_mul]
  have hfMax := ENNReal.rpow_le_rpow
    (centeredBallAverageENN_le_dyadicBallMaximal (fun x => ENNReal.ofReal (f x)) a ⟨r,hr⟩) hα
  have hgMax := ENNReal.rpow_le_rpow
    (centeredBallAverageENN_le_dyadicBallMaximal (fun x => ENNReal.ofReal (g x)) a ⟨2*r,by positivity⟩) hα
  rw [ENNReal.mul_rpow_of_nonneg _ _ hα] at hfMax hgMax
  have hLift := ENNReal.ofReal_le_ofReal hBound
  have hLiftEq : ENNReal.ofReal (K*(⨍ x in Metric.ball a r,f x)^α*(⨍ x in Metric.ball a (2*r),g x)^α)=
      ENNReal.ofReal K*(ENNReal.ofReal (⨍ x in Metric.ball a r,f x))^α*
        (ENNReal.ofReal (⨍ x in Metric.ball a (2*r),g x))^α := by
    rw [ENNReal.ofReal_mul (mul_nonneg hK.le (Real.rpow_nonneg hfAvg0 _)),
      ENNReal.ofReal_mul hK.le,← ENNReal.ofReal_rpow_of_nonneg hfAvg0 hα,
      ← ENNReal.ofReal_rpow_of_nonneg hgAvg0 hα]
  change ENNReal.ofReal |∫ x,κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i)| ≤
    ENNReal.ofReal (K*(⨍ x in Metric.ball a r,f x)^α*(⨍ x in Metric.ball a (2*r),g x)^α) at hLift
  rw [hLiftEq,hfAvg,hgAvg] at hLift
  have hCoefficient : ENNReal.ofReal K*(ENNReal.ofReal ((2 : ℝ)^n))^α*
      (ENNReal.ofReal ((2 : ℝ)^n))^α=ENNReal.ofReal C := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ (2 : ℝ)^n) hα,
      ← ENNReal.ofReal_mul hK.le,← ENNReal.ofReal_mul (mul_nonneg hK.le (Real.rpow_nonneg (by positivity) _))]
  refine ⟨hWhole,hLift.trans ?_⟩
  calc
    _ ≤ ENNReal.ofReal K*((ENNReal.ofReal ((2 : ℝ)^n))^α*
        (dyadicBallMaximal (fun x => ENNReal.ofReal (f x)) a)^α)*
        ((ENNReal.ofReal ((2 : ℝ)^n))^α*(dyadicBallMaximal (fun x => ENNReal.ofReal (g x)) a)^α) :=
      mul_le_mul (mul_le_mul_right hfMax _) hgMax zero_le zero_le
    _ = ENNReal.ofReal C*(dyadicBallMaximal (fun x => ENNReal.ofReal (f x)) a)^α*
        (dyadicBallMaximal (fun x => ENNReal.ofReal (g x)) a)^α := by
      rw [← hCoefficient]
      ac_rfl

end StationaryHarmonicMaps.Analysis

end
