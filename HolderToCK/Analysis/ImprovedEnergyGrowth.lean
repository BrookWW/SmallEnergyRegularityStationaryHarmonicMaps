module

public import HolderToCK.Analysis.ImprovedGrowthParameters
public import HolderToCK.Analysis.ScalarRadiusIteration

/-! # Improved energy growth from the actual weak quadratic equation

The harmonic comparison producer is applied to the original map and displayed
weak gradient. One positive Holder threshold supplies a homogeneous contraction
at the fixed reference radius. Scalar iteration and energy monotonicity give
the estimate at every positive inner radius, including zero total energy.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace HolderToCK

theorem uniform_improved_energy_growth (n : ℕ) (hn : 2 ≤ n)
    (α K : ℝ) (hα : 0 < α) (hαOne : α < 1) (hK : 0 ≤ K) :
    ∃ H₀ C_E : ℝ, 0 < H₀ ∧ H₀ ≤ 1 ∧ 0 < C_E ∧
      ∀ (q : ℕ) (u F : Domain n → Ambient q) (Du : Domain n → Gradient n q) (H : ℝ),
        MemW12 (ballDomain (0 : Domain n) (3 / 4 : ℝ)) u Du →
        WeakPoissonOn (ballDomain (0 : Domain n) (3 / 4 : ℝ)) Du F →
        0 ≤ H → H ≤ H₀ →
        HolderBoundOn (Metric.ball (0 : Domain n) (3 / 4 : ℝ)) u α H →
        (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) (3 / 4 : ℝ)),
          ‖F x‖ ≤ K * hsNormSq (Du x)) →
        ∀ a ∈ Metric.ball (0 : Domain n) (5 / 8 : ℝ),
          ∀ r : ℝ, 0 < r → r ≤ growthReferenceRadius →
            (∫ x in Metric.ball a r, hsNormSq (Du x)) ≤
              C_E * (∫ x in Metric.ball (0 : Domain n) (3 / 4 : ℝ), hsNormSq (Du x)) *
                Real.rpow r (improvedEnergyExponent n α) := by
  obtain ⟨c, hc, hcompare⟩ := quadratic_energy_excess_comparison n hn
  obtain ⟨θ, H₀, hθ, hθquarter, hH₀, hH₀One, _, _, hell, hcoefficient⟩ :=
    exists_improved_growth_parameters n hn hα hαOne hK hc
  let C_E : ℝ := Real.rpow θ (-improvedEnergyExponent n α) *
    Real.rpow growthReferenceRadius (-improvedEnergyExponent n α)
  have hr₀ : 0 < growthReferenceRadius := by norm_num [growthReferenceRadius]
  have hC_E : 0 < C_E := mul_pos (Real.rpow_pos_of_pos hθ _) (Real.rpow_pos_of_pos hr₀ _)
  have hθOne : θ < 1 := hθquarter.trans_lt (by norm_num)
  have hθhalf : θ ≤ 1 / 2 := hθquarter.trans (by norm_num)
  refine ⟨H₀, C_E, hH₀, hH₀One, hC_E, ?_⟩
  intro q u F Du H hu hEq hH hHH hHolder hBound a ha
  let E : ℝ := ∫ x in Metric.ball (0 : Domain n) (3 / 4 : ℝ), hsNormSq (Du x)
  let f : ℝ → ℝ := fun r => ∫ x in Metric.ball a r, hsNormSq (Du x)
  have hE : 0 ≤ E := integral_nonneg (fun _ => hsNormSq_nonneg _)
  have hmono : ∀ r s : ℝ, 0 < r → r ≤ s → s ≤ growthReferenceRadius → f r ≤ f s := by
    intro r s _ hrs hsr₀
    have hsub : Metric.ball a s ⊆ (ballDomain (0 : Domain n) (3 / 4 : ℝ)).val :=
      Metric.ball_subset_closedBall.trans (small_center_closedBall_subset_threeQuarter ha hsr₀)
    exact setIntegral_mono_set (hu.integrable_hsNormSq.mono_set hsub)
      (Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Eventually.of_forall fun _ hx => Metric.ball_subset_ball hrs hx)
  have hbase : f growthReferenceRadius ≤ E := by
    exact setIntegral_mono_set hu.integrable_hsNormSq
      (Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Eventually.of_forall fun _ hx => Metric.ball_subset_closedBall.trans
        (small_center_closedBall_subset_threeQuarter ha le_rfl) hx)
  have hstep : ∀ r : ℝ, 0 < r → r ≤ growthReferenceRadius →
      f (θ * r) ≤ θ ^ (improvedEnergyExponent n α) * f r := by
    intro r hr hrr₀
    have hclosed := small_center_closedBall_subset_threeQuarter ha hrr₀
    have hcmp := (hcompare q (ballDomain (0 : Domain n) (3 / 4 : ℝ)) u F Du
      hu.to_memW12Loc hEq α H K hα hH hK hHolder hBound a ⟨r, hr⟩ hclosed θ hθ hθhalf).1
    have hcoef := hcoefficient H hH hHH r hr hrr₀
    have hf : 0 ≤ f r := integral_nonneg (fun _ => hsNormSq_nonneg _)
    have hpower : 0 ≤ Real.rpow θ (improvedEnergyExponent n α) := Real.rpow_nonneg hθ.le _
    calc
      _ ≤ (c * θ ^ n + c * K * H * Real.rpow r α) * f r := hcmp
      _ ≤ ((1 / 2 : ℝ) * Real.rpow θ (improvedEnergyExponent n α)) * f r :=
        mul_le_mul_of_nonneg_right hcoef hf
      _ ≤ Real.rpow θ (improvedEnergyExponent n α) * f r :=
        mul_le_mul_of_nonneg_right (by linarith only [hpower]) hf
      _ = _ := by rw [Real.rpow_eq_pow]
  have hgrowth := all_radius_decay_of_homogeneous_recurrence f hθ hθOne hr₀ hell.le hE
    hmono hbase hstep
  intro r hr hrr₀
  simpa only [C_E, E, f, Real.rpow_eq_pow, mul_assoc] using hgrowth r hr hrr₀

end HolderToCK
end
