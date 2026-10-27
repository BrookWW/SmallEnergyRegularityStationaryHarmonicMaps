module

public import HolderToCK.Analysis.ImprovedEnergyGrowth

/-! # Uniform excess decay of the original weak gradient

The actual quadratic comparison and the improved energy bound give an
inhomogeneous contraction with a strictly higher forcing exponent. The column
mean minimizes squared Hilbert--Schmidt distance, so excess is monotone on
nested balls. Scalar iteration gives the full radius range under the same
positive Holder threshold used for energy growth.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology

namespace HolderToCK

theorem gradient_variance_mono_ball {n q : ℕ} (a : Domain n) {r s : ℝ}
    (hrs : r ≤ s) {D : Domain n → Gradient n q}
    (hD : ∀ i, MemLp (fun x => D x i) 2 (volume.restrict (Metric.ball a s))) :
    (∫ x in Metric.ball a r, hsNormSq (fun i => D x i - ⨍ y in Metric.ball a r, D y i)) ≤
      ∫ x in Metric.ball a s, hsNormSq (fun i => D x i - ⨍ y in Metric.ball a s, D y i) := by
  let μ := volume.restrict (Metric.ball a s)
  let ν := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let B : Gradient n q := fun i => ⨍ y in Metric.ball a s, D y i
  have hsub : Metric.ball a r ⊆ Metric.ball a s := Metric.ball_subset_ball hrs
  have hDr (i : Fin n) := (hD i).mono_measure (Measure.restrict_mono_set volume hsub)
  have hminimal := gradient_variance_minimal ν hDr B
  have hcenter : IntegrableOn (fun x => hsNormSq (fun i => D x i - B i))
      (Metric.ball a s) volume :=
    integrable_hsNormSq_of_memLp_columns (fun i => (hD i).sub (memLp_const (B i)))
  exact hminimal.trans (setIntegral_mono_set hcenter
    (Eventually.of_forall fun _ => hsNormSq_nonneg _)
    (Eventually.of_forall fun _ hx => hsub hx))

theorem uniform_energy_growth_and_gradient_excess_decay (n : ℕ) (hn : 2 ≤ n)
    (α K : ℝ) (hα : 0 < α) (hαOne : α < 1) (hK : 0 ≤ K) :
    ∃ H₀ C_E C_Φ : ℝ, 0 < H₀ ∧ H₀ ≤ 1 ∧ 0 < C_E ∧ 0 < C_Φ ∧
      ∀ (q : ℕ) (u F : Domain n → Ambient q) (Du : Domain n → Gradient n q) (H : ℝ),
        MemW12 (ballDomain (0 : Domain n) (3 / 4 : ℝ)) u Du →
        WeakPoissonOn (ballDomain (0 : Domain n) (3 / 4 : ℝ)) Du F →
        0 ≤ H → H ≤ H₀ →
        HolderBoundOn (Metric.ball (0 : Domain n) (3 / 4 : ℝ)) u α H →
        (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) (3 / 4 : ℝ)),
          ‖F x‖ ≤ K * hsNormSq (Du x)) →
        ∀ a ∈ Metric.ball (0 : Domain n) (5 / 8 : ℝ),
          ∀ r : ℝ, 0 < r → r ≤ growthReferenceRadius →
            ((∫ x in Metric.ball a r, hsNormSq (Du x)) ≤
              C_E * (∫ x in Metric.ball (0 : Domain n) (3 / 4 : ℝ), hsNormSq (Du x)) *
                Real.rpow r (improvedEnergyExponent n α)) ∧
            ((∫ x in Metric.ball a r, hsNormSq (fun i => Du x i - ⨍ y in Metric.ball a r, Du y i)) ≤
              C_Φ * (∫ x in Metric.ball (0 : Domain n) (3 / 4 : ℝ), hsNormSq (Du x)) *
                Real.rpow r (gradientExcessExponent n α)) := by
  obtain ⟨H₀, C_E, hH₀, hH₀One, hC_E, hGrowth⟩ := uniform_improved_energy_growth n hn α K hα hαOne hK
  obtain ⟨c, hc, hCompare⟩ := quadratic_energy_excess_comparison n hn
  let ν := gradientExcessExponent n α
  let μ : ℝ := (n : ℝ) + α / 2
  let δ : ℝ := 2 - α / 4
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [hαOne]
  have hν : 0 < ν := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp only [ν, gradientExcessExponent]
    linarith only [hnR, hα]
  have hμν : ν < μ := by
    dsimp only [ν, μ, gradientExcessExponent]
    linarith only [hα]
  obtain ⟨θ, hθ, hθquarter, hθpower⟩ := exists_small_rpow_coefficient c hδ
  have hθOne : θ < 1 := hθquarter.trans_lt (by norm_num)
  have hθhalf : θ ≤ 1 / 2 := hθquarter.trans (by norm_num)
  have hfactor : θ ^ (n + 2) = Real.rpow θ δ * Real.rpow θ ν := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hθ]
    have hexp : δ + ν = ((n + 2 : ℕ) : ℝ) := by
      dsimp only [δ, ν, gradientExcessExponent]
      push_cast
      ring
    rw [hexp, Real.rpow_natCast]
  have hθcoefficient : c * θ ^ (n + 2) ≤ (1 / 2 : ℝ) * θ ^ ν := by
    have hpow : 0 ≤ Real.rpow θ ν := Real.rpow_nonneg hθ.le _
    calc
      _ = (c * Real.rpow θ δ) * Real.rpow θ ν := by rw [hfactor]; ring
      _ ≤ (1 / 4 : ℝ) * Real.rpow θ ν := mul_le_mul_of_nonneg_right hθpower hpow
      _ ≤ (1 / 2 : ℝ) * Real.rpow θ ν := mul_le_mul_of_nonneg_right (by norm_num) hpow
      _ = _ := by rw [Real.rpow_eq_pow]
  let A := c * K * C_E
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (lt_of_lt_of_le zero_lt_one hc).le hK) hC_E.le
  have hr₀ : 0 < growthReferenceRadius := by norm_num [growthReferenceRadius]
  let C_Φ : ℝ := θ ^ (-ν) *
    (growthReferenceRadius ^ (-ν) + 2 * A * θ ^ (-ν) * growthReferenceRadius ^ (μ - ν))
  have hC_Φ : 0 < C_Φ := by
    have hterm : 0 ≤ 2 * A * θ ^ (-ν) * growthReferenceRadius ^ (μ - ν) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) (Real.rpow_nonneg hθ.le _))
        (Real.rpow_nonneg hr₀.le _)
    exact mul_pos (Real.rpow_pos_of_pos hθ _)
      (add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hr₀ _) hterm)
  refine ⟨H₀, C_E, C_Φ, hH₀, hH₀One, hC_E, hC_Φ, ?_⟩
  intro q u F Du H hu hEq hH hHH hHolder hBound a ha
  let E : ℝ := ∫ x in Metric.ball (0 : Domain n) (3 / 4 : ℝ), hsNormSq (Du x)
  let Φ : ℝ → ℝ := fun r => ∫ x in Metric.ball a r,
    hsNormSq (fun i => Du x i - ⨍ y in Metric.ball a r, Du y i)
  have hE : 0 ≤ E := integral_nonneg (fun _ => hsNormSq_nonneg _)
  have hHOne : H ≤ 1 := hHH.trans hH₀One
  have hcolumns (s : ℝ) (hs : s ≤ growthReferenceRadius) (i : Fin n) :
      MemLp (fun x => Du x i) 2 (volume.restrict (Metric.ball a s)) :=
    (hu.2.2 i).mono_measure (Measure.restrict_mono_set volume
      (Metric.ball_subset_closedBall.trans (small_center_closedBall_subset_threeQuarter ha hs)))
  have hmono : ∀ r s : ℝ, 0 < r → r ≤ s → s ≤ growthReferenceRadius → Φ r ≤ Φ s :=
    fun r s _ hrs hs => gradient_variance_mono_ball a hrs (hcolumns s hs)
  have hbase : Φ growthReferenceRadius ≤ E := by
    letI : IsFiniteMeasure (volume.restrict (Metric.ball a growthReferenceRadius)) :=
      isFiniteMeasure_restrict.mpr measure_ball_ne_top
    have hminimal := gradient_variance_minimal (volume.restrict (Metric.ball a growthReferenceRadius))
      (hcolumns growthReferenceRadius le_rfl) (0 : Gradient n q)
    have henergy : (∫ x in Metric.ball a growthReferenceRadius, hsNormSq (Du x)) ≤ E :=
      setIntegral_mono_set hu.integrable_hsNormSq
        (Eventually.of_forall fun _ => hsNormSq_nonneg _)
        (Eventually.of_forall fun _ hx => Metric.ball_subset_closedBall.trans
          (small_center_closedBall_subset_threeQuarter ha le_rfl) hx)
    have hPhiEnergy : Φ growthReferenceRadius ≤
        ∫ x in Metric.ball a growthReferenceRadius, hsNormSq (Du x) := by
      simpa only [Pi.zero_apply, sub_zero] using hminimal
    exact hPhiEnergy.trans henergy
  have hstep : ∀ r : ℝ, 0 < r → r ≤ growthReferenceRadius →
      Φ (θ * r) ≤ (1 / 2 : ℝ) * θ ^ ν * Φ r + A * E * r ^ μ := by
    intro r hr hrr₀
    have hclosed := small_center_closedBall_subset_threeQuarter ha hrr₀
    have hcmp := (hCompare q (ballDomain (0 : Domain n) (3 / 4 : ℝ)) u F Du hu.to_memW12Loc
      hEq α H K hα hH hK hHolder hBound a ⟨r, hr⟩ hclosed θ hθ hθhalf).2
    have hgrowth := hGrowth q u F Du H hu hEq hH hHH hHolder hBound a ha r hr hrr₀
    have hsplit : Real.rpow r α * Real.rpow r (improvedEnergyExponent n α) = r ^ μ := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hr]
      congr 1
      dsimp only [improvedEnergyExponent, μ]
      ring
    have hforce : c * K * H * Real.rpow r α *
        (∫ x in Metric.ball a r, hsNormSq (Du x)) ≤ A * E * r ^ μ := by
      calc
        _ ≤ (c * K * H * Real.rpow r α) *
            (C_E * E * Real.rpow r (improvedEnergyExponent n α)) :=
          mul_le_mul_of_nonneg_left hgrowth
            (mul_nonneg (mul_nonneg (mul_nonneg (lt_of_lt_of_le zero_lt_one hc).le hK) hH)
              (Real.rpow_nonneg hr.le _))
        _ = (A * E * r ^ μ) * H := by dsimp only [A]; rw [← hsplit]; ring
        _ ≤ A * E * r ^ μ := mul_le_of_le_one_right
          (mul_nonneg (mul_nonneg hA hE) (Real.rpow_nonneg hr.le _)) hHOne
    have hΦ : 0 ≤ Φ r := integral_nonneg (fun _ => hsNormSq_nonneg _)
    exact hcmp.trans (add_le_add (mul_le_mul_of_nonneg_right hθcoefficient hΦ) hforce)
  have hexcess := all_radius_decay_of_inhomogeneous_recurrence Φ hθ hθOne hr₀ hν.le hμν hA hE
    hmono hbase hstep
  intro r hr hrr₀
  refine ⟨hGrowth q u F Du H hu hEq hH hHH hHolder hBound a ha r hr hrr₀, ?_⟩
  simpa only [Φ, E, C_Φ, ν, Real.rpow_eq_pow, mul_assoc] using hexcess r hr hrr₀

end HolderToCK
end
