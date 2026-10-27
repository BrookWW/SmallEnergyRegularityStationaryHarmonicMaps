module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Radius-independent limits from comparable-scale mean estimates -/

public section

open Filter Set
open scoped Topology

namespace HarmonicMaps

private theorem dyadic_allRadius_limit {E : Type*} [MetricSpace E] [CompleteSpace E]
    (F : ℝ → E) {α K r : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hcompare : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ 1 / 2 → t ≤ 2 * s →
      dist (F s) (F t) ≤ K * t ^ α) :
    ∃ w : E, Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 w) ∧
      dist (F r) w ≤ K * r ^ α / (1 - (1 / 2 : ℝ) ^ α) := by
  let rate : ℝ := (1 / 2 : ℝ) ^ α
  let ρ : ℕ → ℝ := fun k => r * (1 / 2 : ℝ) ^ k
  let u : ℕ → E := fun k => F (ρ k)
  have hrate0 : 0 < rate := Real.rpow_pos_of_pos (by norm_num) α
  have hrate1 : rate < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hden : 0 < 1 - rate := sub_pos.mpr hrate1
  have hρ0 (k : ℕ) : 0 < ρ k := mul_pos hr (pow_pos (by norm_num) _)
  have hρhalf (k : ℕ) : ρ k ≤ 1 / 2 := by
    exact (mul_le_of_le_one_right hr.le (pow_le_one₀ (by norm_num) (by norm_num))).trans hrhalf
  have hρsucc (k : ℕ) : ρ (k + 1) = ρ k / 2 := by
    dsimp only [ρ]
    rw [pow_succ]
    ring
  have hρpow (k : ℕ) : (ρ k) ^ α = r ^ α * rate ^ k := by
    dsimp only [ρ, rate]
    rw [Real.mul_rpow hr.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [mul_comm (k : ℝ) α, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hstep (k : ℕ) : dist (u k) (u (k + 1)) ≤ (K * r ^ α) * rate ^ k := by
    rw [dist_comm]
    have h := hcompare (ρ (k + 1)) (ρ k) (hρ0 _) (by rw [hρsucc]; linarith only [hρ0 k])
      (hρhalf _) (by rw [hρsucc]; linarith)
    simpa only [u, hρpow, mul_assoc] using h
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric rate (K * r ^ α) hrate1 hstep)
  have htail (k : ℕ) : dist (F (ρ k)) w ≤ K * (ρ k) ^ α / (1 - rate) := by
    simpa only [u, hρpow, mul_assoc] using
      dist_le_of_le_geometric_of_tendsto rate (K * r ^ α) hrate1 hstep hw k
  have hnear (t : ℝ) (ht : 0 < t) (htr : t ≤ r) :
      ∃ k : ℕ, ρ (k + 1) < t ∧ t ≤ ρ k := by
    obtain ⟨k, hkl, hku⟩ := exists_nat_pow_near_of_lt_one
      (div_pos ht hr) ((div_le_one hr).mpr htr) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨k, ?_, ?_⟩
    · simpa only [ρ, mul_comm] using (lt_div_iff₀ hr).mp hkl
    · exact (div_le_iff₀ hr).mp hku |>.trans_eq (mul_comm _ _)
  have herror (t : ℝ) (ht : 0 < t) (htr : t ≤ r) :
      dist (F t) w ≤ (K + K / (1 - rate)) * (2 * t) ^ α := by
    obtain ⟨k, hkl, hku⟩ := hnear t ht htr
    have hrati : ρ k ≤ 2 * t := by
      rw [hρsucc] at hkl
      linarith only [hkl]
    have hcomp := hcompare t (ρ k) ht hku (hρhalf _) hrati
    have hp := Real.rpow_le_rpow (hρ0 k).le hrati hα.le
    calc
      _ ≤ dist (F t) (F (ρ k)) + dist (F (ρ k)) w := dist_triangle _ _ _
      _ ≤ K * (ρ k) ^ α + K * (ρ k) ^ α / (1 - rate) := add_le_add hcomp (htail k)
      _ = (K + K / (1 - rate)) * (ρ k) ^ α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  have herrlim : Tendsto (fun t : ℝ => (K + K / (1 - rate)) * (2 * t) ^ α)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc := (Real.continuous_rpow_const hα.le).tendsto (0 : ℝ)
    have hbase : Tendsto (fun t : ℝ => 2 * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [mul_zero, id_eq] using
        ((tendsto_const_nhds.mul (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0))).mono_left nhdsWithin_le_nhds :
          Tendsto (fun t : ℝ => 2 * t) (𝓝[>] (0 : ℝ)) (𝓝 (2 * 0)))
    have hz := hc.comp hbase
    simpa only [mul_zero, Real.zero_rpow hα.ne', mul_zero] using
      (tendsto_const_nhds.mul hz : Tendsto
        (fun t : ℝ => (K + K / (1 - rate)) * (2 * t) ^ α) _ _)
  have hall : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hb := (tendsto_order.mp herrlim).2 ε hε
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr, hb] with t ht htr hbound
    exact lt_of_le_of_lt (herror t ht htr.2.le) hbound
  refine ⟨w, hall, ?_⟩
  simpa only [ρ, pow_zero, mul_one, rate] using htail 0

/-- Comparable-scale control produces one all-radius limit and every-radius tail estimate. -/
theorem existsUnique_allRadius_limit_of_comparable {E : Type*} [MetricSpace E] [CompleteSpace E]
    (F : ℝ → E) {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hcompare : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ 1 / 2 → t ≤ 2 * s →
      dist (F s) (F t) ≤ K * t ^ α) :
    ∃! w : E, Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 w) ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
        dist (F r) w ≤ K * r ^ α / (1 - (1 / 2 : ℝ) ^ α) := by
  obtain ⟨w, hw, _⟩ := dyadic_allRadius_limit F hα hK (by norm_num : (0 : ℝ) < 1 / 2)
    (by rfl) hcompare
  refine ⟨w, ⟨hw, ?_⟩, ?_⟩
  · intro r hr hrhalf
    obtain ⟨v, hv, hbound⟩ := dyadic_allRadius_limit F hα hK hr hrhalf hcompare
    have hvw : v = w := tendsto_nhds_unique hv hw
    simpa only [hvw] using hbound
  · intro v hv
    exact tendsto_nhds_unique hv.1 hw

end HarmonicMaps
