module

public import StationaryHarmonicMaps.Analysis.L2ClosedRange
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Strong L² continuity of bounded multipliers

A uniformly bounded actual L² sequence passes its bound to its original
strong limit. A fixed L² weight then multiplies its difference in strong L².
The full sequence need not converge pointwise: every subsequence has an
almost-everywhere convergent further subsequence, to which genuine dominated
convergence applies. The subsequence criterion recovers the full conclusion.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem tendsto_eLpNorm_two_of_integral_norm_sq {X E : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}
    (f : ℕ → X → E) (hf : ∀ k, MemLp (f k) 2 μ)
    (hI : Tendsto (fun k => ∫ x, ‖f k x‖ ^ 2 ∂μ) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k => eLpNorm (f k) 2 μ) atTop (𝓝 0) := by
  have hnorm (k : ℕ) : eLpNorm (f k) 2 μ =
      ENNReal.ofReal (Real.sqrt (∫ x, ‖f k x‖ ^ 2 ∂μ)) := by
    rw [← ofReal_lpNorm (hf k), lpNorm_eq_integral_norm_rpow_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp) (hf k).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [← one_div, ← Real.sqrt_eq_rpow]
  have H := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp hI)
  simpa only [Function.comp_def, hnorm, Real.sqrt_zero, ENNReal.ofReal_zero] using H

/-- The original strong L² limit inherits the actual uniform a.e. norm bound. -/
theorem ae_norm_le_of_bounded_L2_limit {X : Type*} [MeasurableSpace X] {m : ℕ}
    (μ : Measure X) (P : ℕ → X → Ambient m) (Q : X → Ambient m)
    (hP : ∀ k, MemLp (P k) 2 μ) (hQ : MemLp Q 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (P k - Q) 2 μ) atTop (𝓝 0))
    {B : ℝ} (hbound : ∀ k, ∀ᵐ x ∂μ, ‖P k x‖ ≤ B) :
    ∀ᵐ x ∂μ, ‖Q x‖ ≤ B := by
  have H := ae_mem_closed_of_L2_limit μ P Q hP hQ hconv
    (Metric.closedBall (0 : Ambient m) B) Metric.isClosed_closedBall
    (fun k => (hbound k).mono fun x hx => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  simpa only [Metric.mem_closedBall, dist_zero_right] using H

/-- A genuine fixed L² scalar weight multiplies a uniformly bounded strong L² difference in strong L². -/
theorem bounded_L2_limit_smul_fixed_L2 {X : Type*} [MeasurableSpace X] {m : ℕ}
    (μ : Measure X) (P : ℕ → X → Ambient m) (Q : X → Ambient m)
    (hP : ∀ k, MemLp (P k) 2 μ) (hQ : MemLp Q 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (P k - Q) 2 μ) atTop (𝓝 0))
    {B : ℝ} (hbound : ∀ k, ∀ᵐ x ∂μ, ‖P k x‖ ≤ B)
    (a : X → ℝ) (ha : MemLp a 2 μ) :
    (∀ᵐ x ∂μ, ‖Q x‖ ≤ B) ∧
      (∀ k, MemLp (fun x => a x • (P k x - Q x)) 2 μ) ∧
      Tendsto (fun k => eLpNorm (fun x => a x • (P k x - Q x)) 2 μ) atTop (𝓝 0) := by
  have hQbound := ae_norm_le_of_bounded_L2_limit μ P Q hP hQ hconv hbound
  let C : ℝ := 2 * |B|
  have hboundDiff (k : ℕ) : ∀ᵐ x ∂μ, ‖P k x - Q x‖ ≤ C := by
    filter_upwards [hbound k, hQbound] with x hxP hxQ
    calc
      _ ≤ ‖P k x‖ + ‖Q x‖ := norm_sub_le _ _
      _ ≤ |B| + |B| := add_le_add (hxP.trans (le_abs_self B)) (hxQ.trans (le_abs_self B))
      _ = C := by dsimp only [C]; ring
  let w (k : ℕ) (x : X) := a x • (P k x - Q x)
  have hwm (k : ℕ) : AEStronglyMeasurable (w k) μ :=
    ha.aestronglyMeasurable.smul ((hP k).aestronglyMeasurable.sub hQ.aestronglyMeasurable)
  have hwbound (k : ℕ) : ∀ᵐ x ∂μ, ‖w k x‖ ≤ C * ‖a x‖ := by
    filter_upwards [hboundDiff k] with x hx
    calc
      _ = ‖a x‖ * ‖P k x - Q x‖ := norm_smul _ _
      _ ≤ ‖a x‖ * C := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hw (k : ℕ) : MemLp (w k) 2 μ := ha.of_le_mul (hwm k) (hwbound k)
  refine ⟨hQbound, hw, ?_⟩
  have hmeasure : TendstoInMeasure μ P atTop Q :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun k => (hP k).aestronglyMeasurable) hQ.aestronglyMeasurable hconv
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, _hms, hseq⟩ := (hmeasure.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  apply tendsto_eLpNorm_two_of_integral_norm_sq
    (fun k => w (ns (ms k))) (fun k => hw (ns (ms k)))
  have hdom : Integrable (fun x => C ^ 2 * ‖a x‖ ^ 2) μ :=
    (ha.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul _
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun k => ‖w (ns (ms k)) x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hseq] with x hx
    have hsmul : Tendsto (fun k => a x • (P (ns (ms k)) x - Q x))
        atTop (𝓝 (a x • (Q x - Q x))) :=
      tendsto_const_nhds.smul (hx.sub tendsto_const_nhds)
    have H := hsmul.norm.pow 2
    simpa only [w, sub_self, smul_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using H
  have H := tendsto_integral_of_dominated_convergence (fun x => C ^ 2 * ‖a x‖ ^ 2)
    (fun k => (hw (ns (ms k))).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0) |>.aestronglyMeasurable)
    hdom (fun k => ?_) hlim
  · simpa only [integral_zero] using H
  · filter_upwards [hwbound (ns (ms k))] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact (pow_le_pow_left₀ (norm_nonneg _) hx 2).trans_eq (mul_pow _ _ _)

/-- An actual L² operator field multiplies the same bounded strong L² limit continuously. -/
theorem bounded_L2_limit_fixed_operator_L2 {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (μ : Measure X) (P : ℕ → X → Ambient m) (Q : X → Ambient m)
    (hP : ∀ k, MemLp (P k) 2 μ) (hQ : MemLp Q 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (P k - Q) 2 μ) atTop (𝓝 0))
    {B : ℝ} (hbound : ∀ k, ∀ᵐ x ∂μ, ‖P k x‖ ≤ B)
    (A : X → Ambient m →L[ℝ] E) (hA : MemLp A 2 μ) :
    (∀ᵐ x ∂μ, ‖Q x‖ ≤ B) ∧
      MemLp (fun x => A x (Q x)) 2 μ ∧
      (∀ k, MemLp (fun x => A x (P k x)) 2 μ) ∧
      (∀ k, MemLp (fun x => A x (P k x - Q x)) 2 μ) ∧
      Tendsto (fun k => eLpNorm (fun x => A x (P k x - Q x)) 2 μ) atTop (𝓝 0) := by
  obtain ⟨hQbound, hweighted, hweightedConv⟩ := bounded_L2_limit_smul_fixed_L2
    μ P Q hP hQ hconv hbound (fun x => ‖A x‖) hA.norm
  have hmeas (V : X → Ambient m) (hV : AEStronglyMeasurable V μ) :
      AEStronglyMeasurable (fun x => A x (V x)) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.aestronglyMeasurable.prodMk hV)
  have hproduct (V : X → Ambient m) (hV : AEStronglyMeasurable V μ)
      (hVbound : ∀ᵐ x ∂μ, ‖V x‖ ≤ B) : MemLp (fun x => A x (V x)) 2 μ := by
    apply hA.of_le_mul (c := |B|) (hmeas V hV)
    filter_upwards [hVbound] with x hx
    calc
      _ ≤ ‖A x‖ * ‖V x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖A x‖ * |B| := mul_le_mul_of_nonneg_left (hx.trans (le_abs_self B)) (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hnorm (k : ℕ) (x : X) :
      ‖A x (P k x - Q x)‖ ≤ ‖‖A x‖ • (P k x - Q x)‖ := by
    rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
    exact ContinuousLinearMap.le_opNorm _ _
  have hdiff (k : ℕ) : MemLp (fun x => A x (P k x - Q x)) 2 μ :=
    (hweighted k).norm.mono'
      (hmeas _ ((hP k).aestronglyMeasurable.sub hQ.aestronglyMeasurable))
      (Eventually.of_forall (hnorm k))
  refine ⟨hQbound, hproduct Q hQ.aestronglyMeasurable hQbound,
    fun k => hproduct (P k) (hP k).aestronglyMeasurable (hbound k), hdiff, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hweightedConv
    (fun _ => bot_le) (fun k => eLpNorm_mono (hnorm k))

end StationaryHarmonicMaps.Analysis

end
