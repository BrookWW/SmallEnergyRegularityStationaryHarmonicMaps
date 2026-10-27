module

public import HarmonicMaps.Analysis.L2TranslationContinuity
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# L2 continuity of centered dilations

Nonzero dilations preserve L2 membership, with their Jacobian giving the exact
change in the L2 seminorm. Compactly supported continuous approximation then
gives convergence to the identity for every global L2 function.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace HarmonicMaps

/-- Nonzero centered dilations preserve global L2 membership. -/
theorem memLp_comp_centeredDilation {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : Domain n → E} (hf : MemLp f 2 volume) (a : Domain n)
    {t : ℝ} (ht : t ≠ 0) :
    MemLp (fun x => f (a + t • (x - a))) 2 volume := by
  have ha := hf.comp_measurePreserving (measurePreserving_add_left volume a)
  have hs : MemLp ((f ∘ (a + ·)) ∘ (t • ·)) 2 volume := by
    apply MemLp.comp_of_map _ (measurable_const_smul t).aemeasurable
    rw [Measure.map_addHaar_smul volume ht]
    exact ha.smul_measure ENNReal.ofReal_ne_top
  exact hs.comp_measurePreserving (measurePreserving_sub_right volume a)

/-- The exact L2 change of variables for a centered dilation. -/
theorem eLpNorm_comp_centeredDilation {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : Domain n → E} (hf : MemLp f 2 volume) (a : Domain n)
    {t : ℝ} (ht : t ≠ 0) :
    eLpNorm (fun x => f (a + t • (x - a))) 2 volume =
      ENNReal.ofReal (abs (t ^ n)⁻¹) ^ (1 / 2 : ℝ) * eLpNorm f 2 volume := by
  have ha := hf.comp_measurePreserving (measurePreserving_add_left volume a)
  have ham : AEStronglyMeasurable (f ∘ (a + ·)) (Measure.map (t • ·) volume) := by
    rw [Measure.map_addHaar_smul volume ht]
    exact (ha.smul_measure ENNReal.ofReal_ne_top).aestronglyMeasurable
  have hsm : AEStronglyMeasurable ((f ∘ (a + ·)) ∘ (t • ·)) volume :=
    ham.comp_aemeasurable (measurable_const_smul t).aemeasurable
  change eLpNorm (((f ∘ (a + ·)) ∘ (t • ·)) ∘ (· - a)) 2 volume = _
  rw [eLpNorm_comp_measurePreserving hsm (measurePreserving_sub_right volume a),
    ← eLpNorm_map_measure ham (measurable_const_smul t).aemeasurable,
    Measure.map_addHaar_smul volume ht,
    eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
    eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
      (measurePreserving_add_left volume a)]
  simp only [Domain, finrank_euclideanSpace, Fintype.card_fin,
    smul_eq_mul]
  norm_num

private theorem tendsto_eLpNorm_centeredDilation_sub_of_continuous
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {g : Domain n → E} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (a : Domain n) :
    Tendsto (fun t : ℝ => eLpNorm (fun x => g (a + t • (x - a)) - g x) 2 volume)
      (𝓝 1) (𝓝 0) := by
  obtain ⟨R, hR, hsR⟩ := hgs.isCompact.isBounded.subset_ball_lt 0 a
  obtain ⟨C, hC⟩ := hgs.exists_bound_of_continuous hgc
  have hC0 : 0 ≤ C := (norm_nonneg (g a)).trans (hC a)
  let K := Metric.closedBall a (2 * R)
  let B : Domain n → ℝ≥0∞ := K.indicator (fun _ => ENNReal.ofReal ((2 * C) ^ 2))
  let F : ℝ → Domain n → ℝ≥0∞ := fun t x =>
    ENNReal.ofReal (‖g (a + t • (x - a)) - g x‖ ^ 2)
  have hFmeas (t : ℝ) : Measurable (F t) := by
    dsimp [F]
    exact (((hgc.comp (by fun_prop)).sub hgc).norm.pow 2).measurable.ennreal_ofReal
  have hBfin : ∫⁻ x, B x ∂volume ≠ ∞ := by
    dsimp [B]
    rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]
    have hK : IsCompact K := isCompact_closedBall a (2 * R)
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK.measure_ne_top
  have hbound : ∀ᶠ t : ℝ in 𝓝 1, ∀ᵐ x ∂volume, F t x ≤ B x := by
    filter_upwards [eventually_ge_nhds (by norm_num : (1 / 2 : ℝ) < 1)] with t ht
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · rw [show B x = ENNReal.ofReal ((2 * C) ^ 2) from indicator_of_mem hx _]
        apply ENNReal.ofReal_le_ofReal
        have hb : ‖g (a + t • (x - a)) - g x‖ ≤ 2 * C :=
          (norm_sub_le _ _).trans (by linarith only [hC (a + t • (x - a)), hC x])
        exact pow_le_pow_left₀ (norm_nonneg _) hb 2
      · have hxR : 2 * R < ‖x - a‖ := by
          simpa only [K, Metric.mem_closedBall, dist_eq_norm, not_le] using hx
        have hgx : g x = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hxt
          have := hsR hxt
          simp only [Metric.mem_ball, dist_eq_norm] at this
          linarith only [hxR, this, hR]
        have hgy : g (a + t • (x - a)) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hyt
          have hy := hsR hyt
          simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
            norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith only [ht] : 0 ≤ t)] at hy
          have hmul : (1 / 2 : ℝ) * ‖x - a‖ ≤ t * ‖x - a‖ :=
            mul_le_mul_of_nonneg_right ht (norm_nonneg _)
          linarith only [hxR, hy, hmul]
        simp only [F, hgx, hgy, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
          ENNReal.ofReal_zero, zero_le]
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun t => F t x) (𝓝 1) (𝓝 0) := by
    exact Eventually.of_forall fun x => by
      have hx : Tendsto (fun t : ℝ => g (a + t • (x - a)) - g x) (𝓝 1) (𝓝 0) := by
        have hxc : Continuous (fun t : ℝ => g (a + t • (x - a)) - g x) :=
          (hgc.comp (by fun_prop)).sub continuous_const
        simpa only [one_smul, add_sub_cancel, sub_self] using hxc.tendsto 1
      simpa only [F, Function.comp_def, norm_zero, zero_pow (by decide : 2 ≠ 0),
        ENNReal.ofReal_zero] using
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
          (by simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using hx.norm.pow 2)
  have hlin : Tendsto (fun t => ∫⁻ x, F t x ∂volume) (𝓝 1) (𝓝 0) := by
    simpa only [lintegral_zero] using
      tendsto_lintegral_filter_of_dominated_convergence B
        (Eventually.of_forall hFmeas) hbound hBfin hlim
  have hroot : Tendsto (fun t => (∫⁻ x, F t x ∂volume) ^ (1 / 2 : ℝ))
      (𝓝 1) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
      (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp hlin
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞), ENNReal.toReal_ofNat, ENNReal.rpow_two,
    ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2,
    Function.comp_def, F, one_div]
    using hroot

/-- Centered dilations tending to the identity converge in the actual L2 seminorm. -/
theorem tendsto_eLpNorm_centeredDilation_sub {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Domain n → E} (hf : MemLp f 2 volume) (a : Domain n) :
    Tendsto (fun t : ℝ => eLpNorm (fun x => f (a + t • (x - a)) - f x) 2 volume)
      (𝓝 1) (𝓝 0) := by
  let c : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (abs (t ^ n)⁻¹) ^ (1 / 2 : ℝ)
  have hc : Tendsto c (𝓝 1) (𝓝 1) := by
    have hi : ContinuousAt (fun t : ℝ => (t ^ n)⁻¹) 1 :=
      (continuousAt_id.pow n).inv₀ (by simp)
    have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.comp
      (ENNReal.continuous_ofReal.continuousAt.comp hi.abs)
    simpa only [ContinuousAt, Function.comp_def, c, one_pow, inv_one, abs_one,
      ENNReal.ofReal_one, ENNReal.one_rpow] using h
  have hc2 : ∀ᶠ t : ℝ in 𝓝 1, c t ≤ 2 :=
    hc.eventually (eventually_le_nhds (by norm_num : (1 : ℝ≥0∞) < 2))
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  let δ : ℝ≥0∞ := ε / 4
  have hδ : 0 < δ := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨g, hgs, hfg, hgc, hg⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hδ.ne'
  have hgconv := tendsto_eLpNorm_centeredDilation_sub_of_continuous hgc hgs a
  have hgle : ∀ᶠ t : ℝ in 𝓝 1,
      eLpNorm (fun x => g (a + t • (x - a)) - g x) 2 volume ≤ δ :=
    (ENNReal.tendsto_nhds_zero.mp hgconv) δ hδ
  filter_upwards [hc2, hgle, eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)]
    with t ht2 hgt ht
  have hpull := memLp_comp_centeredDilation (hf.sub hg) a ht
  have hgd := (memLp_comp_centeredDilation hg a ht).sub hg
  have hgf := hg.sub hf
  have hsplit : (fun x => f (a + t • (x - a)) - f x) =
      ((fun x => (f - g) (a + t • (x - a))) +
        (fun x => g (a + t • (x - a)) - g x)) + (g - f) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  calc
    eLpNorm (fun x => f (a + t • (x - a)) - f x) 2 volume
      ≤ eLpNorm (fun x => (f - g) (a + t • (x - a))) 2 volume +
          eLpNorm (fun x => g (a + t • (x - a)) - g x) 2 volume +
          eLpNorm (g - f) 2 volume := by
        rw [hsplit]
        have h1 := eLpNorm_add_le (p := (2 : ℝ≥0∞)) (μ := volume)
          (hpull.add hgd).aestronglyMeasurable hgf.aestronglyMeasurable (by norm_num)
        have h2 := eLpNorm_add_le (p := (2 : ℝ≥0∞)) (μ := volume)
          hpull.aestronglyMeasurable hgd.aestronglyMeasurable (by norm_num)
        exact h1.trans (add_le_add h2 le_rfl)
    _ = c t * eLpNorm (f - g) 2 volume +
          eLpNorm (fun x => g (a + t • (x - a)) - g x) 2 volume +
          eLpNorm (f - g) 2 volume := by
        rw [eLpNorm_comp_centeredDilation (hf.sub hg) a ht,
          show g - f = -(f - g) by abel, eLpNorm_neg]
    _ ≤ 2 * δ + δ + δ := by gcongr
    _ = ε := by
      calc
        2 * δ + δ + δ = 4 * δ := by ring
        _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

/-- The amplitude from a transformed weak gradient also converges in L2. -/
theorem tendsto_eLpNorm_smul_centeredDilation_sub {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Domain n → E} (hf : MemLp f 2 volume) (a : Domain n) :
    Tendsto (fun t : ℝ => eLpNorm (fun x => t • f (a + t • (x - a)) - f x) 2 volume)
      (𝓝 1) (𝓝 0) := by
  let D : ℝ → Domain n → E := fun t x => f (a + t • (x - a)) - f x
  let A : ℝ → Domain n → E := fun t x => t • f x - f x
  have hD := tendsto_eLpNorm_centeredDilation_sub hf a
  have hA := tendsto_eLpNorm_amplitude_sub hf
  have hn : Tendsto (fun t : ℝ => ‖t‖ₑ) (𝓝 1) (𝓝 1) := by
    simpa only [enorm_one] using continuous_enorm.tendsto (1 : ℝ)
  have hprod : Tendsto (fun t : ℝ => ‖t‖ₑ * eLpNorm (D t) 2 volume) (𝓝 1) (𝓝 0) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul hn (Or.inl (by norm_num)) hD
      (Or.inr (by norm_num))
  have hsum : Tendsto (fun t : ℝ => ‖t‖ₑ * eLpNorm (D t) 2 volume +
      eLpNorm (A t) 2 volume) (𝓝 1) (𝓝 0) := by
    simpa only [add_zero] using hprod.add hA
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le)
  filter_upwards [eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)] with t ht
  have hDm : MemLp (D t) 2 volume := (memLp_comp_centeredDilation hf a ht).sub hf
  have hAm : MemLp (A t) 2 volume := (hf.const_smul t).sub hf
  have heq : (fun x => t • f (a + t • (x - a)) - f x) = t • D t + A t := by
    funext x
    simp only [D, A, Pi.add_apply, Pi.smul_apply, smul_sub]
    abel
  rw [heq]
  calc
    eLpNorm (t • D t + A t) 2 volume ≤
        eLpNorm (t • D t) 2 volume + eLpNorm (A t) 2 volume :=
      eLpNorm_add_le (hDm.const_smul t).aestronglyMeasurable
        hAm.aestronglyMeasurable (by norm_num)
    _ = _ := by rw [eLpNorm_const_smul]

end HarmonicMaps
