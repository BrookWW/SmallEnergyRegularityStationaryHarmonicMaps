module

public import HarmonicMaps.Analysis.VariableMollificationAveraging
public import HarmonicMaps.Analysis.SobolevMollificationGradient

/-!
# Sharp map and tensor bounds for variable smoothing

The literal map average and original-gradient tensor average have finite
L2 data. Their exact square bounds combine weighted Jensen with the proved
restricted forward pushforward domination.
-/

public section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped BigOperators ENNReal ContDiff

namespace HarmonicMaps

/-- The actual map average has the sharp square estimate from its proved
fixed-direction restricted pushforward bound. -/
theorem variableMollification_map_bounds {n q : ℕ}
    {s : Domain n → ℝ} (hs : ContDiff ℝ ∞ s)
    {μ ν : Measure (Domain n)} [SFinite μ] [IsFiniteMeasure ν]
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ y ∈ Metric.ball (0 : Domain n) 1,
      Measure.map (variableShift s y) μ ≤ ENNReal.ofReal K • ν)
    {f : Domain n → Ambient q} (hf : MemLp f 2 ν) :
    Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 • f (variableShift s p.2 p.1))
      (μ.prod (volume.restrict (Metric.ball (0 : Domain n) 1))) ∧
    Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * ‖f (variableShift s p.2 p.1)‖ ^ 2)
      (μ.prod (volume.restrict (Metric.ball (0 : Domain n) 1))) ∧
    MemLp (fun x => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • f (variableShift s y x)) 2 μ ∧
    (∫ x, ‖∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • f (variableShift s y x)‖ ^ 2 ∂μ) ≤
      K * ∫ z, ‖f z‖ ^ 2 ∂ν := by
  have hi : Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 • f (variableShift s p.2 p.1))
      (μ.prod (volume.restrict (Metric.ball (0 : Domain n) 1))) :=
    variableMollification_weighted_joint_integrable hs hK hbound
    (hf.integrable (by norm_num))
  have hisq : Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * ‖f (variableShift s p.2 p.1)‖ ^ 2)
      (μ.prod (volume.restrict (Metric.ball (0 : Domain n) 1))) :=
    variableMollification_weighted_joint_integrable hs hK hbound
    (hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  obtain ⟨hM, hJ⟩ := fixedMollifier_average_memLp_two
    (H := fun x y => f (variableShift s y x)) hi hisq
  exact ⟨hi, hisq, hM, hJ.trans
    (variableMollification_weighted_joint_integral_le hs hK hbound
      (hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
      (Eventually.of_forall fun _ => sq_nonneg _))⟩

private theorem tensor_coefficient_continuous {n : ℕ} {s : Domain n → ℝ}
    (hs : ContDiff ℝ ∞ s) (i j : Fin n) :
    Continuous (fun p : Domain n × Domain n =>
      ((ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s p.1).smulRight p.2)
        (EuclideanSpace.single i 1)) j) := by
  have hsc : Continuous (fun x : Domain n => fderiv ℝ s x (EuclideanSpace.single i 1)) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  change Continuous (fun p : Domain n × Domain n =>
    (EuclideanSpace.single i 1) j -
      fderiv ℝ s p.1 (EuclideanSpace.single i 1) * p.2 j)
  fun_prop

private theorem tensor_coefficient_norm_le {n : ℕ} {s : Domain n → ℝ} {L : ℝ}
    (hs : ContDiff ℝ ∞ s) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L)
    (x : Domain n) {y : Domain n} (hy : y ∈ Metric.ball 0 1) (i j : Fin n) :
    ‖((ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y)
      (EuclideanSpace.single i 1)) j‖ ≤ 1 + L := by
  have hB : ‖ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y‖ ≤ 1 + L := by
    rw [← fderiv_variableShift ((hs.differentiable (by simp)) x) y]
    exact norm_fderiv_variableShift_le ((hs.differentiable (by simp)) x) hDs y hy
  exact (PiLp.norm_apply_le _ j).trans
    ((ContinuousLinearMap.le_opNorm _ _).trans
      (by simpa only [PiLp.norm_single, norm_one, mul_one] using hB))

/-- Sharp HS and actual coordinate L2 estimates for the original-gradient
tensor average. The conditional measure input is produced by the source
restricted pushforward theorem at every source application. -/
theorem variableMollification_tensor_bounds {n q : ℕ}
    {s : Domain n → ℝ} {L : ℝ} (hs : ContDiff ℝ ∞ s)
    (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L)
    {μ ν : Measure (Domain n)} [SFinite μ] [IsFiniteMeasure ν]
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ y ∈ Metric.ball (0 : Domain n) 1,
      Measure.map (variableShift s y) μ ≤ ENNReal.ofReal K • ν)
    {Df : Domain n → Gradient n q} (hDf : ∀ j : Fin n, MemLp (fun x => Df x j) 2 ν) :
    let G := fun x y (i : Fin n) => ∑ j : Fin n,
      ((ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y)
        (EuclideanSpace.single i 1)) j • Df (variableShift s y x) j
    let DT := fun x (i : Fin n) => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • G x y i
    (∀ i : Fin n, Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 • G p.1 p.2 i)
      (μ.prod (volume.restrict (Metric.ball (0 : Domain n) 1)))) ∧
    Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * hsNormSq (G p.1 p.2))
      (μ.prod (volume.restrict (Metric.ball (0 : Domain n) 1))) ∧
    (∀ i : Fin n, MemLp (fun x => DT x i) 2 μ) ∧
    (∫ x, hsNormSq (DT x) ∂μ) ≤ ((1 + L) ^ 2 * K) * ∫ z, hsNormSq (Df z) ∂ν := by
  let σ := volume.restrict (Metric.ball (0 : Domain n) 1)
  let c := fun (i j : Fin n) (p : Domain n × Domain n) =>
    ((ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s p.1).smulRight p.2)
      (EuclideanSpace.single i 1)) j
  let G := fun x y (i : Fin n) => ∑ j : Fin n, c i j (x, y) • Df (variableShift s y x) j
  let DT := fun x (i : Fin n) => ∫ y in Metric.ball (0 : Domain n) 1,
    fixedMollifierKernel n y • G x y i
  have hqm := variableMollification_joint_quasiMeasurePreserving hs hbound
  have hc (i j : Fin n) : AEStronglyMeasurable (c i j) (μ.prod σ) :=
    (tensor_coefficient_continuous hs i j).aestronglyMeasurable
  have hcmp (j : Fin n) : AEStronglyMeasurable
      (fun p : Domain n × Domain n => Df (variableShift s p.2 p.1) j) (μ.prod σ) :=
    (hDf j).aestronglyMeasurable.comp_quasiMeasurePreserving hqm
  have hG (i : Fin n) : AEStronglyMeasurable
      (fun p : Domain n × Domain n => G p.1 p.2 i) (μ.prod σ) := by
    have hh := Finset.aestronglyMeasurable_sum Finset.univ fun j _ =>
      (hc i j).smul (hcmp j)
    convert hh using 1
    funext p
    simp only [Finset.sum_apply]
    rfl
  have hGi (i : Fin n) : Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 • G p.1 p.2 i) (μ.prod σ) := by
    have hi (j : Fin n) : Integrable (fun p : Domain n × Domain n =>
        c i j p • (fixedMollifierKernel n p.2 • Df (variableShift s p.2 p.1) j))
        (μ.prod σ) := by
      apply (variableMollification_weighted_joint_integrable hs hK hbound
        ((hDf j).integrable (by norm_num))).bdd_smul (1 + L) (hc i j)
      filter_upwards [quasiMeasurePreserving_snd.ae
        (ae_restrict_mem (μ := volume) measurableSet_ball)] with p hp
      exact tensor_coefficient_norm_le hs hDs p.1 hp i j
    apply (integrable_finsetSum Finset.univ (fun j _ => hi j)).congr
    exact Eventually.of_forall fun p => by
      dsimp only [G]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm (c i j p)
        (fixedMollifierKernel n p.2) (Df (variableShift s p.2 p.1) j)
  have hiDf := integrable_hsNormSq_of_memLp_columns hDf
  have hiBase : Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * hsNormSq (Df (variableShift s p.2 p.1))) (μ.prod σ) :=
    variableMollification_weighted_joint_integrable hs hK hbound hiDf
  have hmSq : AEStronglyMeasurable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * hsNormSq (G p.1 p.2)) (μ.prod σ) := by
    apply ((fixedMollifierKernel_contDiff n).continuous.comp continuous_snd).aestronglyMeasurable.mul
    have hh := Finset.aestronglyMeasurable_sum Finset.univ fun i _ => (hG i).norm.pow 2
    convert hh using 1
    funext p
    simp only [Finset.sum_apply, hsNormSq, Pi.pow_apply]
  have hsqbound : ∀ᵐ p ∂μ.prod σ,
      fixedMollifierKernel n p.2 * hsNormSq (G p.1 p.2) ≤
        (1 + L) ^ 2 * (fixedMollifierKernel n p.2 * hsNormSq (Df (variableShift s p.2 p.1))) := by
    filter_upwards [quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (μ := volume) measurableSet_ball)] with p hp
    exact (mul_le_mul_of_nonneg_left
      (variableMollification_tensor_hsNormSq_le hs hDs hp Df p.1)
      (fixedMollifierKernel_nonneg n p.2)).trans_eq (by ring)
  have hiSq : Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * hsNormSq (G p.1 p.2)) (μ.prod σ) := by
    apply (hiBase.const_mul ((1 + L) ^ 2)).mono' hmSq
    exact hsqbound.mono fun p hp =>
      (Real.norm_of_nonneg (mul_nonneg (fixedMollifierKernel_nonneg n p.2)
        (hsNormSq_nonneg (G p.1 p.2)))).trans_le hp
  have hiColSq (i : Fin n) : Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * ‖G p.1 p.2 i‖ ^ 2) (μ.prod σ) := by
    apply hiSq.mono'
      (((fixedMollifierKernel_contDiff n).continuous.comp continuous_snd).aestronglyMeasurable.mul
        ((hG i).norm.pow 2))
    exact Eventually.of_forall fun p => by
      change ‖fixedMollifierKernel n p.2 * ‖G p.1 p.2 i‖ ^ 2‖ ≤
        fixedMollifierKernel n p.2 * hsNormSq (G p.1 p.2)
      rw [Real.norm_of_nonneg (mul_nonneg (fixedMollifierKernel_nonneg n p.2) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => sq_nonneg ‖G p.1 p.2 j‖)
        (Finset.mem_univ i)) (fixedMollifierKernel_nonneg n p.2)
  have hAvg (i : Fin n) := fixedMollifier_average_memLp_two
    (H := fun x y => G x y i) (hGi i) (hiColSq i)
  refine ⟨hGi, hiSq, fun i => (hAvg i).1, ?_⟩
  calc
    (∫ x, hsNormSq (DT x) ∂μ) = ∑ i : Fin n, ∫ x, ‖DT x i‖ ^ 2 ∂μ :=
      integral_finsetSum Finset.univ fun i _ =>
        ((hAvg i).1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
    _ ≤ ∑ i : Fin n, ∫ x, (∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y * ‖G x y i‖ ^ 2) ∂μ :=
      Finset.sum_le_sum fun i _ => (hAvg i).2
    _ = ∫ x, (∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y * hsNormSq (G x y)) ∂μ := by
      rw [← integral_finsetSum Finset.univ (fun i _ => (hiColSq i).integral_prod_left)]
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr (fun i : Fin n => (hiColSq i).prod_right_ae)] with x hx
      change (∑ i : Fin n, ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y * ‖G x y i‖ ^ 2) =
        ∫ y in Metric.ball (0 : Domain n) 1,
          fixedMollifierKernel n y * ∑ i : Fin n, ‖G x y i‖ ^ 2
      simp_rw [Finset.mul_sum]
      exact (integral_finsetSum Finset.univ (fun i _ => hx i)).symm
    _ ≤ (1 + L) ^ 2 * (∫ x, (∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y * hsNormSq (Df (variableShift s y x))) ∂μ) := by
      calc
        _ = ∫ p : Domain n × Domain n,
            fixedMollifierKernel n p.2 * hsNormSq (G p.1 p.2) ∂μ.prod σ :=
          (integral_prod _ hiSq).symm
        _ ≤ ∫ p : Domain n × Domain n,
            (1 + L) ^ 2 * (fixedMollifierKernel n p.2 *
              hsNormSq (Df (variableShift s p.2 p.1))) ∂μ.prod σ :=
          integral_mono_ae hiSq (hiBase.const_mul _) hsqbound
        _ = _ := by
          rw [integral_const_mul]
          exact congrArg (fun t : ℝ => (1 + L) ^ 2 * t) (integral_prod _ hiBase)
    _ ≤ (1 + L) ^ 2 * (K * ∫ z, hsNormSq (Df z) ∂ν) :=
      mul_le_mul_of_nonneg_left
        (variableMollification_weighted_joint_integral_le hs hK hbound hiDf
          (Eventually.of_forall fun z => hsNormSq_nonneg (Df z))) (sq_nonneg _)
    _ = ((1 + L) ^ 2 * K) * ∫ z, hsNormSq (Df z) ∂ν := by ring

end HarmonicMaps
