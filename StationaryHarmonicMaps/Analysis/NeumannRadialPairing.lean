module

public import StationaryHarmonicMaps.Analysis.NeumannRadialL2Sampling
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual adjoint change of variables for the Neumann radial integral

The positive dilation parameter is bounded away from zero. Its exact Haar
Jacobian and genuine joint integrability justify the two Fubini operations
in the natural radial test pairing, for the original integrable field.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

private theorem inverse_power_window_bound {n : ℕ} (t : ℝ) (ht : t∈Icc (1/4 : ℝ) 1) :
    |(t^n)⁻¹|≤(4 : ℝ)^n := by
  have ht0 : 0<t := lt_of_lt_of_le (by norm_num) ht.1
  rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg ht0.le _)),← inv_pow]
  apply pow_le_pow_left₀ (inv_nonneg.mpr ht0.le)
  have H := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1/4) ht.1
  norm_num only [one_div,inv_div,div_one] at H
  exact H

/-- Bounded actual radial coefficients and an original compact continuous test have both genuine joint pairings and their exact positive-Jacobian adjoint identity. -/
theorem neumann_radial_window_pairing_change_variables {n q : ℕ}
    (w : Domain n × ℝ → ℝ) (hw : Measurable w) (C : ℝ) (hC : 0≤C)
    (hBound : ∀x t,t∈Icc (1/4 : ℝ) 1 → ‖w (x,t)‖≤C)
    (u v : Domain n → Ambient q) (hu : Integrable u volume)
    (hv : Continuous v) (hcv : HasCompactSupport v) :
    let σ := volume.restrict (Icc (1/4 : ℝ) 1)
    let f := fun p : Domain n × ℝ=>inner ℝ (w p • u (p.2 • p.1)) (v p.1)
    let g := fun p : Domain n × ℝ=>|(p.2^n)⁻¹| *w (p.2⁻¹ • p.1,p.2)*
      inner ℝ (u p.1) (v (p.2⁻¹ • p.1))
    Integrable f (volume.prod σ) ∧ Integrable g (volume.prod σ) ∧
      (∫x,(∫t,f (x,t) ∂σ))=∫y,(∫t,g (y,t) ∂σ) := by
  intro σ f g
  letI : IsFiniteMeasure σ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_ne_top
  obtain ⟨M,hM⟩ := hcv.exists_bound_of_continuous hv
  have hM0 : 0≤M := (norm_nonneg (v 0)).trans (hM 0)
  have hParam : ∀ᵐ(p : Domain n × ℝ) ∂volume.prod σ,p.2∈Icc (1/4 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  have hWBound : ∀ᵐp∂volume.prod σ,‖w p‖≤C := hParam.mono fun p hp=>hBound p.1 p.2 hp
  have hJoint := (radial_window_joint_integrable u hu).bdd_smul C hw.aestronglyMeasurable hWBound
  have hfMeas : AEStronglyMeasurable f (volume.prod σ) :=
    hJoint.aestronglyMeasurable.inner hv.aestronglyMeasurable.comp_fst
  have hf : Integrable f (volume.prod σ) := by
    apply (hJoint.norm.mul_const M).mono' hfMeas
    exact Eventually.of_forall fun p=>(norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hM p.1) (norm_nonneg _))
  have hMap : Measurable (fun p : Domain n × ℝ=>p.2⁻¹ • p.1) := measurable_snd.inv.smul measurable_fst
  have hWeight : AEStronglyMeasurable (fun p : Domain n × ℝ=>|(p.2^n)⁻¹| *w (p.2⁻¹ • p.1,p.2))
      (volume.prod σ) :=
    ((measurable_snd.pow_const n).inv.norm.mul (hw.comp (hMap.prodMk measurable_snd))).aestronglyMeasurable
  have hgMeas : AEStronglyMeasurable g (volume.prod σ) := hWeight.mul
    (hu.aestronglyMeasurable.comp_fst.inner (hv.measurable.comp hMap).aestronglyMeasurable)
  have hDom : Integrable (fun p : Domain n × ℝ=>‖u p.1‖*((4 : ℝ)^n*C*M)) (volume.prod σ) :=
    hu.norm.mul_prod (integrable_const _)
  have hg : Integrable g (volume.prod σ) := by
    apply hDom.mono' hgMeas
    filter_upwards [hParam] with p hp
    have hJ := inverse_power_window_bound (n := n) p.2 hp
    have hW := hBound (p.2⁻¹ • p.1) p.2 hp
    have hV := hM (p.2⁻¹ • p.1)
    change ‖|(p.2^n)⁻¹| *w (p.2⁻¹ • p.1,p.2)*inner ℝ (u p.1) (v (p.2⁻¹ • p.1))‖≤_
    rw [norm_mul,norm_mul,Real.norm_of_nonneg (abs_nonneg _)]
    calc
      _≤((4 : ℝ)^n*C)*(‖u p.1‖*M) := mul_le_mul
        (mul_le_mul hJ hW (norm_nonneg _) (by positivity))
        ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hV (norm_nonneg _)))
        (norm_nonneg _) (by positivity)
      _=_ := by ring
  have hChange (t : ℝ) (ht : 0<t) : (∫y,g (y,t))=(∫x,f (x,t)) := by
    have hPoint (y : Domain n) : g (y,t)=|(t^n)⁻¹| *f (t⁻¹ • y,t) := by
      simp only [g,f,smul_smul,mul_inv_cancel₀ ht.ne',one_smul,real_inner_smul_left]
      ring
    calc
      _=|(t^n)⁻¹| *(∫y,f (t⁻¹ • y,t)) := by rw [integral_congr_ae (Eventually.of_forall hPoint),integral_const_mul]
      _=|(t^n)⁻¹| *(|t^n| *(∫x,f (x,t))) := by
        rw [Measure.integral_comp_inv_smul volume (fun x=>f (x,t)) t]
        simp only [Domain,finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul]
      _=_ := by rw [abs_inv,← mul_assoc,inv_mul_cancel₀ (abs_ne_zero.mpr (pow_ne_zero n ht.ne')),one_mul]
  refine ⟨hf,hg,?_⟩
  calc
    _=(∫t,(∫x,f (x,t)) ∂σ) := integral_integral_swap hf
    _=(∫t,(∫y,g (y,t)) ∂σ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact (hChange t (lt_of_lt_of_le (by norm_num) ht.1)).symm
    _=_ := (integral_integral_swap hg).symm

end StationaryHarmonicMaps.Analysis

end
