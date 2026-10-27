module

public import StationaryHarmonicMaps.Analysis.NeumannKelvinRadial
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Smoothness of the genuine Neumann Kelvin reflection

An affine change of the radial integration parameter puts the correction
on the fixed compact unit interval. Joint smoothness then holds for every
positive radius, including coincident integration endpoints. Composition
with the actual radius and direction gives a smooth punctured reflection.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

theorem neumann_radial_intervalIntegral_affine_unit {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : ℝ → G) (a b : ℝ) :
    (∫ t in a..b, f t) =
      ∫ s : Icc (0 : ℝ) 1, (b-a) • f (a+(b-a)*(s : ℝ)) := by
  have hSubtype : (∫ s : Icc (0 : ℝ) 1, (b-a) • f (a+(b-a)*(s : ℝ))) =
      ∫ s in (0 : ℝ)..1, (b-a) • f (a+(b-a)*s) := by
    change (∫ s : Icc (0 : ℝ) 1, (b-a) • f (a+(b-a)*(s : ℝ))
      ∂Measure.comap Subtype.val volume) = _
    rw [integral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Icc
      (fun s : ℝ => (b-a) • f (a+(b-a)*s)),
      integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]
  rw [hSubtype, intervalIntegral.integral_smul]
  by_cases h : b-a = 0
  · have hab : b = a := sub_eq_zero.mp h
    simp only [hab, sub_self, zero_smul, intervalIntegral.integral_same]
  · have H := intervalIntegral.integral_comp_add_mul (a := (0 : ℝ)) (b := 1) f h a
    have hEnd : a+(b-a)*1 = b := by ring
    simp only [mul_zero, add_zero, hEnd] at H
    rw [H, smul_smul, mul_inv_cancel₀ h, one_smul]

theorem positive_neumann_radial_interpolation (upper : ℝ) (hUpper : 0 < upper)
    (r : ℝ) (hr : 0 < r) (s : Icc (0 : ℝ) 1) :
    0 < r⁻¹ + (upper-r⁻¹)*(s : ℝ) := by
  have hInv : 0 < r⁻¹ := inv_pos.mpr hr
  by_cases hs : (s : ℝ) = 1
  · rw [hs, mul_one, add_sub_cancel]
    exact hUpper
  · have hOne : 0 < 1-(s : ℝ) := sub_pos.mpr (lt_of_le_of_ne s.property.2 hs)
    have H := add_pos_of_pos_of_nonneg (mul_pos hOne hInv) (mul_nonneg s.property.1 hUpper.le)
    nlinarith only [H]

/-- The original radial correction has its literal compact-parameter formula. -/
theorem neumannKelvinRay_eq_compactIntegral {n q : ℕ} (upper : ℝ)
    (u : Domain n → Ambient q) (θ : Domain n) (r : ℝ) :
    neumannKelvinRay upper u θ r = r ^ (2-(n : ℝ)) • u (r⁻¹ • θ) +
      ((n : ℝ)-2) • (∫ s : Icc (0 : ℝ) 1,
        (upper-r⁻¹) • ((r⁻¹+(upper-r⁻¹)*(s : ℝ)) ^ ((n : ℝ)-3) •
          u ((r⁻¹+(upper-r⁻¹)*(s : ℝ)) • θ))) := by
  rw [neumannKelvinRay, neumann_radial_intervalIntegral_affine_unit]

/-- The actual reflection is jointly smooth in direction and every positive radius. -/
theorem neumannKelvinRay_contDiffOn {n q : ℕ} (upper : ℝ) (hUpper : 0 < upper)
    (u : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u) :
    ContDiffOn ℝ ∞ (fun z : Domain n × ℝ => neumannKelvinRay upper u z.1 z.2)
      {z | 0 < z.2} := by
  let τ := fun p : (Domain n × ℝ) × ℝ => p.1.2⁻¹ + (upper-p.1.2⁻¹)*p.2
  let U : Set (Domain n × ℝ) := {z | 0 < z.2}
  let W : Set ((Domain n × ℝ) × ℝ) := {p | 0 < p.1.2 ∧ 0 < τ p}
  let J := fun p : (Domain n × ℝ) × ℝ =>
    (upper-p.1.2⁻¹) • ((τ p) ^ ((n : ℝ)-3) • u ((τ p) • p.1.1))
  have hU : IsOpen U := isOpen_lt continuous_const continuous_snd
  have hτ (p : (Domain n × ℝ) × ℝ) (hp : 0 < p.1.2) : ContDiffAt ℝ ∞ τ p := by
    have hi : ContDiffAt ℝ ∞ (fun z : (Domain n × ℝ) × ℝ => z.1.2⁻¹) p :=
      (contDiffAt_fst.snd).inv hp.ne'
    exact hi.add ((contDiffAt_const.sub hi).mul contDiffAt_snd)
  have hW : IsOpen W := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hR : ∀ᶠ z : (Domain n × ℝ) × ℝ in 𝓝 p, 0 < z.1.2 :=
      (continuous_fst.snd.continuousAt.tendsto).eventually (Ioi_mem_nhds hp.1)
    have hT : ∀ᶠ z : (Domain n × ℝ) × ℝ in 𝓝 p, 0 < τ z :=
      ((hτ p hp.1).continuousAt.tendsto).eventually (Ioi_mem_nhds hp.2)
    exact hR.and hT
  have hPairs : ∀ z ∈ U, ∀ s : Icc (0 : ℝ) 1, (z, (s : ℝ)) ∈ W := by
    intro z hz s
    exact ⟨hz, positive_neumann_radial_interpolation upper hUpper z.2 hz s⟩
  have hJ : ContDiffOn ℝ ∞ J W := by
    intro p hp
    have hi : ContDiffAt ℝ ∞ (fun z : (Domain n × ℝ) × ℝ => z.1.2⁻¹) p :=
      (contDiffAt_fst.snd).inv hp.1.ne'
    exact ((contDiffAt_const.sub hi).smul
      (((hτ p hp.1).rpow_const_of_ne hp.2.ne').smul
        (hu.contDiffAt.comp p ((hτ p hp.1).smul (contDiffAt_fst.fst))))).contDiffWithinAt
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ (Domain n) ℝ
  let L := e.toContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ ℝ)
  have hLift := compactParametricIntegral_contDiffOn (volume : Measure (Icc (0 : ℝ) 1))
    (fun s : Icc (0 : ℝ) 1 => (s : ℝ)) continuous_subtype_val
    (e ⁻¹' U) (hU.preimage e.continuous) (L ⁻¹' W) (hW.preimage L.continuous)
    (fun z hz s => hPairs (e z) hz s) (J ∘ L)
    (hJ.comp L.contDiff.contDiffOn (fun _ hz => hz))
  have hIntegral : ContDiffOn ℝ ∞ (fun z : Domain n × ℝ =>
      ∫ s : Icc (0 : ℝ) 1, J (z, (s : ℝ))) U := by
    have HT := hLift.comp e.symm.contDiff.contDiffOn
      (fun z (hz : z ∈ U) => show e.symm z ∈ e ⁻¹' U by simpa only [mem_preimage, e.apply_symm_apply] using hz)
    have hMap (z : Domain n × ℝ) (s : ℝ) : L (e.symm z, s) = (z, s) := by
      change (e (e.symm z), s) = (z, s)
      rw [e.apply_symm_apply]
    simpa only [Function.comp_def, hMap] using HT
  have hFirst : ContDiffOn ℝ ∞ (fun z : Domain n × ℝ =>
      z.2 ^ (2-(n : ℝ)) • u (z.2⁻¹ • z.1)) U := by
    intro z hz
    exact (((contDiffAt_snd.rpow_const_of_ne hz.ne').smul
      (hu.contDiffAt.comp z ((contDiffAt_snd.inv hz.ne').smul contDiffAt_fst)))).contDiffWithinAt
  apply (hFirst.add (hIntegral.const_smul ((n : ℝ)-2))).congr
  intro z hz
  exact neumannKelvinRay_eq_compactIntegral upper u z.1 z.2

/-- The same actual radius-direction reflection is smooth at every nonzero point. -/
theorem neumannKelvinReflection_contDiffAt {n q : ℕ} (upper : ℝ) (hUpper : 0 < upper)
    (u : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u)
    (x : Domain n) (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : Domain n => neumannKelvinRay upper u (‖y‖⁻¹ • y) ‖y‖) x := by
  have hNorm : ContDiffAt ℝ ∞ (fun y : Domain n => ‖y‖) x := contDiffAt_norm ℝ hx
  have hDirection : ContDiffAt ℝ ∞ (fun y : Domain n => ‖y‖⁻¹ • y) x :=
    (hNorm.inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id
  have hPair := hDirection.prodMk hNorm
  have hOpen : IsOpen ({z : Domain n × ℝ | 0 < z.2}) :=
    isOpen_lt continuous_const continuous_snd
  have hIn : (‖x‖⁻¹ • x, ‖x‖) ∈ {z : Domain n × ℝ | 0 < z.2} := norm_pos_iff.mpr hx
  have hRay := (neumannKelvinRay_contDiffOn upper hUpper u hu).contDiffAt
    (hOpen.mem_nhds hIn)
  have HC := hRay.comp x hPair
  exact HC

end StationaryHarmonicMaps.Analysis

end
