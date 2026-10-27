module

public import HolderToCK.Analysis.Poisson.KernelCancellation
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! # Pointwise kernel bounds and local integrability of the fundamental solution -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace HolderToCK

theorem norm_rpow_hasFDerivAt_of_ne_zero {n : ℕ} (p : ℝ) (x : Domain n) (hx : x ≠ 0) :
    HasFDerivAt (fun z : Domain n => ‖z‖ ^ p)
      ((p * ‖x‖ ^ (p - 2)) • innerSL ℝ x) x := by
  have hd := normSq_rpow_hasFDerivAt (0 : Domain n) (p / 2) x hx
  simp only [sub_zero] at hd
  simp_rw [normSq_real_rpow, show 2 * (p / 2) = p by ring,
    show 2 * (p / 2 - 1) = p - 2 by ring] at hd
  exact hd

theorem norm_rpow_fderiv_norm_of_ne_zero {n : ℕ} (p : ℝ) (x : Domain n) (hx : x ≠ 0) :
    ‖fderiv ℝ (fun z : Domain n => ‖z‖ ^ p) x‖ = |p| * ‖x‖ ^ (p - 1) := by
  rw [(norm_rpow_hasFDerivAt_of_ne_zero p x hx).fderiv,
    norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    innerSL_apply_norm]
  rw [mul_assoc, ← Real.rpow_add_one (norm_ne_zero_iff.mpr hx)]
  congr 2
  ring

theorem hessianKernelExpression_bound {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (z : Domain n) (hz : z ≠ 0) :
    |hessianKernelExpression i j z| ≤
      ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ * ‖z‖ ^ (-(n : ℝ)) := by
  have hS : 0 ≤ (euclideanSphereArea n)⁻¹ := inv_nonneg.mpr (euclideanSphereArea_pos hn).le
  have hp : 0 ≤ ‖z‖ ^ (-(n : ℝ)) := Real.rpow_nonneg (norm_nonneg z) _
  have hq : 0 ≤ ‖z‖ ^ (-(n : ℝ) - 2) := Real.rpow_nonneg (norm_nonneg z) _
  have hi : |z i| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
  have hj : |z j| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z j
  have hδ : |(if i = j then 1 else 0 : ℝ)| ≤ 1 := by split_ifs <;> norm_num
  have hpow : ‖z‖ ^ 2 * ‖z‖ ^ (-(n : ℝ) - 2) = ‖z‖ ^ (-(n : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_add (norm_pos_iff.mpr hz)]
    congr 1
    ring
  rw [hessianKernelExpression, abs_mul, abs_of_nonneg hS]
  calc
    _ ≤ (euclideanSphereArea n)⁻¹ *
        (|(if i = j then 1 else 0 : ℝ) * ‖z‖ ^ (-(n : ℝ))| +
          |(n : ℝ) * z i * z j * ‖z‖ ^ (-(n : ℝ) - 2)|) :=
      mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using
        (norm_sub_le ((if i = j then 1 else 0 : ℝ) * ‖z‖ ^ (-(n : ℝ)))
          ((n : ℝ) * z i * z j * ‖z‖ ^ (-(n : ℝ) - 2)))) hS
    _ = (euclideanSphereArea n)⁻¹ *
        (|(if i = j then 1 else 0 : ℝ)| * ‖z‖ ^ (-(n : ℝ)) +
          (n : ℝ) * |z i| * |z j| * ‖z‖ ^ (-(n : ℝ) - 2)) := by
      simp only [abs_mul, abs_of_nonneg hp,
        abs_of_nonneg hq, abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
    _ ≤ (euclideanSphereArea n)⁻¹ *
        (‖z‖ ^ (-(n : ℝ)) + (n : ℝ) * ‖z‖ ^ 2 * ‖z‖ ^ (-(n : ℝ) - 2)) := by
      apply mul_le_mul_of_nonneg_left _ hS
      apply add_le_add
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right hδ hp
      · calc
          _ ≤ (n : ℝ) * ‖z‖ * ‖z‖ * ‖z‖ ^ (-(n : ℝ) - 2) := by gcongr
          _ = _ := by ring
    _ = _ := by rw [mul_assoc (n : ℝ), hpow]; ring

theorem norm_rpow_locallyIntegrable {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : -(n : ℝ) < p) :
    LocallyIntegrable (fun z : Domain n => ‖z‖ ^ p) volume := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := -p)
    (by simp only [finrank_euclideanSpace, Fintype.card_fin]; omega)
  · simp only [finrank_euclideanSpace, Fintype.card_fin]
    linarith only [hp]
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), neg_neg, one_mul]
  · exact (measurable_norm.pow measurable_const).aestronglyMeasurable

theorem fundamentalPowerExpression_eq_rpow {n : ℕ} (z : Domain n) :
    fundamentalPowerExpression z = ((2 - (n : ℝ)) * euclideanSphereArea n)⁻¹ *
      ‖z‖ ^ (2 - (n : ℝ)) := by
  rw [fundamentalPowerExpression, normSq_real_rpow,
    show 2 * ((2 - (n : ℝ)) / 2) = 2 - (n : ℝ) by ring]

theorem fundamentalPower_locallyIntegrable {n : ℕ} (hn : 3 ≤ n) :
    LocallyIntegrable (fundamentalPowerExpression : Domain n → ℝ) volume := by
  have hi := (norm_rpow_locallyIntegrable (by omega : 0 < n)
    (by linarith : -(n : ℝ) < 2 - (n : ℝ))).smul
      (((2 - (n : ℝ)) * euclideanSphereArea n)⁻¹)
  have heq : (((2 - (n : ℝ)) * euclideanSphereArea n)⁻¹ •
      (fun z : Domain n => ‖z‖ ^ (2 - (n : ℝ)))) = fundamentalPowerExpression := by
    funext z
    exact (fundamentalPowerExpression_eq_rpow z).symm
  rw [heq] at hi
  exact hi

@[expose] noncomputable def fundamentalGradientExpression {n : ℕ} (z : Domain n) :
    Domain n →L[ℝ] ℝ :=
  (((euclideanSphereArea n)⁻¹ * ‖z‖ ^ (-(n : ℝ))) • innerSL ℝ z)

theorem fundamentalGradientExpression_norm {n : ℕ} (hn : 0 < n)
    (z : Domain n) (hz : z ≠ 0) :
    ‖fundamentalGradientExpression z‖ =
      (euclideanSphereArea n)⁻¹ * ‖z‖ ^ (1 - (n : ℝ)) := by
  rw [fundamentalGradientExpression, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (euclideanSphereArea_pos hn).le)
      (Real.rpow_nonneg (norm_nonneg _) _)), innerSL_apply_norm,
    mul_assoc, ← Real.rpow_add_one (norm_ne_zero_iff.mpr hz)]
  congr 2
  ring

theorem fundamentalGradientExpression_locallyIntegrable {n : ℕ} (hn : 0 < n) :
    LocallyIntegrable (fundamentalGradientExpression : Domain n → Domain n →L[ℝ] ℝ) volume := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  apply locallyIntegrable_of_norm_le_rpow (C := (euclideanSphereArea n)⁻¹)
    (α := (n : ℝ) - 1)
    (by simp only [finrank_euclideanSpace, Fintype.card_fin]; omega)
  · simp only [finrank_euclideanSpace, Fintype.card_fin]
    linarith
  · filter_upwards [(volume : Measure (Domain n)).ae_ne 0] with z hz
    rw [fundamentalGradientExpression_norm hn z hz,
      show -((n : ℝ) - 1) = 1 - (n : ℝ) by ring]
  · exact ((measurable_const.mul (measurable_norm.pow measurable_const)).smul
      (innerSL ℝ).continuous.measurable).aestronglyMeasurable

theorem fundamentalPower_fderiv_locallyIntegrable {n : ℕ} (hn : 3 ≤ n) :
    LocallyIntegrable (fderiv ℝ (fundamentalPowerExpression : Domain n → ℝ)) volume := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega : 0 < n)
  apply (fundamentalGradientExpression_locallyIntegrable (by omega : 0 < n)).congr
  filter_upwards [(volume : Measure (Domain n)).ae_ne 0] with z hz
  exact (fundamentalPower_hasFDerivAt hn z hz).fderiv.symm

theorem fundamentalLog_fderiv_locallyIntegrable :
    LocallyIntegrable (fderiv ℝ fundamentalLogExpression) volume := by
  apply (fundamentalGradientExpression_locallyIntegrable (by omega : 0 < 2)).congr
  filter_upwards [(volume : Measure (Domain 2)).ae_ne 0] with z hz
  exact (fundamentalLog_hasFDerivAt z hz).fderiv.symm

theorem fundamentalLog_locallyIntegrable :
    LocallyIntegrable fundamentalLogExpression volume := by
  have hi := norm_rpow_locallyIntegrable (n := 2) (by omega)
    (p := -1) (by norm_num)
  simp only [Real.rpow_neg_one] at hi
  have hm : LocallyIntegrable (fun z : Domain 2 => Real.log ‖z‖) volume := by
    apply (continuous_norm.locallyIntegrable.add hi).mono
      (measurable_norm.log.aestronglyMeasurable)
    filter_upwards with z
    rw [Pi.add_apply, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (norm_nonneg z) (inv_nonneg.mpr (norm_nonneg z)))]
    apply abs_le.mpr
    have hlo := Real.neg_inv_le_log (norm_nonneg z)
    have hhi := Real.log_le_self (norm_nonneg z)
    exact ⟨by linarith only [hlo, norm_nonneg z],
      by linarith only [hhi, inv_nonneg.mpr (norm_nonneg z)]⟩
  have hc := hm.smul ((2 * Real.pi)⁻¹)
  exact hc

theorem scalarProduct_fderiv_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun z => f z * g z) x‖ ≤
      |f x| * ‖fderiv ℝ g x‖ + |g x| * ‖fderiv ℝ f x‖ := by
  change ‖fderiv ℝ (f * g) x‖ ≤ _
  rw [fderiv_mul hf hg]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs])

theorem coordinateProjection_norm_le_one {n : ℕ} (i : Fin n) :
    ‖PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [PiLp.proj_apply, one_mul] using PiLp.norm_apply_le z i

theorem coordinateProduct_fderiv_norm_le {n : ℕ} (i j : Fin n) (z : Domain n) :
    ‖fderiv ℝ (fun x : Domain n => x i * x j) z‖ ≤ 2 * ‖z‖ := by
  have hdi := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).differentiableAt (x := z)
  have hdj := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).differentiableAt (x := z)
  have hi : |z i| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
  have hj : |z j| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z j
  calc
    _ ≤ |z i| * ‖PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j‖ +
        |z j| * ‖PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i‖ := by
      simpa only [PiLp.proj_apply, ContinuousLinearMap.fderiv] using
        scalarProduct_fderiv_norm_le hdi hdj
    _ ≤ ‖z‖ * 1 + ‖z‖ * 1 := by
      gcongr
      · exact coordinateProjection_norm_le_one j
      · exact coordinateProjection_norm_le_one i
    _ = _ := by ring

theorem hessianKernelExpression_fderiv_bound {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (z : Domain n) (hz : z ≠ 0) :
    ‖fderiv ℝ (hessianKernelExpression i j) z‖ ≤
      (n : ℝ) * ((n : ℝ) + 5) * (euclideanSphereArea n)⁻¹ *
        ‖z‖ ^ (-(n : ℝ) - 1) := by
  let p : Domain n → ℝ := fun x => ‖x‖ ^ (-(n : ℝ))
  let q : Domain n → ℝ := fun x => ‖x‖ ^ (-(n : ℝ) - 2)
  let c : Domain n → ℝ := fun x => x i * x j
  let d : ℝ := if i = j then 1 else 0
  have hp : DifferentiableAt ℝ p z := (norm_rpow_hasFDerivAt_of_ne_zero _ z hz).differentiableAt
  have hq : DifferentiableAt ℝ q z := (norm_rpow_hasFDerivAt_of_ne_zero _ z hz).differentiableAt
  have hc : DifferentiableAt ℝ c z :=
    ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).differentiableAt).mul
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).differentiableAt
  have hprod : DifferentiableAt ℝ (fun x => c x * q x) z := by
    simpa only [Pi.mul_def] using hc.mul hq
  have hdiff : DifferentiableAt ℝ (fun x => d * p x - (n : ℝ) * (c x * q x)) z := by
    exact (hp.const_mul d).sub (hprod.const_mul n)
  have hδ : |d| ≤ 1 := by dsimp only [d]; split_ifs <;> norm_num
  have hpnorm : ‖fderiv ℝ p z‖ = (n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 1) := by
    rw [norm_rpow_fderiv_norm_of_ne_zero _ z hz, abs_neg,
      abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
  have hqnorm : ‖fderiv ℝ q z‖ = ((n : ℝ) + 2) * ‖z‖ ^ (-(n : ℝ) - 3) := by
    rw [norm_rpow_fderiv_norm_of_ne_zero _ z hz]
    rw [show -(n : ℝ) - 2 = -((n : ℝ) + 2) by ring, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 2),
      show -((n : ℝ) + 2) - 1 = -(n : ℝ) - 3 by ring]
  have hcnorm : ‖fderiv ℝ c z‖ ≤ 2 * ‖z‖ := coordinateProduct_fderiv_norm_le i j z
  have hcz : |c z| ≤ ‖z‖ ^ 2 := by
    dsimp only [c]
    rw [abs_mul, pow_two]
    apply mul_le_mul (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i)
      (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z j) (abs_nonneg _) (norm_nonneg _)
  have hS : 0 ≤ (euclideanSphereArea n)⁻¹ := inv_nonneg.mpr (euclideanSphereArea_pos hn).le
  have heq : (hessianKernelExpression i j : Domain n → ℝ) =
      fun x => (euclideanSphereArea n)⁻¹ * (d * p x - (n : ℝ) * (c x * q x)) := by
    funext x
    dsimp only [hessianKernelExpression, p, q, c, d]
    ring
  rw [heq, fderiv_const_mul hdiff,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hS]
  change (euclideanSphereArea n)⁻¹ * ‖fderiv ℝ
    ((fun x => d * p x) - (fun x => (n : ℝ) * (c x * q x))) z‖ ≤ _
  rw [fderiv_sub (hp.const_mul d) (hprod.const_mul n)]
  calc
    _ ≤ (euclideanSphereArea n)⁻¹ *
        (‖fderiv ℝ (fun x => d * p x) z‖ +
          ‖fderiv ℝ (fun x => (n : ℝ) * (c x * q x)) z‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hS
    _ = (euclideanSphereArea n)⁻¹ *
        (|d| * ‖fderiv ℝ p z‖ + (n : ℝ) * ‖fderiv ℝ (fun x => c x * q x) z‖) := by
      rw [fderiv_const_mul hp, fderiv_const_mul hprod, norm_smul, norm_smul,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
    _ ≤ (euclideanSphereArea n)⁻¹ *
        (‖fderiv ℝ p z‖ + (n : ℝ) *
          (|c z| * ‖fderiv ℝ q z‖ + |q z| * ‖fderiv ℝ c z‖)) := by
      apply mul_le_mul_of_nonneg_left _ hS
      apply add_le_add
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right hδ (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_left (scalarProduct_fderiv_norm_le hc hq) (Nat.cast_nonneg n)
    _ ≤ (euclideanSphereArea n)⁻¹ *
        ((n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 1) + (n : ℝ) *
          (‖z‖ ^ 2 * (((n : ℝ) + 2) * ‖z‖ ^ (-(n : ℝ) - 3)) +
            ‖z‖ ^ (-(n : ℝ) - 2) * (2 * ‖z‖))) := by
      rw [hpnorm, hqnorm]
      have hqz : |q z| = ‖z‖ ^ (-(n : ℝ) - 2) :=
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      rw [hqz]
      gcongr
    _ = _ := by
      have hpow₂ : ‖z‖ ^ 2 * ‖z‖ ^ (-(n : ℝ) - 3) = ‖z‖ ^ (-(n : ℝ) - 1) := by
        rw [← Real.rpow_two, ← Real.rpow_add (norm_pos_iff.mpr hz)]
        congr 1
        ring
      have hpow₁ : ‖z‖ ^ (-(n : ℝ) - 2) * ‖z‖ = ‖z‖ ^ (-(n : ℝ) - 1) := by
        rw [← Real.rpow_add_one (norm_ne_zero_iff.mpr hz)]
        congr 1
        ring
      calc
        _ = (euclideanSphereArea n)⁻¹ *
            ((n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 1) + (n : ℝ) *
              (((n : ℝ) + 2) * (‖z‖ ^ 2 * ‖z‖ ^ (-(n : ℝ) - 3)) +
                2 * (‖z‖ ^ (-(n : ℝ) - 2) * ‖z‖))) := by ring
        _ = _ := by rw [hpow₂, hpow₁]; ring

end HolderToCK
end
