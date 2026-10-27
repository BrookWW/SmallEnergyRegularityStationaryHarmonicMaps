module

public import HolderToCK.Analysis.Poisson.PotentialHessianIntegrability
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Exact exterior radial powers for the far Holder estimate -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace HolderToCK

private theorem exteriorRadialPower_jacobian {n : ℕ} (hn : 0 < n)
    {η R : ℝ} {r : ℝ} (hr : 0 < r) :
    r ^ (n - 1) * (Ici R).indicator (fun t : ℝ => t ^ (η - (n : ℝ) - 1)) r =
      (Ici R).indicator (fun t : ℝ => t ^ (η - 2)) r := by
  by_cases hrR : r ∈ Ici R
  · rw [indicator_of_mem hrR, indicator_of_mem hrR, ← Real.rpow_natCast, ← Real.rpow_add hr]
    congr 1
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      simpa only [Nat.cast_one] using (Nat.cast_sub (by omega : 1 ≤ n) :
        ((n - 1 : ℕ) : ℝ) = (n : ℝ) - ((1 : ℕ) : ℝ))
    rw [hn1]
    ring
  · rw [indicator_of_notMem hrR, indicator_of_notMem hrR, mul_zero]

theorem radialExteriorPower_integrableOn {n : ℕ} (hn : 0 < n) {η R : ℝ}
    (hη : η < 1) (hR : 0 < R) :
    IntegrableOn (fun z : Domain n => ‖z‖ ^ (η - (n : ℝ) - 1))
      (Metric.ball (0 : Domain n) R)ᶜ volume := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let f : ℝ → ℝ := (Ici R).indicator (fun t => t ^ (η - (n : ℝ) - 1))
  have heq : (fun z : Domain n => f ‖z‖) =
      (Metric.ball (0 : Domain n) R)ᶜ.indicator
        (fun z : Domain n => ‖z‖ ^ (η - (n : ℝ) - 1)) := by
    funext z
    simp only [f, indicator, mem_Ici, mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt]
  rw [← integrable_indicator_iff measurableSet_ball.compl, ← heq,
    integrable_fun_norm_addHaar volume]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  have hi : IntegrableOn (fun r : ℝ => r ^ (η - 2)) (Ici R) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      (integrableOn_Ioi_rpow_of_lt (by linarith only [hη] : η - 2 < -1) hR)
  apply (hi.integrable_indicator measurableSet_Ici).integrableOn.congr_fun
    (fun r hr => (exteriorRadialPower_jacobian hn hr).symm) measurableSet_Ioi

theorem radialExteriorPower_integral {n : ℕ} (hn : 0 < n) {η R : ℝ}
    (hη : η < 1) (hR : 0 < R) :
    (∫ z in (Metric.ball (0 : Domain n) R)ᶜ, ‖z‖ ^ (η - (n : ℝ) - 1)) =
      euclideanSphereArea n * R ^ (η - 1) / (1 - η) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let f : ℝ → ℝ := (Ici R).indicator (fun t => t ^ (η - (n : ℝ) - 1))
  have heq : (fun z : Domain n => f ‖z‖) =
      (Metric.ball (0 : Domain n) R)ᶜ.indicator
        (fun z : Domain n => ‖z‖ ^ (η - (n : ℝ) - 1)) := by
    funext z
    simp only [f, indicator, mem_Ici, mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt]
  rw [← integral_indicator measurableSet_ball.compl, ← heq, integral_fun_norm_addHaar volume]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, ← euclideanSphereArea_eq]
  have hJac : (∫ r in Ioi (0 : ℝ), r ^ (n - 1) * f r) =
      ∫ r in Ioi (0 : ℝ), (Ici R).indicator (fun t : ℝ => t ^ (η - 2)) r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    exact exteriorRadialPower_jacobian hn hr
  rw [hJac, setIntegral_indicator measurableSet_Ici,
    inter_eq_right.mpr (show Ici R ⊆ Ioi (0 : ℝ) from fun _ hr => hR.trans_le hr),
    integral_Ici_eq_integral_Ioi,
    integral_Ioi_rpow_of_lt (by linarith only [hη] : η - 2 < -1) hR,
    show η - 2 + 1 = η - 1 by ring]
  have hinv : (η - 1)⁻¹ = -(1 - η)⁻¹ := by
    rw [show η - 1 = -(1 - η) by ring, inv_neg]
  simp only [div_eq_mul_inv]
  rw [hinv]
  ring

end HolderToCK
end
