module

public import HolderToCK
public import HolderToCK.Analysis.Poisson.ForcingLocalization
public import HolderToCK.Analysis.Poisson.InteriorPoissonRegularity
public import HolderToCK.Analysis.Poisson.PotentialRegularityBounds
public import HolderToCK.Analysis.Harmonic.UnitC2Bounds

/-! # Constant-coefficient weak Poisson interior Schauder estimates

The actual compact-data potential and the same smooth harmonic remainder
give the uniform second derivative bounds and full Holder exponent.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK.Providers.PoissonInteriorSchauder

theorem result
    (n q : ℕ) (hn : 2 ≤ n) (γ : ℝ) (hγ : 0 < γ) (hγOne : γ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q)
        (f : Domain n → Ambient q) (c : Ambient q) (M L H : ℝ),
        MemW12Loc (ballDomain (0 : Domain n) 1) v Dv →
        ContinuousOn v (Metric.ball (0 : Domain n) 1) →
        WeakPoissonOn (ballDomain (0 : Domain n) 1) Dv f →
        0 ≤ M → (∀ x ∈ Metric.ball (0 : Domain n) 1, ‖v x - c‖ ≤ M) →
        0 ≤ L → (∀ x ∈ Metric.ball (0 : Domain n) 1, ‖f x‖ ≤ L) →
        0 ≤ H → HolderBoundOn (Metric.ball (0 : Domain n) 1) f γ H →
        ContDiffOn ℝ 2 v (Metric.ball (0 : Domain n) (1 / 2)) ∧
        (∀ j : ℕ, j ≤ 2 → ∀ x ∈ Metric.ball (0 : Domain n) (1 / 2),
          ‖iteratedFDeriv ℝ j (fun y => v y - c) x‖ ≤ C * (M + L + H)) ∧
        HolderBoundOn (Metric.ball (0 : Domain n) (1 / 2))
          (iteratedFDeriv ℝ 2 v) γ (C * (M + L + H)) ∧
        ∀ x ∈ Metric.ball (0 : Domain n) (1 / 2), Laplacian.laplacian v x = f x := by
  obtain ⟨C_F, hC_F, hlocalize⟩ := schauderForcing_localization_bounds n γ hγ hγOne.le
  obtain ⟨C_H, hC_H, hharmonic⟩ := harmonic_unit_c2_bounds n hn γ hγ.le hγOne.le
  let V := potentialValueConstant n
  let C_P := potentialC2SupConstant n γ
  let C_J := (n : ℝ) * potentialHessianHolderConstant n γ
  have hV : 0 ≤ V := potentialValueConstant_nonneg n
  have hC_P : 0 ≤ C_P := potentialC2SupConstant_nonneg (by omega) hγ
  have hC_J : 0 ≤ C_J := mul_nonneg (Nat.cast_nonneg n)
    (potentialHessianHolderConstant_nonneg (by omega) hγ hγOne)
  let C := 1 + C_H * (1 + V) + (C_P + C_J) * (1 + C_F)
  have hC : 0 ≤ C := by positivity
  have hCoefNorm : C_H * (1 + V) + C_P * (1 + C_F) ≤ C := by
    have hterm : 0 ≤ C_J * (1 + C_F) := by positivity
    dsimp only [C]
    nlinarith only [hterm]
  have hCoefHolder : C_H * (1 + V) + C_J * C_F ≤ C := by
    have hterm : 0 ≤ C_P * (1 + C_F) := by positivity
    dsimp only [C]
    nlinarith only [hterm, hC_J]
  refine ⟨C, hC, ?_⟩
  intro v Dv f c M L H hv hcont hEq hM hvBound hL hfBound hH hfHolder
  let T : ℝ := M + L + H
  have hT : 0 ≤ T := by positivity
  have hMT : M ≤ T := by dsimp only [T]; linarith only [hL, hH]
  have hLT : L ≤ T := by dsimp only [T]; linarith only [hM, hH]
  have hLHT : L + H ≤ T := by dsimp only [T]; linarith only [hM]
  let G := C_F * (L + H)
  have hG : 0 ≤ G := mul_nonneg hC_F (add_nonneg hL hH)
  have hGT : G ≤ C_F * T := mul_le_mul_of_nonneg_left hLHT hC_F
  obtain ⟨hcg, hSupp, hgBound, hgHolder, _⟩ := hlocalize q f L H hL hH hfBound hfHolder
  let g := schauderForcing f
  let P := newtonianPotential hn g
  have hP : ContDiff ℝ 2 P := newtonianPotential_holder_contDiff_two hn hγ hG hgHolder hcg
  obtain ⟨hPBound, hPHolder⟩ := newtonianPotential_holder_unitData_derivative_bounds hn hγ hγOne
    hG hL hgHolder hcg (hSupp.trans (Metric.closedBall_subset_closedBall (by norm_num))) hgBound
  obtain ⟨hv2, hvLap⟩ := weak_poisson_holder_contDiffOn_two hn hγ hγOne.le
    hv hcont hEq hL hfBound hH hfHolder
  obtain ⟨hr, hrLap⟩ := weak_poisson_holder_newtonian_remainder hn hγ hγOne.le
    hv hcont hEq hL hfBound hH hfHolder
  let r := v - P
  let h : Domain n → Ambient q := fun x => r x - c
  have hh : ContDiffOn ℝ ∞ h (Metric.ball (0 : Domain n) (5 / 8)) := hr.sub contDiffOn_const
  have hhLap : ∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), Laplacian.laplacian h x = 0 := by
    intro x hx
    have hrAt := hr.contDiffAt (Metric.isOpen_ball.mem_nhds hx)
    have heq := (hrAt.of_le (WithTop.coe_le_coe.mpr le_top)).laplacian_sub
      (f₂ := fun _ => c) contDiffAt_const
    change Laplacian.laplacian ((v - newtonianPotential hn (schauderForcing f)) -
      (fun _ : Domain n => c)) x = 0
    rw [heq, hrLap x hx, InnerProductSpace.laplacian_const, Pi.zero_apply, sub_zero]
  let A : ℝ := M + V * L
  have hA : 0 ≤ A := by positivity
  have hAT : A ≤ (1 + V) * T := by
    calc
      _ ≤ T + V * T := add_le_add hMT (mul_le_mul_of_nonneg_left hLT hV)
      _ = _ := by ring
  have hPT : L + G ≤ (1 + C_F) * T := by
    calc
      _ ≤ T + C_F * T := add_le_add hLT hGT
      _ = _ := by ring
  have hhBound : ∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ‖h x‖ ≤ A := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := by
      have hnrm : ‖x‖ < 5 / 8 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      linarith only [hnrm]
    have hPv : ‖P x‖ ≤ V * L := newtonianPotential_unitData_norm_bound hn
      (continuousOn_univ.mp (hgHolder.continuousOn hγ)) hcg
      (hSupp.trans (Metric.closedBall_subset_closedBall (by norm_num))) hL hgBound hx1
    have heq : h x = (v x - c) - P x := by dsimp only [h, r, Pi.sub_apply]; abel
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add
      (hvBound x (Metric.ball_subset_ball (by norm_num : (5 / 8 : ℝ) ≤ 1) hx)) hPv)
  obtain ⟨hhSup, hhHolder⟩ := hharmonic q h A hA hh hhLap hhBound
  have hhalf : Metric.ball (0 : Domain n) (1 / 2) ⊆ Metric.ball (0 : Domain n) (5 / 8) :=
    Metric.ball_subset_ball (by norm_num)
  have hsum (j : ℕ) (hj : j ≤ 2) (x : Domain n)
      (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2)) :
      iteratedFDeriv ℝ j (fun y => v y - c) x =
        iteratedFDeriv ℝ j h x + iteratedFDeriv ℝ j P x := by
    have heq : (fun y => v y - c) = h + P := by
      funext y
      dsimp only [h, r, Pi.add_apply, Pi.sub_apply]
      abel
    rw [heq]
    exact iteratedFDeriv_add_apply
      ((hh.contDiffAt (Metric.isOpen_ball.mem_nhds (hhalf hx))).of_le
        (WithTop.coe_le_coe.mpr (show (j : ℕ∞) ≤ ⊤ from le_top)))
      (hP.contDiffAt.of_le (by exact_mod_cast hj))
  have hSupCoef : C_H * A + C_P * (L + G) ≤ C * T := by
    calc
      _ ≤ C_H * ((1 + V) * T) + C_P * ((1 + C_F) * T) :=
        add_le_add (mul_le_mul_of_nonneg_left hAT hC_H)
          (mul_le_mul_of_nonneg_left hPT hC_P)
      _ = (C_H * (1 + V) + C_P * (1 + C_F)) * T := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCoefNorm hT
  have hHolderCoef : C_H * A + C_J * G ≤ C * T := by
    calc
      _ ≤ C_H * ((1 + V) * T) + C_J * (C_F * T) :=
        add_le_add (mul_le_mul_of_nonneg_left hAT hC_H)
          (mul_le_mul_of_nonneg_left hGT hC_J)
      _ = (C_H * (1 + V) + C_J * C_F) * T := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCoefHolder hT
  have hcenter (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2)) :
      iteratedFDeriv ℝ 2 (fun y => v y - c) x = iteratedFDeriv ℝ 2 v x := by
    rw [fun_iteratedFDeriv_sub_apply
      (hv2.contDiffAt (Metric.isOpen_ball.mem_nhds (hhalf hx))) contDiffAt_const,
      iteratedFDeriv_const_of_ne two_ne_zero, Pi.zero_apply, sub_zero]
  refine ⟨hv2.mono hhalf, ?_, ?_, fun x hx => hvLap x (hhalf hx)⟩
  · intro j hj x hx
    rw [hsum j hj x hx]
    have hx1 : ‖x‖ ≤ 1 := by
      have hnrm : ‖x‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      linarith only [hnrm]
    exact ((norm_add_le _ _).trans (add_le_add (hhSup j hj x hx)
      (hPBound j hj x hx1))).trans hSupCoef
  · intro x hx y hy
    rw [← hcenter x hx, ← hcenter y hy, hsum 2 le_rfl x hx, hsum 2 le_rfl y hy]
    have heq : (iteratedFDeriv ℝ 2 h x + iteratedFDeriv ℝ 2 P x) -
        (iteratedFDeriv ℝ 2 h y + iteratedFDeriv ℝ 2 P y) =
        (iteratedFDeriv ℝ 2 h x - iteratedFDeriv ℝ 2 h y) +
          (iteratedFDeriv ℝ 2 P x - iteratedFDeriv ℝ 2 P y) := by abel
    rw [heq]
    calc
      _ ≤ ‖iteratedFDeriv ℝ 2 h x - iteratedFDeriv ℝ 2 h y‖ +
          ‖iteratedFDeriv ℝ 2 P x - iteratedFDeriv ℝ 2 P y‖ := norm_add_le _ _
      _ ≤ (C_H * A) * (dist x y) ^ γ + (C_J * G) * (dist x y) ^ γ :=
        add_le_add (hhHolder x hx y hy) (hPHolder x (mem_univ _) y (mem_univ _))
      _ = (C_H * A + C_J * G) * (dist x y) ^ γ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hHolderCoef (Real.rpow_nonneg dist_nonneg _)

end HolderToCK.Providers.PoissonInteriorSchauder
end
