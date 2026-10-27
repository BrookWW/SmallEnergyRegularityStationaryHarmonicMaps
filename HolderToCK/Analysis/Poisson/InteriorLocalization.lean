/- Copyright (c) 2026. All rights reserved. -/
module

public import HolderToCK.Frozen.PoissonInteriorSchauder
public import HolderToCK.Analysis.Poisson.InteriorLocalizationBoundsNested

/-! # Interior Poisson Schauder estimates on arbitrary and nested balls

The unit estimate applies to the actual affine pullback of local Sobolev and
weak Poisson data. Inverse differentiation gives the exact radius powers;
uniform local estimates give the full Holder exponent between nested balls.
-/

public section

open HarmonicMaps Set
open scoped ContDiff

namespace HolderToCK

theorem poissonInteriorSchauder_ball
    (n q : ℕ) (hn : 2 ≤ n) (γ : ℝ) (hγ : 0 < γ) (hγOne : γ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : Domain n) (R : PositiveRadius)
        (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q)
        (f : Domain n → Ambient q) (c : Ambient q) (M L H : ℝ),
        MemW12Loc (ballDomain a R.val) v Dv →
        ContinuousOn v (Metric.ball a R.val) →
        WeakPoissonOn (ballDomain a R.val) Dv f →
        0 ≤ M → (∀ x ∈ Metric.ball a R.val, ‖v x - c‖ ≤ M) →
        0 ≤ L → (∀ x ∈ Metric.ball a R.val, ‖f x‖ ≤ L) →
        0 ≤ H → HolderBoundOn (Metric.ball a R.val) f γ H →
        ContDiffOn ℝ 2 v (Metric.ball a (R.val / 2)) ∧
        (∀ j : ℕ, j ≤ 2 → ∀ x ∈ Metric.ball a (R.val / 2),
          ‖iteratedFDeriv ℝ j (fun y => v y - c) x‖ ≤
            C * Real.rpow R.val (-(j : ℝ)) *
              (M + R.val ^ 2 * L + Real.rpow R.val (2 + γ) * H)) ∧
        HolderBoundOn (Metric.ball a (R.val / 2)) (iteratedFDeriv ℝ 2 v) γ
          (C * Real.rpow R.val (-(2 + γ)) *
            (M + R.val ^ 2 * L + Real.rpow R.val (2 + γ) * H)) ∧
        ∀ x ∈ Metric.ball a (R.val / 2), Laplacian.laplacian v x = f x := by
  obtain ⟨C, hC, hunit⟩ := poissonInteriorSchauder n q hn γ hγ hγOne
  refine ⟨C, hC, ?_⟩
  intro a R v Dv f c M L H hv hcont hEq hM hvBound hL hfBound hH hfHolder
  have hmap := affine_unit_mapsTo a R
  have hvScaled := HolderToCK.MemW12Loc.affineBall_pullback_local hv
    (0 : Domain n) R.property
  have hEqScaled := hEq.affineBall_pullback_local (0 : Domain n) R.property
  have hcontScaled : ContinuousOn (fun z => v (a + R.val • z))
      (Metric.ball (0 : Domain n) 1) := by
    have haff : Continuous (fun z : Domain n => a + R.val • z) := by fun_prop
    exact hcont.comp haff.continuousOn hmap
  have hvScaledBound : ∀ z ∈ Metric.ball (0 : Domain n) 1,
      ‖v (a + R.val • z) - c‖ ≤ M := fun z hz => hvBound _ (hmap hz)
  have hfScaledBound : ∀ z ∈ Metric.ball (0 : Domain n) 1,
      ‖R.val ^ 2 • f (a + R.val • z)‖ ≤ R.val ^ 2 * L := by
    intro z hz
    rw [norm_smul, Real.norm_of_nonneg (sq_nonneg R.val)]
    exact mul_le_mul_of_nonneg_left (hfBound _ (hmap hz)) (sq_nonneg R.val)
  obtain ⟨hv2, hsup, hhessian, _⟩ := hunit
    (fun z => v (a + R.val • z))
    (fun z i => R.val • Dv (a + R.val • z) i)
    (fun z => R.val ^ 2 • f (a + R.val • z)) c M
    (R.val ^ 2 * L) (Real.rpow R.val (2 + γ) * H)
    (by simpa only [div_self R.property.ne', sub_zero] using hvScaled)
    hcontScaled
    (by simpa only [div_self R.property.ne', sub_zero] using hEqScaled)
    hM hvScaledBound (mul_nonneg (sq_nonneg R.val) hL) hfScaledBound
    (mul_nonneg (Real.rpow_nonneg R.property.le _) hH)
    (affine_unit_forcing_holderBound a R hfHolder)
  have hback := affine_unit_contDiffOn a R hv2
  have hsub : Metric.ball a (R.val / 2) ⊆ Metric.ball a R.val :=
    Metric.ball_subset_ball (by linarith only [R.property])
  refine ⟨hback, ?_, ?_, ?_⟩
  · intro j hj x hx
    have h := affine_unit_iteratedFDeriv_norm_bound a R c j (hsup j hj) x hx
    exact h.trans_eq (by ring)
  · have h := affine_unit_hessian_holderBound a R hhessian
    convert h using 1
    ring
  · have hEqHalf : WeakPoissonOn (ballDomain a (R.val / 2)) Dv f := hEq.mono hsub
    have hWeakHalf : HasWeakGradient (ballDomain a (R.val / 2)) v Dv := hv.1.mono hsub
    exact hEqHalf.laplacian_eq_of_contDiffOn_two hWeakHalf hback
      ((hfHolder.continuousOn hγ).mono hsub)

theorem poissonInteriorSchauder_nested
    (n q : ℕ) (hn : 2 ≤ n) (γ : ℝ) (hγ : 0 < γ) (hγOne : γ < 1)
    (s t : ℝ) (_hs : 0 < s) (hst : s < t) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q)
        (f : Domain n → Ambient q) (c : Ambient q) (M L H : ℝ),
        MemW12Loc (ballDomain (0 : Domain n) t) v Dv →
        ContinuousOn v (Metric.ball (0 : Domain n) t) →
        WeakPoissonOn (ballDomain (0 : Domain n) t) Dv f →
        0 ≤ M → (∀ x ∈ Metric.ball (0 : Domain n) t, ‖v x - c‖ ≤ M) →
        0 ≤ L → (∀ x ∈ Metric.ball (0 : Domain n) t, ‖f x‖ ≤ L) →
        0 ≤ H → HolderBoundOn (Metric.ball (0 : Domain n) t) f γ H →
        ContDiffOn ℝ 2 v (Metric.ball (0 : Domain n) s) ∧
        (∀ j : ℕ, j ≤ 2 → ∀ x ∈ Metric.ball (0 : Domain n) s,
          ‖iteratedFDeriv ℝ j (fun y => v y - c) x‖ ≤ C * (M + L + H)) ∧
        HolderBoundOn (Metric.ball (0 : Domain n) s) (iteratedFDeriv ℝ 2 v) γ
          (C * (M + L + H)) ∧
        ∀ x ∈ Metric.ball (0 : Domain n) s, Laplacian.laplacian v x = f x := by
  obtain ⟨C₀, hC₀, hball⟩ := poissonInteriorSchauder_ball n q hn γ hγ hγOne
  let r : PositiveRadius := ⟨(t - s) / 2, by linarith only [hst]⟩
  let P : ℝ := 1 + r.val ^ 2 + Real.rpow r.val (2 + γ)
  let J : ℝ := 1 + Real.rpow r.val (-1) + Real.rpow r.val (-2)
  let K : ℝ := C₀ * P * J
  let A : ℝ := C₀ * P * Real.rpow r.val (-(2 + γ))
  let C : ℝ := K + (A + 2 * K / Real.rpow ((t - s) / 8) γ)
  have hr : 0 < r.val := r.property
  have hP : 0 ≤ P := add_nonneg (add_nonneg zero_le_one (sq_nonneg r.val))
    (Real.rpow_nonneg hr.le _)
  have hJ : 0 ≤ J := add_nonneg
    (add_nonneg zero_le_one (Real.rpow_nonneg hr.le _)) (Real.rpow_nonneg hr.le _)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC₀ hP) hJ
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hC₀ hP) (Real.rpow_nonneg hr.le _)
  have hgap : 0 < (t - s) / 8 := by linarith only [hst]
  have hpow : 0 < Real.rpow ((t - s) / 8) γ := Real.rpow_pos_of_pos hgap γ
  have hfar : 0 ≤ 2 * K / Real.rpow ((t - s) / 8) γ := by positivity
  have hC : 0 ≤ C := by positivity
  have hKC : K ≤ C := by dsimp only [C]; linarith only [hA, hfar]
  have hAC : A + 2 * K / Real.rpow ((t - s) / 8) γ ≤ C := by
    exact le_add_of_nonneg_left hK
  refine ⟨C, hC, ?_⟩
  intro v Dv f c M L H hv hcont hEq hM hvBound hL hfBound hH hfHolder
  let T : ℝ := M + L + H
  have hT : 0 ≤ T := by positivity
  have hamp : M + r.val ^ 2 * L + Real.rpow r.val (2 + γ) * H ≤ P * T :=
    poisson_affine_amplitude_le r.property.le hM hL hH
  have hhalf : 0 < r.val / 2 := div_pos r.property (by norm_num)
  have hlocal (b : Domain n) (hb : b ∈ Metric.ball (0 : Domain n) s) := by
    have hsub : Metric.ball b r.val ⊆ Metric.ball (0 : Domain n) t := by
      exact nested_center_ball_subset hst hb
    exact hball b r v Dv f c M L H (hv.mono hsub) (hcont.mono hsub)
      (hEq.mono hsub) hM (fun x hx => hvBound x (hsub hx))
      hL (fun x hx => hfBound x (hsub hx)) hH (hfHolder.mono hsub)
  have hv2 : ContDiffOn ℝ 2 v (Metric.ball (0 : Domain n) s) := by
    intro x hx
    exact ((hlocal x hx).1.contDiffAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hhalf))).contDiffWithinAt
  have hsup : ∀ j : ℕ, j ≤ 2 → ∀ x ∈ Metric.ball (0 : Domain n) s,
      ‖iteratedFDeriv ℝ j (fun y => v y - c) x‖ ≤ K * T := by
    intro j hj x hx
    have h := (hlocal x hx).2.1 j hj x (Metric.mem_ball_self hhalf)
    have hscale : Real.rpow r.val (-(j : ℝ)) ≤ J :=
      poisson_affine_derivative_scale_le r.property j hj
    have hcoef : 0 ≤ C₀ * Real.rpow r.val (-(j : ℝ)) :=
      mul_nonneg hC₀ (Real.rpow_nonneg hr.le _)
    calc
      _ ≤ C₀ * Real.rpow r.val (-(j : ℝ)) *
          (M + r.val ^ 2 * L + Real.rpow r.val (2 + γ) * H) := h
      _ ≤ C₀ * Real.rpow r.val (-(j : ℝ)) * (P * T) :=
        mul_le_mul_of_nonneg_left hamp hcoef
      _ = C₀ * P * Real.rpow r.val (-(j : ℝ)) * T := by ring
      _ ≤ C₀ * P * J * T := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscale (mul_nonneg hC₀ hP)) hT
  have hlocalHolder : ∀ x ∈ Metric.ball (0 : Domain n) s,
      HolderBoundOn (Metric.ball x ((t - s) / 4)) (iteratedFDeriv ℝ 2 v) γ (A * T) := by
    intro x hx
    have hcoef : 0 ≤ C₀ * Real.rpow r.val (-(2 + γ)) :=
      mul_nonneg hC₀ (Real.rpow_nonneg hr.le _)
    have hbound : C₀ * Real.rpow r.val (-(2 + γ)) *
        (M + r.val ^ 2 * L + Real.rpow r.val (2 + γ) * H) ≤ A * T := by
      calc
        _ ≤ C₀ * Real.rpow r.val (-(2 + γ)) * (P * T) :=
          mul_le_mul_of_nonneg_left hamp hcoef
        _ = _ := by dsimp only [A]; ring
    have h := ((hlocal x hx).2.2.1).mono_const hbound
    have hradius : r.val / 2 = (t - s) / 4 := by dsimp only [r]; ring
    simpa only [hradius] using h
  have hhessianSup : ∀ x ∈ Metric.ball (0 : Domain n) s,
      ‖iteratedFDeriv ℝ 2 v x‖ ≤ K * T := by
    intro x hx
    have hcenter : iteratedFDeriv ℝ 2 (fun y => v y - c) x =
        iteratedFDeriv ℝ 2 v x := by
      rw [fun_iteratedFDeriv_sub_apply
        (hv2.contDiffAt (Metric.isOpen_ball.mem_nhds hx)) contDiffAt_const,
        iteratedFDeriv_const_of_ne two_ne_zero, Pi.zero_apply, sub_zero]
    rw [← hcenter]
    exact hsup 2 le_rfl x hx
  have hhessian := nested_holderBoundOn_of_local_and_sup hst hγ.le
    (mul_nonneg hA hT) (mul_nonneg hK hT) hlocalHolder hhessianSup
  have hHolderCoef : A * T + 2 * (K * T) / Real.rpow ((t - s) / 8) γ ≤ C * T := by
    calc
      _ = (A + 2 * K / Real.rpow ((t - s) / 8) γ) * T := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hAC hT
  refine ⟨hv2, ?_, hhessian.mono_const hHolderCoef, ?_⟩
  · intro j hj x hx
    exact (hsup j hj x hx).trans (mul_le_mul_of_nonneg_right hKC hT)
  · intro x hx
    exact (hlocal x hx).2.2.2 x (Metric.mem_ball_self hhalf)

end HolderToCK
end
