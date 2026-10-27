module

public import HolderToCK.Analysis.Bootstrap.NestedBalls
public import HolderToCK.Analysis.Bootstrap.NestedRadii

/-! # Uniform quantitative bootstrapping on the fixed nested balls

The constants are selected before the map and its small parameter. At index
`k`, the same map has derivatives through order `k + 1` on `nestedRadius k`.
Restriction to the half ball gives smoothness and estimates at every order.
-/

public section

open HarmonicMaps Set
open scoped ContDiff NNReal

namespace HolderToCK

theorem quadratic_poisson_nested_bootstrap (n q : ℕ) (hn : 2 ≤ n)
    (γ : ℝ) (hγ : 0 < γ) (hγOne : γ < 1)
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    (hA : ContDiff ℝ ∞ A) (c : Ambient q) (R M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℕ → ℝ≥0, C 0 = ⟨M, hM⟩ ∧ Monotone C ∧
      ∀ (u : Domain n → Ambient q) (δ : ℝ), 0 ≤ δ → δ ≤ 1 →
      ContDiffOn ℝ 1 u (Metric.ball (0 : Domain n) (5 / 8)) →
      MapsTo u (Metric.ball (0 : Domain n) (5 / 8)) (Metric.closedBall c R) →
      WeakPoissonOn (ballDomain (0 : Domain n) (5 / 8))
        (fun x i => fderiv ℝ u x (EuclideanSpace.single i 1)) (classicalQuadraticForcing A u) →
      (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ‖u x - u 0‖ ≤ M * δ) →
      (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ‖iteratedFDeriv ℝ 1 u x‖ ≤ M * δ) →
      HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
        (iteratedFDeriv ℝ 1 u) γ (M * δ) →
      ∀ k : ℕ,
        ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) u (Metric.ball (0 : Domain n) (nestedRadius k)) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) (nestedRadius k),
          ‖u x - u 0‖ ≤ (C k : ℝ) * δ) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) (nestedRadius k), ∀ j : ℕ,
          1 ≤ j → j ≤ k + 1 → ‖iteratedFDeriv ℝ j u x‖ ≤ (C k : ℝ) * δ) ∧
        HolderBoundOn (Metric.ball (0 : Domain n) (nestedRadius k))
          (iteratedFDeriv ℝ (k + 1) u) γ ((C k : ℝ) * δ) := by
  classical
  let step (k : ℕ) (T : ℝ≥0) :=
    quadratic_poisson_nested_step n q (k + 1) hn (by omega) γ hγ hγOne A hA c R
      (nestedRadius (k + 1)) (nestedRadius k) T
      (nestedRadius_pos (k + 1)) (nestedRadius_succ_lt k) T.property
  let next (k : ℕ) (T : ℝ≥0) : ℝ≥0 :=
    ⟨Classical.choose (step k T), (Classical.choose_spec (step k T)).1⟩
  let C : ℕ → ℝ≥0 := Nat.rec ⟨M, hM⟩ next
  have hCmono : Monotone C := by
    apply monotone_nat_of_le_succ
    intro k
    apply NNReal.coe_le_coe.mp
    exact (Classical.choose_spec (step k (C k))).2.1
  refine ⟨C, rfl, hCmono, ?_⟩
  intro u δ hδ hδOne hu hRange hEq hzero hderiv hHolder k
  have hsub (k : ℕ) : Metric.ball (0 : Domain n) (nestedRadius k) ⊆
      Metric.ball (0 : Domain n) (5 / 8) :=
    Metric.ball_subset_ball (nestedRadius_le_fiveEighths k)
  induction k with
  | zero =>
      rw [nestedRadius_zero]
      refine ⟨hu, hzero, ?_, hHolder⟩
      intro x hx j hj hjOne
      have hjEq : j = 1 := by omega
      subst j
      exact hderiv x hx
  | succ k ih =>
      obtain ⟨huK, hzeroK, hderivK, hHolderK⟩ := ih
      have hEqK : WeakPoissonOn (ballDomain (0 : Domain n) (nestedRadius k))
          (fun x i => fderiv ℝ u x (EuclideanSpace.single i 1))
          (classicalQuadraticForcing A u) := hEq.mono (hsub k)
      exact (Classical.choose_spec (step k (C k))).2.2 u δ hδ hδOne huK
        (hRange.mono (hsub k) (Subset.refl _)) hEqK hzeroK hderivK hHolderK

theorem quadratic_poisson_smooth_halfBall (n q : ℕ) (hn : 2 ≤ n)
    (γ : ℝ) (hγ : 0 < γ) (hγOne : γ < 1)
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    (hA : ContDiff ℝ ∞ A) (c : Ambient q) (R M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℕ → ℝ≥0, C 0 = ⟨M, hM⟩ ∧ Monotone C ∧
      ∀ (u : Domain n → Ambient q) (δ : ℝ), 0 ≤ δ → δ ≤ 1 →
      ContDiffOn ℝ 1 u (Metric.ball (0 : Domain n) (5 / 8)) →
      MapsTo u (Metric.ball (0 : Domain n) (5 / 8)) (Metric.closedBall c R) →
      WeakPoissonOn (ballDomain (0 : Domain n) (5 / 8))
        (fun x i => fderiv ℝ u x (EuclideanSpace.single i 1)) (classicalQuadraticForcing A u) →
      (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ‖u x - u 0‖ ≤ M * δ) →
      (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ‖iteratedFDeriv ℝ 1 u x‖ ≤ M * δ) →
      HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
        (iteratedFDeriv ℝ 1 u) γ (M * δ) →
      ContDiffOn ℝ ∞ u (Metric.ball (0 : Domain n) (1 / 2)) ∧
      (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2), ‖u x - u 0‖ ≤ (C 0 : ℝ) * δ) ∧
      (∀ j : ℕ, 1 ≤ j → ∀ x ∈ Metric.ball (0 : Domain n) (1 / 2),
        ‖iteratedFDeriv ℝ j u x‖ ≤ (C j : ℝ) * δ) ∧
      ∀ j : ℕ, 1 ≤ j → HolderBoundOn (Metric.ball (0 : Domain n) (1 / 2))
        (iteratedFDeriv ℝ j u) γ ((C j : ℝ) * δ) := by
  obtain ⟨B, hBzero, hBmono, hboot⟩ :=
    quadratic_poisson_nested_bootstrap n q hn γ hγ hγOne A hA c R M hM
  let C : ℕ → ℝ≥0 := fun j => B (j - 1)
  have hCzero : C 0 = ⟨M, hM⟩ := hBzero
  have hCmono : Monotone C := fun i j hij => hBmono (Nat.sub_le_sub_right hij 1)
  refine ⟨C, hCzero, hCmono, ?_⟩
  intro u δ hδ hδOne hu hRange hEq hzero hderiv hHolder
  have horder (k : ℕ) := hboot u δ hδ hδOne hu hRange hEq hzero hderiv hHolder k
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply contDiffOn_infty.mpr
    intro k
    exact ((horder k).1.mono (halfBall_subset_nestedBall k)).of_le
      (by exact_mod_cast Nat.le_succ k)
  · intro x hx
    exact (horder 0).2.1 x (halfBall_subset_nestedBall 0 hx)
  · intro j hj x hx
    have hpred : j - 1 + 1 = j := Nat.sub_add_cancel hj
    exact (horder (j - 1)).2.2.1 x (halfBall_subset_nestedBall (j - 1) hx) j hj hpred.ge
  · intro j hj
    have hpred : j - 1 + 1 = j := Nat.sub_add_cancel hj
    have h := (horder (j - 1)).2.2.2.mono (halfBall_subset_nestedBall (j - 1))
    rw [hpred] at h
    exact h

end HolderToCK
end
