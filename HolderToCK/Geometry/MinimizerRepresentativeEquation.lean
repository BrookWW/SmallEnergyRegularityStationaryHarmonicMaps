module

public import HolderToCK.Analysis.LocalHolder
public import HolderToCK.Geometry.ProjectionCoefficients

/-! # The same enlarged-ball representative and quadratic equation

The original minimizing-map data supply one continuous target-valued map,
the original weak gradient, and the actual signed projection equation.
All constants and the smooth coefficient are fixed before the map.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff

namespace HolderToCK

theorem smallEnergy_enlarged_holder_quadratic_equation {n q : ℕ}
    (hn : 2 ≤ n) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ε α L K : ℝ,
      ∃ A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q,
        0 < ε ∧ 0 < α ∧ α < 1 ∧ 0 < L ∧ 0 < K ∧ ContDiff ℝ ∞ A ∧
        ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
          MemW12Loc Ω u Du → TakesValuesIn N Ω u → IsLocallyEnergyMinimizing N Ω u Du →
          Metric.closedBall (0 : Domain n) 1 ⊆ Ω.val →
          (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x)) ≤ ε →
          ∃ w F : Domain n → Ambient q,
            ContinuousOn w (Metric.ball (0 : Domain n) (3 / 4)) ∧
            w =ᵐ[volume.restrict (Metric.ball (0 : Domain n) (3 / 4))] u ∧
            (∀ x ∈ Metric.ball (0 : Domain n) (3 / 4), w x ∈ N.carrierSet) ∧
            HolderBoundOn (Metric.ball (0 : Domain n) (3 / 4)) w α
              (L * Real.sqrt (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x))) ∧
            MemW12 (ballDomain (0 : Domain n) (3 / 4)) w Du ∧
            ((∫ x in Metric.ball (0 : Domain n) (3 / 4), hsNormSq (Du x)) ≤
              ∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x)) ∧
            WeakPoissonOn (ballDomain (0 : Domain n) (3 / 4)) Du F ∧
            (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) (3 / 4)),
              F x = ∑ i : Fin n, A (w x) (Du x i) (Du x i)) ∧
            (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) (3 / 4)),
              ‖F x‖ ≤ K * hsNormSq (Du x)) := by
  obtain ⟨ε, α, L, hε, hα, hαone, hL, hHolder⟩ := smallEnergy_enlarged_holder_representative hn N
  obtain ⟨A, hA, K, hK, _, hEquation⟩ := minimizer_projection_quadratic_weakPoisson N
  refine ⟨ε, α, L, K, A, hε, hα, hαone, hL, hK, hA, ?_⟩
  intro Ω u Du hu huN hmin hclosed henergy
  obtain ⟨w, hwcont, hwAE, hwN, hwHolder, _, _, hwEnergy⟩ :=
    hHolder Ω u Du hu huN hmin hclosed henergy
  obtain ⟨F, hEq, hFormula, hBound⟩ := hEquation n hn Ω u Du hu huN hmin
  have hsub : (ballDomain (0 : Domain n) (3 / 4)).val ⊆ Ω.val :=
    (Metric.ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 1)).trans
      (Metric.ball_subset_closedBall.trans hclosed)
  have hsmallClosed : Metric.closedBall (0 : Domain n) (3 / 4) ⊆ Ω.val :=
    (Metric.closedBall_subset_closedBall (by norm_num : (3 / 4 : ℝ) ≤ 1)).trans hclosed
  have hwW := (hu.memW12_ball hsmallClosed).congr_ae hwAE.symm (Filter.EventuallyEq.refl _ _)
  refine ⟨w, F, hwcont, hwAE, hwN, hwHolder, hwW, hwEnergy, hEq.mono hsub, ?_,
    ae_restrict_of_ae_restrict_of_subset hsub hBound⟩
  have hFormulaSmall := ae_restrict_of_ae_restrict_of_subset hsub hFormula
  filter_upwards [hFormulaSmall, hwAE] with x hx hxw
  rw [hxw]
  exact hx

end HolderToCK
end
