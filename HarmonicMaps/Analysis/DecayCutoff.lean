module

public import HarmonicMaps.Analysis.DecayGoodShell
public import HarmonicMaps.Analysis.QuantitativeRadialCutoffGeometry

/-!
# Complete source cutoff on the energy-selected annulus

One fixed density defines the literal profile and radial cutoff. The same
uniform parameter and actual energy-selected shell produce every gluing
condition, including the sharp operator bound and both source energy bounds.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology BigOperators

namespace HarmonicMaps

/-- One fixed density, the uniform source scales, and an actual good shell
produce the complete literal gluing cutoff for every original source map. -/
theorem decay_cutoff_complete :
    ∃ b : ℝ → ℝ,
      ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ tsupport b ⊆ Ioo 0 1 ∧
      (∀ t, 0 ≤ b t ∧ b t ≤ 2) ∧ (∫ t, b t) = 1 ∧
      (let beta : ℝ → ℝ := fun t => 1 - ∫ y in Iic t, b y
       ContDiff ℝ ∞ beta ∧
       (∀ t, 0 ≤ beta t ∧ beta t ≤ 1) ∧
       (∀ t, t ≤ 0 → beta t = 1) ∧
       (∀ t, 1 ≤ t → beta t = 0) ∧
       (∀ t, HasDerivAt beta (-b t) t) ∧
       (∀ t, deriv beta t = -b t) ∧
       ∀ (n : ℕ) (_hn : 2 ≤ n) (C₀ ρ : ℝ),
         0 < C₀ → 0 < ρ →
         ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧
           ∀ η : ℝ, 0 < η → η ≤ η₀ →
           let hbar := η ^ (1 / 4 : ℝ)
           let delta := η ^ (1 / 8 : ℝ)
           let gamma := 1 / (64 * ((n : ℝ) - 1))
           let tau := η ^ gamma
           let p := ⌊tau / (3 * delta)⌋₊
           (0 < η ∧ η < 1 ∧ 0 < hbar ∧ 0 < delta ∧ 0 < tau ∧
             0 < gamma ∧ gamma < 1 / 8 ∧
             hbar = delta ^ 2 ∧ hbar ≤ delta ∧
             Real.sqrt (C₀ * η) < ρ ∧ hbar ≤ 1 / 4 ∧
             delta ≤ 1 / 8 ∧ 2 * delta ≤ 1 / 4 ∧
             2 * tau < 1 / 4 ∧ 2 ≤ tau / (3 * delta)) ∧
           2 ≤ p ∧ tau / (6 * delta) ≤ (p : ℝ) ∧
           ∀ (q : ℕ) (N : CompactSmoothEmbeddedTarget q)
             (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
             MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
             TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
             dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal η →
             ∃ j : ℕ, 1 ≤ j ∧ j ≤ p ∧
               let theta := tau + (3 * (j : ℝ) - 2) * delta
               let s : Domain n → ℝ := fun x => hbar * beta ((‖x‖ - theta) / delta)
               tau < theta ∧ theta < 2 * tau ∧ delta < theta ∧
               theta + 2 * delta ≤ 2 * tau ∧ theta + 2 * delta < 1 / 4 ∧
               (Metric.ball (0 : Domain n) (theta + 2 * delta) \
                 Metric.closedBall 0 (theta - delta)) =
                 {x : Domain n | tau + 3 * ((j : ℝ) - 1) * delta < ‖x‖ ∧
                   ‖x‖ < tau + 3 * (j : ℝ) * delta} ∧
               IntegrableOn (fun x => hsNormSq (Du x))
                 (Metric.ball (0 : Domain n) (theta + 2 * delta) \
                   Metric.closedBall 0 (theta - delta)) volume ∧
               (∫ x in Metric.ball (0 : Domain n) (theta + 2 * delta) \
                   Metric.closedBall 0 (theta - delta), hsNormSq (Du x)) ≤
                 (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal / (p : ℝ) ∧
               (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal / (p : ℝ) ≤
                 6 * delta / tau * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal ∧
               hbar ≤ delta ∧ 2 * hbar / delta = 2 * delta ∧ 2 * delta ≤ 1 / 4 ∧
               ContDiff ℝ ∞ s ∧ HasCompactSupport s ∧
               tsupport s ⊆ Metric.closedBall 0 (theta + delta) ∧
               (∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z) ∧
               (∀ x, 0 ≤ s x ∧ s x ≤ hbar) ∧
               (∀ x ∈ Metric.ball (0 : Domain n) theta, s x = hbar) ∧
               (∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0) ∧
               (∀ x, ‖fderiv ℝ s x‖ ≤ 2 * delta) ∧
               (∀ x, ‖fderiv ℝ s x‖ ≤ 1 / 4)) := by
  obtain ⟨b, hb, hc, hs, hv, hm, hbeta, hbetaRange, hbetaOne, hbetaZero,
    hbetaDeriv, hbetaActual, _⟩ := quantitativeRadialCutoff_exists
  refine ⟨b, hb, hc, hs, hv, hm, hbeta, hbetaRange, hbetaOne, hbetaZero,
    hbetaDeriv, hbetaActual, ?_⟩
  intro n hn C₀ ρ hC₀ hρ
  obtain ⟨η₀, hη₀, hη₀One, hShell⟩ := decay_good_shell n hn C₀ ρ hC₀ hρ
  refine ⟨η₀, hη₀, hη₀One, ?_⟩
  intro η hη hηSmall
  dsimp only
  obtain ⟨hG, hp, hPbound, hMaps⟩ := hShell η hη hηSmall
  have hGcopy := hG
  obtain ⟨_, _, _, hd, _, _, _, hSquare, hScale, _, _, _, hSmall, hTau, _⟩ := hGcopy
  refine ⟨hG, hp, hPbound, ?_⟩
  intro q N u Du hu hN hE
  obtain ⟨j, hj1, hjp, hTheta, hThetaUpper, hDeltaTheta, hOuter, hIdentity,
    hInt, hFirst, hSecond⟩ := hMaps q N u Du hu hN hE
  have hQuarter :
      η ^ (1 / (64 * ((n : ℝ) - 1))) + (3 * (j : ℝ) - 2) * η ^ (1 / 8 : ℝ) +
        2 * η ^ (1 / 8 : ℝ) < 1 / 4 := hOuter.trans_lt hTau
  have hHalf :
      η ^ (1 / (64 * ((n : ℝ) - 1))) + (3 * (j : ℝ) - 2) * η ^ (1 / 8 : ℝ) +
        2 * η ^ (1 / 8 : ℝ) < 1 / 2 := hQuarter.trans (by norm_num)
  have hL : 2 * η ^ (1 / 4 : ℝ) / η ^ (1 / 8 : ℝ) = 2 * η ^ (1 / 8 : ℝ) := by
    rw [hSquare]
    field_simp [hd.ne']
  obtain ⟨_, _, _, hSmooth, hCompact, hSupport, hRadial, hValues,
    hOn, hOff, hD, _⟩ := quantitativeRadialCutoff_sourceScale b hb hc hs hv hm n
      (η ^ (1 / (64 * ((n : ℝ) - 1))) + (3 * (j : ℝ) - 2) * η ^ (1 / 8 : ℝ))
      (η ^ (1 / 8 : ℝ)) hd hDeltaTheta hHalf hSmall
  refine ⟨j, hj1, hjp, hTheta, hThetaUpper, hDeltaTheta, hOuter, hQuarter,
    hIdentity, hInt, hFirst, hSecond, hScale, hL, hSmall, ?_⟩
  rw [hSquare]
  refine ⟨hSmooth, hCompact, hSupport, hRadial, hValues, hOn, hOff, ?_, ?_⟩
  · intro x
    have hx := hD x
    have hLeq : 2 * (η ^ (1 / 8 : ℝ)) ^ 2 / η ^ (1 / 8 : ℝ) =
        2 * η ^ (1 / 8 : ℝ) := by field_simp [hd.ne']
    rw [hLeq] at hx
    exact hx
  · intro x
    have hx := hD x
    have hLeq : 2 * (η ^ (1 / 8 : ℝ)) ^ 2 / η ^ (1 / 8 : ℝ) =
        2 * η ^ (1 / 8 : ℝ) := by field_simp [hd.ne']
    rw [hLeq] at hx
    exact hx.trans hSmall

end HarmonicMaps

end
