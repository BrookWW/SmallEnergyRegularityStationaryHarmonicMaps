module

public import HarmonicMaps.Analysis.IterationScales
public import HarmonicMaps.Analysis.AffineMinimizerTransport
public import HarmonicMaps.Analysis.Monotonicity
public import HarmonicMaps.Frozen.OneStepEnergyDecay

/-!
# Discrete and all-radius normalized-energy decay

One fixed witness pair from the one-step energy decay theorem applies on every
compactly contained ball through genuine affine minimizer transport. Induction
preserves its small-energy threshold and gives the dyadic bound. Native
monotonicity and the literal source logarithmic exponent fill all inner radii.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps

private theorem affine_normalized_energy {n q : ℕ} (a : Domain n)
    (s tau : PositiveRadius) (Du : Domain n → Gradient n q) :
    normalizedEnergy (fun z i => s.val • Du (a + s.val • z) i) (0 : Domain n) tau =
      normalizedEnergy Du a ⟨tau.val * s.val, mul_pos tau.property s.property⟩ := by
  have hEnergy := dirichletEnergy_affineBall a (0 : Domain n) s.property
    (tau.val * s.val) Du
  have hRatio : tau.val * s.val / s.val = tau.val := mul_div_cancel_right₀ _ s.property.ne'
  rw [hRatio] at hEnergy
  simp only [sub_zero] at hEnergy
  rw [normalizedEnergy, normalizedEnergy, hEnergy, ← mul_assoc,
    ← ENNReal.ofReal_mul (zpow_pos tau.property _).le, ← mul_zpow]

private theorem source_decay_on_ball {n q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (ε : ℝ) (tau : PositiveRadius)
    (hDecay : ∀ (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
      MemW12Loc (ballDomain (0 : Domain n) 1) v Dv →
      TakesValuesIn N (ballDomain (0 : Domain n) 1) v →
      IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) v Dv →
      dirichletEnergy Dv (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal ε →
      normalizedEnergy Dv (0 : Domain n) tau ≤
        (1 / 2 : ℝ≥0∞) * dirichletEnergy Dv (Metric.ball (0 : Domain n) 1))
    (Ω : OpenDomain n) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc Ω u Du) (hN : TakesValuesIn N Ω u)
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (a : Domain n) (s : PositiveRadius)
    (hclosed : Metric.closedBall a s.val ⊆ Ω.val)
    (hsmall : normalizedEnergy Du a s ≤ ENNReal.ofReal ε) :
    normalizedEnergy Du a ⟨tau.val * s.val, mul_pos tau.property s.property⟩ ≤
      (1 / 2 : ℝ≥0∞) * normalizedEnergy Du a s := by
  obtain ⟨hv, hNv, hMinV, hEnergy⟩ :=
    affineBall_minimizer_transport N Ω a s u Du hclosed hu hN hmin
  have hSmallV : dirichletEnergy (fun z i => s.val • Du (a + s.val • z) i)
      (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal ε := hEnergy.trans_le hsmall
  have hStep := hDecay _ _ hv hNv hMinV hSmallV
  rw [affine_normalized_energy a s tau Du, hEnergy] at hStep
  exact hStep

/-- One source witness pair and its literal logarithmic exponent give every
discrete iterate, threshold preservation and the coefficient-two all-radius
estimate from only the original locally minimizing Sobolev data. -/
theorem energyIteration_complete (n : ℕ) (hn : 2 ≤ n)
    (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ε : ℝ, ∃ tau : PositiveRadius, 0 < ε ∧ tau.val < 1 / 8 ∧
    let alpha := Real.log 2 / (2 * Real.log (1 / tau.val))
    0 < alpha ∧ alpha < 1 ∧ tau.val ^ (2 * alpha) = 1 / 2 ∧
    ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      MemW12Loc Ω u Du → TakesValuesIn N Ω u → IsLocallyEnergyMinimizing N Ω u Du →
    ∀ (a : Domain n) (s : PositiveRadius),
      Metric.closedBall a s.val ⊆ Ω.val → normalizedEnergy Du a s ≤ ENNReal.ofReal ε →
      (∀ k : ℕ,
        let r : PositiveRadius := ⟨tau.val ^ k * s.val, mul_pos (pow_pos tau.property k) s.property⟩
        normalizedEnergy Du a r ≤ (1 / 2 : ℝ≥0∞) ^ k * normalizedEnergy Du a s ∧
        normalizedEnergy Du a r ≤ ENNReal.ofReal ε) ∧
      ∀ r : PositiveRadius, r.val ≤ s.val →
        normalizedEnergy Du a r ≤
          ENNReal.ofReal (2 * (r.val / s.val) ^ (2 * alpha)) * normalizedEnergy Du a s := by
  obtain ⟨ε, tau, hε, hTau, hDecay⟩ := oneStepEnergyDecay hn N
  obtain ⟨hAlpha, hAlphaOne, hPower, hBracket⟩ := iteration_scale_properties tau hTau
  refine ⟨ε, tau, hε, hTau, hAlpha, hAlphaOne, hPower, ?_⟩
  intro Ω u Du hu hN hmin a s hclosed hsmall
  let R : ℕ → PositiveRadius := fun k =>
    ⟨tau.val ^ k * s.val, mul_pos (pow_pos tau.property k) s.property⟩
  have hTauOne : tau.val ≤ 1 := (hTau.trans (by norm_num)).le
  have hRle (k : ℕ) : (R k).val ≤ s.val := by
    change tau.val ^ k * s.val ≤ s.val
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ tau.property.le hTauOne) s.property.le).trans_eq
      (one_mul _)
  have hClosedR (k : ℕ) : Metric.closedBall a (R k).val ⊆ Ω.val :=
    (Metric.closedBall_subset_closedBall (hRle k)).trans hclosed
  have hDiscrete (k : ℕ) : normalizedEnergy Du a (R k) ≤
      (1 / 2 : ℝ≥0∞) ^ k * normalizedEnergy Du a s ∧
      normalizedEnergy Du a (R k) ≤ ENNReal.ofReal ε := by
    induction k with
    | zero =>
      have hR0 : R 0 = s := Subtype.ext (by dsimp only [R]; rw [pow_zero, one_mul])
      rw [hR0, pow_zero, one_mul]
      exact ⟨le_rfl, hsmall⟩
    | succ k ih =>
      have hStep := source_decay_on_ball N ε tau hDecay Ω u Du hu hN hmin a (R k)
        (hClosedR k) ih.2
      have hRadius : (⟨tau.val * (R k).val, mul_pos tau.property (R k).property⟩ : PositiveRadius) =
          R (k + 1) := by
        apply Subtype.ext
        dsimp only [R]
        rw [pow_succ]
        ring
      rw [hRadius] at hStep
      have hDyadic : normalizedEnergy Du a (R (k + 1)) ≤
          (1 / 2 : ℝ≥0∞) ^ (k + 1) * normalizedEnergy Du a s := by
        calc
          _ ≤ (1 / 2 : ℝ≥0∞) * normalizedEnergy Du a (R k) := hStep
          _ ≤ (1 / 2 : ℝ≥0∞) * ((1 / 2 : ℝ≥0∞) ^ k * normalizedEnergy Du a s) :=
            mul_le_mul_right ih.1 _
          _ = _ := by rw [pow_succ]; ac_rfl
      have hPreserve : normalizedEnergy Du a (R (k + 1)) ≤ ENNReal.ofReal ε :=
        hStep.trans (((mul_le_mul_left (by norm_num : (1 / 2 : ℝ≥0∞) ≤ 1)
          (normalizedEnergy Du a (R k))).trans_eq (one_mul _)).trans ih.2)
      exact ⟨hDyadic, hPreserve⟩
  refine ⟨hDiscrete, ?_⟩
  intro r hrs
  obtain ⟨k, _hLower, hUpper, hCoefficient⟩ := hBracket r s hrs
  have hMono := hmin.normalizedEnergy_monotoneOn hn hu hN s.property hclosed
  have hOrder : normalizedEnergy Du a r ≤ normalizedEnergy Du a (R k) :=
    hMono hrs (hRle k) hUpper
  have hCoefficientENN : (1 / 2 : ℝ≥0∞) ^ k ≤
      ENNReal.ofReal (2 * (r.val / s.val) ^
        (2 * (Real.log 2 / (2 * Real.log (1 / tau.val))))) := by
    have hHalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [← hHalf, ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact ENNReal.ofReal_le_ofReal hCoefficient
  exact hOrder.trans ((hDiscrete k).1.trans
    (mul_le_mul_left hCoefficientENN (normalizedEnergy Du a s)))

end HarmonicMaps
end
