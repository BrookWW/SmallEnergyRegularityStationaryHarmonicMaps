module

public import HarmonicMaps.Analysis.HarmonicReplacementEstimates
public import HarmonicMaps.Analysis.HarmonicProjectedEnergy
public import HarmonicMaps.Analysis.FixedSmoothing
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Complete projected harmonic replacement estimate

The literal fixed-scale smoothing, its actual tubular projection and the same
harmonic replacement give the source estimate on every ball of radius at most
one quarter. The coefficient precedes the small parameter, radius and map.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- The complete source harmonic replacement estimate for the actual projected
fixed-scale integral, with target-only projection families and uniform constants. -/
theorem harmonicReplacement_projectedEnergy :
    ∃ ρ : ∀ (q : ℕ), CompactSmoothEmbeddedTarget q → ℝ,
    ∃ Q : ∀ (q : ℕ), CompactSmoothEmbeddedTarget q → Ambient q → Ambient q,
    (∀ (q : ℕ) (N : CompactSmoothEmbeddedTarget q),
      0 < ρ q N ∧ ρ q N ≤ tubularBaseRadius q N ∧ ContDiff ℝ ∞ (Q q N) ∧
      ∀ z : tubularTube q N, Metric.infDist z.val N.carrierSet < ρ q N →
        Q q N z.val = (tubularProjection q N z).val) ∧
    ∀ (n : ℕ), 2 ≤ n →
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (q : ℕ) (N : CompactSmoothEmbeddedTarget q),
    ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ (η : ℝ), 0 < η → η < 1 → η ^ (1 / 4 : ℝ) ≤ 1 / 4 →
      Real.sqrt (C₀ * η) < ρ q N →
    ∀ (θ : ℝ), 0 < θ → θ ≤ 1 / 4 →
    ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
      TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
      IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du →
      dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal η →
    let m : Domain n → Ambient q := fun x =>
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - η ^ (1 / 4 : ℝ) • y)
    ContDiffOn ℝ ∞ m (Metric.ball (0 : Domain n) (3 / 4 : ℝ)) ∧
    ContDiffOn ℝ ∞ (Q q N ∘ m) (Metric.ball (0 : Domain n) (1 / 2 : ℝ)) ∧
    (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ),
      ∃ hx : m x ∈ tubularTube q N,
        Metric.infDist (m x) N.carrierSet < ρ q N ∧
        Q q N (m x) = (tubularProjection q N ⟨m x, hx⟩).val ∧
        Q q N (m x) ∈ N.carrierSet ∧ ‖fderiv ℝ (Q q N) (m x)‖ ≤ 2) ∧
    (∫ x in Metric.ball (0 : Domain n) θ,
      hsNormSq (fun i => fderiv ℝ (Q q N ∘ m) x (EuclideanSpace.single i 1))) ≤
      C₁ * (η ^ (1 / 4 : ℝ) + θ ^ n) *
        (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
  obtain ⟨ρ, Q, hfamily, hFixed⟩ := fixedSmoothing_complete
  refine ⟨ρ, Q, hfamily, ?_⟩
  intro n hn
  obtain ⟨C₀, A, hC₀, _, hFixedn⟩ := hFixed n hn
  refine ⟨C₀, hC₀, ?_⟩
  intro q N
  obtain ⟨C, hC, hEstimates⟩ := harmonicReplacement_estimates n hn q N
  let V : ℝ := (volume : Measure (Domain n)).real (Metric.ball (0 : Domain n) 1)
  let C₁ : ℝ := 8 * C * (1 + V)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hC₁ : 0 < C₁ := mul_pos (mul_pos (by norm_num) hC) (by linarith only [hV])
  have hfirst : 8 * C ≤ C₁ := by
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ 1 + V by linarith only [hV])
      (show 0 ≤ 8 * C by positivity)
    simpa only [mul_one] using h
  have hsecond : 8 * C * V ≤ C₁ :=
    mul_le_mul_of_nonneg_left (by linarith : V ≤ 1 + V) (by positivity)
  refine ⟨C₁, hC₁, ?_⟩
  intro η hη hηone hscale htube θ hθ hθquarter u Du hu hN hmin hsmall
  let m : Domain n → Ambient q := fun x =>
    ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (x - η ^ (1 / 4 : ℝ) • y)
  let E : ℝ := (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal
  have hE : 0 ≤ E := ENNReal.toReal_nonneg
  have hhbar : 0 ≤ η ^ (1 / 4 : ℝ) := (Real.rpow_pos_of_pos hη _).le
  have hθpow : 0 ≤ θ ^ n := pow_nonneg hθ.le n
  obtain ⟨hm, hpm, hpoint, _⟩ :=
    hFixedn q N η hη hηone hscale htube u Du hu hN hmin hsmall
  obtain ⟨w, _, _, _, hwW, _, _, _, _, _, _, hgrad, herror⟩ :=
    hEstimates η hη hscale u Du hu hN hmin hsmall
  have hD (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ)) :
      ‖fderiv ℝ (Q q N) (m x)‖ ≤ 2 := by
    obtain ⟨_, _, _, _, hd, _⟩ := hpoint x hx
    exact hd
  have hcomparison := harmonic_projectedEnergy_le (Q q N) (hfamily q N).2.2.1
    m w hm hwW hD θ hθ hθquarter (C * E) hgrad
  have hvolume : (volume : Measure (Domain n)).real (Metric.ball (0 : Domain n) θ) =
      θ ^ n * V := by
    rw [measureReal_def, Measure.addHaar_ball_of_pos volume 0 hθ, ENNReal.toReal_mul]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    rw [ENNReal.toReal_ofReal (pow_nonneg hθ.le n)]
    rfl
  refine ⟨hm, hpm, ?_, ?_⟩
  · intro x hx
    obtain ⟨ht, hdist, heq, htarget, hd, _⟩ := hpoint x hx
    exact ⟨ht, hdist, heq, htarget, hd⟩
  · calc
      _ ≤ 8 * (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
          hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1) -
            fderiv ℝ w x (EuclideanSpace.single i 1))) +
          8 * (C * E) * (volume : Measure (Domain n)).real
            (Metric.ball (0 : Domain n) θ) := hcomparison
      _ ≤ 8 * (C * η ^ (1 / 4 : ℝ) * E) +
          8 * (C * E) * (volume : Measure (Domain n)).real
            (Metric.ball (0 : Domain n) θ) :=
        add_le_add (mul_le_mul_of_nonneg_left herror
          (by norm_num : (0 : ℝ) ≤ 8)) le_rfl
      _ = (8 * C) * η ^ (1 / 4 : ℝ) * E + (8 * C * V) * θ ^ n * E := by
        rw [hvolume]
        ring
      _ ≤ C₁ * η ^ (1 / 4 : ℝ) * E + C₁ * θ ^ n * E :=
        add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfirst hhbar) hE)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsecond hθpow) hE)
      _ = _ := by ring

end HarmonicMaps
end
