module

public import StationaryHarmonicMaps.Analysis.LinearBoundaryEnergyDecay
public import StationaryHarmonicMaps.Analysis.LinearInteriorPowerGrowth

/-! # Boundary-centered real-power growth for actual linear Dirichlet data

The original forcing's uniform real-power growth controls externally centered
query energies through the proved doubled-ball argument. The original
unweighted solution energy is then iterated at boundary centers.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

/-- Actual zero-boundary linear data and their original total-energy bound give dimension-and-exponent real-power growth at every unit-sphere center. -/
theorem exists_linear_flux_boundary_real_power_growth (n : ℕ) (hn : 2≤n)
    (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (f : Domain n → Ambient q)
      (Df F : Domain n → Gradient n q) (K : ℝ),
      HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) f Df →
      (∀ i,MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) →
      0≤K →
      (∀ (a : Domain n),a∈Metric.ball (0 : Domain n) 1 → ∀ r : ℝ,0<r →
        (∫ x in Metric.ball a r∩Metric.ball (0 : Domain n) 1,hsNormSq (F x))≤K*r^ν) →
      (∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (Df x))≤K →
      HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
        (fun x i => Df x i+F x i) (fun _ => (0 : Ambient q)) →
      ∀ (a : Domain n),‖a‖=1 → ∀ (r : ℝ),0<r → r≤1 →
        (∫ x in Metric.ball a r∩Metric.ball (0 : Domain n) 1,hsNormSq (Df x))≤C*K*r^ν := by
  obtain ⟨D,hD,hDecay⟩ := exists_linear_flux_boundary_energy_decay n hn
  obtain ⟨θ,hθ,hθHalf,hScale⟩ := exists_scale_absorbing_higher_power
    (C := D) (p := (n : ℝ)) (β := ν) hD hνn
  have hθOne : θ<1 := by linarith
  have hScaleN : D*θ^n≤(1/2 : ℝ)*θ^ν := by
    simpa only [Real.rpow_natCast] using hScale
  let ρ := D*θ^n
  have hρ : 0≤ρ := by dsimp only [ρ];positivity
  have hgap : ρ<θ^ν := lt_of_le_of_lt hScaleN (by nlinarith only [Real.rpow_pos_of_pos hθ ν])
  let C₀ := (1+D*(2 : ℝ)^ν/(θ^ν-ρ))/θ^ν
  let C := 1+C₀
  have hC₀ : 0≤C₀ := by dsimp only [C₀];positivity
  have hC : 0<C := by dsimp only [C];positivity
  have hOneC : 1≤C := by dsimp only [C];linarith
  refine ⟨C,hC,?_⟩
  intro q f Df F K hf hF hK hGrowth hEnergy hEquation a ha r hr hrOne
  let E := fun s : ℝ => ∫ x in Metric.ball a s∩Metric.ball (0 : Domain n) 1,hsNormSq (Df x)
  have hMono (s t : ℝ) (_hs : 0<s) (hst : s≤t) (_ht : t≤1) : E s≤E t :=
    setIntegral_mono_set (hf.1.integrable_hsNormSq.mono_set inter_subset_right)
      (Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Eventually.of_forall fun _ hx => ⟨Metric.ball_subset_ball hst hx.1,hx.2⟩)
  have hFull (s : ℝ) : E s≤K :=
    (setIntegral_mono_set hf.1.integrable_hsNormSq
      (Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Eventually.of_forall fun _ hx => hx.2)).trans hEnergy
  by_cases hZero : ν=0
  · have H : E r≤C*K := (hFull r).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hOneC hK)
    simpa only [hZero,Real.rpow_zero,mul_one,one_mul,E] using H
  · have hStep (s : ℝ) (hs : 0<s) (hsOne : s≤1) :
        E (θ*s)≤ρ*E s+(D*(2 : ℝ)^ν*K)*s^ν := by
      have hForceN := integral_hsNormSq_inter_le_of_uniform_power_growth F
        (Metric.ball (0 : Domain n) 1) hF K ν hK hGrowth a hs
      have H := hDecay q f Df F hf hF hEquation a ha s hs hsOne θ hθ hθHalf
      calc
        _ ≤ ρ*E s+D*(∫ x in Metric.ball a s∩Metric.ball (0 : Domain n) 1,hsNormSq (F x)) := H
        _ ≤ ρ*E s+D*((2 : ℝ)^ν*K*s^ν) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hForceN hD.le)
        _ = _ := by ring
    have hBase : E 1≤K*(1 : ℝ)^ν := by simpa only [Real.one_rpow,mul_one] using hFull 1
    have H := all_radius_rpow_bound_of_recurrence E hν hθ hθOne hρ hgap
      (show 0≤D*(2 : ℝ)^ν*K by positivity) hK (by norm_num : (0 : ℝ)<1)
      hMono hBase hStep r hr hrOne
    have hForm : ((K+D*(2 : ℝ)^ν*K/(θ^ν-ρ))/θ^ν)=C₀*K := by
      dsimp only [C₀];ring
    rw [hForm] at H
    exact H.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show C₀≤C by dsimp only [C];linarith) hK)
      (Real.rpow_nonneg hr.le ν))

end StationaryHarmonicMaps.Analysis
end
