module

public import StationaryHarmonicMaps.Analysis.LinearDirichletLocalization
public import StationaryHarmonicMaps.Analysis.BoundaryHarmonicGradient

/-! # Actual boundary decay for zero-boundary linear flux solutions

The restricted original forcing has a genuine zero-boundary response.
The same residual has zero forcing on the query ball, so its actual odd
Kelvin harmonic graph supplies the boundary decay. The original fields
and the original truncated energies occur in the resulting estimate.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

private theorem integral_zeroExtension_hsNormSq_ball {n q : ℕ}
    (D : Domain n → Gradient n q) (a : Domain n) (r : ℝ) :
    (∫ x in Metric.ball a r,hsNormSq (fun i =>
      (Metric.ball (0 : Domain n) 1).indicator (fun y => D y i) x))=
      ∫ x in Metric.ball a r∩Metric.ball (0 : Domain n) 1,hsNormSq (D x) := by
  classical
  have hPoint : (fun x => hsNormSq (fun i =>
      (Metric.ball (0 : Domain n) 1).indicator (fun y => D y i) x))=
      (Metric.ball (0 : Domain n) 1).indicator (fun x => hsNormSq (D x)) := by
    funext x
    by_cases hx : x∈Metric.ball (0 : Domain n) 1
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,hsNormSq,norm_zero,
        zero_pow (by decide : (2 : ℕ)≠0),Finset.sum_const_zero]
  rw [hPoint,setIntegral_indicator measurableSet_ball]

/-- Actual original zero-boundary linear data give same-query boundary decay with dimension-only constants. -/
theorem exists_linear_flux_boundary_energy_decay (n : ℕ) (hn : 2≤n) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (f : Domain n → Ambient q)
      (Df F : Domain n → Gradient n q),
      HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) f Df →
      (∀ i,MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) →
      HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
        (fun x i => Df x i+F x i) (fun _ => (0 : Ambient q)) →
      ∀ (a : Domain n),‖a‖=1 → ∀ (r : ℝ),0<r → r≤1 →
      ∀ (θ : ℝ),0<θ → θ≤1/2 →
        (∫ x in Metric.ball a (θ*r)∩Metric.ball (0 : Domain n) 1,hsNormSq (Df x))≤
          C*θ^n*(∫ x in Metric.ball a r∩Metric.ball (0 : Domain n) 1,hsNormSq (Df x))+
            C*(∫ x in Metric.ball a r∩Metric.ball (0 : Domain n) 1,hsNormSq (F x)) := by
  obtain ⟨C₀,hC₀,hBoundary⟩ := exists_boundary_offSupport_gradient_energy_decay n hn
  let C := 4*C₀+2
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro q f Df F hf hF hEquation a ha r hr hrOne θ hθ hθHalf
  obtain ⟨w,Dw,hw,hwEnergy,_hwEq,hh,hG,hHEq,hZero,hHLocal⟩ :=
    exists_localized_dirichlet_forcing_split (by omega : 1≤n) f Df F hf hF hEquation a r
  let Dh := fun x i => Df x i-Dw x i
  let G := fun x i => (Metric.ball a r).indicator F x i-F x i
  have hZeroAE : G =ᵐ[volume.restrict (Metric.ball (0 : Domain n) 1∩Metric.ball a r)]
      (fun _ => (0 : Gradient n q)) := by
    filter_upwards [ae_restrict_mem (measurableSet_ball.inter measurableSet_ball)] with x hx
    exact hZero x hx.2
  have hDecay := hBoundary q a ha r hr hrOne (f-w) Dh G hh hG hHEq hZeroAE θ hθ hθHalf
  rw [integral_zeroExtension_hsNormSq_ball,integral_zeroExtension_hsNormSq_ball] at hDecay
  let S := Metric.ball a (θ*r)∩Metric.ball (0 : Domain n) 1
  let T := Metric.ball a r∩Metric.ball (0 : Domain n) 1
  have hDfI : IntegrableOn (fun x => hsNormSq (Df x)) S volume :=
    hf.1.integrable_hsNormSq.mono_set inter_subset_right
  have hDhI : IntegrableOn (fun x => hsNormSq (Dh x)) S volume :=
    hh.1.integrable_hsNormSq.mono_set inter_subset_right
  have hDwI : IntegrableOn (fun x => hsNormSq (Dw x)) S volume :=
    hw.1.integrable_hsNormSq.mono_set inter_subset_right
  have hPoint (x : Domain n) : hsNormSq (Df x)≤2*hsNormSq (Dh x)+2*hsNormSq (Dw x) := by
    have HC (i : Fin n) : ‖Df x i‖^2≤2*‖Dh x i‖^2+2*‖Dw x i‖^2 := by
      have H : Df x i=Dh x i+Dw x i := by dsimp only [Dh];abel
      rw [H,norm_add_sq_real]
      nlinarith only [real_inner_le_norm (Dh x i) (Dw x i),sq_nonneg (‖Dh x i‖-‖Dw x i‖)]
    calc
      _ ≤ ∑ i : Fin n,(2*‖Dh x i‖^2+2*‖Dw x i‖^2) := Finset.sum_le_sum fun i _ => HC i
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.mul_sum,hsNormSq]
  have hWLocal : (∫ x in S,hsNormSq (Dw x))≤∫ x in T,hsNormSq (F x) :=
    (setIntegral_mono_set hw.1.integrable_hsNormSq
      (Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Eventually.of_forall fun _ hx => hx.2)).trans hwEnergy
  have hFirst : (∫ x in S,hsNormSq (Df x))≤
      2*(∫ x in S,hsNormSq (Dh x))+2*(∫ x in T,hsNormSq (F x)) := by
    calc
      _ ≤ ∫ x in S,2*hsNormSq (Dh x)+2*hsNormSq (Dw x) :=
        integral_mono hDfI ((hDhI.const_mul 2).add (hDwI.const_mul 2)) hPoint
      _ = 2*(∫ x in S,hsNormSq (Dh x))+2*(∫ x in S,hsNormSq (Dw x)) := by
        rw [integral_add (hDhI.const_mul 2) (hDwI.const_mul 2),integral_const_mul,integral_const_mul]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hWLocal (by norm_num))
  have hθPower : θ^n≤1 := pow_le_one₀ hθ.le (by linarith only [hθHalf])
  have hEf : 0≤∫ x in T,hsNormSq (Df x) := integral_nonneg fun _ => hsNormSq_nonneg _
  have hEF : 0≤∫ x in T,hsNormSq (F x) := integral_nonneg fun _ => hsNormSq_nonneg _
  calc
    _ ≤ 2*(C₀*θ^n*(∫ x in T,hsNormSq (Dh x)))+
        2*(∫ x in T,hsNormSq (F x)) :=
      hFirst.trans (add_le_add (mul_le_mul_of_nonneg_left hDecay (by norm_num)) le_rfl)
    _ ≤ 2*(C₀*θ^n*(2*(∫ x in T,hsNormSq (Df x))+2*(∫ x in T,hsNormSq (F x))))+
        2*(∫ x in T,hsNormSq (F x)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hHLocal (by positivity)) (by norm_num)) le_rfl
    _ ≤ _ := by
      have Hθ := mul_le_mul_of_nonneg_right hθPower (mul_nonneg hC₀.le hEF)
      dsimp only [C]
      nlinarith only [Hθ,mul_nonneg (pow_nonneg hθ.le n) hEf]

end StationaryHarmonicMaps.Analysis
end
