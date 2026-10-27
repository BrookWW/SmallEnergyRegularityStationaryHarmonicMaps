module

public import HolderToCK.Analysis.WeakPoissonLocalization
import HolderToCK.Analysis.QuadraticPoissonC1

/-! # Local first derivatives of a Holder quadratic Poisson solution

A compact inner image bounds the smooth quadratic coefficient. Shrinking the
source ball makes its affine Holder coefficient smaller than the unit-ball
threshold. The actual scaled map, weak gradient, and forcing satisfy every
unit-ball premise, and inverse affine transport gives first derivatives and
their Holder estimates for the original map.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff ENNReal

namespace HolderToCK

/-- A finite Holder ball gives a smaller ball with the first derivative estimates
of the same quadratic weak Poisson map. -/
theorem holder_quadratic_poisson_small_ball_first_derivative {n q : ℕ}
    (hn : 2 ≤ n) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    (hA : ContDiff ℝ ∞ A) (hu : MemW12Loc Ω u Du)
    (hEquation : WeakPoissonOn Ω Du
      (fun x => ∑ i : Fin n, A (u x) (Du x i) (Du x i)))
    (a : Domain n) (R : PositiveRadius)
    (hclosed : Metric.closedBall a R.val ⊆ Ω.val)
    {α H : ℝ} (hα : 0 < α) (hαOne : α < 1) (hH : 0 ≤ H)
    (hHolder : HolderBoundOn (Metric.ball a R.val) u α H) :
    ∃ ρ : PositiveRadius, ρ.val ≤ R.val / 2 ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ContDiffOn ℝ 1 u (Metric.ball a (ρ.val / 2)) ∧
        (∀ x ∈ Metric.ball a (ρ.val / 2),
          ‖fderiv ℝ u x‖ ≤ Real.rpow ρ.val (-1) *
            (C * Real.sqrt (normalizedEnergy Du a ρ).toReal)) ∧
        HolderBoundOn (Metric.ball a (ρ.val / 2)) (fderiv ℝ u) (α / 8)
          ((C * Real.sqrt (normalizedEnergy Du a ρ).toReal) *
            Real.rpow ρ.val (-(1 + α / 8))) := by
  obtain ⟨_, _, _, K, hK, _, _, _, _, hQuadratic⟩ :=
    holder_ball_compact_coefficient_data a R A hA hα hH hHolder
  obtain ⟨H₀, C, hH₀, hC, hC1⟩ :=
    small_holder_quadratic_poisson_unit_first_derivative n q hn α K hα hαOne hK.le
  obtain ⟨ρ, hρhalf, hSmall⟩ := exists_holder_small_scale hα hH hH₀ R
  have hρR : ρ.val ≤ R.val := hρhalf.trans (by linarith only [R.property])
  have hclosedρ : Metric.closedBall a ρ.val ⊆ Ω.val :=
    (Metric.closedBall_subset_closedBall hρR).trans hclosed
  have hballρ : Metric.ball a ρ.val ⊆ Ω.val :=
    Metric.ball_subset_closedBall.trans hclosedρ
  have huρ : MemW12 (ballDomain a ρ.val) u Du := hu.memW12_ball hclosedρ
  have hEqρ : WeakPoissonOn (ballDomain a ρ.val) Du
      (fun x => ∑ i : Fin n, A (u x) (Du x i) (Du x i)) :=
    hEquation.mono hballρ
  have hHolderρ : HolderBoundOn (Metric.ball a ρ.val) u α H :=
    hHolder.mono (Metric.ball_subset_ball hρR)
  have hBoundρ : ∀ᵐ x ∂volume.restrict (Metric.ball a ρ.val),
      ‖∑ i : Fin n, A (u x) (Du x i) (Du x i)‖ ≤ K * hsNormSq (Du x) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hQuadratic Du x ((Metric.closedBall_subset_closedBall hρhalf)
      (Metric.ball_subset_closedBall hx))
  obtain ⟨huScale, hEqScale, hHolderScale, hBoundScale⟩ :=
    quadratic_poisson_affine_unit_data a ρ huρ hEqρ hHolderρ hBoundρ
  obtain ⟨hSmoothScale, hNormScale, hDerivativeHolderScale⟩ :=
    hC1 (fun z => u (a + ρ.val • z)) (fun z i => ρ.val • Du (a + ρ.val • z) i)
      (fun z => ρ.val ^ 2 • (∑ i : Fin n,
        A (u (a + ρ.val • z)) (Du (a + ρ.val • z) i) (Du (a + ρ.val • z) i)))
      (H * Real.rpow ρ.val α) huScale
      (mul_nonneg hH (Real.rpow_nonneg ρ.property.le _)) hSmall
      hHolderScale hEqScale hBoundScale
  rw [affineBall_unit_energy a ρ Du] at hNormScale hDerivativeHolderScale
  have hReturn := fderiv_bounds_of_affine_pullback a ρ hSmoothScale
    hNormScale hDerivativeHolderScale
  have hRadius : ρ.val * (1 / 2 : ℝ) = ρ.val / 2 := by ring
  rw [hRadius] at hReturn
  exact ⟨ρ, hρhalf, C, hC, hReturn⟩

/-- The original function has a first derivative and a finite local Holder bound
for that derivative at every point of the source domain. -/
theorem locally_holder_quadratic_poisson_first_derivative {n q : ℕ}
    (hn : 2 ≤ n) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    (hA : ContDiff ℝ ∞ A) (hu : MemW12Loc Ω u Du)
    (hHolder : LocallyHolderOn Ω u)
    (hEquation : WeakPoissonOn Ω Du
      (fun x => ∑ i : Fin n, A (u x) (Du x i) (Du x i))) :
    ContDiffOn ℝ 1 u Ω.val ∧ LocallyHolderOn Ω (fderiv ℝ u) := by
  have hLocal : ∀ a ∈ Ω.val, ∃ r : PositiveRadius,
      Metric.closedBall a r.val ⊆ Ω.val ∧
      ContDiffOn ℝ 1 u (Metric.ball a r.val) ∧
      ∃ γ B : ℝ, 0 < γ ∧ γ < 1 ∧ 0 ≤ B ∧
        HolderBoundOn (Metric.ball a r.val) (fderiv ℝ u) γ B := by
    intro a ha
    obtain ⟨R, hclosed, α, H, hα, hαOne, hH, hHolderBall⟩ := hHolder a ha
    obtain ⟨ρ, hρhalf, C, hC, hSmooth, _, hDerivativeHolder⟩ :=
      holder_quadratic_poisson_small_ball_first_derivative hn Ω u Du A hA hu hEquation
        a R hclosed hα hαOne hH hHolderBall
    let r : PositiveRadius := ⟨ρ.val / 2, half_pos ρ.property⟩
    have hrR : r.val ≤ R.val := by
      dsimp only [r]
      linarith only [hρhalf, ρ.property, R.property]
    refine ⟨r, (Metric.closedBall_subset_closedBall hrR).trans hclosed, hSmooth,
      α / 8, (C * Real.sqrt (normalizedEnergy Du a ρ).toReal) *
        Real.rpow ρ.val (-(1 + α / 8)), ?_, ?_, ?_, hDerivativeHolder⟩
    · linarith only [hα]
    · linarith only [hαOne]
    · exact mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _))
        (Real.rpow_nonneg ρ.property.le _)
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨r, _, hSmooth, _⟩ := hLocal a ha
    exact (hSmooth.contDiffAt (Metric.ball_mem_nhds a r.property)).contDiffWithinAt
  · intro a ha
    obtain ⟨r, hclosed, _, hData⟩ := hLocal a ha
    exact ⟨r, hclosed, hData⟩

end HolderToCK
end
