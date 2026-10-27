module

public import HolderToCK.Analysis.GradientExcessDecay
public import HolderToCK.Analysis.Campanato.GradientRepresentative
public import HolderToCK.Analysis.ContinuousWeakDerivative

/-! # Classical first derivatives of the same quadratic weak Poisson map

The original gradient excess produces continuous representatives of its actual
columns. Almost-everywhere congruence identifies those columns with the native
weak gradient of the same Holder function. Mollification then gives its
classical derivative and the quantitative operator-norm and Holder bounds.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace HolderToCK

theorem small_holder_quadratic_poisson_first_derivative
    (n q : ℕ) (hn : 2 ≤ n) (α K : ℝ)
    (hα : 0 < α) (hαOne : α < 1) (hK : 0 ≤ K) :
    ∃ H₀ C : ℝ, 0 < H₀ ∧ 0 ≤ C ∧
      ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
        (F : Domain n → Ambient q) (H : ℝ),
        MemW12 (ballDomain (0 : Domain n) (3 / 4 : ℝ)) u Du →
        0 ≤ H → H ≤ H₀ →
        HolderBoundOn (Metric.ball (0 : Domain n) (3 / 4 : ℝ)) u α H →
        WeakPoissonOn (ballDomain (0 : Domain n) (3 / 4 : ℝ)) Du F →
        (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) (3 / 4 : ℝ)),
          ‖F x‖ ≤ K * hsNormSq (Du x)) →
        ContDiffOn ℝ 1 u (Metric.ball (0 : Domain n) (5 / 8 : ℝ)) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8 : ℝ),
          ‖fderiv ℝ u x‖ ≤ C *
            Real.sqrt (dirichletEnergy Du (Metric.ball (0 : Domain n) (3 / 4 : ℝ))).toReal) ∧
        HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8 : ℝ)) (fderiv ℝ u)
          (α / 8) (C *
            Real.sqrt (dirichletEnergy Du (Metric.ball (0 : Domain n) (3 / 4 : ℝ))).toReal) := by
  obtain ⟨H₀, _, C_Φ, hH₀, _, _, hC_Φ, hDecay⟩ :=
    uniform_energy_growth_and_gradient_excess_decay n hn α K hα hαOne hK
  let γ : ℝ := α / 8
  have hγ : 0 < γ := by dsimp only [γ]; linarith only [hα]
  have hγOne : γ < 1 := by dsimp only [γ]; linarith only [hαOne]
  have hr₀ : 0 < growthReferenceRadius := by norm_num [growthReferenceRadius]
  have hr₀small : growthReferenceRadius ≤ 1 / 8 := by norm_num [growthReferenceRadius]
  obtain ⟨C_G, hC_G, hReconstruct⟩ := campanato_gradient_columns_representative
    n γ growthReferenceRadius C_Φ hγ hγOne hr₀ hr₀small hC_Φ.le
  let C : ℝ := Real.sqrt (n : ℝ) * C_G
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) hC_G.le
  refine ⟨H₀, C, hH₀, hC, ?_⟩
  intro u Du F H hu hH hHH hHolder hEq hBound
  let E : ℝ := ∫ x in Metric.ball (0 : Domain n) (3 / 4 : ℝ), hsNormSq (Du x)
  have hE : 0 ≤ E := integral_nonneg (fun _ => hsNormSq_nonneg _)
  have hExcess : ∀ x ∈ Metric.ball (0 : Domain n) (5 / 8 : ℝ),
      ∀ r : ℝ, 0 < r → r ≤ growthReferenceRadius →
        (∫ y in Metric.ball x r, hsNormSq (fun i => Du y i - ⨍ z in Metric.ball x r, Du z i)) ≤
          C_Φ * E * Real.rpow r ((n : ℝ) + 2 * γ) := by
    intro x hx r hr hrr₀
    have h := (hDecay q u F Du H hu hEq hH hHH hHolder hBound x hx r hr hrr₀).2
    have hexp : gradientExcessExponent n α = (n : ℝ) + 2 * γ := by
      dsimp only [gradientExcessExponent, γ]
      ring
    rwa [hexp] at h
  obtain ⟨G, _, hGAE, hGsup, hGHolder, _⟩ :=
    hReconstruct q Du E hu.2.2 hE le_rfl hExcess
  let Ω : OpenDomain n := ballDomain (0 : Domain n) (5 / 8 : ℝ)
  have huInner : MemW12 Ω u Du :=
    hu.to_memW12Loc.memW12_ball (Metric.closedBall_subset_ball (by norm_num : (5 / 8 : ℝ) < 3 / 4))
  have huG : MemW12 Ω u G := huInner.congr_ae (EventuallyEq.refl _ _) hGAE.symm
  have hHolderInner : HolderBoundOn Ω.val u α H :=
    hHolder.mono (Metric.ball_subset_ball (by norm_num : (5 / 8 : ℝ) ≤ 3 / 4))
  have hM : 0 ≤ C_G * Real.sqrt E := mul_nonneg hC_G.le (Real.sqrt_nonneg E)
  obtain ⟨hus, hDuBound, hDuHolder⟩ := holder_weakGradient_firstDerivative_bounds Ω huG
    measure_ball_ne_top hα hγ hH hM hM hHolderInner hGHolder hGsup
  have henergy : (dirichletEnergy Du (Metric.ball (0 : Domain n) (3 / 4 : ℝ))).toReal = E := by
    simpa only [E, ballDomain] using dirichletEnergy_toReal hu.integrable_hsNormSq
  refine ⟨hus, ?_, ?_⟩
  · intro x hx
    rw [henergy]
    exact (hDuBound x hx).trans_eq (by dsimp only [C]; ring)
  · intro x hx y hy
    rw [henergy]
    exact (hDuHolder x hx y hy).trans_eq (by dsimp only [C]; ring)

theorem small_holder_quadratic_poisson_unit_first_derivative
    (n q : ℕ) (hn : 2 ≤ n) (α K : ℝ)
    (hα : 0 < α) (hαOne : α < 1) (hK : 0 ≤ K) :
    ∃ H₀ C : ℝ, 0 < H₀ ∧ 0 ≤ C ∧
      ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
        (F : Domain n → Ambient q) (H : ℝ),
        MemW12 (ballDomain (0 : Domain n) 1) u Du →
        0 ≤ H → H ≤ H₀ →
        HolderBoundOn (Metric.ball (0 : Domain n) 1) u α H →
        WeakPoissonOn (ballDomain (0 : Domain n) 1) Du F →
        (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
          ‖F x‖ ≤ K * hsNormSq (Du x)) →
        ContDiffOn ℝ 1 u (Metric.ball (0 : Domain n) (1 / 2)) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2),
          ‖fderiv ℝ u x‖ ≤ C *
            Real.sqrt (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal) ∧
        HolderBoundOn (Metric.ball (0 : Domain n) (1 / 2)) (fderiv ℝ u)
          (α / 8) (C *
            Real.sqrt (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal) := by
  obtain ⟨H₀, C, hH₀, hC, hFirstDerivative⟩ :=
    small_holder_quadratic_poisson_first_derivative n q hn α K hα hαOne hK
  refine ⟨H₀, C, hH₀, hC, ?_⟩
  intro u Du F H hu hH hHH hHolder hEq hBound
  let Ω := ballDomain (0 : Domain n) (3 / 4 : ℝ)
  have hsub : Ω.val ⊆ (ballDomain (0 : Domain n) 1).val :=
    Metric.ball_subset_ball (by norm_num)
  have huInner : MemW12 Ω u Du := hu.to_memW12Loc.memW12_ball
    (Metric.closedBall_subset_ball (by norm_num : (3 / 4 : ℝ) < 1))
  obtain ⟨hus, hDuBound, hDuHolder⟩ := hFirstDerivative u Du F H huInner hH hHH
    (hHolder.mono hsub) (hEq.mono hsub) (ae_restrict_of_ae_restrict_of_subset hsub hBound)
  have hEnergy : (dirichletEnergy Du (Metric.ball (0 : Domain n) (3 / 4 : ℝ))).toReal ≤
      (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
    have hinner : (dirichletEnergy Du (Metric.ball (0 : Domain n) (3 / 4 : ℝ))).toReal =
        ∫ x in Metric.ball (0 : Domain n) (3 / 4 : ℝ), hsNormSq (Du x) := by
      simpa only [Ω, ballDomain] using dirichletEnergy_toReal huInner.integrable_hsNormSq
    have houter : (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal =
        ∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x) := by
      simpa only [ballDomain] using dirichletEnergy_toReal hu.integrable_hsNormSq
    rw [hinner, houter]
    exact setIntegral_mono_set hu.integrable_hsNormSq
      (Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Eventually.of_forall fun _ hx => hsub hx)
  have hScale := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEnergy) hC
  have hhalf : Metric.ball (0 : Domain n) (1 / 2 : ℝ) ⊆ Metric.ball 0 (5 / 8 : ℝ) :=
    Metric.ball_subset_ball (by norm_num)
  refine ⟨hus.mono hhalf, fun x hx => (hDuBound x (hhalf hx)).trans hScale, ?_⟩
  intro x hx y hy
  exact (hDuHolder x (hhalf hx) y (hhalf hy)).trans
    (mul_le_mul_of_nonneg_right hScale (Real.rpow_nonneg dist_nonneg _))

end HolderToCK
end
