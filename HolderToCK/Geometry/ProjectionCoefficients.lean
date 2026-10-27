module

public import HolderToCK.Integration.HolderInput
public import HolderToCK.Foundation.WeakPoisson
public import HolderToCK.Analysis.WeakPoissonLocality
public import HolderToCK.Analysis.Bootstrap.CoefficientBounds
public import HolderToCK.Analysis.Bootstrap.QuadraticForcingBounds

/-! # The smooth quadratic coefficient of the target projection

The Hessian of a smooth Euclidean extension equals the canonical projection
Hessian at target points. The original outer-variation equation therefore
uses that same smooth coefficient and the original weak gradient.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology NNReal

namespace HolderToCK

theorem projectionExtension_hessian_eq_on_target {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) {ρ : ℝ} (hρ : 0 < ρ)
    (Q : Ambient q → Ambient q) (hQ : ContDiff ℝ ∞ Q)
    (hQeq : ∀ z : tubularTube q N, Metric.infDist z.val N.carrierSet < ρ →
      Q z.val = (tubularProjection q N z).val)
    (p : N.Carrier) (hp : p.val ∈ tubularTube q N) :
    fderiv ℝ (fderiv ℝ Q) p.val = tubularProjectionSecondDerivative q N ⟨p.val, hp⟩ := by
  let V : Set (Ambient q) := tubularTube q N ∩ {x | Metric.infDist x N.carrierSet < ρ}
  have hV : IsOpen V := (tubularProjection_characterization q N).2.1.inter
    (isOpen_lt (Metric.continuous_infDist_pt N.carrierSet) continuous_const)
  have hpV : p.val ∈ V := ⟨hp, by
    change Metric.infDist p.val N.carrierSet < ρ
    rw [Metric.infDist_zero_of_mem p.property]
    exact hρ⟩
  exact (tubularProjectionSecondDerivative_characterization q N).1 ⟨p.val, hp⟩ V Q hV hpV
    inter_subset_left hQ.contDiffOn (fun z hz => hQeq z hz.2)

theorem smooth_projection_quadratic_coefficient {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q,
      ContDiff ℝ ∞ A ∧ ∃ K : ℝ, 0 < K ∧ (∀ z, ‖A z‖ ≤ K) ∧
        ∀ (p : N.Carrier) (hp : p.val ∈ tubularTube q N),
          A p.val = tubularProjectionSecondDerivative q N ⟨p.val, hp⟩ := by
  obtain ⟨ρ, hρ, _, _, _, _, _, _, _, _, _, _, _, Q, hQ, hQeq,
    C₁, C₂, _, hC₂, _, hQH⟩ := tubularProjection_complete q N
  refine ⟨fderiv ℝ (fderiv ℝ Q), ?_, C₂, hC₂, hQH, ?_⟩
  · have hD : ContDiff ℝ ∞ (fderiv ℝ Q) := hQ.fderiv_right (by simp)
    exact hD.fderiv_right (by simp)
  · exact projectionExtension_hessian_eq_on_target N hρ Q hQ hQeq

theorem minimizer_projection_quadratic_weakPoisson {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q,
      ContDiff ℝ ∞ A ∧ ∃ K : ℝ, 0 < K ∧ (∀ z, ‖A z‖ ≤ K) ∧
        ∀ (n : ℕ) (_hn : 2 ≤ n) (Ω : OpenDomain n)
          (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
          MemW12Loc Ω u Du → TakesValuesIn N Ω u → IsLocallyEnergyMinimizing N Ω u Du →
          ∃ F : Domain n → Ambient q,
            WeakPoissonOn Ω Du F ∧
            (∀ᵐ x ∂volume.restrict Ω.val, F x = ∑ i : Fin n, A (u x) (Du x i) (Du x i)) ∧
            (∀ᵐ x ∂volume.restrict Ω.val, ‖F x‖ ≤ K * hsNormSq (Du x)) := by
  obtain ⟨A, hA, K, hK, hAnorm, hAtarget⟩ := smooth_projection_quadratic_coefficient N
  refine ⟨A, hA, K, hK, hAnorm, ?_⟩
  intro n hn Ω u Du hu huN hmin
  obtain ⟨F, hFint, hFformula, hFweak⟩ := outerVariation_weakEquation q N n hn Ω u Du hu huN hmin
  refine ⟨F, ⟨hFint, hFweak⟩, ?_, ?_⟩
  · filter_upwards [hFformula, huN] with x hx hxN
    obtain ⟨hxTube, hxeq, _⟩ := hx
    rw [hxeq]
    exact Finset.sum_congr rfl (fun i _ => by rw [hAtarget ⟨u x, hxN⟩ hxTube])
  · filter_upwards [hFformula, huN] with x hx hxN
    obtain ⟨hxTube, hxeq, _⟩ := hx
    have hcanonical : ‖tubularProjectionSecondDerivative q N ⟨u x, hxTube⟩‖ ≤ K := by
      rw [← hAtarget ⟨u x, hxN⟩ hxTube]
      exact hAnorm (u x)
    rw [hxeq]
    calc
      _ ≤ ‖tubularProjectionSecondDerivative q N ⟨u x, hxTube⟩‖ * hsNormSq (Du x) :=
        norm_quadratic_forcing_le_hsNormSq _ _
      _ ≤ K * hsNormSq (Du x) := mul_le_mul_of_nonneg_right hcanonical (hsNormSq_nonneg _)

theorem smooth_projection_coefficient_compact_bounds {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q,
      ContDiff ℝ ∞ A ∧ ∃ K R : ℝ, ∃ b : ℕ → ℝ≥0,
        0 < K ∧ 0 < R ∧ N.carrierSet ⊆ Metric.ball (0 : Ambient q) R ∧
        (∀ z, ‖A z‖ ≤ K) ∧
        (∀ (p : N.Carrier) (hp : p.val ∈ tubularTube q N),
          A p.val = tubularProjectionSecondDerivative q N ⟨p.val, hp⟩) ∧
        (∀ k : ℕ, ∀ z ∈ Metric.closedBall (0 : Ambient q) R,
          ‖iteratedFDeriv ℝ k A z‖ ≤ (b k : ℝ)) ∧
        ∀ k : ℕ, ∀ x ∈ Metric.closedBall (0 : Ambient q) R,
          ∀ y ∈ Metric.closedBall (0 : Ambient q) R,
          ‖iteratedFDeriv ℝ k A x - iteratedFDeriv ℝ k A y‖ ≤
            (b (k + 1) : ℝ) * ‖x - y‖ := by
  obtain ⟨A, hA, K, hK, hAnorm, hAtarget⟩ := smooth_projection_quadratic_coefficient N
  obtain ⟨R, hR, hNbound⟩ := N.isCompact.isBounded.exists_pos_norm_lt
  obtain ⟨b, hb, hblip⟩ := compact_coefficient_derivative_bounds A hA (0 : Ambient q) R
  refine ⟨A, hA, K, R, b, hK, hR, ?_, hAnorm, hAtarget, hb, hblip⟩
  intro z hz
  simpa only [Metric.mem_ball, dist_zero_right] using hNbound z hz

end HolderToCK
end
