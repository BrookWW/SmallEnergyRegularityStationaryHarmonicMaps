module

public import HolderToCK.Analysis.LocalQuadraticPoissonC1
public import HolderToCK.Analysis.Bootstrap.ForcingRepresentative
public import HolderToCK.Analysis.Bootstrap.QualitativeLocalDataBounds
public import HolderToCK.Analysis.Poisson.InteriorLocalizationAffine

/-! # Finite local initial data for the qualitative higher derivative induction

A positive affine dilation of the original C1 map has finite centered and
first derivative bounds on the fixed initial ball. Local Holder control of its
actual derivative gives the initial native Holder seminorm. The original weak
equation transports to the same affine map and agrees with its classical
quadratic forcing.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff

namespace HolderToCK

theorem c1_locally_holder_affine_initial_data {n q : ℕ}
    (Ω : OpenDomain n) {u : Domain n → Ambient q}
    (hu : ContDiffOn ℝ 1 u Ω.val)
    (hHolder : LocallyHolderOn Ω (fderiv ℝ u)) (a : Domain n) (ha : a ∈ Ω.val) :
    ∃ r : PositiveRadius, ∃ γ M : ℝ, ∃ S : PositiveRadius,
      Metric.closedBall a r.val ⊆ Ω.val ∧
      0 < γ ∧ γ < 1 ∧ 0 < M ∧
      ContDiffOn ℝ 1 (fun z => u (a + r.val • z))
        (Metric.ball (0 : Domain n) (5 / 8)) ∧
      (∀ z ∈ Metric.ball (0 : Domain n) (5 / 8),
        u (a + r.val • z) ∈ Metric.closedBall (u a) S.val) ∧
      (∀ z ∈ Metric.ball (0 : Domain n) (5 / 8),
        ‖u (a + r.val • z) - u (a + r.val • (0 : Domain n))‖ ≤ M) ∧
      (∀ z ∈ Metric.ball (0 : Domain n) (5 / 8),
        ‖fderiv ℝ (fun z => u (a + r.val • z)) z‖ ≤ M) ∧
      (∀ z ∈ Metric.ball (0 : Domain n) (5 / 8),
        ‖iteratedFDeriv ℝ 1 (fun z => u (a + r.val • z)) z‖ ≤ M) ∧
      HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
        (fderiv ℝ (fun z => u (a + r.val • z))) γ M ∧
      HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
        (iteratedFDeriv ℝ 1 (fun z => u (a + r.val • z))) γ M ∧
      HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
        (fun z => u (a + r.val • z)) γ M := by
  obtain ⟨R, hclosed, γ, H, hγ, hγOne, hH, hDerivativeHolder⟩ := hHolder a ha
  let r : PositiveRadius := ⟨R.val / 2, half_pos R.property⟩
  let v : Domain n → Ambient q := fun z => u (a + r.val • z)
  let B : ℝ := ‖fderiv ℝ u a‖ + H * Real.rpow R.val γ
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _)
    (mul_nonneg hH (Real.rpow_nonneg R.property.le _))
  let C : ℝ := r.val * B
  let D : ℝ := r.val * (H * Real.rpow r.val γ)
  have hC : 0 ≤ C := mul_nonneg r.property.le hB
  have hD : 0 ≤ D := mul_nonneg r.property.le
    (mul_nonneg hH (Real.rpow_nonneg r.property.le _))
  have hrR : r.val ≤ R.val := by dsimp only [r]; linarith only [R.property]
  have hclosedr : Metric.closedBall a r.val ⊆ Ω.val :=
    (Metric.closedBall_subset_closedBall hrR).trans hclosed
  have hmapR : ∀ z ∈ Metric.ball (0 : Domain n) (5 / 8),
      a + r.val • z ∈ Metric.ball a R.val := by
    intro z hz
    have hnorm : ‖z‖ < (5 / 8 : ℝ) := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    change dist (a + r.val • z) a < R.val
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg r.property.le]
    have hnormOne : ‖z‖ < 1 := hnorm.trans (by norm_num)
    exact (mul_lt_mul_of_pos_left hnormOne r.property).trans_le (by
      simpa only [mul_one] using hrR)
  have hmapΩ : ∀ z ∈ Metric.ball (0 : Domain n) (5 / 8),
      a + r.val • z ∈ Ω.val := fun z hz =>
    hclosed (Metric.ball_subset_closedBall (hmapR z hz))
  have hv : ContDiffOn ℝ 1 v (Metric.ball (0 : Domain n) (5 / 8)) := by
    apply hu.comp (contDiff_const.add (contDiff_id.const_smul r.val)).contDiffOn
    exact hmapΩ
  have hNativeC : ∀ z ∈ Metric.ball (0 : Domain n) (5 / 8),
      ‖iteratedFDeriv ℝ 1 v z‖ ≤ C := by
    intro z hz
    rw [norm_iteratedFDeriv_one_comp_affine u a r]
    exact mul_le_mul_of_nonneg_left
      (hDerivativeHolder.norm_le_on_ball R.property hγ.le hH _ (hmapR z hz)) r.property.le
  have hNativeHolder : HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
      (iteratedFDeriv ℝ 1 v) γ D :=
    (hDerivativeHolder.iteratedFDeriv_one_comp_affine a r).mono hmapR
  obtain ⟨M, S, hM, hImage, hCentered, hDerivative, hNative, hDerivativeHolderV,
    hNativeHolderV, hvHolder⟩ :=
    qualitative_c1_finite_initial_bounds hv hγ hγOne hC hD hNativeC hNativeHolder
  have hzero : v 0 = u a := by simp only [v, smul_zero, add_zero]
  rw [hzero] at hImage
  exact ⟨r, γ, M, S, hclosedr, hγ, hγOne, hM, hv, hImage, hCentered,
    hDerivative, hNative, hDerivativeHolderV, hNativeHolderV, hvHolder⟩

theorem holder_quadratic_poisson_affine_initial_data {n q : ℕ}
    (hn : 2 ≤ n) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    (hA : ContDiff ℝ ∞ A) (hu : MemW12Loc Ω u Du)
    (hHolder : LocallyHolderOn Ω u)
    (hEquation : WeakPoissonOn Ω Du
      (fun x => ∑ i : Fin n, A (u x) (Du x i) (Du x i)))
    (a : Domain n) (ha : a ∈ Ω.val) :
    ∃ r : PositiveRadius, ∃ γ M : ℝ, ∃ S : PositiveRadius,
      Metric.closedBall a r.val ⊆ Ω.val ∧
      0 < γ ∧ γ < 1 ∧ 0 < M ∧
      ContDiffOn ℝ 1 (fun z => u (a + r.val • z))
        (Metric.ball (0 : Domain n) (5 / 8)) ∧
      (∀ z ∈ Metric.ball (0 : Domain n) (5 / 8),
        u (a + r.val • z) ∈ Metric.closedBall (u a) S.val) ∧
      (∀ z ∈ Metric.ball (0 : Domain n) (5 / 8),
        ‖u (a + r.val • z) - u (a + r.val • (0 : Domain n))‖ ≤ M) ∧
      (∀ z ∈ Metric.ball (0 : Domain n) (5 / 8),
        ‖fderiv ℝ (fun z => u (a + r.val • z)) z‖ ≤ M) ∧
      (∀ z ∈ Metric.ball (0 : Domain n) (5 / 8),
        ‖iteratedFDeriv ℝ 1 (fun z => u (a + r.val • z)) z‖ ≤ M) ∧
      HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
        (fderiv ℝ (fun z => u (a + r.val • z))) γ M ∧
      HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
        (iteratedFDeriv ℝ 1 (fun z => u (a + r.val • z))) γ M ∧
      HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
        (fun z => u (a + r.val • z)) γ M ∧
      MemW12Loc (ballDomain (0 : Domain n) (5 / 8))
        (fun z => u (a + r.val • z))
        (fun z i => fderiv ℝ (fun z => u (a + r.val • z)) z (EuclideanSpace.single i 1)) ∧
      WeakPoissonOn (ballDomain (0 : Domain n) (5 / 8))
        (fun z i => fderiv ℝ (fun z => u (a + r.val • z)) z (EuclideanSpace.single i 1))
        (fun z => ∑ i : Fin n, A (u (a + r.val • z))
          (fderiv ℝ (fun z => u (a + r.val • z)) z (EuclideanSpace.single i 1))
          (fderiv ℝ (fun z => u (a + r.val • z)) z (EuclideanSpace.single i 1))) := by
  obtain ⟨huC1, hDerivativeHolder⟩ :=
    locally_holder_quadratic_poisson_first_derivative hn Ω u Du A hA hu hHolder hEquation
  obtain ⟨r, γ, M, S, hclosedr, hγ, hγOne, hM, hvC1, hImage, hCentered,
    hDerivative, hNative, hDerivativeHolderV, hNativeHolderV, hvHolder⟩ :=
    c1_locally_holder_affine_initial_data Ω huC1 hDerivativeHolder a ha
  let v : Domain n → Ambient q := fun z => u (a + r.val • z)
  let G : Domain n → Gradient n q := fun z i => r.val • Du (a + r.val • z) i
  have hsubΩ : (ballDomain a r.val).val ⊆ Ω.val :=
    Metric.ball_subset_closedBall.trans hclosedr
  have huBall : MemW12Loc (ballDomain a r.val) u Du := hu.mono hsubΩ
  have hvWeak : MemW12Loc (ballDomain (0 : Domain n) 1) v G := by
    simpa only [sub_zero, div_self r.property.ne'] using
      MemW12Loc.affineBall_pullback_local huBall (0 : Domain n) r.property
  have hvEq : WeakPoissonOn (ballDomain (0 : Domain n) 1) G
      (fun z => r.val ^ 2 • (∑ i : Fin n, A (u (a + r.val • z))
        (Du (a + r.val • z) i) (Du (a + r.val • z) i))) := by
    simpa only [sub_zero, div_self r.property.ne'] using
      (hEquation.mono hsubΩ).affineBall_pullback_local (0 : Domain n) r.property
  have hvQuadraticEq : WeakPoissonOn (ballDomain (0 : Domain n) 1) G
      (fun z => ∑ i : Fin n, A (v z) (G z i) (G z i)) :=
    hvEq.congr (EventuallyEq.refl _ _) (Eventually.of_forall fun z =>
      quadratic_forcing_affine_identity A u Du a r.val z)
  have hsub : (ballDomain (0 : Domain n) (5 / 8)).val ⊆
      (ballDomain (0 : Domain n) 1).val := Metric.ball_subset_ball (by norm_num)
  obtain ⟨_, _, hvClassicalEq⟩ := classical_quadratic_forcing_representative
    (ballDomain (0 : Domain n) (5 / 8)) A hA.continuous hvC1
    (hvWeak.mono hsub).1 (hvQuadraticEq.mono hsub) (EventuallyEq.refl _ _)
  exact ⟨r, γ, M, S, hclosedr, hγ, hγOne, hM, hvC1, hImage, hCentered,
    hDerivative, hNative, hDerivativeHolderV, hNativeHolderV, hvHolder,
    memW12Loc_of_contDiffOn_one (ballDomain (0 : Domain n) (5 / 8)) hvC1,
    hvClassicalEq⟩

end HolderToCK
end
