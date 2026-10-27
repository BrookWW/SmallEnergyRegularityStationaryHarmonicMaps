module

public import HolderToCK.Analysis.WeakPoissonAffine
public import HolderToCK.Analysis.Bootstrap.CoefficientBounds
public import HolderToCK.Analysis.Bootstrap.QuadraticForcingBounds
public import HolderToCK.Foundation.HolderContinuity
public import HolderToCK.Analysis.Bootstrap.AffineDerivatives
import HolderToCK.Analysis.Bootstrap.DerivativeProducts

/-! # Local data for the qualitative quadratic Poisson upgrade

A finite local Holder bound places the compact half-ball image inside a genuine
compact ambient neighborhood. Smooth coefficients have all derivative bounds
there and produce a finite quadratic constant. A smaller positive radius makes
the exact affine Holder coefficient as small as the chosen positive threshold.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff NNReal

namespace HolderToCK

theorem exists_holder_small_scale {α H H₀ : ℝ} (hα : 0 < α) (hH : 0 ≤ H)
    (hH₀ : 0 < H₀) (R : PositiveRadius) :
    ∃ ρ : PositiveRadius, ρ.val ≤ R.val / 2 ∧ H * Real.rpow ρ.val α ≤ H₀ := by
  have hden : 0 < 1 + H := by linarith only [hH]
  have hbase : 0 < H₀ / (1 + H) := div_pos hH₀ hden
  let B : ℝ := Real.rpow (H₀ / (1 + H)) (1 / α)
  have hB : 0 < B := Real.rpow_pos_of_pos hbase _
  let ρ : PositiveRadius := ⟨min (R.val / 4) B, lt_min (div_pos R.property (by norm_num)) hB⟩
  refine ⟨ρ, (min_le_left _ _).trans (by linarith only [R.property]), ?_⟩
  have hBpow : Real.rpow B α = H₀ / (1 + H) := by
    simp only [B, Real.rpow_eq_pow]
    rw [← Real.rpow_mul hbase.le, one_div_mul_cancel hα.ne', Real.rpow_one]
  have hρpower : Real.rpow ρ.val α ≤ Real.rpow B α := by
    simpa only [Real.rpow_eq_pow] using Real.rpow_le_rpow ρ.property.le (min_le_right _ _) hα.le
  calc
    H * Real.rpow ρ.val α ≤ H * Real.rpow B α := mul_le_mul_of_nonneg_left hρpower hH
    _ = H * (H₀ / (1 + H)) := by rw [hBpow]
    _ ≤ (1 + H) * (H₀ / (1 + H)) :=
      mul_le_mul_of_nonneg_right (by linarith only) hbase.le
    _ = H₀ := mul_div_cancel₀ _ hden.ne'

theorem holder_ball_compact_coefficient_data {n q : ℕ}
    (a : Domain n) (R : PositiveRadius)
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    (hA : ContDiff ℝ ∞ A) {u : Domain n → Ambient q}
    {α H : ℝ} (hα : 0 < α) (hH : 0 ≤ H)
    (hHolder : HolderBoundOn (Metric.ball a R.val) u α H) :
    IsCompact (u '' Metric.closedBall a (R.val / 2)) ∧
      ∃ S : PositiveRadius, ∃ b : ℕ → ℝ≥0, ∃ K : ℝ, 0 < K ∧
        u '' Metric.closedBall a (R.val / 2) ⊆ Metric.ball (u a) S.val ∧
        (∀ k : ℕ, ∀ z ∈ Metric.closedBall (u a) S.val,
          ‖iteratedFDeriv ℝ k A z‖ ≤ (b k : ℝ)) ∧
        (∀ k : ℕ, ∀ x ∈ Metric.closedBall (u a) S.val,
          ∀ y ∈ Metric.closedBall (u a) S.val,
          ‖iteratedFDeriv ℝ k A x - iteratedFDeriv ℝ k A y‖ ≤
            (b (k + 1) : ℝ) * ‖x - y‖) ∧
        (∀ x ∈ Metric.closedBall a (R.val / 2), ‖A (u x)‖ ≤ K) ∧
        ∀ (Du : Domain n → Gradient n q), ∀ x ∈ Metric.closedBall a (R.val / 2),
          ‖∑ i : Fin n, A (u x) (Du x i) (Du x i)‖ ≤ K * hsNormSq (Du x) := by
  have hsub : Metric.closedBall a (R.val / 2) ⊆ Metric.ball a R.val :=
    Metric.closedBall_subset_ball (half_lt_self R.property)
  have hcont := (hHolder.continuousOn hα).mono hsub
  have hcompact := (isCompact_closedBall a (R.val / 2)).image_of_continuousOn hcont
  let S : PositiveRadius := ⟨H * Real.rpow R.val α + 1,
    add_pos_of_nonneg_of_pos (mul_nonneg hH (Real.rpow_nonneg R.property.le _)) zero_lt_one⟩
  have himage : u '' Metric.closedBall a (R.val / 2) ⊆ Metric.ball (u a) S.val := by
    rintro _ ⟨x, hx, rfl⟩
    have ha : a ∈ Metric.ball a R.val := Metric.mem_ball_self R.property
    have hxa : dist x a ≤ R.val :=
      (show dist x a ≤ R.val / 2 from hx).trans (by linarith only [R.property])
    have hnorm : ‖u x - u a‖ ≤ H * Real.rpow R.val α :=
      (hHolder x (hsub hx) a ha).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hxa hα.le) hH)
    change dist (u x) (u a) < H * Real.rpow R.val α + 1
    rw [dist_eq_norm]
    linarith only [hnorm]
  obtain ⟨b, hb, hbLip⟩ := compact_coefficient_derivative_bounds A hA (u a) S.val
  let K : ℝ := (b 0 : ℝ) + 1
  have hK : 0 < K := by dsimp only [K]; exact add_pos_of_nonneg_of_pos (b 0).coe_nonneg zero_lt_one
  have hcoeff : ∀ x ∈ Metric.closedBall a (R.val / 2), ‖A (u x)‖ ≤ K := by
    intro x hx
    have hnorm : ‖A (u x)‖ ≤ (b 0 : ℝ) := by
      simpa only [norm_iteratedFDeriv_zero] using
        hb 0 (u x) (Metric.ball_subset_closedBall (himage ⟨x, hx, rfl⟩))
    exact hnorm.trans (by dsimp only [K]; linarith only)
  refine ⟨hcompact, S, b, K, hK, himage, hb, hbLip, hcoeff, ?_⟩
  intro Du x hx
  exact (norm_quadratic_forcing_le_hsNormSq (A (u x)) (Du x)).trans
    (mul_le_mul_of_nonneg_right (hcoeff x hx) (hsNormSq_nonneg _))

theorem contDiffOn_of_affine_pullback {n q : ℕ}
    (a : Domain n) (R : PositiveRadius) {s : ℝ} {k : ℕ∞ω}
    {u : Domain n → Ambient q}
    (hSmooth : ContDiffOn ℝ k (fun z => u (a + R.val • z))
      (Metric.ball (0 : Domain n) s)) :
    ContDiffOn ℝ k u (Metric.ball a (R.val * s)) := by
  let m : Domain n → Ambient q := fun z => u (a + R.val • z)
  have hsame : (fun x => m (R.val⁻¹ • (x - a))) = u := by
    funext x
    simp only [m, smul_smul, mul_inv_cancel₀ R.property.ne', one_smul, add_sub_cancel]
  rw [← hsame]
  apply hSmooth.comp ((contDiff_id.sub contDiff_const).const_smul _).contDiffOn
  intro x hx
  exact (inverseAffine_mem_ball_iff a x R s).mpr hx

theorem fderiv_bounds_of_affine_pullback {n q : ℕ}
    (a : Domain n) (R : PositiveRadius) {s γ B : ℝ} {u : Domain n → Ambient q}
    (hSmooth : ContDiffOn ℝ 1 (fun z => u (a + R.val • z))
      (Metric.ball (0 : Domain n) s))
    (hBound : ∀ z ∈ Metric.ball (0 : Domain n) s,
      ‖fderiv ℝ (fun z => u (a + R.val • z)) z‖ ≤ B)
    (hHolder : HolderBoundOn (Metric.ball (0 : Domain n) s)
      (fderiv ℝ (fun z => u (a + R.val • z))) γ B) :
    ContDiffOn ℝ 1 u (Metric.ball a (R.val * s)) ∧
    (∀ x ∈ Metric.ball a (R.val * s),
      ‖fderiv ℝ u x‖ ≤ Real.rpow R.val (-1) * B) ∧
    HolderBoundOn (Metric.ball a (R.val * s)) (fderiv ℝ u) γ
      (B * Real.rpow R.val (-(1 + γ))) := by
  let m : Domain n → Ambient q := fun z => u (a + R.val • z)
  have hsame : (fun x => m (R.val⁻¹ • (x - a))) = u := by
    funext x
    simp only [m, smul_smul, mul_inv_cancel₀ R.property.ne', one_smul, add_sub_cancel]
  have hmap : Metric.ball a (R.val * s) ⊆
      (fun x => R.val⁻¹ • (x - a)) ⁻¹' Metric.ball (0 : Domain n) s := by
    intro x hx
    exact (inverseAffine_mem_ball_iff a x R s).mpr hx
  have hOneHolder : HolderBoundOn (Metric.ball (0 : Domain n) s)
      (iteratedFDeriv ℝ 1 m) γ B := by
    intro x hx y hy
    have hnorm : ‖iteratedFDeriv ℝ 1 m x - iteratedFDeriv ℝ 1 m y‖ =
        ‖fderiv ℝ m x - fderiv ℝ m y‖ := by
      rw [← norm_iteratedFDeriv_fderiv_sub m 0,
        norm_iteratedFDeriv_zero_sub]
    rw [hnorm]
    exact hHolder x hx y hy
  have hOneTrans := (iteratedFDeriv_inverseAffine_holderBoundOn 1 hOneHolder a R).mono hmap
  rw [hsame] at hOneTrans
  refine ⟨contDiffOn_of_affine_pullback a R hSmooth, ?_, ?_⟩
  · intro x hx
    have hnorm := norm_iteratedFDeriv_comp_inverseAffine m a R 1 x
    rw [hsame] at hnorm
    simp only [norm_iteratedFDeriv_one, Nat.cast_one] at hnorm
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (hBound _ (hmap hx)) (Real.rpow_nonneg R.property.le _)
  · intro x hx y hy
    have hnorm : ‖fderiv ℝ u x - fderiv ℝ u y‖ =
        ‖iteratedFDeriv ℝ 1 u x - iteratedFDeriv ℝ 1 u y‖ := by
      rw [← norm_iteratedFDeriv_zero_sub (fderiv ℝ u) x y,
        norm_iteratedFDeriv_fderiv_sub]
    rw [hnorm]
    simpa only [Nat.cast_one] using hOneTrans x hx y hy

end HolderToCK
end
