module

public import HarmonicMaps.Analysis.PoissonPolarCalculus
public import HarmonicMaps.Energy
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Tactic.Module

/-!
# Weighted radial integration of the Euler derivative

The native harmonic equation recovers the Euler derivative from actual angular
second derivatives and interior data at a positive radius. Integer exponents
retain the negative radial weight in dimension two.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff BigOperators Topology

namespace HarmonicMaps

/-- For actual smooth harmonic data, the Euler derivative satisfies the exact
weighted radial integral formula for one produced coordinate-rotation family. -/
theorem poisson_weighted_radialEuler_integral (n : ℕ) :
    ∃ A : Fin n → Fin n → (Domain n →L[ℝ] Domain n),
      (∀ i j, star (A i j) = -A i j ∧
        ∀ x : Domain n, A i j x =
          x i • EuclideanSpace.single j 1 - x j • EuclideanSpace.single i 1) ∧
      ∀ (q : ℕ) (R : PositiveRadius) (f : Domain n → Ambient q),
      ContDiffOn ℝ ∞ f (Metric.ball (0 : Domain n) R.val) →
      (∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian f x = 0) →
      ∀ (a r : ℝ), 0 < a → a ≤ r → r < R.val →
      ∀ θ : Metric.sphere (0 : Domain n) 1,
      let E : Domain n → Ambient q := fun y => fderiv ℝ f y y
      let L : Fin n → Fin n → Domain n → Ambient q :=
        fun i j y => fderiv ℝ f y (A i j y)
      let L₂ : Domain n → Ambient q := fun y =>
        ∑ i : Fin n, ∑ j : Fin n, fderiv ℝ (L i j) y (A i j y)
      r ^ ((n : ℤ) - 2) • E (r • θ.val) =
        a ^ ((n : ℤ) - 2) • E (a • θ.val) -
          (1 / 2 : ℝ) • (∫ s in a..r, s ^ ((n : ℤ) - 3) • L₂ (s • θ.val)) := by
  obtain ⟨A, hA, hPolar⟩ := poisson_coordinate_polar_calculus n
  refine ⟨A, hA, ?_⟩
  intro q R f hf hh a r ha har hr θ
  let E : Domain n → Ambient q := fun y => fderiv ℝ f y y
  let L : Fin n → Fin n → Domain n → Ambient q :=
    fun i j y => fderiv ℝ f y (A i j y)
  let L₂ : Domain n → Ambient q := fun y =>
    ∑ i : Fin n, ∑ j : Fin n, fderiv ℝ (L i j) y (A i j y)
  let k : ℤ := (n : ℤ) - 2
  have hk : (k : ℝ) = (n : ℝ) - 2 := by
    dsimp only [k]
    push_cast
    rfl
  have hkminus : k - 1 = (n : ℤ) - 3 := by dsimp only [k]; omega
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) (Metric.ball (0 : Domain n) R.val) :=
    hf.fderiv_of_isOpen Metric.isOpen_ball (by simp)
  have hE : ContDiffOn ℝ ∞ E (Metric.ball (0 : Domain n) R.val) :=
    hDf.clm_apply contDiffOn_id
  have hL (i j : Fin n) : ContDiffOn ℝ ∞ (L i j) (Metric.ball (0 : Domain n) R.val) :=
    hDf.clm_apply (A i j).contDiff.contDiffOn
  have hL₂ : ContDiffOn ℝ ∞ L₂ (Metric.ball (0 : Domain n) R.val) := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact ((hL i j).fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply
      (A i j).contDiff.contDiffOn
  have htheta : ‖θ.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  have hinside (s : ℝ) (hs : s ∈ Icc a r) : s • θ.val ∈ Metric.ball (0 : Domain n) R.val := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (ha.le.trans hs.1),
      htheta, mul_one]
    exact hs.2.trans_lt hr
  have hSecond (s : ℝ) (hs : s ∈ Icc a r) :
      fderiv ℝ E (s • θ.val) (s • θ.val) =
        -(k : ℝ) • E (s • θ.val) - (1 / 2 : ℝ) • L₂ (s • θ.val) := by
    have h := (hPolar q _ Metric.isOpen_ball f hf _ (hinside s hs)).1
    change L₂ (s • θ.val) = (2 : ℝ) •
      (‖s • θ.val‖ ^ 2 • Laplacian.laplacian f (s • θ.val) -
        fderiv ℝ E (s • θ.val) (s • θ.val) - ((n : ℝ) - 2) • E (s • θ.val)) at h
    rw [hh _ (hinside s hs), smul_zero, zero_sub, ← hk] at h
    rw [h]
    module
  have hderiv (s : ℝ) (hs : s ∈ Icc a r) :
      HasDerivAt (fun t : ℝ => t ^ k • E (t • θ.val))
        ((-(1 / 2) : ℝ) • (s ^ (k - 1) • L₂ (s • θ.val))) s := by
    have hspos : 0 < s := ha.trans_le hs.1
    have hEDiff : DifferentiableAt ℝ E (s • θ.val) :=
      (hE.contDiffAt (Metric.isOpen_ball.mem_nhds (hinside s hs))).differentiableAt (by simp)
    have hcurve := (hasDerivAt_id s).smul_const θ.val
    simp only [one_smul] at hcurve
    have hEDeriv := hEDiff.hasFDerivAt.comp_hasDerivAt s hcurve
    have hPow := hasDerivAt_zpow k s (Or.inl hspos.ne')
    have h := hPow.smul hEDeriv
    have hscale : s ^ k * s⁻¹ = s ^ (k - 1) := by
      rw [← zpow_neg_one, ← zpow_add₀ hspos.ne']
      congr 1
    have hdir : fderiv ℝ E (s • θ.val) θ.val =
        s⁻¹ • fderiv ℝ E (s • θ.val) (s • θ.val) := by
      rw [map_smul, smul_smul, inv_mul_cancel₀ hspos.ne', one_smul]
    apply h.congr_of_eventuallyEq (Eventually.of_forall (fun _ => rfl)) |>.congr_deriv
    change s ^ k • fderiv ℝ E (s • θ.val) θ.val +
      ((k : ℝ) * s ^ (k - 1)) • E (s • θ.val) = _
    rw [hdir, hSecond s hs, smul_smul, hscale]
    module
  have hcont : ContinuousOn (fun s : ℝ => s ^ (k - 1) • L₂ (s • θ.val)) (Icc a r) := by
    have hp : ContinuousOn (fun s : ℝ => s ^ (k - 1)) (Icc a r) :=
      continuousOn_id.zpow₀ _ (fun s hs => Or.inl (ha.trans_le hs.1).ne')
    have hc : ContinuousOn (fun s : ℝ => L₂ (s • θ.val)) (Icc a r) :=
      hL₂.continuousOn.comp (continuousOn_id.smul continuousOn_const) hinside
    exact hp.smul hc
  have hint : IntervalIntegrable
      (fun s : ℝ => (-(1 / 2) : ℝ) • (s ^ (k - 1) • L₂ (s • θ.val))) volume a r :=
    (hcont.const_smul (-(1 / 2) : ℝ)).intervalIntegrable_of_Icc har
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hderiv s ((uIcc_of_le har) ▸ hs)) hint
  rw [intervalIntegral.integral_smul] at hFTC
  change r ^ k • E (r • θ.val) = a ^ k • E (a • θ.val) -
    (1 / 2 : ℝ) • (∫ s in a..r, s ^ ((n : ℤ) - 3) • L₂ (s • θ.val))
  rw [← hkminus]
  rw [neg_smul] at hFTC
  have hEq : (1 / 2 : ℝ) • (∫ s in a..r, s ^ (k - 1) • L₂ (s • θ.val)) =
      a ^ k • E (a • θ.val) - r ^ k • E (r • θ.val) := by
    exact neg_eq_iff_eq_neg.mp hFTC |>.trans (neg_sub _ _)
  rw [hEq]
  abel

end HarmonicMaps
end
