module

public import StationaryHarmonicMaps.Analysis.C1SmoothWeakGradient
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Boundary signs and actual divergence integrals on the Euclidean ball

A compact bad set gives quantitative control in a thin boundary band.
Smooth radial tests retain the genuine coordinate integration-by-parts
identity and its normalization against the identity vector field.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- A continuous nonpositive sphere restriction has arbitrarily small weighted positive part in a true inner boundary band. -/
theorem exists_unitSphere_boundary_band {n : ℕ}
    (f : Domain n → ℝ) (hf : Continuous f)
    (hSphere : ∀ x : Domain n, ‖x‖ = 1 → f x ≤ 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ x : Domain n, ‖x‖ ≤ 1 → 1-δ ≤ ‖x‖^2 → f x ≤ η*‖x‖^2 := by
  let K : Set (Domain n) := closedBall 0 1 ∩ {x | η*‖x‖^2 ≤ f x}
  have hK : IsCompact K := (isCompact_closedBall (0 : Domain n) 1).inter_right
    (isClosed_le ((continuous_norm.pow 2).const_mul η) hf)
  by_cases hne : K.Nonempty
  · obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne (continuous_norm.pow 2).continuousOn
    have hyNorm : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy.1
    have hySq : ‖y‖^2 ≤ 1 := pow_le_one₀ (norm_nonneg y) hyNorm
    have hyLt : ‖y‖^2 < 1 := by
      by_contra hnot
      have heq : ‖y‖^2 = 1 := le_antisymm hySq (not_lt.mp hnot)
      have hyOne : ‖y‖ = 1 := by nlinarith only [heq, norm_nonneg y]
      have hb : η*‖y‖^2 ≤ f y := hy.2
      rw [heq, mul_one] at hb
      exact (not_le_of_gt hη) (hb.trans (hSphere y hyOne))
    refine ⟨(1-‖y‖^2)/2, by linarith only [hyLt], ?_, ?_⟩
    · linarith only [sq_nonneg ‖y‖]
    · intro x hx hxBand
      by_contra hnot
      have hxK : x∈K := ⟨by simpa only [mem_closedBall, dist_zero_right] using hx,
        (lt_of_not_ge hnot).le⟩
      have H : ‖x‖^2 ≤ ‖y‖^2 := hmax hxK
      linarith only [H, hxBand, hyLt]
  · refine ⟨1/2, by norm_num, le_rfl, ?_⟩
    intro x hx _hxBand
    by_contra hnot
    apply hne
    exact ⟨x, by simpa only [mem_closedBall, dist_zero_right] using hx, (lt_of_not_ge hnot).le⟩


/-- The actual radial test derivative gives both integrable divergence pairings and their exact global identity. -/
theorem integral_radial_test_divergence {n : ℕ}
    (V : Domain n → Domain n) (hV : ContDiff ℝ 1 V)
    (κ : Domain n → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (w : Domain n → ℝ)
    (hDκ : ∀ (x : Domain n) (i : Fin n),
      fderiv ℝ κ x (EuclideanSpace.single i 1) = -w x * x i) :
    Integrable (fun x => κ x * ∑ i : Fin n, (fderiv ℝ V x (EuclideanSpace.single i 1)) i) volume ∧
    Integrable (fun x => w x * inner ℝ x (V x)) volume ∧
    (∫ x, κ x * ∑ i : Fin n, (fderiv ℝ V x (EuclideanSpace.single i 1)) i) =
      ∫ x, w x * inner ℝ x (V x) := by
  let A (i : Fin n) (x : Domain n) := fderiv ℝ κ x (EuclideanSpace.single i 1) * (V x) i
  let B (i : Fin n) (x : Domain n) := κ x * (fderiv ℝ V x (EuclideanSpace.single i 1)) i
  have hPair (i : Fin n) : Integrable (A i) volume ∧ Integrable (B i) volume ∧
      (∫ x, B i x) = -(∫ x, A i x) := by
    let π : Domain n →L[ℝ] ℝ := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i
    have hVi : ContDiff ℝ 1 (fun x => (V x) i) := π.contDiff.comp hV
    have hdVi (x : Domain n) : fderiv ℝ (fun y => (V y) i) x (EuclideanSpace.single i 1) =
        (fderiv ℝ V x (EuclideanSpace.single i 1)) i := by
      change fderiv ℝ (π ∘ V) x (EuclideanSpace.single i 1) = _
      rw [fderiv_comp x π.differentiableAt (hV.differentiable (by norm_num) x), π.fderiv]
      rfl
    have ha : Integrable (A i) volume :=
      (((hκ.continuous_fderiv (by simp)).clm_apply continuous_const).mul hVi.continuous).integrable_of_hasCompactSupport
        (hcκ.fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_right
    have hb' : Integrable (fun x => κ x * fderiv ℝ (fun y => (V y) i) x (EuclideanSpace.single i 1)) volume :=
      (hκ.continuous.mul ((hVi.continuous_fderiv (by norm_num)).clm_apply continuous_const)).integrable_of_hasCompactSupport
        hcκ.mul_right
    have hb : Integrable (B i) volume := by simpa only [B, hdVi] using hb'
    have h0 : Integrable (fun x => κ x * (V x) i) volume :=
      (hκ.continuous.mul hVi.continuous).integrable_of_hasCompactSupport hcκ.mul_right
    have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := κ)
      (g := fun x => (V x) i) (v := EuclideanSpace.single i 1) ha hb' h0
      (fun _x _hx => (hκ.differentiable (by simp)).differentiableAt)
      (fun _x _hx => (hVi.differentiable (by norm_num)).differentiableAt)
    refine ⟨ha, hb, ?_⟩
    simpa only [A, B, hdVi] using H
  have hIA : Integrable (fun x => ∑ i : Fin n, A i x) volume :=
    integrable_finsetSum _ fun i _ => (hPair i).1
  have hIB : Integrable (fun x => ∑ i : Fin n, B i x) volume :=
    integrable_finsetSum _ fun i _ => (hPair i).2.1
  have hA (x : Domain n) : (∑ i : Fin n, A i x) = -(w x * inner ℝ x (V x)) := by
    calc
      _ = ∑ i : Fin n, -(w x * ((V x) i * x i)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [A]
        rw [hDκ]
        ring
      _ = -(w x * ∑ i : Fin n, (V x) i * x i) := by
        rw [Finset.mul_sum, Finset.sum_neg_distrib]
      _ = _ := by
        simp only [PiLp.inner_apply, Real.inner_apply]
        rw [show (∑ i : Fin n, (V x) i * x i) = ∑ i : Fin n, x i * (V x) i from
          Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  have hB (x : Domain n) : (∑ i : Fin n, B i x) =
      κ x * ∑ i : Fin n, (fderiv ℝ V x (EuclideanSpace.single i 1)) i := by
    simp only [B, Finset.mul_sum]
  have hIκ : Integrable (fun x => κ x * ∑ i : Fin n, (fderiv ℝ V x (EuclideanSpace.single i 1)) i) volume :=
    hIB.congr (Eventually.of_forall hB)
  have hIw : Integrable (fun x => w x * inner ℝ x (V x)) volume :=
    hIA.neg.congr (Eventually.of_forall fun x => by
      change -(∑ i : Fin n, A i x) = w x * inner ℝ x (V x)
      rw [hA, neg_neg])
  have Hsum : (∫ x, ∑ i : Fin n, B i x) = -(∫ x, ∑ i : Fin n, A i x) := by
    rw [integral_finsetSum _ (fun i _ => (hPair i).2.1),
      integral_finsetSum _ (fun i _ => (hPair i).1)]
    simp_rw [(hPair _).2.2]
    exact Finset.sum_neg_distrib (fun i : Fin n => ∫ x, A i x)
  refine ⟨hIκ, hIw, ?_⟩
  calc
    _ = ∫ x, ∑ i : Fin n, B i x := (integral_congr_ae (Eventually.of_forall hB)).symm
    _ = -(∫ x, ∑ i : Fin n, A i x) := Hsum
    _ = -(∫ x, -(w x * inner ℝ x (V x))) :=
      congrArg Neg.neg (integral_congr_ae (Eventually.of_forall hA))
    _ = _ := by rw [integral_neg, neg_neg]


/-- An actual smooth radial test and its nonnegative derivative weight have the exact thin-band support and gradient formula. -/
theorem radial_unitBall_test_properties (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    let κ := fun x : Domain n => Real.smoothTransition ((1-‖x‖^2)/ε)
    let w := fun x : Domain n => (2/ε) * deriv Real.smoothTransition ((1-‖x‖^2)/ε)
    ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
      (∀ x, 0 ≤ κ x ∧ κ x ≤ 1) ∧
      (∀ x, ‖x‖^2 ≤ 1-ε → κ x = 1) ∧
      (∀ x, 1 ≤ ‖x‖^2 → κ x = 0) ∧
      (∀ x, 0 ≤ w x) ∧
      (∀ x, 1 < ‖x‖^2 ∨ ‖x‖^2 < 1-ε → w x = 0) ∧
      ∀ x i, fderiv ℝ κ x (EuclideanSpace.single i 1) = -w x * x i := by
  intro κ w
  let τ := fun x : Domain n => (1-‖x‖^2)/ε
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hτ : ContDiff ℝ ∞ τ := (contDiff_const.sub (contDiff_norm_sq ℝ)).div_const ε
  have hκ : ContDiff ℝ ∞ κ := hs.comp hτ
  have hOut (x : Domain n) (hx : 1 ≤ ‖x‖^2) : κ x = 0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hε.le)
  have hts : tsupport κ ⊆ closedBall (0 : Domain n) 1 := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hnot
    have hn : 1 < ‖x‖ := not_le.mp (by simpa only [mem_closedBall, dist_zero_right] using hnot)
    exact hx (hOut x (by nlinarith only [sq_nonneg (‖x‖-1), hn]))
  have hcκ : HasCompactSupport κ :=
    (isCompact_closedBall (0 : Domain n) 1).of_isClosed_subset (isClosed_tsupport κ) hts
  refine ⟨hκ, hcκ, (fun x => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩),
    ?_, hOut, ?_, ?_, ?_⟩
  · intro x hx
    exact Real.smoothTransition.one_of_one_le ((le_div_iff₀ hε).mpr (by linarith only [hx]))
  · intro x
    exact mul_nonneg (div_nonneg (by norm_num) hε.le) Real.smoothTransition.monotone.deriv_nonneg
  · intro x hx
    have hd : deriv Real.smoothTransition (τ x) = 0 := by
      rcases hx with hx | hx
      · have ht : τ x < 0 := div_neg_of_neg_of_pos (sub_neg.mpr hx) hε
        have hev : ∀ᶠ t in 𝓝 (τ x), t < 0 := Iio_mem_nhds ht
        have heq : Real.smoothTransition =ᶠ[𝓝 (τ x)] (fun _t : ℝ => 0) :=
          hev.mono fun t ht => Real.smoothTransition.zero_of_nonpos ht.le
        simpa only [deriv_const] using heq.deriv_eq
      · have ht : 1 < τ x := (lt_div_iff₀ hε).mpr (by linarith only [hx])
        have hev : ∀ᶠ t in 𝓝 (τ x), 1 < t := Ioi_mem_nhds ht
        have heq : Real.smoothTransition =ᶠ[𝓝 (τ x)] (fun _t : ℝ => 1) :=
          hev.mono fun t ht => Real.smoothTransition.one_of_one_le ht.le
        simpa only [deriv_const] using heq.deriv_eq
    change (2/ε) * deriv Real.smoothTransition (τ x) = 0
    rw [hd, mul_zero]
  · intro x i
    have hnD : HasFDerivAt (fun y : Domain n => ‖y‖^2)
        ((2 : ℝ) • (innerSL ℝ x : Domain n →L[ℝ] ℝ)) x :=
      by
      simpa only [two_smul] using (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have hsubD : HasFDerivAt (fun y : Domain n => 1-‖y‖^2)
        (-((2 : ℝ) • (innerSL ℝ x : Domain n →L[ℝ] ℝ))) x := hnD.const_sub 1
    have hτD : HasFDerivAt τ ((ε⁻¹ : ℝ) • (-((2 : ℝ) • (innerSL ℝ x : Domain n →L[ℝ] ℝ)))) x := by
      apply (hsubD.const_smul (ε⁻¹ : ℝ)).congr_of_eventuallyEq
      exact Eventually.of_forall (fun y => by change (1-‖y‖^2)/ε = ε⁻¹*(1-‖y‖^2); ring)
    have hψD : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (τ x)) (τ x) :=
      (hs.differentiable (by simp) (τ x)).hasDerivAt
    have H := congrArg (fun D : Domain n →L[ℝ] ℝ => D (EuclideanSpace.single i 1))
      (hψD.comp_hasFDerivAt x hτD).fderiv
    have H' : fderiv ℝ κ x (EuclideanSpace.single i 1) =
        deriv Real.smoothTransition (τ x) * (ε⁻¹ * (-(2*x i))) := by
      simpa only [Function.comp_def, τ, κ, smul_apply, neg_apply,
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
        EuclideanSpace.inner_single_right, conj_trivial, one_mul, smul_eq_mul] using H
    rw [H']
    change deriv Real.smoothTransition (τ x) * (ε⁻¹ * (-(2*x i))) =
      -((2/ε)*deriv Real.smoothTransition (τ x)) * x i
    ring

end StationaryHarmonicMaps.Analysis

end
