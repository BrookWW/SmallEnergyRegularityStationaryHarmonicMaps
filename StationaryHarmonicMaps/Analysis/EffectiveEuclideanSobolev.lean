/-
The norm-power Sobolev argument is adapted from Mathlib's SobolevInequality.lean.
Copyright (c) 2024 Floris van Doorn and Heather Macbeth.
Released under Apache 2.0 license as described in LICENSES/Mathlib-Apache-2.0.txt.
-/
module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Sobolev estimates in the actual Euclidean coordinates

The coordinate map from the finite product to Euclidean space preserves
volume. Its norm is bounded by the dimension, so the coordinate Sobolev
estimate has an explicit constant without an unspecified basis equivalence.
-/

public section

open HarmonicMaps MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

theorem euclidean_toLp_norm_le (n : ℕ) (x : Fin n→ℝ) :
    ‖WithLp.toLp 2 x‖≤(n:ℝ)*‖x‖ := by
  classical
  have hSum : WithLp.toLp 2 x=∑i : Fin n,EuclideanSpace.single i (x i) := by
    ext j
    simp
  calc
    _≤∑i : Fin n,‖EuclideanSpace.single i (x i)‖ := by
      rw [hSum]
      exact norm_sum_le _ _
    _=∑i : Fin n,‖x i‖ := by simp
    _≤∑_i : Fin n,‖x‖ := Finset.sum_le_sum fun i _=>norm_le_pi_norm x i
    _=(n:ℝ)*‖x‖ := by simp

theorem euclidean_coordinate_inverse_norm_le (n : ℕ) :
    ‖((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=>ℝ)).symm :
      (Fin n→ℝ)→L[ℝ]Domain n)‖≤(n:ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg n)
  intro x
  exact euclidean_toLp_norm_le n x

theorem lintegral_pow_le_explicit_euclidean_fderiv
    (n : ℕ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ} (hp : Real.HolderConjugate n p) {u : Domain n→F}
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (∫⁻x,‖u x‖ₑ^p)≤((n:ℝ≥0∞)*(∫⁻x,‖fderiv ℝ u x‖ₑ))^p := by
  classical
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=>ℝ)
  let v : (Fin n→ℝ)→F := u∘e.symm
  have hv : ContDiff ℝ 1 v := hu.comp e.symm.contDiff
  have hvc : HasCompactSupport v := hc.comp_homeomorph e.symm.toHomeomorph
  have hp' : Real.HolderConjugate (Fintype.card (Fin n)) p := by simpa only [Fintype.card_fin] using hp
  have hBase := MeasureTheory.lintegral_pow_le_pow_lintegral_fderiv_aux hp' hv hvc
  have hMeasure : MeasurePreserving (e.symm : (Fin n→ℝ)→Domain n) :=
    PiLp.volume_preserving_toLp (Fin n)
  have hLeft : (∫⁻x,‖v x‖ₑ^p)=(∫⁻x,‖u x‖ₑ^p) := by
    borelize F
    have H := hMeasure.lintegral_comp (f:=fun x : Domain n=>‖u x‖ₑ^p)
      (hu.continuous.measurable.nnnorm.coe_nnreal_ennreal.pow_const _)
    simpa only [v,Function.comp_apply] using H
  have hRight : (∫⁻x,‖fderiv ℝ u (e.symm x)‖ₑ)=(∫⁻x,‖fderiv ℝ u x‖ₑ) := by
    exact hMeasure.lintegral_comp (f:=fun x : Domain n=>‖fderiv ℝ u x‖ₑ)
      ((hu.continuous_fderiv (by norm_num)).measurable.nnnorm.coe_nnreal_ennreal)
  have hDer (x : Fin n→ℝ) :
      ‖fderiv ℝ v x‖ₑ≤(n:ℝ≥0∞)*‖fderiv ℝ u (e.symm x)‖ₑ := by
    have hChain : fderiv ℝ v x=(fderiv ℝ u (e.symm x)).comp (e.symm : (Fin n→ℝ)→L[ℝ]Domain n) := by
      change fderiv ℝ (u∘e.symm) x=_
      rw [fderiv_comp x (hu.differentiable (by norm_num) _) e.symm.differentiableAt,e.symm.fderiv]
    rw [hChain]
    have hNorm : ‖(fderiv ℝ u (e.symm x)).comp (e.symm : (Fin n→ℝ)→L[ℝ]Domain n)‖≤
        (n:ℝ)*‖fderiv ℝ u (e.symm x)‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul_of_nonneg_left (euclidean_coordinate_inverse_norm_le n) (norm_nonneg _)).trans_eq (mul_comm _ _))
    have H := ENNReal.ofReal_le_ofReal hNorm
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
      ofReal_norm] using H
  rw [hLeft] at hBase
  apply hBase.trans
  apply ENNReal.rpow_le_rpow _ hp.symm.nonneg
  calc
    _≤∫⁻x,(n:ℝ≥0∞)*‖fderiv ℝ u (e.symm x)‖ₑ := lintegral_mono hDer
    _=(n:ℝ≥0∞)*(∫⁻x,‖fderiv ℝ u x‖ₑ) := by rw [lintegral_const_mul,hRight];fun_prop


theorem eLpNorm_le_explicit_euclidean_fderiv_one
    (n : ℕ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : Domain n→F} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    {p : ℝ≥0} (hp : NNReal.HolderConjugate n p) :
    eLpNorm u p volume≤(n:ℝ≥0∞)*eLpNorm (fderiv ℝ u) 1 volume := by
  have hp0 : 0<(p:ℝ) := hp.coe.symm.pos
  apply (ENNReal.rpow_le_rpow_iff hp0).mp
  rw [eLpNorm_nnreal_pow_eq_lintegral hp.symm.pos.ne', eLpNorm_one_eq_lintegral_enorm]
  exact lintegral_pow_le_explicit_euclidean_fderiv n hp.coe hu hc

/-- The explicit Euclidean Sobolev coefficient for an exponent below dimension. -/
@[expose] noncomputable def euclideanSobolevCoefficient (n : ℕ) (p : ℝ) : ℝ≥0 :=
  (n:ℝ≥0)*(p*((n:ℝ)-1)/((n:ℝ)-p)).toNNReal


theorem eLpNorm_le_explicit_euclidean_fderiv_of_eq_inner
    (n : ℕ) {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
    {u : Domain n → F'}
    (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hn : 0 < n)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (n : ℝ)⁻¹) :
    eLpNorm u p' volume ≤ euclideanSobolevCoefficient n p * eLpNorm (fderiv ℝ u) p volume := by
  /- Here we derive the GNS-inequality for `p ≥ 1` from the version with `p = 1`.
  For `p > 1` we apply the previous version to the function `|u|^γ` for a suitably chosen `γ`.
  The proof requires that `x ↦ |x|^p` is smooth in the codomain, so we require that it is a
  Hilbert space. -/
  by_cases hp'0 : p' = 0
  · simp [hp'0]
  let n' := NNReal.conjExponent n
  have h2p : (p : ℝ) < n := by
    have : 0 < p⁻¹ - (n : ℝ)⁻¹ :=
      NNReal.coe_lt_coe.mpr (pos_iff_ne_zero.mpr (inv_ne_zero hp'0)) |>.trans_eq hp'
    rwa [NNReal.coe_inv, sub_pos,
      inv_lt_inv₀ _ (zero_lt_one.trans_le (NNReal.coe_le_coe.mpr hp))] at this
    exact_mod_cast hn
  have h0n : 2 ≤ n := Nat.succ_le_of_lt <| Nat.one_lt_cast.mp <| hp.trans_lt h2p
  have hn : NNReal.HolderConjugate n n' := .conjExponent (by norm_cast)
  have h1n : 1 ≤ (n : ℝ≥0) := hn.lt.le
  have h2n : (0 : ℝ) < n - 1 := by simp_rw [sub_pos]; exact hn.coe.lt
  have hnp : (0 : ℝ) < n - p := by simp_rw [sub_pos]; exact h2p
  rcases hp.eq_or_lt with rfl | hp
  -- the case `p = 1`
  · convert! eLpNorm_le_explicit_euclidean_fderiv_one n hu h2u hn using 2
    · suffices (p' : ℝ) = n' by simpa using this
      rw [← inv_inj, hp']
      simp [field, n', NNReal.conjExponent, *]
    · norm_cast
      simp only [euclideanSobolevCoefficient, one_mul,
        div_self h2n.ne', Real.toNNReal_one, mul_one]
  -- the case `p > 1`
  let q := Real.conjExponent p
  have hq : Real.HolderConjugate p q := .conjExponent hp
  have h0p : p ≠ 0 := zero_lt_one.trans hp |>.ne'
  have h1p : (p : ℝ) ≠ 1 := hq.lt.ne'
  have h3p : (p : ℝ) - 1 ≠ 0 := sub_ne_zero_of_ne h1p
  have h2q : 1 / n' - 1 / q = 1 / p' := by
    simp_rw -zeta [one_div, hp']
    rw [← hq.one_sub_inv, ← hn.coe.one_sub_inv, sub_sub_sub_cancel_left]
    simp only [NNReal.coe_natCast, NNReal.coe_inv]
  let γ : ℝ≥0 := .mk (p * (n - 1) / (n - p)) (by positivity)
  have h0γ : (γ : ℝ) = p * (n - 1) / (n - p) := rfl
  have h1γ : 1 < (γ : ℝ) := by
    rwa [h0γ, one_lt_div hnp, mul_sub, mul_one, sub_lt_sub_iff_right, lt_mul_iff_one_lt_left]
    exact hn.coe.pos
  have h2γ : γ * n' = p' := by
    rw [← NNReal.coe_inj, ← inv_inj, hp', NNReal.coe_mul, h0γ, hn.coe.conjugate_eq]
    simp [field]
  have h3γ : (γ - 1) * q = p' := by
    rw [← inv_inj, hp', h0γ, hq.conjugate_eq]
    have : (p : ℝ) * (n - 1) - (n - p) = n * (p - 1) := by ring
    simp [field, this]
  have h4γ : (γ : ℝ) ≠ 0 := (zero_lt_one.trans h1γ).ne'
  by_cases h3u : ∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂volume = 0
  · rw [eLpNorm_nnreal_eq_lintegral hp'0, h3u, ENNReal.zero_rpow_of_pos] <;> positivity
  have h4u : ∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂volume ≠ (⊤ : ℝ≥0∞) := by
    refine lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top
      ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hp'0) ?_ |>.ne
    rw [← eLpNorm_nnreal_eq_eLpNorm' hp'0]
    exact hu.continuous.memLp_of_hasCompactSupport (μ := volume) h2u |>.eLpNorm_lt_top
  have h5u : (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂volume) ^ (1 / q) ≠ 0 :=
    ENNReal.rpow_pos (pos_iff_ne_zero.mpr h3u) h4u |>.ne'
  have h6u : (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂volume) ^ (1 / q) ≠ (⊤ : ℝ≥0∞) := by finiteness
  have h7u := hu.continuous -- for fun_prop
  let v : Domain n → ℝ := fun x ↦ ‖u x‖ ^ (γ : ℝ)
  have hv : ContDiff ℝ 1 v := hu.norm_rpow h1γ
  have h2v : HasCompactSupport v := h2u.norm.rpow_const h4γ
  let C : ℝ≥0 := n
  have :=
  calc (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂volume) ^ (1 / (n' : ℝ)) = eLpNorm v n' volume := by
        rw [← h2γ, eLpNorm_nnreal_eq_lintegral hn.symm.pos.ne']
        simp (discharger := positivity) [v, Real.enorm_rpow_of_nonneg, ENNReal.rpow_mul]
    _ ≤ C * eLpNorm (fderiv ℝ v) 1 volume := eLpNorm_le_explicit_euclidean_fderiv_one n hv h2v hn
    _ = C * ∫⁻ x, ‖fderiv ℝ v x‖ₑ ∂volume := by rw [eLpNorm_one_eq_lintegral_enorm]
    _ ≤ C * γ * ∫⁻ x, ‖u x‖ₑ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ u x‖ₑ ∂volume := by
      rw [mul_assoc, ← lintegral_const_mul γ]
      · gcongr
        simp_rw [← mul_assoc]
        exact enorm_fderiv_norm_rpow_le (hu.differentiable one_ne_zero) h1γ
      dsimp [enorm]
      fun_prop
    _ ≤ C * γ * ((∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂volume) ^ (1 / q) *
        (∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (p : ℝ) ∂volume) ^ (1 / (p : ℝ))) := by
        gcongr
        convert!
          ENNReal.lintegral_mul_le_Lp_mul_Lq volume (.symm <| .conjExponent <| show 1 < (p : ℝ) from hp)
            ?_ ?_ using 5
        · simp [γ, q, ← ENNReal.rpow_mul, ← h3γ]
        · borelize F'
          fun_prop
        · fun_prop
    _ = C * γ * (∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (p : ℝ) ∂volume) ^ (1 / (p : ℝ)) *
      (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂volume) ^ (1 / q) := by ring
  calc
    eLpNorm u p' volume
      = (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂volume) ^ (1 / (p' : ℝ)) := eLpNorm_nnreal_eq_lintegral hp'0
    _ ≤ C * γ * (∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (p : ℝ) ∂volume) ^ (1 / (p : ℝ)) := by
      rwa [← h2q, ENNReal.rpow_sub _ _ h3u h4u, ENNReal.div_le_iff h5u h6u]
    _ = euclideanSobolevCoefficient n p * eLpNorm (fderiv ℝ u) (↑p) volume := by
      suffices (C : ℝ) * γ = euclideanSobolevCoefficient n p by
        rw [eLpNorm_nnreal_eq_lintegral h0p]
        congr
        norm_cast at this ⊢
      simp_rw [euclideanSobolevCoefficient, γ]
      refold_let n' C
      rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal', mul_eq_mul_left_iff, eq_comm,
        max_eq_left_iff]
      left
      positivity

end StationaryHarmonicMaps.Analysis
