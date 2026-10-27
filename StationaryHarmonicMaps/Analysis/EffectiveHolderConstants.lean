module

public import StationaryHarmonicMaps.Analysis.GeometricRpowIteration
public import StationaryHarmonicMaps.Analysis.LocalLpMorreyRepresentative
public import StationaryHarmonicMaps.Analysis.EffectiveEuclideanVolume
public import Mathlib.Data.Rat.Cast.Order

/-!
# Explicit arithmetic for the compensated envelope

The contraction scale and coefficient smallness are rational operations in
the supplied improvement constant. The helper theorems verify the two power
absorptions and the resulting scalar recurrence bound. Analytic estimates
for the improvement constant remain separate inputs to these helpers.
-/

@[expose] public section

namespace StationaryHarmonicMaps.Analysis

open HarmonicMaps MeasureTheory Metric

def rationalEnvelopeScale (G : ℚ) : ℚ := (2 + 8 * G)⁻¹ ^ 2

def rationalEnvelopeSmallness (n : ℕ) (G : ℚ) : ℚ :=
  rationalEnvelopeScale G ^ n / (4 * (1 + G))

noncomputable def effectiveEnvelopeScale (G : ℝ) : ℝ := (2 + 8 * G)⁻¹ ^ 2

noncomputable def effectiveEnvelopeSmallness (n : ℕ) (G : ℝ) : ℝ :=
  effectiveEnvelopeScale G ^ n / (4 * (1 + G))

theorem rationalEnvelopeScale_cast (G : ℚ) :
    (rationalEnvelopeScale G : ℝ) = effectiveEnvelopeScale G := by
  simp only [rationalEnvelopeScale, effectiveEnvelopeScale, Rat.cast_pow,
    Rat.cast_inv, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]

theorem rationalEnvelopeSmallness_cast (n : ℕ) (G : ℚ) :
    (rationalEnvelopeSmallness n G : ℝ) = effectiveEnvelopeSmallness n G := by
  simp only [rationalEnvelopeSmallness, effectiveEnvelopeSmallness,
    Rat.cast_div, Rat.cast_pow, rationalEnvelopeScale_cast,
    Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_one]

theorem effectiveEnvelopeScale_bounds (G : ℝ) (hG : 0 ≤ G) :
    0 < effectiveEnvelopeScale G ∧ effectiveEnvelopeScale G ≤ 1 / 2 := by
  have hbase : (2 : ℝ) ≤ 2 + 8 * G := by linarith only [hG]
  have hpos : 0 < 2 + 8 * G := lt_of_lt_of_le (by norm_num) hbase
  have hinv : (2 + 8 * G)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hbase
  constructor
  · exact sq_pos_of_pos (inv_pos.mpr hpos)
  · change ((2 + 8 * G)⁻¹) ^ 2 ≤ (1 / 2 : ℝ)
    nlinarith only [hinv, inv_nonneg.mpr hpos.le]

theorem effectiveEnvelopeSmallness_bounds (n : ℕ) (G : ℝ) (hG : 0 ≤ G) :
    0 < effectiveEnvelopeSmallness n G ∧ effectiveEnvelopeSmallness n G ≤ 1 := by
  obtain ⟨hθ, hθHalf⟩ := effectiveEnvelopeScale_bounds G hG
  have hden : 0 < 4 * (1 + G) := by positivity
  constructor
  · exact div_pos (pow_pos hθ n) hden
  · apply (div_le_iff₀ hden).mpr
    have hpow := pow_le_one₀ hθ.le (show effectiveEnvelopeScale G ≤ 1 by linarith only [hθHalf]) (n := n)
    change effectiveEnvelopeScale G ^ n ≤ 1 * (4 * (1 + G))
    linarith only [hpow, hG]

/-- Explicit scale absorption for the exponent beta = p/2. -/
theorem effective_envelope_scale_absorption_helper (G p : ℝ) (hG : 0 ≤ G)
    (hp : 1 ≤ p) :
    G * effectiveEnvelopeScale G ^ p ≤ effectiveEnvelopeScale G ^ (p / 2) / 2 := by
  let θ := effectiveEnvelopeScale G
  obtain ⟨hθ, hθHalf⟩ := effectiveEnvelopeScale_bounds G hG
  have hθOne : θ ≤ 1 := by dsimp only [θ]; linarith only [hθHalf]
  have hb : 0 < 2 + 8 * G := by positivity
  have hroot : θ ^ (1 / 2 : ℝ) = (2 + 8 * G)⁻¹ := by
    change (((2 + 8 * G)⁻¹) ^ 2) ^ (1 / 2 : ℝ) = _
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (inv_nonneg.mpr hb.le)]
  have hhalf : (1 / 2 : ℝ) ≤ p / 2 := by linarith only [hp]
  have hβ : θ ^ (p / 2) ≤ (2 + 8 * G)⁻¹ := by
    exact (Real.rpow_le_rpow_of_exponent_ge hθ hθOne hhalf).trans_eq hroot
  have hratio : G * (2 + 8 * G)⁻¹ ≤ (1 / 2 : ℝ) := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hb).mpr (by linarith only [hG])
  have hcoeff : G * θ ^ (p / 2) ≤ (1 / 2 : ℝ) :=
    (mul_le_mul_of_nonneg_left hβ hG).trans hratio
  have hsplit : θ ^ p = θ ^ (p / 2) * θ ^ (p / 2) := by
    rw [← Real.rpow_add hθ]
    congr 1
    ring
  change G * θ ^ p ≤ θ ^ (p / 2) / 2
  rw [hsplit]
  calc
    G * (θ ^ (p / 2) * θ ^ (p / 2)) = (G * θ ^ (p / 2)) * θ ^ (p / 2) := by ring
    _ ≤ (1 / 2 : ℝ) * θ ^ (p / 2) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hθ.le _)
    _ = θ ^ (p / 2) / 2 := by ring

/-- The explicit rational smallness absorbs the original Morrey coefficient. -/
theorem effective_envelope_morrey_absorption_helper (n : ℕ) (G p η : ℝ)
    (hG : 0 ≤ G) (hp : 1 ≤ p) (hη : 0 ≤ η)
    (hηSmall : η ≤ effectiveEnvelopeSmallness n G) :
    G * η ^ p * effectiveEnvelopeScale G ^ (p - (n : ℝ)) ≤
      effectiveEnvelopeScale G ^ (p / 2) / 2 := by
  let θ := effectiveEnvelopeScale G
  obtain ⟨hθ, hθHalf⟩ := effectiveEnvelopeScale_bounds G hG
  have hθOne : θ ≤ 1 := by dsimp only [θ]; linarith only [hθHalf]
  have hηOne : η ≤ 1 := hηSmall.trans (effectiveEnvelopeSmallness_bounds n G hG).2
  have hηp : η ^ p ≤ effectiveEnvelopeSmallness n G :=
    (Real.rpow_le_self_of_le_one hη hηOne hp).trans hηSmall
  have hden : 0 < 4 * (1 + G) := by positivity
  have hcancel : θ ^ n * θ ^ (p - (n : ℝ)) = θ ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hθ]
    congr 1
    ring
  have hcoeff : G / (4 * (1 + G)) ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ hden).mpr (by linarith only [hG])
  have hpower : θ ^ p ≤ θ ^ (p / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hθ hθOne (by linarith only [hp])
  change G * η ^ p * θ ^ (p - (n : ℝ)) ≤ θ ^ (p / 2) / 2
  calc
    _ ≤ G * effectiveEnvelopeSmallness n G * θ ^ (p - (n : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hηp hG) (Real.rpow_nonneg hθ.le _)
    _ = (G / (4 * (1 + G))) * θ ^ p := by
      dsimp only [effectiveEnvelopeSmallness]
      change G * (θ ^ n / (4 * (1 + G))) * θ ^ (p - (n : ℝ)) = _
      rw [div_eq_mul_inv]
      calc
        _ = (G * (4 * (1 + G))⁻¹) * (θ ^ n * θ ^ (p - (n : ℝ))) := by ring
        _ = _ := by rw [hcancel, div_eq_mul_inv]
    _ ≤ (1 / 2 : ℝ) * θ ^ (p / 2) :=
      mul_le_mul hcoeff hpower (Real.rpow_nonneg hθ.le _) (by norm_num)
    _ = θ ^ (p / 2) / 2 := by ring

theorem effective_envelope_combined_absorption_helper (n : ℕ) (G p η : ℝ)
    (hG : 0 ≤ G) (hp : 1 ≤ p) (hη : 0 ≤ η)
    (hηSmall : η ≤ effectiveEnvelopeSmallness n G) :
    G * (η ^ p * effectiveEnvelopeScale G ^ (p - (n : ℝ)) +
        effectiveEnvelopeScale G ^ p) ≤ effectiveEnvelopeScale G ^ (p / 2) := by
  have hfirst := effective_envelope_morrey_absorption_helper n G p η hG hp hη hηSmall
  have hsecond := effective_envelope_scale_absorption_helper G p hG hp
  nlinarith only [hfirst, hsecond]

def rationalRecurrenceMajorant (σ A B : ℚ) : ℚ := (B + 2 * A / σ) / σ

/-- A half-power recurrence admits a coefficient using rational operations
in the supplied scale and forcing constants. This is a scalar helper. -/
theorem effective_half_contraction_growth_helper (f : ℝ → ℝ)
    {β σ A B r₀ : ℝ} (hβ : 0 ≤ β) (hβOne : β ≤ 1)
    (hσ : 0 < σ) (hσOne : σ < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hr₀ : 0 < r₀)
    (hmono : ∀ r s : ℝ, 0 < r → r ≤ s → s ≤ r₀ → f r ≤ f s)
    (hbase : f r₀ ≤ B * r₀ ^ β)
    (hstep : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      f (σ * r) ≤ (σ ^ β / 2) * f r + A * r ^ β) :
    ∀ r : ℝ, 0 < r → r ≤ r₀ →
      f r ≤ ((B + 2 * A / σ) / σ) * r ^ β := by
  have hpow : 0 < σ ^ β := Real.rpow_pos_of_pos hσ _
  have hσPow : σ ≤ σ ^ β := Real.self_le_rpow_of_le_one hσ.le hσOne.le hβOne
  have hgap : σ ^ β / 2 < σ ^ β := half_lt_self hpow
  have H := all_radius_rpow_bound_of_recurrence f hβ hσ hσOne
    (half_pos hpow).le hgap hA hB hr₀ hmono hbase hstep
  have hden : σ ^ β - σ ^ β / 2 = σ ^ β / 2 := by ring
  have hforcing : A / (σ ^ β - σ ^ β / 2) ≤ 2 * A / σ := by
    rw [hden]
    have hEq : A / (σ ^ β / 2) = 2 * A / σ ^ β := by field_simp
    rw [hEq]
    exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hA) hσ hσPow
  have hmajor : (B + A / (σ ^ β - σ ^ β / 2)) / σ ^ β ≤
      (B + 2 * A / σ) / σ := by
    calc
      _ ≤ (B + 2 * A / σ) / σ ^ β :=
        div_le_div_of_nonneg_right (add_le_add_right hforcing B) hpow.le
      _ ≤ _ := div_le_div_of_nonneg_left
        (add_nonneg hB (div_nonneg (mul_nonneg (by norm_num) hA) hσ.le)) hσ hσPow
  intro r hr hcap
  exact (H r hr hcap).trans
    (mul_le_mul_of_nonneg_right hmajor (Real.rpow_nonneg hr.le _))

theorem effective_root_majorant_helper (D p : ℝ) (hD : 0 ≤ D) (hp : 1 ≤ p) :
    D ^ (1 / p) ≤ 1 + D := by
  have hpPos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hinv : 0 ≤ 1 / p := (div_pos zero_lt_one hpPos).le
  by_cases hDOne : D ≤ 1
  · exact (Real.rpow_le_one hD hDOne hinv).trans (le_add_of_nonneg_right hD)
  · have hOneD : 1 ≤ D := (not_le.mp hDOne).le
    have hInvOne : 1 / p ≤ 1 := (div_le_one hpPos).mpr hp
    exact (Real.rpow_le_self_of_one_le hOneD hInvOne).trans
      (le_add_of_nonneg_left zero_le_one)

/-- Coarsening the final root factor does not require computing a real power. -/
theorem effective_holder_assembly_majorant_helper (S D p : ℝ)
    (hS : 0 ≤ S) (hD : 0 ≤ D) (hp : 1 ≤ p) :
    S * D ^ (1 / p) ≤ S * (1 + D) :=
  mul_le_mul_of_nonneg_left (effective_root_majorant_helper D p hD hp) hS

def explicitLpMorreyRepresentativeMajorant (n : ℕ) : ℕ :=
  1 + 512 * 2 ^ n * (2 ^ (n + 1) * (n + 1) * (1 + (n + 1) ^ n))


theorem localLpMorreyRepresentativeConstant_le_of_half_le (n : ℕ) (p α : ℝ) (hp : 1 ≤ p)
    (hαHalf : (1 / 2 : ℝ) ≤ α) (hαOne : α ≤ 1) :
    localLpMorreyRepresentativeConstant n p α ≤
      (explicitLpMorreyRepresentativeMajorant n : ℝ) := by
  let V : ℝ := volume.real (ball (0 : Domain n) 1)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hV : 0 < V := HolderToCK.ball_volume_real_pos 0 (by norm_num : (0 : ℝ) < 1)
  have hsmall : 0 < (1 / ((n : ℝ) + 1)) ^ n := by positivity
  have hInv : V⁻¹ ≤ ((n : ℝ) + 1) ^ n := by
    have H := one_div_le_one_div_of_le hsmall (euclidean_unit_ball_volume_lower_bound n)
    simpa only [one_div, inv_pow, inv_inv, V] using H
  have hpower : V ^ (-(1 / p)) ≤ 1 + ((n : ℝ) + 1) ^ n := by
    have heq : V ^ (-(1 / p)) = V⁻¹ ^ (1 / p) := by
      rw [Real.rpow_neg hV.le, Real.inv_rpow hV.le]
    rw [heq]
    exact (effective_root_majorant_helper V⁻¹ p (inv_nonneg.mpr hV.le) hp).trans
      (add_le_add_right hInv 1)
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) + 1 := by
    have Hsq := Real.sq_sqrt hn
    have Hnonneg := Real.sqrt_nonneg (n : ℝ)
    nlinarith only [Hsq, Hnonneg, hn, sq_nonneg (n : ℝ)]
  have hD : ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) * V ^ (-(1 / p)) ≤
      (2 : ℝ) ^ (n + 1) * ((n : ℝ) + 1) * (1 + ((n : ℝ) + 1) ^ n) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by positivity)) hpower
      (Real.rpow_nonneg hV.le _) (by positivity)
  have H := mul_le_mul (localCampanatoConstant_le_of_half_le n α hαHalf hαOne) hD
    (by positivity : 0 ≤ ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) * V ^ (-(1 / p)))
    (by positivity : 0 ≤ (512 : ℝ) * 2 ^ n)
  change 1 + localCampanatoConstant n α *
    (((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) * V ^ (-(1 / p))) ≤ _
  have Hfinal := add_le_add_right H 1
  simpa only [explicitLpMorreyRepresentativeMajorant, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using Hfinal

theorem localLpMorreyRepresentativeConstant_half_le (n : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    localLpMorreyRepresentativeConstant n p (1 / 2) ≤
      (explicitLpMorreyRepresentativeMajorant n : ℝ) :=
  localLpMorreyRepresentativeConstant_le_of_half_le n p (1 / 2) hp le_rfl (by norm_num)

theorem globalLpMorreyRepresentativeConstant_le_of_half_le (n : ℕ) (p α : ℝ)
    (hp : 1 ≤ p) (hαHalf : (1 / 2 : ℝ) ≤ α) (hαOne : α ≤ 1) :
    globalLpMorreyRepresentativeConstant n p α ≤
      (explicitLpMorreyRepresentativeMajorant n : ℝ) := by
  have hα : 0 < α := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hαHalf
  have hden : 0 < 1 - (1 / 2 : ℝ)^α := sub_pos.mpr
    (Real.rpow_lt_one (by norm_num) (by norm_num) hα)
  have hH : 0 ≤ meanOscillationHolderConstant n α := by
    rw [meanOscillationHolderConstant_eq]
    positivity
  apply le_trans ?_ (localLpMorreyRepresentativeConstant_le_of_half_le n p α hp hαHalf hαOne)
  unfold globalLpMorreyRepresentativeConstant localLpMorreyRepresentativeConstant localCampanatoConstant
  rw [abs_of_nonneg hH, meanOscillationHolderConstant_eq]
  rw [meanOscillationHolderConstant_eq] at hH
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right
  · nlinarith only [hH]
  · positivity

/-- The original local weak graph and gradient growth give the same unique
half-ball representative with a computable integer dimension coefficient. -/
theorem existsUnique_local_representative_of_lp_growth_half_explicit
    (n : ℕ) (p : ℝ) (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2)
    (q : ℕ) (Ω : OpenDomain n) (u : Domain n → Ambient q)
    (Du : Domain n → Gradient n q) (K : ℝ) (a : Domain n) (R : ℝ)
    (hu : MemW12Loc Ω u Du) (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val) (hK : 0 ≤ K)
    (hgrowth : ∀ x : Domain n, x ∈ Metric.ball a (3 * R / 4) →
      ∀ r : ℝ, 0 < r → r ≤ R / 4 →
        (∫ y in Metric.ball x r, (Real.sqrt (hsNormSq (Du y))) ^ p) ≤
          K ^ p * r ^ ((n : ℝ) - p + p * (1 / 2))) :
    ∃! w : Metric.ball a (R / 2) → Ambient q,
      IsContinuousRepresentative (ballDomain a (R / 2)) u w ∧
      ∀ x y : Metric.ball a (R / 2),
        ‖w x - w y‖ ≤ (explicitLpMorreyRepresentativeMajorant n : ℝ) * K *
          (dist (x : Domain n) (y : Domain n)) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, _hC, hFormula, H⟩ :=
    existsUnique_local_representative_of_lp_gradient_growth_explicit
      n p (1 / 2) hp₁ hp₂ (by norm_num) (by norm_num)
  have hCbound : C ≤ (explicitLpMorreyRepresentativeMajorant n : ℝ) := by
    rw [hFormula]
    exact localLpMorreyRepresentativeConstant_half_le n p hp₁
  obtain ⟨w, hw, _hUnique⟩ := H q Ω u Du K a R hu hR hball hK hgrowth
  refine ⟨w, ⟨hw.1, ?_⟩, ?_⟩
  · intro x y
    exact (hw.2 x y).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCbound hK) (Real.rpow_nonneg dist_nonneg _))
  · intro v hv
    exact hv.1.unique hw.1

end StationaryHarmonicMaps.Analysis

end
