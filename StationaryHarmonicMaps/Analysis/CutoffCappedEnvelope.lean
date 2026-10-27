module

public import StationaryHarmonicMaps.Analysis.CutoffLpEnvelope
public import StationaryHarmonicMaps.Analysis.LpMorreyRepresentative
public import StationaryHarmonicMaps.Analysis.CriticalMorreyMeanOscillation
public import StationaryHarmonicMaps.Analysis.LocalLpCriticalCutoff

/-!
# The finite scale envelope of the actual Sobolev cutoff

The supremum uses every center and every positive radius below its cap.
The actual cutoff estimate supplies boundedness before any conditional
completeness lemma is used. Poincare then bounds the mean oscillation on
every subball by the same envelope, with no boundary restriction on centers.
-/

@[expose] public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem capped_sup_properties {X : Type*} (a : X) (Φ : X → ℝ → ℝ)
    {r₀ K : ℝ} (hbound : ∀ x r, 0 < r → r ≤ r₀ → Φ x r ≤ K)
    (hnonneg : ∀ x r, 0 < r → 0 ≤ Φ x r) :
    let Ψ := fun t : ℝ => sSup {z : ℝ | ∃ x r, 0 < r ∧ r ≤ t ∧ z = Φ x r}
    ∀ t, 0 < t → t ≤ r₀ →
      0 ≤ Ψ t ∧ Ψ t ≤ K ∧
      (∀ x r, 0 < r → r ≤ t → Φ x r ≤ Ψ t) ∧
      (∀ s, 0 < s → s ≤ t → Ψ s ≤ Ψ t) := by
  intro Ψ t ht htr₀
  have hne (s : ℝ) (hs : 0 < s) :
      ({z : ℝ | ∃ x r, 0 < r ∧ r ≤ s ∧ z = Φ x r}).Nonempty :=
    ⟨Φ a s, a, s, hs, le_rfl, rfl⟩
  have hbd (s : ℝ) (hs : s ≤ r₀) :
      BddAbove {z : ℝ | ∃ x r, 0 < r ∧ r ≤ s ∧ z = Φ x r} := by
    refine ⟨K, ?_⟩
    rintro z ⟨x, r, hr, hrs, rfl⟩
    exact hbound x r hr (hrs.trans hs)
  have hterm (x : X) (r : ℝ) (hr : 0 < r) (hrt : r ≤ t) : Φ x r ≤ Ψ t :=
    le_csSup (hbd t htr₀) ⟨x, r, hr, hrt, rfl⟩
  refine ⟨(hnonneg a t ht).trans (hterm a t ht le_rfl), ?_, hterm, ?_⟩
  · apply csSup_le (hne t ht)
    rintro z ⟨x, r, hr, hrt, rfl⟩
    exact hbound x r hr (hrt.trans htr₀)
  · intro s hs hst
    apply csSup_le (hne s hs)
    rintro z ⟨x, r, hr, hrs, rfl⟩
    exact hterm x r hr (hrs.trans hst)

def effectiveCutoffCappedEnvelopeConstant (n A B : ℕ) : ℕ :=
  1+effectiveCutoffLpEnvelopeConstant n A B+effectiveLpMeanOscillationConstant n

/-- The actual cutoff has a finite, monotone, all-center envelope controlling every ball mean oscillation. -/
theorem exists_cutoff_capped_envelope (n : ℕ) (hn : 2 ≤ n)
    (p : ℝ) (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      ∀ (χ : Domain n → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Metric.closedBall (0 : Domain n) (3 / 4 : ℝ) →
      (∀ x, |χ x| ≤ A) →
      (∀ (x : Domain n) (i : Fin n), |fderiv ℝ χ x (EuclideanSpace.single i 1)| ≤ B) →
      let c := ⨍ y in Metric.ball (0 : Domain n) 1, u y
      let v := fun x => χ x • (u x - c)
      let Dv := fun x i => χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c)
      let Φ := fun (x : Domain n) (r : ℝ) => r ^ (p - (n : ℝ)) *
        ∫ y in Metric.ball x r, (Real.sqrt (hsNormSq (Dv y))) ^ p
      let Ψ := fun t : ℝ => sSup {z : ℝ | ∃ x r, 0 < r ∧ r ≤ t ∧ z = Φ x r}
      MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) v Dv ∧
      ∀ t : ℝ, 0 < t → t ≤ (1 / 16 : ℝ) →
        0 ≤ Ψ t ∧ Ψ t ≤ C * η ^ p ∧
        (∀ (x : Domain n) (r : ℝ), 0 < r → r ≤ t → Φ x r ≤ Ψ t) ∧
        (∀ s : ℝ, 0 < s → s ≤ t → Ψ s ≤ Ψ t) ∧
        (∀ (x : Domain n) (r : ℝ), 0 < r → r ≤ t →
          (⨍ y in Metric.ball x r, ‖v y - (⨍ z in Metric.ball x r, v z)‖) ≤
            C * (Ψ t) ^ (1 / p) ∧
          (⨍ y in Metric.ball x r, ‖v y - (⨍ z in Metric.ball x r, v z)‖) ^ p ≤
            C ^ p * Ψ t) := by
  have hp : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp₁
  obtain ⟨D, hD, hinitial⟩ := exists_cutoff_lp_envelope_bound n hn p hp hp₂ A B hA hB
  let P : ℝ := ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) *
    (volume.real (Metric.ball (0 : Domain n) 1)) ^ (-(1 / p))
  let C : ℝ := 1 + D + P
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hDC : D ≤ C := by dsimp only [C]; linarith only [hP]
  have hPC : P ≤ C := by dsimp only [C]; linarith only [hD]
  refine ⟨C, hC, ?_⟩
  intro q u Du η hu hη hcritical χ hχ hcχ hsχ hχA hDχB c v Dv Φ Ψ
  obtain ⟨hW, hbound⟩ := hinitial q u Du η hu hη hcritical χ hχ hcχ hsχ hχA hDχB
  have hΦ (x : Domain n) (r : ℝ) (hr : 0 < r) : 0 ≤ Φ x r :=
    mul_nonneg (Real.rpow_nonneg hr.le _)
      (integral_nonneg fun _y => Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hΨ := capped_sup_properties (0 : Domain n) Φ
    (r₀ := (1 / 16 : ℝ)) (K := D * η ^ p)
    (fun x r hr _ => (hbound x r hr).2) hΦ
  refine ⟨hW, ?_⟩
  intro t ht htcap
  obtain ⟨hnonneg, hupper, hterm, hmono⟩ := hΨ t ht htcap
  refine ⟨hnonneg, hupper.trans (mul_le_mul_of_nonneg_right hDC (Real.rpow_nonneg hη _)),
    hterm, hmono, ?_⟩
  intro x r hr hrt
  have hcancel : r ^ ((n : ℝ) - p) * r ^ (p - (n : ℝ)) = 1 := by
    rw [← Real.rpow_add hr]
    have he : (n : ℝ) - p + (p - (n : ℝ)) = 0 := by ring
    rw [he, Real.rpow_zero]
  have hgrowth : (∫ y in Metric.ball x r, (Real.sqrt (hsNormSq (Dv y))) ^ p) ≤
      ((Ψ t) ^ (1 / p)) ^ p * r ^ ((n : ℝ) - p + p * (0 : ℝ)) := by
    have H := mul_le_mul_of_nonneg_left (hterm x r hr hrt)
      (Real.rpow_nonneg hr.le ((n : ℝ) - p))
    change r ^ ((n : ℝ) - p) *
      (r ^ (p - (n : ℝ)) * ∫ y in Metric.ball x r,
        (Real.sqrt (hsNormSq (Dv y))) ^ p) ≤ r ^ ((n : ℝ) - p) * Ψ t at H
    rw [← mul_assoc, hcancel, one_mul] at H
    rw [one_div, Real.rpow_inv_rpow hnonneg hp.ne', mul_zero, add_zero]
    exact H.trans_eq (mul_comm _ _)
  have hlocal : MemW12 (ballDomain x r) v Dv :=
    memW12_of_openDomain_subset hW (subset_univ _)
  have H := sobolev_meanOscillation_of_lp_growth (p := p) (α := 0) x hr hp₁ hp₂
    (Real.rpow_nonneg hnonneg (1 / p)) hlocal hgrowth
  rw [Real.rpow_zero, mul_one] at H
  have Hroot := H.trans (mul_le_mul_of_nonneg_right hPC (Real.rpow_nonneg hnonneg _))
  refine ⟨Hroot, ?_⟩
  have hmean0 : 0 ≤ (⨍ y in Metric.ball x r, ‖v y - (⨍ z in Metric.ball x r, v z)‖) := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun _y => norm_nonneg _)
  have Hpower := Real.rpow_le_rpow hmean0 Hroot hp.le
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg hnonneg _), one_div,
    Real.rpow_inv_rpow hnonneg hp.ne'] at Hpower
  exact Hpower

theorem exists_cutoff_capped_envelope_effective (n : ℕ) (hn : 2 ≤ n)
    (p : ℝ) (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2)
    (A B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ C=(effectiveCutoffCappedEnvelopeConstant n A B:ℝ) ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      ∀ (χ : Domain n → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Metric.closedBall (0 : Domain n) (3 / 4 : ℝ) →
      (∀ x, |χ x| ≤ (A:ℝ)) →
      (∀ (x : Domain n) (i : Fin n), |fderiv ℝ χ x (EuclideanSpace.single i 1)| ≤ (B:ℝ)) →
      let c := ⨍ y in Metric.ball (0 : Domain n) 1, u y
      let v := fun x => χ x • (u x - c)
      let Dv := fun x i => χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c)
      let Φ := fun (x : Domain n) (r : ℝ) => r ^ (p - (n : ℝ)) *
        ∫ y in Metric.ball x r, (Real.sqrt (hsNormSq (Dv y))) ^ p
      let Ψ := fun t : ℝ => sSup {z : ℝ | ∃ x r, 0 < r ∧ r ≤ t ∧ z = Φ x r}
      MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) v Dv ∧
      ∀ t : ℝ, 0 < t → t ≤ (1 / 16 : ℝ) →
        0 ≤ Ψ t ∧ Ψ t ≤ C * η ^ p ∧
        (∀ (x : Domain n) (r : ℝ), 0 < r → r ≤ t → Φ x r ≤ Ψ t) ∧
        (∀ s : ℝ, 0 < s → s ≤ t → Ψ s ≤ Ψ t) ∧
        (∀ (x : Domain n) (r : ℝ), 0 < r → r ≤ t →
          (⨍ y in Metric.ball x r, ‖v y - (⨍ z in Metric.ball x r, v z)‖) ≤
            C * (Ψ t) ^ (1 / p) ∧
          (⨍ y in Metric.ball x r, ‖v y - (⨍ z in Metric.ball x r, v z)‖) ^ p ≤
            C ^ p * Ψ t) := by
  have hp : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp₁
  obtain ⟨D, hD, hDEq, hinitial⟩ := exists_cutoff_lp_envelope_bound_effective n hn p hp hp₂ A B
  let P : ℝ := ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) *
    (volume.real (Metric.ball (0 : Domain n) 1)) ^ (-(1 / p))
  let C : ℝ := (effectiveCutoffCappedEnvelopeConstant n A B:ℝ)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hC : 0<C := by dsimp only [C,effectiveCutoffCappedEnvelopeConstant];push_cast;positivity
  have hPMajorant := lpMeanOscillationFactor_le_effective n p hp₁
  have hDC : D≤C := by rw [hDEq];dsimp only [C,effectiveCutoffCappedEnvelopeConstant];push_cast;have H:=Nat.cast_nonneg (α:=ℝ) (effectiveLpMeanOscillationConstant n);linarith only [H]
  have hPC : P≤C := by
    calc
      _≤(effectiveLpMeanOscillationConstant n:ℝ) := hPMajorant
      _≤C := by dsimp only [C,effectiveCutoffCappedEnvelopeConstant];push_cast;have H:=Nat.cast_nonneg (α:=ℝ) (effectiveCutoffLpEnvelopeConstant n A B);linarith only [H]
  refine ⟨C,hC,rfl,?_⟩
  intro q u Du η hu hη hcritical χ hχ hcχ hsχ hχA hDχB c v Dv Φ Ψ
  obtain ⟨hW, hbound⟩ := hinitial q u Du η hu hη hcritical χ hχ hcχ hsχ hχA hDχB
  have hΦ (x : Domain n) (r : ℝ) (hr : 0 < r) : 0 ≤ Φ x r :=
    mul_nonneg (Real.rpow_nonneg hr.le _)
      (integral_nonneg fun _y => Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hΨ := capped_sup_properties (0 : Domain n) Φ
    (r₀ := (1 / 16 : ℝ)) (K := D * η ^ p)
    (fun x r hr _ => (hbound x r hr).2) hΦ
  refine ⟨hW, ?_⟩
  intro t ht htcap
  obtain ⟨hnonneg, hupper, hterm, hmono⟩ := hΨ t ht htcap
  refine ⟨hnonneg, hupper.trans (mul_le_mul_of_nonneg_right hDC (Real.rpow_nonneg hη _)),
    hterm, hmono, ?_⟩
  intro x r hr hrt
  have hcancel : r ^ ((n : ℝ) - p) * r ^ (p - (n : ℝ)) = 1 := by
    rw [← Real.rpow_add hr]
    have he : (n : ℝ) - p + (p - (n : ℝ)) = 0 := by ring
    rw [he, Real.rpow_zero]
  have hgrowth : (∫ y in Metric.ball x r, (Real.sqrt (hsNormSq (Dv y))) ^ p) ≤
      ((Ψ t) ^ (1 / p)) ^ p * r ^ ((n : ℝ) - p + p * (0 : ℝ)) := by
    have H := mul_le_mul_of_nonneg_left (hterm x r hr hrt)
      (Real.rpow_nonneg hr.le ((n : ℝ) - p))
    change r ^ ((n : ℝ) - p) *
      (r ^ (p - (n : ℝ)) * ∫ y in Metric.ball x r,
        (Real.sqrt (hsNormSq (Dv y))) ^ p) ≤ r ^ ((n : ℝ) - p) * Ψ t at H
    rw [← mul_assoc, hcancel, one_mul] at H
    rw [one_div, Real.rpow_inv_rpow hnonneg hp.ne', mul_zero, add_zero]
    exact H.trans_eq (mul_comm _ _)
  have hlocal : MemW12 (ballDomain x r) v Dv :=
    memW12_of_openDomain_subset hW (subset_univ _)
  have H := sobolev_meanOscillation_of_lp_growth (p := p) (α := 0) x hr hp₁ hp₂
    (Real.rpow_nonneg hnonneg (1 / p)) hlocal hgrowth
  rw [Real.rpow_zero, mul_one] at H
  have Hroot := H.trans (mul_le_mul_of_nonneg_right hPC (Real.rpow_nonneg hnonneg _))
  refine ⟨Hroot, ?_⟩
  have hmean0 : 0 ≤ (⨍ y in Metric.ball x r, ‖v y - (⨍ z in Metric.ball x r, v z)‖) := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun _y => norm_nonneg _)
  have Hpower := Real.rpow_le_rpow hmean0 Hroot hp.le
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg hnonneg _), one_div,
    Real.rpow_inv_rpow hnonneg hp.ne'] at Hpower
  exact Hpower

end StationaryHarmonicMaps.Analysis

end
