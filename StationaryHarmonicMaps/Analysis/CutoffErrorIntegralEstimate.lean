module

public import StationaryHarmonicMaps.Analysis.CutoffErrorIntegrability
public import StationaryHarmonicMaps.Analysis.CriticalMorreyLocalValueBound
import HolderToCK.Foundation.BallVolume

/-!
# Integral growth of the actual four-term cutoff error

Critical Morrey energy bounds, actual interior value moments and forward
Cauchy--Schwarz estimate all four terms of the same expanded error. Its
support handles every center, including centers outside the interior ball.
-/

@[expose] public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- A small ball meeting the cutoff support has its center inside the actual inner domain. -/
theorem cutoff_support_point_forces_center_inner {n : ℕ} {x y : Domain n} {t : ℝ}
    (ht : t ≤ 1 / 16) (hy : y ∈ Metric.ball x t)
    (hy0 : y ∈ Metric.closedBall (0 : Domain n) (3 / 4 : ℝ)) :
    x ∈ Metric.ball (0 : Domain n) (7 / 8 : ℝ) := by
  have hyx : dist y x < t := hy
  have hxy : dist x y < t := by simpa only [dist_comm] using hyx
  have hyz : dist y (0 : Domain n) ≤ (3 / 4 : ℝ) := hy0
  change dist x (0 : Domain n) < (7 / 8 : ℝ)
  exact lt_of_le_of_lt (dist_triangle x y 0) (by linarith only [hxy, hyz, ht])

/-- Taking the genuine value-energy root preserves zero amplitude and the precise radius exponent. -/
theorem cutoff_error_sqrt_value_growth {n : ℕ} {δ A η t J : ℝ}
    (hA : 0 ≤ A) (hη : 0 ≤ η) (ht : 0 < t)
    (hJ : J ≤ A * η ^ 2 * t ^ ((n : ℝ) - 2 * δ)) :
    Real.sqrt J ≤ Real.sqrt A * η * t ^ ((n : ℝ) / 2 - δ) := by
  have hpower : Real.sqrt (t ^ ((n : ℝ) - 2 * δ)) = t ^ ((n : ℝ) / 2 - δ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    congr 1
    ring
  exact (Real.sqrt_le_sqrt hJ).trans_eq (by
    rw [Real.sqrt_mul (mul_nonneg hA (sq_nonneg η)), Real.sqrt_mul hA,
      Real.sqrt_sq_eq_abs, abs_of_nonneg hη, hpower])

/-- The two energy-root product has the required error growth when the common amplitude is small. -/
theorem cutoff_error_product_radius_le {n : ℕ} {δ A η t : ℝ}
    (hη : 0 ≤ η) (hηOne : η ≤ 1) (ht : 0 < t) :
    (η * t ^ ((n : ℝ) / 2 - 1)) *
        (Real.sqrt A * η * t ^ ((n : ℝ) / 2 - δ)) ≤
      Real.sqrt A * η * t ^ ((n : ℝ) - 1 - δ) := by
  have hpower : t ^ ((n : ℝ) / 2 - 1) * t ^ ((n : ℝ) / 2 - δ) =
      t ^ ((n : ℝ) - 1 - δ) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hηsq : η ^ 2 ≤ η := by nlinarith only [hη, hηOne]
  calc
    _ = Real.sqrt A * η ^ 2 *
        (t ^ ((n : ℝ) / 2 - 1) * t ^ ((n : ℝ) / 2 - δ)) := by ring
    _ = Real.sqrt A * η ^ 2 * t ^ ((n : ℝ) - 1 - δ) := by rw [hpower]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hηsq (Real.sqrt_nonneg A)) (Real.rpow_nonneg ht.le _)

/-- The same expanded error has actual local L¹ growth uniformly in the maps, amplitude and center. -/
theorem exists_cutoff_error_integral_bound (n m q : ℕ) (hn : 2 ≤ n)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    {δ B K : ℝ} (hδ : 0 < δ) (hδOne : δ < 1) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
      (p : Domain n → Ambient m) (Dp z : Domain n → Gradient n m)
      (χ : Domain n → ℝ) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      MemW12Loc (ballDomain (0 : Domain n) 1) p Dp →
      (∀ i, LocallyMemL2 (ballDomain (0 : Domain n) 1) (fun x => z x i)) →
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), star (R (p x)) * R (p x) = 1) →
      0 ≤ η → η ≤ 1 →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      criticalGradientMorreySquare Dp (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      criticalGradientMorreySquare z (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Metric.closedBall (0 : Domain n) (3 / 4 : ℝ) →
      (∀ x i, |fderiv ℝ χ x (EuclideanSpace.single i 1)| ≤ B) →
      (∀ x, |Laplacian.laplacian χ x| ≤ K) →
      let a (x : Domain n) := u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)
      let e (x : Domain n) :=
        (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • star (R (Dp x i)) (a x)) +
        (2 : ℝ) • (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • star (R (p x)) (Du x i)) +
        Laplacian.laplacian χ x • star (R (p x)) (a x) +
        ∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • R (z x i) (star (R (p x)) (a x))
      ∀ (x : Domain n) (t : ℝ), 0 < t → t ≤ 1 / 16 →
        IntegrableOn (fun y => ‖e y‖) (Metric.ball x t) volume ∧
        (∫ y in Metric.ball x t, ‖e y‖) ≤ C * η * t ^ ((n : ℝ) - 1 - δ) := by
  obtain ⟨A, hA, hvalue⟩ := exists_local_value_L2_bound_of_criticalMorrey n hn hδ hδOne
  let V : ℝ := volume.real (Metric.ball (0 : Domain n) 1)
  have hV : 0 < V := HolderToCK.ball_volume_real_pos (0 : Domain n) (by norm_num)
  let L : ℝ := B * Real.sqrt (n : ℝ) * (2 * ‖R‖ * Real.sqrt A + 2 * Real.sqrt V) +
    K * (Real.sqrt V * Real.sqrt A)
  let C : ℝ := 1 + L
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hLC : L ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro u Du p Dp z χ η hu hp hz horth hη hηOne hDuCrit hDpCrit hzCrit hχ _hcχ hsχ hdχ hlapχ
  dsimp only
  let w (y : Domain n) := u y - (⨍ v in Metric.ball (0 : Domain n) 1, u v)
  let e (y : Domain n) :=
    (∑ i : Fin n, fderiv ℝ χ y (EuclideanSpace.single i 1) • star (R (Dp y i)) (w y)) +
    (2 : ℝ) • (∑ i : Fin n, fderiv ℝ χ y (EuclideanSpace.single i 1) • star (R (p y)) (Du y i)) +
    Laplacian.laplacian χ y • star (R (p y)) (w y) +
    ∑ i : Fin n, fderiv ℝ χ y (EuclideanSpace.single i 1) • R (z y i) (star (R (p y)) (w y))
  let I : Set (Domain n) := Metric.ball (0 : Domain n) (7 / 8 : ℝ)
  have hIunit : I ⊆ Metric.ball (0 : Domain n) 1 := Metric.ball_subset_ball (by norm_num)
  have hIclosed : Metric.closedBall (0 : Domain n) (7 / 8 : ℝ) ⊆
      (ballDomain (0 : Domain n) 1).val := Metric.closedBall_subset_ball (by norm_num)
  have hpW := hp.memW12_ball hIclosed
  have hpI : MemLp p 2 (volume.restrict I) := hpW.2.1
  have hDpI (i : Fin n) : MemLp (fun y => Dp y i) 2 (volume.restrict I) := hpW.2.2 i
  have hzI (i : Fin n) : MemLp (fun y => z y i) 2 (volume.restrict I) :=
    ((hz i) _ (isCompact_closedBall _ _) hIclosed).mono_measure
      (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
  have hDuI (i : Fin n) : MemLp (fun y => Du y i) 2 (volume.restrict I) :=
    (hu.2.2 i).mono_measure (Measure.restrict_mono_set volume hIunit)
  letI : IsFiniteMeasure (volume.restrict I) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hwI : MemLp w 2 (volume.restrict I) :=
    (hu.2.1.mono_measure (Measure.restrict_mono_set volume hIunit)).sub (memLp_const _)
  have horthI := ae_restrict_of_ae_restrict_of_subset hIunit horth
  have heI := integrable_expanded_cutoff_error_of_L2 R p Dp z w Du hpI hDpI hzI hwI hDuI
    horthI χ hχ hB hdχ hlapχ
  have heSupport : tsupport e ⊆ tsupport χ := tsupport_expanded_cutoff_error_subset
    (fun y => R (p y)) (fun y i => R (Dp y i)) (fun y i => R (z y i)) w Du χ
  have hχI : tsupport χ ⊆ I := hsχ.trans (Metric.closedBall_subset_ball (by norm_num))
  have heGlobal : Integrable e volume :=
    (integrableOn_iff_integrable_of_support_subset
      ((subset_tsupport e).trans (heSupport.trans hχI))).mp heI.1
  have heZero (y : Domain n) (hy : y ∉ I) : e y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy (hχI (heSupport h)))
  intro x t ht htSmall
  have htOne : t ≤ 1 := htSmall.trans (by norm_num)
  refine ⟨heGlobal.norm.integrableOn, ?_⟩
  by_cases hx : x ∈ I
  · let S := Metric.ball x t ∩ I
    let μ := volume.restrict S
    have hSI : S ⊆ I := inter_subset_right
    have hSball : S ⊆ Metric.ball x t := inter_subset_left
    have hSunit : S ⊆ Metric.ball x t ∩ Metric.ball (0 : Domain n) 1 :=
      fun y hy => ⟨hy.1, hIunit hy.2⟩
    letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
      ((measure_mono hSI).trans_lt (measure_ball_lt_top : volume I < ⊤)).ne
    have hpS : MemLp p 2 μ := hpI.mono_measure (Measure.restrict_mono_set volume hSI)
    have hDpS (i : Fin n) : MemLp (fun y => Dp y i) 2 μ :=
      (hDpI i).mono_measure (Measure.restrict_mono_set volume hSI)
    have hzS (i : Fin n) : MemLp (fun y => z y i) 2 μ :=
      (hzI i).mono_measure (Measure.restrict_mono_set volume hSI)
    have hDuS (i : Fin n) : MemLp (fun y => Du y i) 2 μ :=
      (hDuI i).mono_measure (Measure.restrict_mono_set volume hSI)
    have hwS : MemLp w 2 μ := hwI.mono_measure (Measure.restrict_mono_set volume hSI)
    have horthS := ae_restrict_of_ae_restrict_of_subset hSI horthI
    have hraw := (integrable_expanded_cutoff_error_of_L2 R p Dp z w Du hpS hDpS hzS hwS hDuS
      horthS χ hχ hB hdχ hlapχ).2
    have henergy (j : ℕ) (F : Domain n → Gradient n j)
        (hF : ∀ i, MemLp (fun y => F y i) 2 μ)
        (hcrit : criticalGradientMorreySquare F (Metric.ball (0 : Domain n) 1) ≤
          ENNReal.ofReal (η ^ 2)) :
        Real.sqrt (∫ y, hsNormSq (F y) ∂μ) ≤ η * t ^ ((n : ℝ) / 2 - 1) := by
      have H := sqrt_integral_hsNormSq_le_of_criticalMorrey F (hIunit hx) ht (sq_nonneg η)
        hSunit hF hcrit
      simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg hη] using H
    have hvalueRoot : Real.sqrt (∫ y, ‖w y‖ ^ 2 ∂μ) ≤
        Real.sqrt A * η * t ^ ((n : ℝ) / 2 - δ) :=
      cutoff_error_sqrt_value_growth hA.le hη ht
        (hvalue q u Du η hu hη hDuCrit x t ht htOne).2.2
    have hproduct (F : Domain n → Gradient n m)
        (hF : ∀ i, MemLp (fun y => F y i) 2 μ)
        (hcrit : criticalGradientMorreySquare F (Metric.ball (0 : Domain n) 1) ≤
          ENNReal.ofReal (η ^ 2)) :
        (∫ y, Real.sqrt (hsNormSq (F y)) * ‖w y‖ ∂μ) ≤
          Real.sqrt A * η * t ^ ((n : ℝ) - 1 - δ) := by
      exact (integral_hs_mul_norm_le F w hF hwS).2.trans
        ((mul_le_mul (henergy m F hF hcrit) hvalueRoot (Real.sqrt_nonneg _)
          (by positivity)).trans (cutoff_error_product_radius_le hη hηOne ht))
    have hmass : μ.real univ ≤ V * t ^ n := by
      change (volume.restrict S).real univ ≤ _
      rw [measureReal_restrict_apply_univ]
      calc
        _ ≤ volume.real (Metric.ball x t) := ENNReal.toReal_mono measure_ball_ne_top (measure_mono hSball)
        _ = _ := by rw [HolderToCK.ball_volume_real x ht]; ring
    have hmassRoot : Real.sqrt (μ.real univ) ≤ Real.sqrt V * t ^ ((n : ℝ) / 2) := by
      have hpower : Real.sqrt (t ^ n) = t ^ ((n : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast t n, ← Real.rpow_mul ht.le]
        congr 1
        ring
      exact (Real.sqrt_le_sqrt hmass).trans_eq (by rw [Real.sqrt_mul hV.le, hpower])
    have hDuL1 : (∫ y, Real.sqrt (hsNormSq (Du y)) ∂μ) ≤
        Real.sqrt V * η * t ^ ((n : ℝ) - 1 - δ) := by
      have hpower : t ^ ((n : ℝ) / 2) * t ^ ((n : ℝ) / 2 - 1) = t ^ ((n : ℝ) - 1) := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      calc
        _ ≤ Real.sqrt (μ.real univ) * Real.sqrt (∫ y, hsNormSq (Du y) ∂μ) :=
          (integral_hs_le_sqrt_measure_mul_energy Du hDuS).2
        _ ≤ (Real.sqrt V * t ^ ((n : ℝ) / 2)) * (η * t ^ ((n : ℝ) / 2 - 1)) :=
          mul_le_mul hmassRoot (henergy q Du hDuS hDuCrit) (Real.sqrt_nonneg _) (by positivity)
        _ = Real.sqrt V * η * (t ^ ((n : ℝ) / 2) * t ^ ((n : ℝ) / 2 - 1)) := by ring
        _ = Real.sqrt V * η * t ^ ((n : ℝ) - 1) := by rw [hpower]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge ht htOne (by linarith only [hδ])) (by positivity)
    have hwL1 : (∫ y, ‖w y‖ ∂μ) ≤
        Real.sqrt V * Real.sqrt A * η * t ^ ((n : ℝ) - 1 - δ) := by
      have H := integral_mul_le_sqrt_energy_roots (memLp_const (1 : ℝ)) hwS.norm
        (Eventually.of_forall fun _ => zero_le_one) (Eventually.of_forall fun y => norm_nonneg (w y))
      have hb : (∫ y, ‖w y‖ ∂μ) ≤ Real.sqrt (μ.real univ) * Real.sqrt (∫ y, ‖w y‖ ^ 2 ∂μ) := by
        simpa only [one_mul, one_pow, integral_const, smul_eq_mul, mul_one] using H.2
      have hpower : t ^ ((n : ℝ) / 2) * t ^ ((n : ℝ) / 2 - δ) = t ^ ((n : ℝ) - δ) := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      calc
        _ ≤ Real.sqrt (μ.real univ) * Real.sqrt (∫ y, ‖w y‖ ^ 2 ∂μ) := hb
        _ ≤ (Real.sqrt V * t ^ ((n : ℝ) / 2)) *
            (Real.sqrt A * η * t ^ ((n : ℝ) / 2 - δ)) :=
          mul_le_mul hmassRoot hvalueRoot (Real.sqrt_nonneg _) (by positivity)
        _ = Real.sqrt V * Real.sqrt A * η * (t ^ ((n : ℝ) / 2) * t ^ ((n : ℝ) / 2 - δ)) := by ring
        _ = Real.sqrt V * Real.sqrt A * η * t ^ ((n : ℝ) - δ) := by rw [hpower]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge ht htOne (by linarith)) (by positivity)
    have hnormIndicator : I.indicator (fun y => ‖e y‖) = (fun y => ‖e y‖) := by
      funext y
      by_cases hy : y ∈ I
      · simp only [indicator_of_mem hy]
      · simp only [indicator_of_notMem hy, heZero y hy, norm_zero]
    have hIntegral : (∫ y in Metric.ball x t, ‖e y‖) = ∫ y, ‖e y‖ ∂μ := by
      change _ = ∫ y in Metric.ball x t ∩ I, ‖e y‖
      rw [← setIntegral_indicator (f := fun y => ‖e y‖) (s := Metric.ball x t) measurableSet_ball,
        hnormIndicator]
    calc
      _ = ∫ y, ‖e y‖ ∂μ := hIntegral
      _ ≤ B * Real.sqrt (n : ℝ) *
          (‖R‖ * (∫ y, Real.sqrt (hsNormSq (Dp y)) * ‖w y‖ ∂μ) +
            2 * (∫ y, Real.sqrt (hsNormSq (Du y)) ∂μ) +
            ‖R‖ * (∫ y, Real.sqrt (hsNormSq (z y)) * ‖w y‖ ∂μ)) + K * ∫ y, ‖w y‖ ∂μ := hraw
      _ ≤ B * Real.sqrt (n : ℝ) *
          (‖R‖ * (Real.sqrt A * η * t ^ ((n : ℝ) - 1 - δ)) +
            2 * (Real.sqrt V * η * t ^ ((n : ℝ) - 1 - δ)) +
            ‖R‖ * (Real.sqrt A * η * t ^ ((n : ℝ) - 1 - δ))) +
          K * (Real.sqrt V * Real.sqrt A * η * t ^ ((n : ℝ) - 1 - δ)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left (hproduct Dp hDpS hDpCrit) (norm_nonneg R))
            (mul_le_mul_of_nonneg_left hDuL1 (by norm_num)))
            (mul_le_mul_of_nonneg_left (hproduct z hzS hzCrit) (norm_nonneg R))) (by positivity))
          (mul_le_mul_of_nonneg_left hwL1 hK)
      _ = L * η * t ^ ((n : ℝ) - 1 - δ) := by dsimp only [L]; ring
      _ ≤ C * η * t ^ ((n : ℝ) - 1 - δ) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLC hη) (Real.rpow_nonneg ht.le _)
  · have hzball : ∀ y ∈ Metric.ball x t, e y = 0 := by
      intro y hy
      apply image_eq_zero_of_notMem_tsupport
      intro he
      exact hx (cutoff_support_point_forces_center_inner htSmall hy (hsχ (heSupport he)))
    have hzero : (∫ y in Metric.ball x t, ‖e y‖) = 0 := by
      calc
        _ = ∫ _y in Metric.ball x t, (0 : ℝ) := integral_congr_ae
          ((ae_restrict_mem measurableSet_ball).mono fun y hy => by rw [hzball y hy, norm_zero])
        _ = 0 := integral_zero _ _
    rw [hzero]
    positivity

def effectiveHalfCutoffErrorConstant (n B K : ℕ) : ℕ :=
  1+B*(n+1)*(2*(1+effectiveHalfLocalValueConstant n)+2*(1+2^n))+
    K*((1+2^n)*(1+effectiveHalfLocalValueConstant n))

theorem exists_cutoff_error_integral_bound_half_effective (n m q : ℕ) (hn : 2 ≤ n)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRNorm : ‖R‖≤1) (B K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ C=(effectiveHalfCutoffErrorConstant n B K:ℝ) ∧ ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
      (p : Domain n → Ambient m) (Dp z : Domain n → Gradient n m)
      (χ : Domain n → ℝ) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      MemW12Loc (ballDomain (0 : Domain n) 1) p Dp →
      (∀ i, LocallyMemL2 (ballDomain (0 : Domain n) 1) (fun x => z x i)) →
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), star (R (p x)) * R (p x) = 1) →
      0 ≤ η → η ≤ 1 →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      criticalGradientMorreySquare Dp (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      criticalGradientMorreySquare z (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Metric.closedBall (0 : Domain n) (3 / 4 : ℝ) →
      (∀ x i, |fderiv ℝ χ x (EuclideanSpace.single i 1)| ≤ (B:ℝ)) →
      (∀ x, |Laplacian.laplacian χ x| ≤ K) →
      let a (x : Domain n) := u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)
      let e (x : Domain n) :=
        (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • star (R (Dp x i)) (a x)) +
        (2 : ℝ) • (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • star (R (p x)) (Du x i)) +
        Laplacian.laplacian χ x • star (R (p x)) (a x) +
        ∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • R (z x i) (star (R (p x)) (a x))
      ∀ (x : Domain n) (t : ℝ), 0 < t → t ≤ 1 / 16 →
        IntegrableOn (fun y => ‖e y‖) (Metric.ball x t) volume ∧
        (∫ y in Metric.ball x t, ‖e y‖) ≤ C * η * t ^ ((n : ℝ) - 1 - (1/2:ℝ)) := by
  have hδ : (0:ℝ)<1/2 := by norm_num
  have hδOne : (1/2:ℝ)<1 := by norm_num
  have hB : 0≤(B:ℝ) := Nat.cast_nonneg B
  have hK : 0≤(K:ℝ) := Nat.cast_nonneg K
  obtain ⟨A,hA,hAEq,hvalue⟩ := exists_local_value_L2_bound_of_criticalMorrey_half_effective n hn
  let V : ℝ := volume.real (Metric.ball (0 : Domain n) 1)
  have hV : 0 < V := HolderToCK.ball_volume_real_pos (0 : Domain n) (by norm_num)
  let L : ℝ := (B:ℝ) * Real.sqrt (n : ℝ) * (2 * ‖R‖ * Real.sqrt A + 2 * Real.sqrt V) +
    (K:ℝ) * (Real.sqrt V * Real.sqrt A)
  let C : ℝ := (effectiveHalfCutoffErrorConstant n B K:ℝ)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hRootA : Real.sqrt A≤1+(effectiveHalfLocalValueConstant n:ℝ) := by
    rw [hAEq]
    apply (Real.sqrt_le_left (by positivity : 0≤1+(effectiveHalfLocalValueConstant n:ℝ))).mpr
    nlinarith only [sq_nonneg (effectiveHalfLocalValueConstant n:ℝ),Nat.cast_nonneg (α:=ℝ) (effectiveHalfLocalValueConstant n)]
  have hRootV : Real.sqrt V≤1+(2:ℝ)^n := by
    have H := Real.sqrt_le_sqrt (euclidean_unit_ball_volume_upper_bound n)
    have H' : Real.sqrt ((2:ℝ)^n)≤1+(2:ℝ)^n := by
      apply (Real.sqrt_le_left (by positivity : 0≤1+(2:ℝ)^n)).mpr
      nlinarith only [sq_nonneg ((2:ℝ)^n),pow_nonneg (by norm_num : (0:ℝ)≤2) n]
    exact H.trans H'
  have hRootN : Real.sqrt (n:ℝ)≤(n:ℝ)+1 := by
    apply (Real.sqrt_le_left (by positivity : 0≤(n:ℝ)+1)).mpr
    nlinarith only [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]
  have hC : 0<C := by dsimp only [C,effectiveHalfCutoffErrorConstant];push_cast;positivity
  have hLC : L≤C := by
    calc
      _≤(B:ℝ)*((n:ℝ)+1)*(2*(1+(effectiveHalfLocalValueConstant n:ℝ))+2*(1+(2:ℝ)^n))+
          (K:ℝ)*((1+(2:ℝ)^n)*(1+(effectiveHalfLocalValueConstant n:ℝ))) := by
        dsimp only [L]
        gcongr
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hRNorm (by norm_num : (0:ℝ)≤2)
      _≤C := by dsimp only [C,effectiveHalfCutoffErrorConstant];push_cast;linarith
  refine ⟨C,hC,rfl,?_⟩
  intro u Du p Dp z χ η hu hp hz horth hη hηOne hDuCrit hDpCrit hzCrit hχ _hcχ hsχ hdχ hlapχ
  dsimp only
  let w (y : Domain n) := u y - (⨍ v in Metric.ball (0 : Domain n) 1, u v)
  let e (y : Domain n) :=
    (∑ i : Fin n, fderiv ℝ χ y (EuclideanSpace.single i 1) • star (R (Dp y i)) (w y)) +
    (2 : ℝ) • (∑ i : Fin n, fderiv ℝ χ y (EuclideanSpace.single i 1) • star (R (p y)) (Du y i)) +
    Laplacian.laplacian χ y • star (R (p y)) (w y) +
    ∑ i : Fin n, fderiv ℝ χ y (EuclideanSpace.single i 1) • R (z y i) (star (R (p y)) (w y))
  let I : Set (Domain n) := Metric.ball (0 : Domain n) (7 / 8 : ℝ)
  have hIunit : I ⊆ Metric.ball (0 : Domain n) 1 := Metric.ball_subset_ball (by norm_num)
  have hIclosed : Metric.closedBall (0 : Domain n) (7 / 8 : ℝ) ⊆
      (ballDomain (0 : Domain n) 1).val := Metric.closedBall_subset_ball (by norm_num)
  have hpW := hp.memW12_ball hIclosed
  have hpI : MemLp p 2 (volume.restrict I) := hpW.2.1
  have hDpI (i : Fin n) : MemLp (fun y => Dp y i) 2 (volume.restrict I) := hpW.2.2 i
  have hzI (i : Fin n) : MemLp (fun y => z y i) 2 (volume.restrict I) :=
    ((hz i) _ (isCompact_closedBall _ _) hIclosed).mono_measure
      (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
  have hDuI (i : Fin n) : MemLp (fun y => Du y i) 2 (volume.restrict I) :=
    (hu.2.2 i).mono_measure (Measure.restrict_mono_set volume hIunit)
  letI : IsFiniteMeasure (volume.restrict I) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hwI : MemLp w 2 (volume.restrict I) :=
    (hu.2.1.mono_measure (Measure.restrict_mono_set volume hIunit)).sub (memLp_const _)
  have horthI := ae_restrict_of_ae_restrict_of_subset hIunit horth
  have heI := integrable_expanded_cutoff_error_of_L2 R p Dp z w Du hpI hDpI hzI hwI hDuI
    horthI χ hχ hB hdχ hlapχ
  have heSupport : tsupport e ⊆ tsupport χ := tsupport_expanded_cutoff_error_subset
    (fun y => R (p y)) (fun y i => R (Dp y i)) (fun y i => R (z y i)) w Du χ
  have hχI : tsupport χ ⊆ I := hsχ.trans (Metric.closedBall_subset_ball (by norm_num))
  have heGlobal : Integrable e volume :=
    (integrableOn_iff_integrable_of_support_subset
      ((subset_tsupport e).trans (heSupport.trans hχI))).mp heI.1
  have heZero (y : Domain n) (hy : y ∉ I) : e y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy (hχI (heSupport h)))
  intro x t ht htSmall
  have htOne : t ≤ 1 := htSmall.trans (by norm_num)
  refine ⟨heGlobal.norm.integrableOn, ?_⟩
  by_cases hx : x ∈ I
  · let S := Metric.ball x t ∩ I
    let μ := volume.restrict S
    have hSI : S ⊆ I := inter_subset_right
    have hSball : S ⊆ Metric.ball x t := inter_subset_left
    have hSunit : S ⊆ Metric.ball x t ∩ Metric.ball (0 : Domain n) 1 :=
      fun y hy => ⟨hy.1, hIunit hy.2⟩
    letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
      ((measure_mono hSI).trans_lt (measure_ball_lt_top : volume I < ⊤)).ne
    have hpS : MemLp p 2 μ := hpI.mono_measure (Measure.restrict_mono_set volume hSI)
    have hDpS (i : Fin n) : MemLp (fun y => Dp y i) 2 μ :=
      (hDpI i).mono_measure (Measure.restrict_mono_set volume hSI)
    have hzS (i : Fin n) : MemLp (fun y => z y i) 2 μ :=
      (hzI i).mono_measure (Measure.restrict_mono_set volume hSI)
    have hDuS (i : Fin n) : MemLp (fun y => Du y i) 2 μ :=
      (hDuI i).mono_measure (Measure.restrict_mono_set volume hSI)
    have hwS : MemLp w 2 μ := hwI.mono_measure (Measure.restrict_mono_set volume hSI)
    have horthS := ae_restrict_of_ae_restrict_of_subset hSI horthI
    have hraw := (integrable_expanded_cutoff_error_of_L2 R p Dp z w Du hpS hDpS hzS hwS hDuS
      horthS χ hχ hB hdχ hlapχ).2
    have henergy (j : ℕ) (F : Domain n → Gradient n j)
        (hF : ∀ i, MemLp (fun y => F y i) 2 μ)
        (hcrit : criticalGradientMorreySquare F (Metric.ball (0 : Domain n) 1) ≤
          ENNReal.ofReal (η ^ 2)) :
        Real.sqrt (∫ y, hsNormSq (F y) ∂μ) ≤ η * t ^ ((n : ℝ) / 2 - 1) := by
      have H := sqrt_integral_hsNormSq_le_of_criticalMorrey F (hIunit hx) ht (sq_nonneg η)
        hSunit hF hcrit
      simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg hη] using H
    have hvalueRoot : Real.sqrt (∫ y, ‖w y‖ ^ 2 ∂μ) ≤
        Real.sqrt A * η * t ^ ((n : ℝ) / 2 - (1/2:ℝ)) :=
      cutoff_error_sqrt_value_growth hA.le hη ht
        (hvalue q u Du η hu hη hDuCrit x t ht htOne).2.2
    have hproduct (F : Domain n → Gradient n m)
        (hF : ∀ i, MemLp (fun y => F y i) 2 μ)
        (hcrit : criticalGradientMorreySquare F (Metric.ball (0 : Domain n) 1) ≤
          ENNReal.ofReal (η ^ 2)) :
        (∫ y, Real.sqrt (hsNormSq (F y)) * ‖w y‖ ∂μ) ≤
          Real.sqrt A * η * t ^ ((n : ℝ) - 1 - (1/2:ℝ)) := by
      exact (integral_hs_mul_norm_le F w hF hwS).2.trans
        ((mul_le_mul (henergy m F hF hcrit) hvalueRoot (Real.sqrt_nonneg _)
          (by positivity)).trans (cutoff_error_product_radius_le hη hηOne ht))
    have hmass : μ.real univ ≤ V * t ^ n := by
      change (volume.restrict S).real univ ≤ _
      rw [measureReal_restrict_apply_univ]
      calc
        _ ≤ volume.real (Metric.ball x t) := ENNReal.toReal_mono measure_ball_ne_top (measure_mono hSball)
        _ = _ := by rw [HolderToCK.ball_volume_real x ht]; ring
    have hmassRoot : Real.sqrt (μ.real univ) ≤ Real.sqrt V * t ^ ((n : ℝ) / 2) := by
      have hpower : Real.sqrt (t ^ n) = t ^ ((n : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast t n, ← Real.rpow_mul ht.le]
        congr 1
        ring
      exact (Real.sqrt_le_sqrt hmass).trans_eq (by rw [Real.sqrt_mul hV.le, hpower])
    have hDuL1 : (∫ y, Real.sqrt (hsNormSq (Du y)) ∂μ) ≤
        Real.sqrt V * η * t ^ ((n : ℝ) - 1 - (1/2:ℝ)) := by
      have hpower : t ^ ((n : ℝ) / 2) * t ^ ((n : ℝ) / 2 - 1) = t ^ ((n : ℝ) - 1) := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      calc
        _ ≤ Real.sqrt (μ.real univ) * Real.sqrt (∫ y, hsNormSq (Du y) ∂μ) :=
          (integral_hs_le_sqrt_measure_mul_energy Du hDuS).2
        _ ≤ (Real.sqrt V * t ^ ((n : ℝ) / 2)) * (η * t ^ ((n : ℝ) / 2 - 1)) :=
          mul_le_mul hmassRoot (henergy q Du hDuS hDuCrit) (Real.sqrt_nonneg _) (by positivity)
        _ = Real.sqrt V * η * (t ^ ((n : ℝ) / 2) * t ^ ((n : ℝ) / 2 - 1)) := by ring
        _ = Real.sqrt V * η * t ^ ((n : ℝ) - 1) := by rw [hpower]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge ht htOne (by linarith only [hδ])) (by positivity)
    have hwL1 : (∫ y, ‖w y‖ ∂μ) ≤
        Real.sqrt V * Real.sqrt A * η * t ^ ((n : ℝ) - 1 - (1/2:ℝ)) := by
      have H := integral_mul_le_sqrt_energy_roots (memLp_const (1 : ℝ)) hwS.norm
        (Eventually.of_forall fun _ => zero_le_one) (Eventually.of_forall fun y => norm_nonneg (w y))
      have hb : (∫ y, ‖w y‖ ∂μ) ≤ Real.sqrt (μ.real univ) * Real.sqrt (∫ y, ‖w y‖ ^ 2 ∂μ) := by
        simpa only [one_mul, one_pow, integral_const, smul_eq_mul, mul_one] using H.2
      have hpower : t ^ ((n : ℝ) / 2) * t ^ ((n : ℝ) / 2 - (1/2:ℝ)) = t ^ ((n : ℝ) - (1/2:ℝ)) := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      calc
        _ ≤ Real.sqrt (μ.real univ) * Real.sqrt (∫ y, ‖w y‖ ^ 2 ∂μ) := hb
        _ ≤ (Real.sqrt V * t ^ ((n : ℝ) / 2)) *
            (Real.sqrt A * η * t ^ ((n : ℝ) / 2 - (1/2:ℝ))) :=
          mul_le_mul hmassRoot hvalueRoot (Real.sqrt_nonneg _) (by positivity)
        _ = Real.sqrt V * Real.sqrt A * η * (t ^ ((n : ℝ) / 2) * t ^ ((n : ℝ) / 2 - (1/2:ℝ))) := by ring
        _ = Real.sqrt V * Real.sqrt A * η * t ^ ((n : ℝ) - (1/2:ℝ)) := by rw [hpower]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge ht htOne (by linarith)) (by positivity)
    have hnormIndicator : I.indicator (fun y => ‖e y‖) = (fun y => ‖e y‖) := by
      funext y
      by_cases hy : y ∈ I
      · simp only [indicator_of_mem hy]
      · simp only [indicator_of_notMem hy, heZero y hy, norm_zero]
    have hIntegral : (∫ y in Metric.ball x t, ‖e y‖) = ∫ y, ‖e y‖ ∂μ := by
      change _ = ∫ y in Metric.ball x t ∩ I, ‖e y‖
      rw [← setIntegral_indicator (f := fun y => ‖e y‖) (s := Metric.ball x t) measurableSet_ball,
        hnormIndicator]
    calc
      _ = ∫ y, ‖e y‖ ∂μ := hIntegral
      _ ≤ B * Real.sqrt (n : ℝ) *
          (‖R‖ * (∫ y, Real.sqrt (hsNormSq (Dp y)) * ‖w y‖ ∂μ) +
            2 * (∫ y, Real.sqrt (hsNormSq (Du y)) ∂μ) +
            ‖R‖ * (∫ y, Real.sqrt (hsNormSq (z y)) * ‖w y‖ ∂μ)) + K * ∫ y, ‖w y‖ ∂μ := hraw
      _ ≤ B * Real.sqrt (n : ℝ) *
          (‖R‖ * (Real.sqrt A * η * t ^ ((n : ℝ) - 1 - (1/2:ℝ))) +
            2 * (Real.sqrt V * η * t ^ ((n : ℝ) - 1 - (1/2:ℝ))) +
            ‖R‖ * (Real.sqrt A * η * t ^ ((n : ℝ) - 1 - (1/2:ℝ)))) +
          K * (Real.sqrt V * Real.sqrt A * η * t ^ ((n : ℝ) - 1 - (1/2:ℝ))) := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left (hproduct Dp hDpS hDpCrit) (norm_nonneg R))
            (mul_le_mul_of_nonneg_left hDuL1 (by norm_num)))
            (mul_le_mul_of_nonneg_left (hproduct z hzS hzCrit) (norm_nonneg R))) (by positivity))
          (mul_le_mul_of_nonneg_left hwL1 hK)
      _ = L * η * t ^ ((n : ℝ) - 1 - (1/2:ℝ)) := by dsimp only [L]; ring
      _ ≤ C * η * t ^ ((n : ℝ) - 1 - (1/2:ℝ)) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLC hη) (Real.rpow_nonneg ht.le _)
  · have hzball : ∀ y ∈ Metric.ball x t, e y = 0 := by
      intro y hy
      apply image_eq_zero_of_notMem_tsupport
      intro he
      exact hx (cutoff_support_point_forces_center_inner htSmall hy (hsχ (heSupport he)))
    have hzero : (∫ y in Metric.ball x t, ‖e y‖) = 0 := by
      calc
        _ = ∫ _y in Metric.ball x t, (0 : ℝ) := integral_congr_ae
          ((ae_restrict_mem measurableSet_ball).mono fun y hy => by rw [hzball y hy, norm_zero])
        _ = 0 := integral_zero _ _
    rw [hzero]
    positivity

end StationaryHarmonicMaps.Analysis

end
