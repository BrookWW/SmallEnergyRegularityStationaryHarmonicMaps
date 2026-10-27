module

public import HolderToCK.Analysis.Harmonic.GradientVariance
public import HolderToCK.Analysis.Harmonic.GradientExcess
public import HolderToCK.Analysis.Harmonic.WeakEnergyOrthogonality
public import HolderToCK.Analysis.ClassicalPoisson
public import HolderToCK.Analysis.WeakPoissonLocality
public import HolderToCK.Analysis.Harmonic.QuadraticError

/-! # Energy and excess comparison with a harmonic replacement

The displayed Sobolev columns are compared with the actual classical gradient
of the harmonic map. The error energy remains explicit in both inequalities.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK

theorem harmonic_replacement_energy_comparison {n q : ℕ} (hn : 2 ≤ n)
    (a : Domain n) (R : PositiveRadius)
    {u w : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R.val) u Du)
    (hw : MemW12 (ballDomain a R.val) w
      (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)))
    (hws : ContDiffOn ℝ ∞ w (Metric.ball a R.val))
    (hwh : ∀ x ∈ Metric.ball a R.val, Laplacian.laplacian w x = 0)
    (hzero : HasZeroBoundaryValues (ballDomain a R.val) (u - w)
      (fun x i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1)))
    {θ : ℝ} (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2) :
    (∫ x in Metric.ball a (θ * R.val), hsNormSq (Du x)) ≤
      2 * (2 : ℝ) ^ n * θ ^ n * (∫ x in Metric.ball a R.val, hsNormSq (Du x)) +
        2 * ∫ x in Metric.ball a R.val, hsNormSq (fun i =>
          Du x i - fderiv ℝ w x (EuclideanSpace.single i 1)) := by
  let Dw : Domain n → Gradient n q := fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)
  have hEq : WeakPoissonOn (ballDomain a R.val) Dw (fun _ => 0) := by
    have heq : WeakPoissonOn (ballDomain a R.val) Dw (Laplacian.laplacian w) :=
      weakPoissonOn_of_contDiffOn_two (ballDomain a R.val)
      (hws.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    apply heq.congr (Filter.EventuallyEq.refl _ _)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hwh x hx
  have hsub : Metric.ball a (θ * R.val) ⊆ Metric.ball a R.val := by
    apply Metric.ball_subset_ball
    nlinarith only [hθhalf, R.property]
  have hDsmall (i : Fin n) := (hu.2.2 i).mono_measure (Measure.restrict_mono_set volume hsub)
  have hWsmall (i : Fin n) := (hw.2.2 i).mono_measure (Measure.restrict_mono_set volume hsub)
  have htriangle := integral_hsNormSq_triangle_le
    (volume.restrict (Metric.ball a (θ * R.val))) hDsmall hWsmall
  have hdecay := harmonic_energy_decay hn a R w hws hwh hw.integrable_hsNormSq hθ hθhalf
  have horth := (weak_harmonic_replacement_energy_orthogonality
    (ballDomain a R.val) hu hw hEq hzero).1
  have herrpos : 0 ≤ ∫ x in Metric.ball a R.val, hsNormSq (fun i => Du x i - Dw x i) :=
    integral_nonneg (fun _ => hsNormSq_nonneg _)
  have hWle : (∫ x in Metric.ball a R.val, hsNormSq (Dw x)) ≤
      ∫ x in Metric.ball a R.val, hsNormSq (Du x) := by
    change (∫ x in Metric.ball a R.val, hsNormSq (Du x)) =
      (∫ x in Metric.ball a R.val, hsNormSq (Dw x)) +
        (∫ x in Metric.ball a R.val, hsNormSq (fun i => Du x i - Dw x i)) at horth
    linarith only [horth, herrpos]
  have herrle : (∫ x in Metric.ball a (θ * R.val), hsNormSq (fun i => Du x i - Dw x i)) ≤
      ∫ x in Metric.ball a R.val, hsNormSq (fun i => Du x i - Dw x i) :=
    setIntegral_mono_set hzero.1.integrable_hsNormSq
      (Filter.Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Filter.Eventually.of_forall fun _ hx => hsub hx)
  calc
    _ ≤ 2 * (∫ x in Metric.ball a (θ * R.val), hsNormSq (Dw x)) +
        2 * ∫ x in Metric.ball a (θ * R.val), hsNormSq (fun i => Du x i - Dw x i) := htriangle
    _ ≤ 2 * ((2 : ℝ) ^ n * θ ^ n * ∫ x in Metric.ball a R.val, hsNormSq (Du x)) +
        2 * ∫ x in Metric.ball a R.val, hsNormSq (fun i => Du x i - Dw x i) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (hdecay.trans (mul_le_mul_of_nonneg_left hWle (by positivity))) (by norm_num))
        (mul_le_mul_of_nonneg_left herrle (by norm_num))
    _ = _ := by ring

theorem harmonic_replacement_excess_comparison (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (R : PositiveRadius)
      (Du : Domain n → Gradient n q) (w : Domain n → Ambient q),
      (∀ i, MemLp (fun x => Du x i) 2 (volume.restrict (Metric.ball a R.val))) →
      (∀ i, MemLp (fun x => fderiv ℝ w x (EuclideanSpace.single i 1)) 2
        (volume.restrict (Metric.ball a R.val))) →
      ContDiffOn ℝ ∞ w (Metric.ball a R.val) →
      (∀ x ∈ Metric.ball a R.val, Laplacian.laplacian w x = 0) →
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
        (∫ x in Metric.ball a (θ * R.val), hsNormSq (fun i =>
          Du x i - ⨍ y in Metric.ball a (θ * R.val), Du y i)) ≤
        4 * C * θ ^ (n + 2) * (∫ x in Metric.ball a R.val, hsNormSq (fun i =>
          Du x i - ⨍ y in Metric.ball a R.val, Du y i)) +
        (4 * C * θ ^ (n + 2) + 2) * ∫ x in Metric.ball a R.val, hsNormSq (fun i =>
          Du x i - fderiv ℝ w x (EuclideanSpace.single i 1)) := by
  obtain ⟨C, hC, hdecay⟩ := harmonic_gradient_excess_decay n hn
  refine ⟨C, hC, ?_⟩
  intro q a R Du w hDu hDw hws hwh θ hθ hθhalf
  let Dw : Domain n → Gradient n q := fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)
  let μ := volume.restrict (Metric.ball a R.val)
  let ν := volume.restrict (Metric.ball a (θ * R.val))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hsub : Metric.ball a (θ * R.val) ⊆ Metric.ball a R.val := by
    apply Metric.ball_subset_ball
    nlinarith only [hθhalf, R.property]
  have hDsmall (i : Fin n) := (hDu i).mono_measure (Measure.restrict_mono_set volume hsub)
  have hWsmall (i : Fin n) := (hDw i).mono_measure (Measure.restrict_mono_set volume hsub)
  have hsmall := gradient_variance_difference_le ν hWsmall hDsmall
  have herrsymm : (∫ x, hsNormSq (fun i => Dw x i - Du x i) ∂ν) =
      ∫ x, hsNormSq (fun i => Du x i - Dw x i) ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by simp only [hsNormSq, norm_sub_rev])
  change (∫ x, hsNormSq (fun i => Du x i - ⨍ y, Du y i ∂ν) ∂ν) ≤
    2 * (∫ x, hsNormSq (fun i => Dw x i - ⨍ y, Dw y i ∂ν) ∂ν) +
      2 * ∫ x, hsNormSq (fun i => Dw x i - Du x i) ∂ν at hsmall
  rw [herrsymm] at hsmall
  have hlarge := gradient_variance_difference_le μ hDu hDw
  have hwi := HarmonicMaps.integrable_hsNormSq_of_memLp_columns hDw
  have hdec := hdecay q a R w hws hwh hwi θ hθ hθhalf
  change (∫ x, hsNormSq (fun i => Dw x i - ⨍ y, Dw y i ∂ν) ∂ν) ≤
    C * θ ^ (n + 2) * (∫ x, hsNormSq (fun i => Dw x i - ⨍ y, Dw y i ∂μ) ∂μ) at hdec
  have herror : Integrable (fun x => hsNormSq (fun i => Du x i - Dw x i)) μ :=
    HarmonicMaps.integrable_hsNormSq_of_memLp_columns (fun i => (hDu i).sub (hDw i))
  have herrle : (∫ x, hsNormSq (fun i => Du x i - Dw x i) ∂ν) ≤
      ∫ x, hsNormSq (fun i => Du x i - Dw x i) ∂μ :=
    setIntegral_mono_set herror (Filter.Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Filter.Eventually.of_forall fun _ hx => hsub hx)
  change (∫ x, hsNormSq (fun i => Du x i - ⨍ y, Du y i ∂ν) ∂ν) ≤ _
  calc
    _ ≤ 2 * (C * θ ^ (n + 2) *
        (2 * (∫ x, hsNormSq (fun i => Du x i - ⨍ y, Du y i ∂μ) ∂μ) +
          2 * ∫ x, hsNormSq (fun i => Du x i - Dw x i) ∂μ)) +
        2 * ∫ x, hsNormSq (fun i => Du x i - Dw x i) ∂μ :=
      hsmall.trans (add_le_add (mul_le_mul_of_nonneg_left
        (hdec.trans (mul_le_mul_of_nonneg_left hlarge (by positivity))) (by norm_num))
        (mul_le_mul_of_nonneg_left herrle (by norm_num)))
    _ = _ := by ring

private theorem scalar_energy_error_comparison (es E err A c t S : ℝ)
    (hE : 0 ≤ E) (hS : 0 ≤ S) (ht : 0 ≤ t) (hAc : A ≤ c) (hc4 : 4 ≤ c)
    (hbase : es ≤ A * t * E + 2 * err) (herr : err ≤ 2 * S * E) :
    es ≤ (c * t + c * S) * E := by
  calc
    _ ≤ A * t * E + 2 * err := hbase
    _ ≤ A * t * E + 2 * (2 * S * E) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 2))
    _ = (A * t + 4 * S) * E := by ring
    _ ≤ (c * t + c * S) * E := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right hAc ht)
        (mul_le_mul_of_nonneg_right hc4 hS)) hE

private theorem scalar_excess_error_comparison (ps Φ E err C c t S : ℝ)
    (hE : 0 ≤ E) (hΦ : 0 ≤ Φ) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hcΦ : 4 * C ≤ c) (hcerr : 8 * C + 4 ≤ c)
    (hbase : ps ≤ 4 * C * t * Φ + (4 * C * t + 2) * err)
    (herr : err ≤ 2 * S * E) :
    ps ≤ c * t * Φ + c * S * E := by
  have hcoeff : 0 ≤ 4 * C * t + 2 := by positivity
  calc
    _ ≤ 4 * C * t * Φ + (4 * C * t + 2) * err := hbase
    _ ≤ 4 * C * t * Φ + (4 * C * t + 2) * (2 * S * E) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left herr hcoeff)
    _ = (4 * C) * t * Φ + (8 * C * t + 4) * S * E := by ring
    _ ≤ c * t * Φ + c * S * E := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcΦ ht) hΦ
      · apply mul_le_mul_of_nonneg_right _ hE
        apply mul_le_mul_of_nonneg_right _ hS
        have htcoeff : 8 * C * t + 4 ≤ 8 * C + 4 := by
          simpa only [mul_one] using add_le_add (mul_le_mul_of_nonneg_left ht1
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hC)) (le_rfl : (4 : ℝ) ≤ 4)
        exact htcoeff.trans hcerr

theorem quadratic_energy_excess_comparison (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (q : ℕ) (Ω : OpenDomain n)
      (u F : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      MemW12Loc Ω u Du → WeakPoissonOn Ω Du F →
      ∀ α H K : ℝ, 0 < α → 0 ≤ H → 0 ≤ K → HolderBoundOn Ω.val u α H →
        (∀ᵐ x ∂volume.restrict Ω.val, ‖F x‖ ≤ K * hsNormSq (Du x)) →
        ∀ (a : Domain n) (r : PositiveRadius), Metric.closedBall a r.val ⊆ Ω.val →
          ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
            ((∫ x in Metric.ball a (θ * r.val), hsNormSq (Du x)) ≤
              (c * θ ^ n + c * K * H * Real.rpow r.val α) *
                ∫ x in Metric.ball a r.val, hsNormSq (Du x)) ∧
            ((∫ x in Metric.ball a (θ * r.val), hsNormSq (fun i =>
              Du x i - ⨍ y in Metric.ball a (θ * r.val), Du y i)) ≤
              c * θ ^ (n + 2) * (∫ x in Metric.ball a r.val, hsNormSq (fun i =>
                Du x i - ⨍ y in Metric.ball a r.val, Du y i)) +
              c * K * H * Real.rpow r.val α * ∫ x in Metric.ball a r.val, hsNormSq (Du x)) := by
  obtain ⟨C, hC, hcompare⟩ := harmonic_replacement_excess_comparison n hn
  let c : ℝ := 2 * (2 : ℝ) ^ n + 12 * C + 5
  have hp : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) _
  have hc1 : 1 ≤ c := by dsimp only [c]; linarith only [hp, hC]
  have hcenergy : 2 * (2 : ℝ) ^ n ≤ c := by dsimp only [c]; linarith only [hC]
  have hc4 : 4 ≤ c := by dsimp only [c]; linarith only [hp, hC]
  have hcexcess : 4 * C ≤ c := by dsimp only [c]; linarith only [hp, hC]
  have hcerror : 8 * C + 4 ≤ c := by dsimp only [c]; linarith only [hp, hC]
  refine ⟨c, hc1, ?_⟩
  intro q Ω u F Du hu hEq α H K hα hH hK hHolder hBound a r hclosed θ hθ hθhalf
  obtain ⟨w, _, _, hws, hwh, hwW, hzero, _, _, herror⟩ :=
    quadratic_harmonic_replacement_exists_on hn Ω a r hu hEq hα hH hK hHolder hBound hclosed
  have huW := hu.memW12_ball hclosed
  have hbaseE := harmonic_replacement_energy_comparison hn a r huW hwW hws hwh hzero hθ hθhalf
  have hbaseΦ := hcompare q a r Du w huW.2.2 hwW.2.2 hws hwh θ hθ hθhalf
  let E : ℝ := ∫ x in Metric.ball a r.val, hsNormSq (Du x)
  let Φ : ℝ := ∫ x in Metric.ball a r.val, hsNormSq (fun i =>
    Du x i - ⨍ y in Metric.ball a r.val, Du y i)
  let err : ℝ := ∫ x in Metric.ball a r.val, hsNormSq (fun i =>
    Du x i - fderiv ℝ w x (EuclideanSpace.single i 1))
  let S : ℝ := K * H * Real.rpow r.val α
  have hE : 0 ≤ E := integral_nonneg (fun _ => hsNormSq_nonneg _)
  have hΦ : 0 ≤ Φ := integral_nonneg (fun _ => hsNormSq_nonneg _)
  have hS : 0 ≤ S := mul_nonneg (mul_nonneg hK hH) (Real.rpow_nonneg r.property.le _)
  have herr : err ≤ 2 * S * E := by
    change err ≤ _ at herror
    have hcoeff : 2 * K * H * Real.rpow r.val α = 2 * S := by dsimp only [S]; ring
    rw [hcoeff] at herror
    exact herror
  have hθn : 0 ≤ θ ^ n := pow_nonneg hθ.le _
  have hθp : 0 ≤ θ ^ (n + 2) := pow_nonneg hθ.le _
  have hθpone : θ ^ (n + 2) ≤ 1 := pow_le_one₀ hθ.le (by linarith only [hθhalf])
  have hSE : c * S = c * K * H * Real.rpow r.val α := by dsimp only [S]; ring
  constructor
  · have h := scalar_energy_error_comparison _ E err (2 * (2 : ℝ) ^ n) c (θ ^ n) S
      hE hS hθn hcenergy hc4 hbaseE herr
    rw [hSE] at h
    exact h
  · have h := scalar_excess_error_comparison _ Φ E err C c (θ ^ (n + 2)) S
      hE hΦ hS hC.le hθp hθpone hcexcess hcerror hbaseΦ herr
    rw [hSE] at h
    exact h

end HolderToCK
end
