module

public import HarmonicMaps.Analysis.VariableMollificationBounds
public import HarmonicMaps.Analysis.VariableMollificationLinear
public import HarmonicMaps.Analysis.SobolevL2Closure

/-!
# Actual L2 continuity of the variable averages

The square estimates identify the map and each tensor-column average as
the actual limits of averages of convergent input data. All limit functions
are the displayed integrals.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

namespace HarmonicMaps

/-- The real L2 square integral is the square of the finite L2 norm. -/
theorem integral_norm_sq_eq_eLpNorm_two_toReal_sq {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α} {f : α → E}
    (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  have hpos : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have heq : eLpNorm f 2 μ = ENNReal.ofReal ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  rw [heq, ENNReal.toReal_ofReal (Real.rpow_nonneg hpos _)]
  exact (Real.rpow_inv_natCast_pow (n := 2) hpos (by decide)).symm

/-- Actual L2 convergence to zero gives convergence of the real square integrals. -/
theorem tendsto_integral_norm_sq_zero_of_eLpNorm_two {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α} {f : ℕ → α → E}
    (hf : ∀ k, MemLp (f k) 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖f k x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have ht := ((ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp hconv).pow 2
  have heq (k : ℕ) := integral_norm_sq_eq_eLpNorm_two_toReal_sq (hf k)
  simpa only [Function.comp_apply, ENNReal.toReal_zero,
    zero_pow (by decide : 2 ≠ 0), ← heq] using ht

/-- Convergence of actual square integrals identifies the actual L2 norm limit. -/
theorem tendsto_eLpNorm_two_zero_of_integral_norm_sq {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α} {f : ℕ → α → E}
    (hf : ∀ k, MemLp (f k) 2 μ)
    (hconv : Tendsto (fun k => ∫ x, ‖f k x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k) 2 μ) atTop (𝓝 0) := by
  have ht := ENNReal.tendsto_ofReal (Real.continuous_sqrt.continuousAt.tendsto.comp hconv)
  have heq (k : ℕ) : eLpNorm (f k) 2 μ =
      ENNReal.ofReal (Real.sqrt (∫ x, ‖f k x‖ ^ 2 ∂μ)) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, one_div] using
      (hf k).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  simpa only [Function.comp_apply, Real.sqrt_zero, ENNReal.ofReal_zero, ← heq] using ht

/-- Coordinatewise L2 convergence to zero gives the actual HS square limit. -/
theorem tendsto_integral_hsNormSq_zero {n q : ℕ} {μ : Measure (Domain n)}
    {D : ℕ → Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 μ)
    (hconv : ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D k x i) 2 μ)
      atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, hsNormSq (D k x) ∂μ) atTop (𝓝 0) := by
  have ht := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_integral_norm_sq_zero_of_eLpNorm_two (fun k => hD k i) (hconv i)
  have heq (k : ℕ) : (∫ x, hsNormSq (D k x) ∂μ) =
      ∑ i : Fin n, ∫ x, ‖D k x i‖ ^ 2 ∂μ :=
    integral_finsetSum Finset.univ fun i _ =>
      (hD k i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  simpa only [Finset.sum_const_zero, ← heq] using ht

/-- The literal map average preserves actual L2 convergence on the source
ball, with its sharp measure bound supplied by the source geometry. -/
theorem variableMollification_tendsto_map {n q : ℕ}
    {s : Domain n → ℝ} {theta delta hbar K : ℝ} (hs : ContDiff ℝ ∞ s)
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar) (hhbar : hbar ≤ delta)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (hK : 0 ≤ K)
    (hbound : ∀ y ∈ Metric.ball (0 : Domain n) 1,
      Measure.map (variableShift s y) (volume.restrict (Metric.ball 0 (theta + 2 * delta))) ≤
        ENNReal.ofReal K • volume.restrict (Metric.ball 0 (theta + 2 * delta)))
    {f : ℕ → Domain n → Ambient q} {g : Domain n → Ambient q}
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict (Metric.ball 0 (theta + 2 * delta))))
    (hg : MemLp g 2 (volume.restrict (Metric.ball 0 (theta + 2 * delta))))
    (hconv : Tendsto (fun k => eLpNorm (f k - g) 2
      (volume.restrict (Metric.ball 0 (theta + 2 * delta)))) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm
      ((fun x => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • f k (variableShift s y x)) -
       (fun x => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • g (variableShift s y x)))
      2 (volume.restrict (Metric.ball 0 (theta + 2 * delta)))) atTop (𝓝 0) := by
  let μ := volume.restrict (Metric.ball (0 : Domain n) (theta + 2 * delta))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let H := fun k (x : Domain n) => ∫ y in Metric.ball (0 : Domain n) 1,
    fixedMollifierKernel n y • (f k (variableShift s y x) - g (variableShift s y x))
  have hH (k : ℕ) := variableMollification_map_bounds hs hK hbound ((hf k).sub hg)
  have hE : Tendsto (fun k => ∫ z, ‖f k z - g z‖ ^ 2 ∂μ) atTop (𝓝 0) :=
    tendsto_integral_norm_sq_zero_of_eLpNorm_two (fun k => (hf k).sub hg) hconv
  have hUpper : Tendsto (fun k => K * ∫ z, ‖f k z - g z‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using hE.const_mul K
  have hSquare : Tendsto (fun k => ∫ x, ‖H k x‖ ^ 2 ∂μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
      (fun _ => integral_nonneg (fun _ => sq_nonneg _)) (fun k => (hH k).2.2.2)
  have ht : Tendsto (fun k => eLpNorm (H k) 2 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_two_zero_of_integral_norm_sq (fun k => (hH k).2.2.1) hSquare
  have heq (k : ℕ) : H k =
      (fun x => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • f k (variableShift s y x)) -
      (fun x => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • g (variableShift s y x)) := by
    funext x
    exact variableMollification_sub hvalues hhbar hoff
      ((hf k).integrable (by norm_num)) (hg.integrable (by norm_num)) x
  simp_rw [heq] at ht
  exact ht

/-- Each literal tensor-column average preserves actual coordinatewise L2
convergence of the original gradient fields. -/
theorem variableMollification_tendsto_tensor {n q : ℕ}
    {s : Domain n → ℝ} {theta delta hbar L K : ℝ} (hs : ContDiff ℝ ∞ s)
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar) (hhbar : hbar ≤ delta)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hK : 0 ≤ K)
    (hbound : ∀ y ∈ Metric.ball (0 : Domain n) 1,
      Measure.map (variableShift s y) (volume.restrict (Metric.ball 0 (theta + 2 * delta))) ≤
        ENNReal.ofReal K • volume.restrict (Metric.ball 0 (theta + 2 * delta)))
    {D : ℕ → Domain n → Gradient n q} {Dg : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2
      (volume.restrict (Metric.ball 0 (theta + 2 * delta))))
    (hDg : ∀ i : Fin n, MemLp (fun x => Dg x i) 2
      (volume.restrict (Metric.ball 0 (theta + 2 * delta))))
    (hconv : ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => D k x i - Dg x i)
      2 (volume.restrict (Metric.ball 0 (theta + 2 * delta)))) atTop (𝓝 0)) :
    let G := fun (A : Domain n → Gradient n q) x (i : Fin n) =>
      ∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y •
        ∑ j : Fin n, ((ContinuousLinearMap.id ℝ (Domain n) -
          (fderiv ℝ s x).smulRight y) (EuclideanSpace.single i 1)) j • A (variableShift s y x) j
    ∀ i : Fin n, Tendsto (fun k => eLpNorm (fun x => G (D k) x i - G Dg x i)
      2 (volume.restrict (Metric.ball 0 (theta + 2 * delta)))) atTop (𝓝 0) := by
  dsimp only
  let μ := volume.restrict (Metric.ball (0 : Domain n) (theta + 2 * delta))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let E := fun k (x : Domain n) (i : Fin n) => D k x i - Dg x i
  let H := fun k (x : Domain n) (i : Fin n) =>
    ∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y •
      ∑ j : Fin n, ((ContinuousLinearMap.id ℝ (Domain n) -
        (fderiv ℝ s x).smulRight y) (EuclideanSpace.single i 1)) j • E k (variableShift s y x) j
  have hE (k : ℕ) (i : Fin n) : MemLp (fun x => E k x i) 2 μ := (hD k i).sub (hDg i)
  have hH (k : ℕ) := variableMollification_tensor_bounds hs hDs hK hbound (hE k)
  have hEnergy : Tendsto (fun k => ∫ z, hsNormSq (E k z) ∂μ) atTop (𝓝 0) :=
    tendsto_integral_hsNormSq_zero hE hconv
  have hUpper : Tendsto
      (fun k => ((1 + L) ^ 2 * K) * ∫ z, hsNormSq (E k z) ∂μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using hEnergy.const_mul ((1 + L) ^ 2 * K)
  intro i
  have hSquare : Tendsto (fun k => ∫ x, ‖H k x i‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
      (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    intro k
    calc
      (∫ x, ‖H k x i‖ ^ 2 ∂μ) ≤ ∫ x, hsNormSq (H k x) ∂μ :=
        integral_mono (((hH k).2.2.1 i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
          (integrable_hsNormSq_of_memLp_columns (hH k).2.2.1)
          (fun x => Finset.single_le_sum (fun j _ => sq_nonneg ‖H k x j‖) (Finset.mem_univ i))
      _ ≤ _ := (hH k).2.2.2
  have ht : Tendsto (fun k => eLpNorm (fun x => H k x i) 2 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_two_zero_of_integral_norm_sq (fun k => (hH k).2.2.1 i) hSquare
  have heq (k : ℕ) (x : Domain n) : H k x i =
      (∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y •
        ∑ j : Fin n, ((ContinuousLinearMap.id ℝ (Domain n) -
          (fderiv ℝ s x).smulRight y) (EuclideanSpace.single i 1)) j • D k (variableShift s y x) j) -
      (∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y •
        ∑ j : Fin n, ((ContinuousLinearMap.id ℝ (Domain n) -
          (fderiv ℝ s x).smulRight y) (EuclideanSpace.single i 1)) j • Dg (variableShift s y x) j) :=
    variableMollification_tensor_sub hvalues hhbar hoff
      (fun j => (hD k j).integrable (by norm_num))
      (fun j => (hDg j).integrable (by norm_num)) x i
  simp_rw [heq] at ht
  exact ht

end HarmonicMaps
