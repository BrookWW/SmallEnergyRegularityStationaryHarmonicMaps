module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import HarmonicMaps.Analysis.BallVariance
public import HarmonicMaps.Analysis.MollificationJensen
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import HarmonicMaps.Analysis.MollificationChangeVariables
public import HarmonicMaps.Analysis.VariableMollificationMatrix
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Normed.Module.Convex
public import HarmonicMaps.Analysis.SobolevMollificationGradient
public import HarmonicMaps.Analysis.SobolevL2Closure

/-!
# L2 norms and convergence of Hilbert--Schmidt squares

Actual square integrals and finite L2 norms determine one another.
Coordinatewise L2 convergence gives convergence of the gradient square sum.
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


end HarmonicMaps
