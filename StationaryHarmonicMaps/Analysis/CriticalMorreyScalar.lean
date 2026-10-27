module

public import StationaryHarmonicMaps.Foundation.CriticalGradientMorrey
public import HarmonicMaps.Analysis.AffineEnergyScaling
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Exact scalar paths in the complete critical class

The actual extended energy and full all-center/all-radius supremum scale
by the scalar square, including zero multipliers and infinite energy.
Actual L2 data also give genuine strong continuity of the original
scalar path on every original measure.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original extended energy scales exactly by the scalar square without a finiteness hypothesis. -/
theorem dirichletEnergy_const_smul (c : ℝ) {n q : ℕ}
    (F : Domain n → Gradient n q) (S : Set (Domain n)) :
    dirichletEnergy (fun x i=>c • F x i) S=ENNReal.ofReal (c^2)*dirichletEnergy F S := by
  unfold dirichletEnergy
  simp_rw [hsNormSq_const_smul,ENNReal.ofReal_mul (sq_nonneg c)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Every original center and radius is retained in the exact scalar law for the complete critical supremum. -/
theorem criticalGradientMorreySquare_const_smul (c : ℝ) {n q : ℕ}
    (F : Domain n → Gradient n q) (D : Set (Domain n)) :
    criticalGradientMorreySquare (fun x i=>c • F x i) D=
      ENNReal.ofReal (c^2)*criticalGradientMorreySquare F D := by
  unfold criticalGradientMorreySquare
  simp_rw [dirichletEnergy_const_smul,ENNReal.mul_iSup]
  congr 1
  funext x
  congr 1
  funext r
  ac_rfl

/-- Original L2 membership makes every actual scalar parameter path strongly continuous on the same original measure. -/
theorem tendsto_L2_scalar_path {X I : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (F : X → Ambient q) (hF : MemLp F 2 μ)
    (l : Filter I) (c : I → ℝ) (t : ℝ) (hc : Tendsto c l (𝓝 t)) :
    Tendsto (fun k=>eLpNorm (fun x=>c k • F x-t • F x) 2 μ) l (𝓝 0) := by
  have hScalar : Tendsto (fun k=>ENNReal.ofReal |c k-t|) l (𝓝 0) := by
    have H := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hc.sub_const t).abs)
    change Tendsto (fun k=>ENNReal.ofReal |c k-t|) l (𝓝 (ENNReal.ofReal |t-t|)) at H
    simpa only [sub_self,abs_zero,ENNReal.ofReal_zero] using H
  have H := ENNReal.Tendsto.mul_const hScalar (Or.inr hF.eLpNorm_ne_top)
  change Tendsto (fun k=>ENNReal.ofReal |c k-t| *eLpNorm F 2 μ) l (𝓝 (0*eLpNorm F 2 μ)) at H
  have hEq (k : I) : eLpNorm (fun x=>c k • F x-t • F x) 2 μ=
      ENNReal.ofReal |c k-t| *eLpNorm F 2 μ := by
    have hFun : (fun x=>c k • F x-t • F x)=(c k-t) • F := by
      funext x
      exact (sub_smul (c k) t (F x)).symm
    rw [hFun,eLpNorm_const_smul,Real.enorm_eq_ofReal_abs]
  simpa only [zero_mul,← hEq] using H

/-- Finiteness of the original complete critical quantity gives genuine continuity of the same scalar path in that complete quantity. -/
theorem tendsto_criticalMorreySquare_scalar_path {n q : ℕ} {I : Type*}
    (F : Domain n → Gradient n q) (D : Set (Domain n))
    (hF : criticalGradientMorreySquare F D≠∞)
    (l : Filter I) (c : I → ℝ) (t : ℝ) (hc : Tendsto c l (𝓝 t)) :
    Tendsto (fun k=>criticalGradientMorreySquare (fun x i=>c k • F x i-t • F x i) D)
      l (𝓝 0) := by
  have hScalar : Tendsto (fun k=>ENNReal.ofReal ((c k-t)^2)) l (𝓝 0) := by
    have H := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hc.sub_const t).pow 2)
    change Tendsto (fun k=>ENNReal.ofReal ((c k-t)^2)) l (𝓝 (ENNReal.ofReal ((t-t)^2))) at H
    simpa only [sub_self,zero_pow (by decide : (2 : ℕ)≠0),ENNReal.ofReal_zero] using H
  have H := ENNReal.Tendsto.mul_const hScalar (Or.inr hF)
  have hEq (k : I) : criticalGradientMorreySquare (fun x i=>c k • F x i-t • F x i) D=
      ENNReal.ofReal ((c k-t)^2)*criticalGradientMorreySquare F D := by
    have hFun : (fun x i=>c k • F x i-t • F x i)=(fun x i=>(c k-t) • F x i) := by
      funext x i
      exact (sub_smul (c k) t (F x i)).symm
    rw [hFun,criticalGradientMorreySquare_const_smul]
  simpa only [zero_mul,← hEq] using H

end StationaryHarmonicMaps.Analysis

end
