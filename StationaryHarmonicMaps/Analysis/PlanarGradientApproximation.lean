module

public import HolderToCK.Analysis.GradientLinearAlgebra
public import HolderToCK.Analysis.ClassicalWeakGradient
public import HarmonicMaps.SobolevRestriction
public import HarmonicMaps.Analysis.SobolevAECongruence
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import HolderToCK.Analysis.ConvolutionDerivatives
public import HolderToCK.Foundation.WeakPoisson
public import HarmonicMaps.Analysis.InteriorSobolevApproximation
public import HarmonicMaps.Analysis.L2AffineContinuity
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Actual L² convergence of contracted smooth convolutions

The original fixed-kernel approximation and the true Jacobian formula for
centered dilations give strong L² convergence of the same contracted
convolutions. The original field is assumed only integrable and L²;
no weak gradient or Sobolev zero extension is used.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The same smooth mollifications contracted by actual near-identity dilations converge in genuine global L². -/
theorem tendsto_eLpNorm_mollification_centeredDilation_sub {n q : ℕ}
    (f : Domain n → Ambient q) (hf : Integrable f volume) (hf₂ : MemLp f 2 volume)
    (a : Domain n) (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 1)) (htne : ∀ k, t k ≠ 0)
    (ε : ℕ → PositiveRadius) (hε : Tendsto (fun k => (ε k).val) atTop (𝓝 (0 : ℝ))) :
    (∀ k, MemLp (fun x => ∫ z, scaledMollifierKernel n (ε k) z •
      f (a+t k • (x-a)-z)) 2 volume) ∧
    Tendsto (fun k => eLpNorm (fun x => (∫ z, scaledMollifierKernel n (ε k) z •
      f (a+t k • (x-a)-z))-f x) 2 volume) atTop (𝓝 0) := by
  let m (k : ℕ) (x : Domain n) := ∫ z, scaledMollifierKernel n (ε k) z • f (x-z)
  have hm (k : ℕ) : MemLp (m k) 2 volume := by
    have H := fixedKernelAverage_memLp hf hf₂ (ε k)
    simpa only [fixedKernelAverage_eq_scaledConvolution] using H
  have heFilter : Tendsto ε atTop (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) :=
    tendsto_comap_iff.mpr hε
  have hmconv : Tendsto (fun k => eLpNorm (m k-f) 2 volume) atTop (𝓝 0) := by
    have H := (tendsto_eLpNorm_fixedKernelAverage_sub hf hf₂).comp heFilter
    have Hraw : Tendsto (fun k => eLpNorm (fun x => m k x-f x) 2 volume) atTop (𝓝 0) := by
      simpa only [Function.comp_def,m,fixedKernelAverage_eq_scaledConvolution] using H
    apply Hraw.congr
    intro k
    congr 1
  let c (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (abs (s^n)⁻¹) ^ (1/2 : ℝ)
  have hc : Tendsto (fun k => c (t k)) atTop (𝓝 1) := by
    have hi : ContinuousAt (fun s : ℝ => (s^n)⁻¹) 1 :=
      (continuousAt_id.pow n).inv₀ (by simp)
    have H := (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).continuousAt.comp
      (ENNReal.continuous_ofReal.continuousAt.comp hi.abs)
    have H₁ : Tendsto c (𝓝 1) (𝓝 1) := by
      simpa only [ContinuousAt,Function.comp_def,c,one_pow,inv_one,abs_one,
        ENNReal.ofReal_one,ENNReal.one_rpow] using H
    exact H₁.comp ht
  have hfirst : Tendsto (fun k => c (t k)*eLpNorm (m k-f) 2 volume) atTop (𝓝 0) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul hc (Or.inl (by norm_num)) hmconv (Or.inr (by norm_num))
  have hsecond := (tendsto_eLpNorm_centeredDilation_sub hf₂ a).comp ht
  have hsum : Tendsto (fun k => c (t k)*eLpNorm (m k-f) 2 volume+
      eLpNorm (fun x => f (a+t k • (x-a))-f x) 2 volume) atTop (𝓝 0) := by
    simpa only [Function.comp_def,add_zero] using hfirst.add hsecond
  refine ⟨fun k => memLp_comp_centeredDilation (hm k) a (htne k),?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
  intro k
  have hfirstLp := memLp_comp_centeredDilation ((hm k).sub hf₂) a (htne k)
  have hsecondLp := (memLp_comp_centeredDilation hf₂ a (htne k)).sub hf₂
  have heq : (fun x => m k (a+t k • (x-a))-f x) =
      (fun x => (m k-f) (a+t k • (x-a)))+(fun x => f (a+t k • (x-a))-f x) := by
    funext x
    simp only [Pi.add_apply,Pi.sub_apply]
    abel
  change eLpNorm (fun x => m k (a+t k • (x-a))-f x) 2 volume ≤ _
  rw [heq]
  exact (eLpNorm_add_le hfirstLp.aestronglyMeasurable hsecondLp.aestronglyMeasurable (by norm_num)).trans_eq
    (congrArg (fun z => z+eLpNorm (fun x => f (a+t k • (x-a))-f x) 2 volume)
      (eLpNorm_comp_centeredDilation ((hm k).sub hf₂) a (htne k)))


end StationaryHarmonicMaps.Analysis

end
