module

public import StationaryHarmonicMaps.Analysis.CutoffGlobalMeanOscillation
public import StationaryHarmonicMaps.Analysis.LocalDivCurlContinuousPairing
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Normed.Group.Bounded
public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Compensated native tests for the Coulomb product

Constant linear images preserve the original solenoidal equation. The actual
Hilbert--Schmidt energy bounds for these images support the native
bilinear estimates for the Coulomb equation.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- A constant target-linear map preserves the original zero-divergence equation. -/
theorem weakPoissonOn_zero_comp_clm {n k q : ℕ} (Ω : OpenDomain n)
    (Z : Domain n → Gradient n k) (L : Ambient k →L[ℝ] Ambient q)
    (hZ : HolderToCK.WeakPoissonOn Ω Z (fun _=>(0 : Ambient k))) :
    HolderToCK.WeakPoissonOn Ω (fun x i=>L (Z x i)) (fun _=>(0 : Ambient q)) := by
  refine ⟨locallyIntegrableOn_zero,?_⟩
  intro ψ hψ hc hs
  let φ := fun x=>L.adjoint (ψ x)
  have hφ : ContDiff ℝ ∞ φ := L.adjoint.contDiff.comp hψ
  have hcφ : HasCompactSupport φ := hc.comp_left (map_zero L.adjoint)
  have hSupport : tsupport φ⊆tsupport ψ := by
    apply closure_mono
    intro x hx hz
    apply hx
    change L.adjoint (ψ x)=0
    rw [hz,map_zero]
  have hD (x : Domain n) (i : Fin n) :
      fderiv ℝ φ x (EuclideanSpace.single i 1)=L.adjoint (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    have HD := (L.adjoint.hasFDerivAt.comp x (hψ.differentiable (by simp) x).hasFDerivAt).fderiv
    exact congrArg (fun D : Domain n →L[ℝ] Ambient k=>D (EuclideanSpace.single i 1)) HD
  have hPair (x : Domain n) :
      (∑i : Fin n,inner ℝ (Z x i) (fderiv ℝ φ x (EuclideanSpace.single i 1)))=
        ∑i : Fin n,inner ℝ (L (Z x i)) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hD,ContinuousLinearMap.adjoint_inner_right]
  have H := hZ.2 φ hφ hcφ (hSupport.trans hs)
  refine ⟨H.1.congr (Eventually.of_forall hPair),?_,?_⟩
  · simp only [inner_zero_left]
    exact integrable_zero _ _ _
  · rw [← integral_congr_ae (Eventually.of_forall hPair),H.2.2]
    simp only [inner_zero_left]

/-- Constant linear images have the actual full-HS root-energy estimate. -/
theorem sqrt_integral_hs_clm_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {n k q : ℕ} (Z : X → Gradient n k) (L : Ambient k →L[ℝ] Ambient q)
    (hZ : ∀i,MemLp (fun x=>Z x i) 2 μ) :
    Real.sqrt (∫x,hsNormSq (fun i=>L (Z x i)) ∂μ)≤
      ‖L‖*Real.sqrt (∫x,hsNormSq (Z x) ∂μ) := by
  have hLZ (i : Fin n) : MemLp (fun x=>L (Z x i)) 2 μ :=
    L.lipschitz.comp_memLp (map_zero L) (hZ i)
  have hPoint (x : X) : hsNormSq (fun i=>L (Z x i))≤‖L‖^2*hsNormSq (Z x) := by
    simp only [hsNormSq,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have H := L.le_opNorm (Z x i)
    nlinarith only [H,norm_nonneg (L (Z x i)),norm_nonneg (Z x i),norm_nonneg L]
  have hEnergy : (∫x,hsNormSq (fun i=>L (Z x i)) ∂μ)≤‖L‖^2*(∫x,hsNormSq (Z x) ∂μ) := by
    calc
      _≤∫x,‖L‖^2*hsNormSq (Z x) ∂μ := integral_mono
        (integrable_hsNormSq_of_columns _ hLZ)
        ((integrable_hsNormSq_of_columns Z hZ).const_mul _) hPoint
      _=_ := integral_const_mul _ _
  have hNonneg : 0≤∫x,hsNormSq (Z x) ∂μ := integral_nonneg fun _=>hsNormSq_nonneg _
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity,?_⟩
  simpa only [mul_pow,Real.sq_sqrt hNonneg] using hEnergy


end StationaryHarmonicMaps.Analysis

end
