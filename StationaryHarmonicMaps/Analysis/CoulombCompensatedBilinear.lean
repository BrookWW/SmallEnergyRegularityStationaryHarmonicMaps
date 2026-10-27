module

public import StationaryHarmonicMaps.Analysis.BoundedCriticalNativeDivCurl
public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Compensated native tests for the Coulomb product

Constant linear images preserve the original solenoidal equation. A finite
orthonormal expansion of the bounded critical coefficient therefore gives
the native compensated estimate for a genuine bilinear product, including
the encoded matrix multiplication used by the Coulomb equation.
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

/-- A genuine bilinear coefficient times the original solenoidal field admits the critical native W0 estimate on all interior balls. -/
theorem exists_bilinear_critical_native_divcurl_bound (n : ℕ) (hn : 2≤n)
    (m k q : ℕ) (B : Ambient m →L[ℝ] Ambient k →L[ℝ] Ambient q) :
    ∃ C : ℝ,0<C ∧ ∀ (u : Domain n → Ambient m) (Du : Domain n → Gradient n m)
      (η M : ℝ),MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M) →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀ (a : Domain n) (r : ℝ),0<r → ball a r⊆ball (0 : Domain n) (1/2 : ℝ) →
        ∀ (Z : Domain n → Gradient n k),
          (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball a r))) →
          HolderToCK.WeakPoissonOn (ballDomain a r) Z (fun _=>(0 : Ambient k)) →
          ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
            HasZeroBoundaryValues (ballDomain a r) w Dw →
            IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (u x) (Z x i)) (Dw x i)) (ball a r) volume ∧
            |∫x in ball a r,∑i : Fin n,inner ℝ (B (u x) (Z x i)) (Dw x i)|≤
              C*η*Real.sqrt (∫x in ball a r,hsNormSq (Z x))*
                Real.sqrt (∫x in ball a r,hsNormSq (Dw x)) := by
  obtain ⟨D,hD,Hpair⟩ := exists_bounded_critical_native_divcurl_bound n hn
  let e := EuclideanSpace.basisFun (Fin m) ℝ
  let L : Fin m → Ambient m →L[ℝ] ℝ := fun j=>innerSL ℝ (e j)
  let T : Fin m → Ambient k →L[ℝ] Ambient q := fun j=>B (e j)
  let S : ℝ := ∑j : Fin m,‖L j‖*‖T j‖
  have hS : 0≤S := Finset.sum_nonneg fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨D*(1+S),mul_pos hD (by linarith),?_⟩
  intro u Du η M hu hη hBound hCritical a r hr hBall Z hZ hDiv w Dw hw
  let μ := volume.restrict (ball a r)
  let EZ := Real.sqrt (∫x,hsNormSq (Z x) ∂μ)
  let EW := Real.sqrt (∫x,hsNormSq (Dw x) ∂μ)
  let f := fun j x=>(∑i : Fin n,inner ℝ (T j (Z x i)) (Dw x i))*L j (u x)
  have hTests (j : Fin m) : Integrable (f j) μ ∧
      |∫x,f j x ∂μ|≤D*‖L j‖*η*‖T j‖*EZ*EW := by
    have hTZ (i : Fin n) : MemLp (fun x=>T j (Z x i)) 2 μ :=
      (T j).lipschitz.comp_memLp (map_zero (T j)) (hZ i)
    obtain ⟨hI,hEstimate⟩ := Hpair m u Du η M hu hη hBound hCritical a r hr hBall (L j) q
      (fun x i=>T j (Z x i)) hTZ (weakPoissonOn_zero_comp_clm _ Z (T j) hDiv) w Dw hw
    refine ⟨hI,?_⟩
    calc
      _≤D*‖L j‖*η*Real.sqrt (∫x,hsNormSq (fun i=>T j (Z x i)) ∂μ)*EW := hEstimate
      _≤D*‖L j‖*η*(‖T j‖*EZ)*EW := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sqrt_integral_hs_clm_le Z (T j) hZ) (by positivity)) (Real.sqrt_nonneg _)
      _=_ := by ring
  have hExpand (v : Ambient m) (z : Ambient k) : B v z=∑j : Fin m,(L j v) • T j z := by
    have Hv : (∑j : Fin m,L j v • e j)=v := e.sum_repr' v
    nth_rw 1 [← Hv]
    rw [map_sum]
    simp only [map_smul,sum_apply,smul_apply,T]
  have hPoint (x : Domain n) :
      (∑i : Fin n,inner ℝ (B (u x) (Z x i)) (Dw x i))=∑j : Fin m,f j x := by
    simp only [hExpand,sum_inner,real_inner_smul_left]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [f,Finset.mul_sum,mul_comm]
  have hI : Integrable (fun x=>∑j : Fin m,f j x) μ :=
    integrable_finsetSum _ (fun j _=>(hTests j).1)
  refine ⟨hI.congr (Eventually.of_forall fun x=>(hPoint x).symm),?_⟩
  rw [integral_congr_ae (Eventually.of_forall hPoint),integral_finsetSum _ (fun j _=>(hTests j).1)]
  calc
    _≤∑j : Fin m,|∫x,f j x ∂μ| := Finset.abs_sum_le_sum_abs _ _
    _≤∑j : Fin m,D*‖L j‖*η*‖T j‖*EZ*EW := Finset.sum_le_sum fun j _=>(hTests j).2
    _=D*S*η*EZ*EW := by
      dsimp only [S]
      simp only [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _≤D*(1+S)*η*EZ*EW := by gcongr;linarith

end StationaryHarmonicMaps.Analysis

end
