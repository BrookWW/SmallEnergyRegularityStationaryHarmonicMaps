module

public import StationaryHarmonicMaps.Analysis.BoundaryCriticalNativeDivCurl
public import StationaryHarmonicMaps.Analysis.CoulombCompensatedBilinear

/-!
# Boundary compensated bilinear native pairings

Constant linear images preserve all native natural boundary tests. Finite
orthonormal expansion then transfers the full-ball scalar compensated
bound to the bilinear products in the actual Coulomb equation.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Constant linear images preserve the original all-native natural tests. -/
theorem natural_solenoidal_comp_clm_unitBall {n k q : ℕ}
    (Z : Domain n → Gradient n k)
    (hNatural : ∀ (f : Domain n → Ambient k) (Df : Domain n → Gradient n k),
      MemW12 (ballDomain (0 : Domain n) 1) f Df →
      (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Df x i))=0)
    (L : Ambient k →L[ℝ] Ambient q)
    (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q)
    (hw : MemW12 (ballDomain (0 : Domain n) 1) w Dw) :
    (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (L (Z x i)) (Dw x i))=0 := by
  have hAdj : MemW12 (ballDomain (0 : Domain n) 1) (fun x=>L.adjoint (w x))
      (fun x i=>L.adjoint (Dw x i)) :=
    ⟨(memW12Loc_continuousLinearMap hw.to_memW12Loc L.adjoint).1,
      L.adjoint.lipschitz.comp_memLp (map_zero L.adjoint) hw.2.1,
      fun i=>L.adjoint.lipschitz.comp_memLp (map_zero L.adjoint) (hw.2.2 i)⟩
  simpa only [ContinuousLinearMap.adjoint_inner_right] using hNatural _ _ hAdj

@[expose] noncomputable def boundaryBilinearCoordinateFactor (m k q : ℕ)
    (B : Ambient m →L[ℝ] Ambient k →L[ℝ] Ambient q) : ℝ :=
  ∑ j : Fin m, ‖innerSL ℝ ((EuclideanSpace.basisFun (Fin m) ℝ) j)‖ *
    ‖B ((EuclideanSpace.basisFun (Fin m) ℝ) j)‖

@[expose] def effectiveBoundaryBilinearConstant (n m : ℕ) (b : ℚ) : ℚ :=
  effectiveBoundaryScalarConstant n * (1+(m : ℚ)*b)

theorem effectiveBoundaryBilinearConstant_pos (n : ℕ) (hn : 2≤n) (m : ℕ)
    (b : ℚ) (hb : 0≤b) : 0<effectiveBoundaryBilinearConstant n m b := by
  have H := effectiveBoundaryScalarConstant_pos n hn
  unfold effectiveBoundaryBilinearConstant
  positivity

theorem boundaryBilinearCoordinateFactor_le (m k q : ℕ) (b : ℚ)
    (B : Ambient m →L[ℝ] Ambient k →L[ℝ] Ambient q) (hB : ‖B‖≤(b : ℝ)) :
    boundaryBilinearCoordinateFactor m k q B ≤ (m : ℝ)*(b : ℝ) := by
  unfold boundaryBilinearCoordinateFactor
  calc
    _≤∑ _j : Fin m,(b : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [innerSL_apply_norm,(EuclideanSpace.basisFun (Fin m) ℝ).norm_eq_one,one_mul]
      simpa only [(EuclideanSpace.basisFun (Fin m) ℝ).norm_eq_one,mul_one] using
        B.le_of_opNorm_le hB ((EuclideanSpace.basisFun (Fin m) ℝ) j)
    _=(m : ℝ)*(b : ℝ) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- Actual bilinear products satisfy the homogeneous compensated estimate
for arbitrary native tests on the entire ball, including the boundary. -/
theorem exists_boundary_bilinear_critical_native_divcurl_bound_explicit (n : ℕ) (hn : 2≤n)
    (m k q : ℕ) (B : Ambient m →L[ℝ] Ambient k →L[ℝ] Ambient q) :
    ∃ C : ℝ,0<C ∧ C=(effectiveBoundaryScalarConstant n : ℝ)*
      (1+boundaryBilinearCoordinateFactor m k q B) ∧ ∀ (u : Domain n → Ambient m) (Du : Domain n → Gradient n m)
      (η M : ℝ),MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M) →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀ (Z : Domain n → Gradient n k),
        (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
        (∀ (f : Domain n → Ambient k) (Df : Domain n → Gradient n k),
          MemW12 (ballDomain (0 : Domain n) 1) f Df →
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Df x i))=0) →
        ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
          MemW12 (ballDomain (0 : Domain n) 1) w Dw →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (u x) (Z x i)) (Dw x i))
            (ball (0 : Domain n) 1) volume ∧
          |∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (B (u x) (Z x i)) (Dw x i)|≤
            C*η*Real.sqrt (∫x in ball (0 : Domain n) 1,hsNormSq (Z x))*
              Real.sqrt (∫x in ball (0 : Domain n) 1,hsNormSq (Dw x)) := by
  obtain ⟨D,hD,hDEq,Hpair⟩ := exists_boundary_critical_native_divcurl_bound_explicit n hn
  let e := EuclideanSpace.basisFun (Fin m) ℝ
  let L : Fin m → Ambient m →L[ℝ] ℝ := fun j=>innerSL ℝ (e j)
  let T : Fin m → Ambient k →L[ℝ] Ambient q := fun j=>B (e j)
  let S : ℝ := ∑j : Fin m,‖L j‖*‖T j‖
  have hS : 0≤S := Finset.sum_nonneg fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨D*(1+S),mul_pos hD (by linarith),?_,?_⟩
  · rw [hDEq]
    rfl
  intro u Du η M hu hη hBound hCritical Z hZ hNatural w Dw hw
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let EZ := Real.sqrt (∫x,hsNormSq (Z x) ∂μ)
  let EW := Real.sqrt (∫x,hsNormSq (Dw x) ∂μ)
  let f := fun j x=>(∑i : Fin n,inner ℝ (T j (Z x i)) (Dw x i))*L j (u x)
  have hTests (j : Fin m) : Integrable (f j) μ ∧
      |∫x,f j x ∂μ|≤D*‖L j‖*η*‖T j‖*EZ*EW := by
    have hTZ (i : Fin n) : MemLp (fun x=>T j (Z x i)) 2 μ :=
      (T j).lipschitz.comp_memLp (map_zero (T j)) (hZ i)
    obtain ⟨hI,hEstimate⟩ := Hpair m u Du η M hu hη hBound hCritical (L j) q
      (fun x i=>T j (Z x i)) hTZ (natural_solenoidal_comp_clm_unitBall Z hNatural (T j)) w Dw hw
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

theorem exists_boundary_bilinear_critical_native_divcurl_bound (n : ℕ) (hn : 2≤n)
    (m k q : ℕ) (B : Ambient m →L[ℝ] Ambient k →L[ℝ] Ambient q) :
    ∃ C : ℝ,0<C ∧ ∀ (u : Domain n → Ambient m) (Du : Domain n → Gradient n m)
      (η M : ℝ),MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M) →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀ (Z : Domain n → Gradient n k),
        (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
        (∀ (f : Domain n → Ambient k) (Df : Domain n → Gradient n k),
          MemW12 (ballDomain (0 : Domain n) 1) f Df →
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Df x i))=0) →
        ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
          MemW12 (ballDomain (0 : Domain n) 1) w Dw →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (u x) (Z x i)) (Dw x i))
            (ball (0 : Domain n) 1) volume ∧
          |∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (B (u x) (Z x i)) (Dw x i)|≤
            C*η*Real.sqrt (∫x in ball (0 : Domain n) 1,hsNormSq (Z x))*
              Real.sqrt (∫x in ball (0 : Domain n) 1,hsNormSq (Dw x)) := by
  obtain ⟨C,hC,_hCEq,H⟩ := exists_boundary_bilinear_critical_native_divcurl_bound_explicit n hn m k q B
  exact ⟨C,hC,H⟩

theorem effective_boundary_bilinear_critical_native_divcurl_bound (n : ℕ) (hn : 2≤n)
    (m k q : ℕ) (b : ℚ) (_hb : 0≤b)
    (B : Ambient m →L[ℝ] Ambient k →L[ℝ] Ambient q) (hB : ‖B‖≤(b : ℝ)) :
    ∀ (u : Domain n → Ambient m) (Du : Domain n → Gradient n m)
      (η M : ℝ),MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M) →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀ (Z : Domain n → Gradient n k),
        (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
        (∀ (f : Domain n → Ambient k) (Df : Domain n → Gradient n k),
          MemW12 (ballDomain (0 : Domain n) 1) f Df →
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Df x i))=0) →
        ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
          MemW12 (ballDomain (0 : Domain n) 1) w Dw →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (u x) (Z x i)) (Dw x i))
            (ball (0 : Domain n) 1) volume ∧
          |∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (B (u x) (Z x i)) (Dw x i)|≤
            (effectiveBoundaryBilinearConstant n m b : ℝ)*η*Real.sqrt (∫x in ball (0 : Domain n) 1,hsNormSq (Z x))*
              Real.sqrt (∫x in ball (0 : Domain n) 1,hsNormSq (Dw x)) := by
  obtain ⟨C,_hC,hCEq,H⟩ := exists_boundary_bilinear_critical_native_divcurl_bound_explicit n hn m k q B
  have hScalar : 0≤(effectiveBoundaryScalarConstant n : ℝ) := by
    exact_mod_cast (effectiveBoundaryScalarConstant_pos n hn).le
  have hC : C≤(effectiveBoundaryBilinearConstant n m b : ℝ) := by
    rw [hCEq]
    have hFactor := boundaryBilinearCoordinateFactor_le m k q b B hB
    have H := mul_le_mul_of_nonneg_left
      (show 1+boundaryBilinearCoordinateFactor m k q B≤1+(m : ℝ)*(b : ℝ) by
        linarith only [hFactor]) hScalar
    refine H.trans_eq ?_
    simp only [effectiveBoundaryBilinearConstant,Rat.cast_mul,Rat.cast_add,Rat.cast_one,Rat.cast_natCast]
  intro u Du η M hu hη hBound hCritical Z hZ hNatural w Dw hw
  obtain ⟨hI,hEstimate⟩ := H u Du η M hu hη hBound hCritical Z hZ hNatural w Dw hw
  refine ⟨hI,hEstimate.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hη) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

end StationaryHarmonicMaps.Analysis

end
