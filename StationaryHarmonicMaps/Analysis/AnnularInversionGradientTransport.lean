module

public import StationaryHarmonicMaps.Analysis.AnnularInversionTransport
public import HarmonicMaps.Analysis.VariableMollificationMatrix
public import StationaryHarmonicMaps.Analysis.ZeroBoundaryPoincare
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Actual annular transport of derivative columns

The true derivative of inversion has the reciprocal squared-radius
operator bound. The literal coordinate-chain columns of an original L2
field therefore have actual L2 membership and the displayed full HS energy
bound on every radially bounded punctured measurable set. The sharp
right-composition HS estimate is reused from the pinned minimizer project;
its proof is pure finite-dimensional algebra. No weak-chain rule is assumed.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open StationaryHarmonicMaps.Geometry
open scoped ENNReal Topology

namespace StationaryHarmonicMaps.Analysis

/-- The actual inversion derivative has the true reciprocal squared-radius operator bound. -/
theorem norm_fderiv_unit_inversion_le {n : ℕ} (x : Domain n) (hx : x≠0) :
    ‖fderiv ℝ (inversion (0 : Domain n) 1) x‖≤(‖x‖^2)⁻¹ := by
  apply (fderiv ℝ (inversion (0 : Domain n) 1) x).opNorm_le_bound (inv_nonneg.mpr (sq_nonneg _))
  intro v
  rw [(hasFDerivAt_unit_inversion x hx).fderiv]
  change ‖(‖x‖^2)⁻¹ • (ℝ ∙ x)ᗮ.reflection v‖≤(‖x‖^2)⁻¹*‖v‖
  rw [norm_smul,(ℝ ∙ x)ᗮ.reflection.norm_map,Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]

/-- Original raw L2 columns give the actual coordinate-chain columns under inversion and a sharp dimension-free HS composition factor, without a weak-derivative premise. -/
theorem unit_inversion_L2_gradient_columns_transport {n q : ℕ}
    (S : Set (Domain n)) (hS : MeasurableSet S)
    (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (hLower : ∀ x∈S,a≤‖x‖) (hUpper : ∀ x∈S,‖x‖≤b)
    (D : Domain n → Gradient n q)
    (hD : ∀ j,MemLp (fun y=>D y j) 2
      (volume.restrict (inversion (0 : Domain n) 1 '' S))) :
    let I := inversion (0 : Domain n) 1
    let T := fun x i=>∑ j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • D (I x) j
    (∀ i,MemLp (fun x=>T x i) 2 (volume.restrict S)) ∧
      (∫ x in S,hsNormSq (T x))≤
        ((a^2)⁻¹)^2*b^(2*n)*(∫ y in I '' S,hsNormSq (D y)) := by
  intro I T
  let μ := volume.restrict S
  let ν := volume.restrict (I '' S)
  let M := (a^2)⁻¹
  have hM : 0≤M := inv_nonneg.mpr (sq_nonneg _)
  have hS0 (x : Domain n) (hx : x∈S) : x≠0 := norm_pos_iff.mp (ha.trans_le (hLower x hx))
  have hDerivative (x : Domain n) (hx : x∈S) : ‖fderiv ℝ I x‖≤M := by
    apply (norm_fderiv_unit_inversion_le x (hS0 x hx)).trans
    exact inv_le_inv₀ (sq_pos_of_pos (ha.trans_le (hLower x hx))) (sq_pos_of_pos ha) |>.mpr
      (pow_le_pow_left₀ ha.le (hLower x hx) 2)
  have hPull (j : Fin n) := unit_inversion_L2_transport_bounded_set S hS hS0 b hb hUpper
    (fun y=>D y j) (hD j)
  have hFD : AEStronglyMeasurable (fderiv ℝ I) μ :=
    (aemeasurable_fderivWithin volume hS (fun x hx=>
      (hasFDerivAt_unit_inversion x (hS0 x hx)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)).aestronglyMeasurable
  have hTerm (i j : Fin n) : MemLp
      (fun x=>(fderiv ℝ I x (EuclideanSpace.single i 1)) j • D (I x) j) 2 μ := by
    have hCoeff : AEStronglyMeasurable (fun x=>(fderiv ℝ I x (EuclideanSpace.single i 1)) j) μ :=
      (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin n=>ℝ) j).continuous.comp_aestronglyMeasurable
        (hFD.apply_continuousLinearMap (EuclideanSpace.single i 1))
    apply (hPull j).1.of_le_mul (c:=M) (hCoeff.smul (hPull j).1.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem hS] with x hx
    have hCoord : |(fderiv ℝ I x (EuclideanSpace.single i 1)) j|≤M := by
      calc
        _ ≤ ‖fderiv ℝ I x (EuclideanSpace.single i 1)‖ := PiLp.norm_apply_le _ j
        _ ≤ ‖fderiv ℝ I x‖*‖EuclideanSpace.single i (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ I x‖ := by simp
        _ ≤ M := hDerivative x hx
    change ‖(fderiv ℝ I x (EuclideanSpace.single i 1)) j • D (I x) j‖≤M*‖D (I x) j‖
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hCoord (norm_nonneg _)
  have hT (i : Fin n) : MemLp (fun x=>T x i) 2 μ := memLp_finsetSum _ (fun j _=>hTerm i j)
  have hTI : Integrable (fun x=>hsNormSq (T x)) μ :=
    integrable_finsetSum _ (fun i _=>(hT i).integrable_norm_pow (by decide : (2 : ℕ)≠0))
  have hPI : Integrable (fun x=>hsNormSq (D (I x))) μ :=
    integrable_finsetSum _ (fun j _=>(hPull j).1.integrable_norm_pow (by decide : (2 : ℕ)≠0))
  have hDI : Integrable (fun y=>hsNormSq (D y)) ν :=
    integrable_finsetSum _ (fun j _=>(hD j).integrable_norm_pow (by decide : (2 : ℕ)≠0))
  have hColP (j : Fin n) : Integrable (fun x=>‖D (I x) j‖^2) μ :=
    (hPull j).1.integrable_norm_pow (by decide : (2 : ℕ)≠0)
  have hColD (j : Fin n) : Integrable (fun y=>‖D y j‖^2) ν :=
    (hD j).integrable_norm_pow (by decide : (2 : ℕ)≠0)
  have hPullEnergy : (∫ x,hsNormSq (D (I x)) ∂μ)≤b^(2*n)*(∫ y,hsNormSq (D y) ∂ν) := by
    change (∫ x,∑ j : Fin n,‖D (I x) j‖^2 ∂μ)≤b^(2*n)*(∫ y,∑ j : Fin n,‖D y j‖^2 ∂ν)
    rw [integral_finsetSum _ (fun j _=>hColP j),integral_finsetSum _ (fun j _=>hColD j),Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _=>(hPull j).2)
  refine ⟨hT,?_⟩
  calc
    _ ≤ ∫ x,M^2*hsNormSq (D (I x)) ∂μ := by
      apply integral_mono_ae hTI (hPI.const_mul (M^2))
      filter_upwards [ae_restrict_mem hS] with x hx
      exact hsNormSq_right_comp_le_of_norm_le (D (I x)) (fderiv ℝ I x) (hDerivative x hx)
    _ = M^2*(∫ x,hsNormSq (D (I x)) ∂μ) := integral_const_mul _ _
    _ ≤ M^2*(b^(2*n)*(∫ y,hsNormSq (D y) ∂ν)) :=
      mul_le_mul_of_nonneg_left hPullEnergy (sq_nonneg _)
    _ = _ := by dsimp only [M,ν];ring

/-- Actual strong L2 convergence of the original columns produces actual strong L2 convergence of the same displayed inversion-chain columns. -/
theorem tendsto_unit_inversion_L2_gradient_columns {n q : ℕ}
    (S : Set (Domain n)) (hS : MeasurableSet S)
    (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (hLower : ∀ x∈S,a≤‖x‖) (hUpper : ∀ x∈S,‖x‖≤b)
    (D : ℕ → Domain n → Gradient n q) (D₀ : Domain n → Gradient n q)
    (hD : ∀ k j,MemLp (fun y=>D k y j) 2
      (volume.restrict (inversion (0 : Domain n) 1 '' S)))
    (hD₀ : ∀ j,MemLp (fun y=>D₀ y j) 2
      (volume.restrict (inversion (0 : Domain n) 1 '' S)))
    (hStrong : ∀ j,Tendsto (fun k=>eLpNorm (fun y=>D k y j-D₀ y j) 2
      (volume.restrict (inversion (0 : Domain n) 1 '' S))) atTop (𝓝 0)) :
    let I := inversion (0 : Domain n) 1
    let T := fun k x i=>∑ j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • D k (I x) j
    let T₀ := fun x i=>∑ j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • D₀ (I x) j
    ∀ i,Tendsto (fun k=>eLpNorm (fun x=>T k x i-T₀ x i) 2 (volume.restrict S)) atTop (𝓝 0) := by
  intro I T T₀
  let μ := volume.restrict S
  let ν := volume.restrict (I '' S)
  let F := fun k y j=>D k y j-D₀ y j
  let TF := fun k x i=>∑ j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • F k (I x) j
  let C := ((a^2)⁻¹)^2*b^(2*n)
  have hF (k : ℕ) (j : Fin n) : MemLp (fun y=>F k y j) 2 ν := (hD k j).sub (hD₀ j)
  have hFStrong (j : Fin n) : Tendsto (fun k=>eLpNorm
      (fun y=>F k y j-(0 : Ambient q)) 2 ν) atTop (𝓝 0) := by
    simpa only [sub_zero] using hStrong j
  have hFZero : Tendsto (fun k=>∫ y,hsNormSq (F k y) ∂ν) atTop (𝓝 (0 : ℝ)) := by
    have H := tendsto_integral_hsNormSq_of_columns_L2 hF (fun _=>MemLp.zero) hFStrong
    simpa only [hsNormSq,Pi.zero_apply,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),Finset.sum_const_zero,integral_zero] using H
  have hTF (k : ℕ) := unit_inversion_L2_gradient_columns_transport S hS a b ha hb hLower hUpper (F k) (hF k)
  have hTFI (k : ℕ) : Integrable (fun x=>hsNormSq (TF k x)) μ :=
    integrable_finsetSum _ (fun i _=>(hTF k).1 i |>.integrable_norm_pow (by decide : (2 : ℕ)≠0))
  have hUpperLimit : Tendsto (fun k=>C*(∫ y,hsNormSq (F k y) ∂ν)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hFZero.const_mul C
  have hEnergy : Tendsto (fun k=>∫ x,hsNormSq (TF k x) ∂μ) atTop (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpperLimit
      (fun k=>integral_nonneg fun x=>hsNormSq_nonneg _) (fun k=>(hTF k).2)
  intro i
  have hColLimit : Tendsto (fun k=>∫ x,‖TF k x i‖^2 ∂μ) atTop (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hEnergy
      (fun k=>integral_nonneg fun x=>sq_nonneg _) (fun k=>by
        apply integral_mono ((hTF k).1 i |>.integrable_norm_pow (by decide : (2 : ℕ)≠0)) (hTFI k)
        intro x
        exact Finset.single_le_sum (fun j _=>sq_nonneg ‖TF k x j‖) (Finset.mem_univ i))
  have hNorm (k : ℕ) : eLpNorm (fun x=>TF k x i) 2 μ=
      ENNReal.ofReal (Real.sqrt (∫ x,‖TF k x i‖^2 ∂μ)) := by
    rw [← ofReal_lpNorm ((hTF k).1 i),lpNorm_eq_integral_norm_rpow_toReal
      (by norm_num : (2 : ℝ≥0∞)≠0) (by simp) ((hTF k).1 i).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat,Real.rpow_two]
    rw [← one_div,← Real.sqrt_eq_rpow]
  have hChain (k : ℕ) : (fun x=>T k x i-T₀ x i)=(fun x=>TF k x i) := by
    funext x
    simp only [T,T₀,TF,F,smul_sub,Finset.sum_sub_distrib]
  have H := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp hColLimit)
  simp_rw [hChain]
  change Tendsto (fun k=>eLpNorm (fun x=>TF k x i) 2 μ) atTop (𝓝 0)
  simp_rw [hNorm]
  simpa only [Function.comp_def,Real.sqrt_zero,ENNReal.ofReal_zero] using H

end StationaryHarmonicMaps.Analysis

end
