module

public import StationaryHarmonicMaps.Analysis.KelvinGradientPairing
public import StationaryHarmonicMaps.Analysis.AnnularInversionGradientTransport
public import StationaryHarmonicMaps.Analysis.NeumannGradientSpace

/-!
# The inversion part of the natural Kelvin test pairing

The positive weighted pullback of the original derivative has the exact
Jacobian-transferred pairing. Both actual annular integrals are integrable
for raw L2 columns. The radial integral correction is a separate summand of
the Neumann reflection.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The inversion component of the Neumann reflected gradient has the positive conformal pairing with the original columns. -/
theorem unit_inversion_neumann_gradient_pairing {n q : ℕ}
    (x : Domain n) (hx : x≠0) (D : Gradient n q) (B : Domain n →L[ℝ] Ambient q) :
    let I := inversion (0 : Domain n) 1
    |(fderiv ℝ I x).det| *(∑i : Fin n,inner ℝ
      (‖I x‖^(2-(n : ℝ)) • (∑j : Fin n,(fderiv ℝ I (I x) (EuclideanSpace.single i 1)) j • D j))
      (B (EuclideanSpace.single i 1)))=
      ∑i : Fin n,inner ℝ (D i) (‖x‖^(2-(n : ℝ)) • B (fderiv ℝ I x (EuclideanSpace.single i 1))) := by
  intro I
  let F : Domain n →L[ℝ] Ambient q :=
    ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constr ℝ D).toContinuousLinearMap
  have hFCol (i : Fin n) : F (EuclideanSpace.single i 1)=D i := by
    change ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constr ℝ D) (EuclideanSpace.single i 1)=D i
    simpa only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constr_basis ℝ D i
  have hApply (v : Domain n) : F v=∑j : Fin n,v j • D j := by
    have hRepr := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
    have H := congrArg F hRepr
    simpa only [map_sum,map_smul,EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,hFCol] using H.symm
  have H := unit_inversion_weighted_gradient_pairing x hx F B (0 : Ambient q)
  simp only [hFCol,smul_zero,sub_zero,inner_zero_right,mul_zero,add_zero,neg_smul,
    inner_neg_left,Finset.sum_neg_distrib,mul_neg,neg_inj] at H
  simpa only [I,hApply] using H

/-- Original raw L2 columns give both actual annular inversion pairings and their exact integral equality. -/
theorem neumann_kelvin_inversion_integral_pairing {n q : ℕ} (hn : 2≤n)
    (D : Domain n → Gradient n q)
    (hD : ∀j,MemLp (fun x=>D x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ) :
    let I := inversion (0 : Domain n) 1
    let S := {x : Domain n | (1/2 : ℝ)<‖x‖ ∧ ‖x‖<1}
    let O := {x : Domain n | (1 : ℝ)<‖x‖ ∧ ‖x‖<2}
    let W := fun x i=>‖x‖^(2-(n : ℝ)) •
      (∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • D (I x) j)
    IntegrableOn (fun x=>∑i : Fin n,inner ℝ (W x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) O volume ∧
    IntegrableOn (fun x=>∑i : Fin n,inner ℝ (D x i)
      (‖x‖^(2-(n : ℝ)) • fderiv ℝ ψ (I x) (fderiv ℝ I x (EuclideanSpace.single i 1)))) S volume ∧
    (∫x in O,∑i : Fin n,inner ℝ (W x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=
      ∫x in S,∑i : Fin n,inner ℝ (D x i)
        (‖x‖^(2-(n : ℝ)) • fderiv ℝ ψ (I x) (fderiv ℝ I x (EuclideanSpace.single i 1))) := by
  intro I S O W
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have hO : MeasurableSet O := (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have hS0 (x : Domain n) (hx : x∈S) : x≠0 := norm_pos_iff.mp (by linarith only [hx.1])
  have hIS : I '' S=O := by
    have H := unit_inversion_image_annulus (n := n) (1/2) 1 (by norm_num) (by norm_num)
    simpa only [I,S,O,one_div,inv_one,inv_inv] using H
  have hIO : I '' O=S := by
    have H := unit_inversion_image_annulus (n := n) 1 2 (by norm_num) (by norm_num)
    simpa only [I,S,O,one_div,inv_one] using H
  have hSInside : S⊆ball (0 : Domain n) 1 := fun _ hx=>by simpa only [mem_ball,dist_zero_right] using hx.2
  have hDImage (j : Fin n) : MemLp (fun x=>D x j) 2 (volume.restrict (I '' O)) := by
    rw [hIO]
    exact (hD j).mono_measure (Measure.restrict_mono_set volume hSInside)
  let T := fun x i=>∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • D (I x) j
  have hT := (unit_inversion_L2_gradient_columns_transport O hO 1 2 (by norm_num) (by norm_num)
    (fun _ hx=>hx.1.le) (fun _ hx=>hx.2.le) D hDImage).1
  have hwMeas : AEStronglyMeasurable (fun x : Domain n=>‖x‖^(2-(n : ℝ))) (volume.restrict O) :=
    (measurable_norm.pow_const _).aestronglyMeasurable
  have hwBound : ∀ᵐ x ∂volume.restrict O,‖‖x‖^(2-(n : ℝ))‖≤1 := by
    filter_upwards [ae_restrict_mem hO] with x hx
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx.1.le (sub_nonpos.mpr (by exact_mod_cast hn))
  have hW (i : Fin n) : MemLp (fun x=>W x i) 2 (volume.restrict O) := by
    apply (hT i).of_le_mul (c := 1) (hwMeas.smul (hT i).aestronglyMeasurable)
    filter_upwards [hwBound] with x hx
    change ‖‖x‖^(2-(n : ℝ)) • T x i‖≤1*‖T x i‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hψW := memW12_ball_of_ambient_c1 (0 : Domain n) 2 ψ (hψ.of_le (by simp))
  have hOInside : O⊆ball (0 : Domain n) 2 := fun _ hx=>by simpa only [mem_ball,dist_zero_right] using hx.2
  have hDψ (i : Fin n) : MemLp (fun x=>fderiv ℝ ψ x (EuclideanSpace.single i 1)) 2 (volume.restrict O) :=
    (hψW.2.2 i).mono_measure (Measure.restrict_mono_set volume hOInside)
  let f := fun x=>∑i : Fin n,inner ℝ (W x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))
  let g := fun x=>∑i : Fin n,inner ℝ (D x i)
    (‖x‖^(2-(n : ℝ)) • fderiv ℝ ψ (I x) (fderiv ℝ I x (EuclideanSpace.single i 1)))
  have hf : IntegrableOn f O volume := integrable_finsetSum _ fun i _=>
    HolderToCK.integrable_inner_of_memLp_two (hW i) (hDψ i)
  have hDeriv (x : Domain n) (hx : x∈S) : HasFDerivWithinAt I (fderiv ℝ I x) S x :=
    (hasFDerivAt_unit_inversion x (hS0 x hx)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hInj : InjOn I S := (inversion_injective (0 : Domain n) (by norm_num : (1 : ℝ)≠0)).injOn
  have hPoint : (fun x=>|(fderiv ℝ I x).det| *f (I x))=ᵐ[volume.restrict S]g := by
    filter_upwards [ae_restrict_mem hS] with x hx
    simpa only [f,g,W,I,inversion_inversion _ (by norm_num : (1 : ℝ)≠0)] using
      unit_inversion_neumann_gradient_pairing x (hS0 x hx) (D x) (fderiv ℝ ψ (I x))
  have hTrans := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS hDeriv hInj f).mp
    (by simpa only [hIS] using hf)
  have hg : IntegrableOn g S volume := hTrans.congr hPoint
  have hChange := integral_image_eq_integral_abs_det_fderiv_smul volume hS hDeriv hInj f
  rw [hIS] at hChange
  simp only [smul_eq_mul] at hChange
  exact ⟨hf,hg,hChange.trans (integral_congr_ae hPoint)⟩

end StationaryHarmonicMaps.Analysis

end
