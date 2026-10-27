module

public import StationaryHarmonicMaps.Analysis.NativeMorreySobolevBanach
public import StationaryHarmonicMaps.Analysis.SkewConnectionAndTests
public import StationaryHarmonicMaps.Geometry.OrthogonalRightHS
import StationaryHarmonicMaps.Analysis.HilbertSchmidtDecoding

/-!
# Original scalar-path frame and connection data in the native Banach carriers

An original Sobolev special-orthogonal frame and its original all-query
power bounds give the same native frame and the same transformed and
parameter-direction coefficient classes. Their L2 membership is proved
from the original frame and connection; conjugation preserves the full
original coefficient square density.
-/

public section
open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal
noncomputable section
namespace StationaryHarmonicMaps.Analysis

private theorem growth_constant_nonneg {n k : ℕ} (ν K : ℝ)
    (F : Domain n→Gradient n k)
    (hGrowth : ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (F x))≤K*r^ν) : 0≤K := by
  have H := hGrowth 0 (mem_ball_self zero_lt_one) 1 zero_lt_one
  rw [Real.one_rpow,mul_one] at H
  exact (integral_nonneg fun x=>Finset.sum_nonneg fun i _=>sq_nonneg ‖F x i‖).trans H

private theorem conjugated_skew {q : ℕ} (P A : Ambient q→L[ℝ]Ambient q)
    (hA : star A= -A) : star (star P*A*P)= -(star P*A*P) := by
  rw [star_mul (star P*A) P,star_mul (star P) A,star_star P,hA]
  apply ContinuousLinearMap.ext
  intro v
  change star P ((-A) (P v))= -(star P (A (P v)))
  rw [neg_apply,map_neg]

private theorem conjugated_density {n q : ℕ}
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,
      ‖e.symm T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (P : Ambient q→L[ℝ]Ambient q) (hP : star P*P=1)
    (A : Fin n→(Ambient q→L[ℝ]Ambient q)) :
    hsNormSq (fun i=>e.symm (star P*A i*P))=hsNormSq (fun i=>e.symm (A i)) := by
  have hStar : star (star P)*star P=1 := by
    rw [star_star]
    exact mul_star_eq_one_of_star_mul_eq_one P hP
  apply Finset.sum_congr rfl
  intro i _
  change ‖e.symm (star P*A i*P)‖^2=‖e.symm (A i)‖^2
  exact (encoded_norm_sq_mul_right_orthogonal e.symm.toContinuousLinearMap hE (star P*A i) P hP).trans
    (encoded_norm_sq_mul_left_orthogonal e.symm.toContinuousLinearMap hE (star P) (A i) hStar)

private theorem conjugated_columns_memLp {n q : ℕ}
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (p : Domain n→Ambient (q*q))
    (hp : MemLp p 2 (volume.restrict (ball (0:Domain n) 1)))
    (hOrth : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (e (p x))*e (p x)=1)
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q))
    (hA : ∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0:Domain n) 1))) :
    ∀i,MemLp (fun x=>e.symm (star (e (p x))*A x i*e (p x))) 2
      (volume.restrict (ball (0:Domain n) 1)) := by
  let μ := volume.restrict (ball (0:Domain n) 1)
  have hP := e.continuous.comp_aestronglyMeasurable hp.aestronglyMeasurable
  have hPb : ∀ᵐx∂μ,‖e (p x)‖≤(1:ℝ) :=
    hOrth.mono fun x hx=>orthogonal_opNorm_le_one _ hx
  have hSP : AEStronglyMeasurable (fun x=>star (e (p x))) μ :=
    (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).continuous.comp_aestronglyMeasurable hP
  have hSPb : ∀ᵐx∂μ,‖star (e (p x))‖≤(1:ℝ) := by
    filter_upwards [hPb] with x hx
    rw [norm_star (e (p x))]
    exact hx
  intro i
  exact e.symm.toContinuousLinearMap.lipschitz.comp_memLp (map_zero e.symm)
    (memLp_two_bounded_mul_right hP hPb (memLp_two_bounded_mul_left hSP hSPb (hA i)))

private theorem conjugated_power_growth {n q : ℕ} (ν KA : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,
      ‖e.symm T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (p : Domain n→Ambient (q*q))
    (hOrth : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (e (p x))*e (p x)=1)
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q))
    (hGrowth : ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>e.symm (A x i)))≤KA*r^ν) :
    ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>e.symm (star (e (p x))*A x i*e (p x))))≤KA*r^ν := by
  intro a ha r hr
  have hO : ∀ᵐx∂volume.restrict (ball a r∩ball (0:Domain n) 1),star (e (p x))*e (p x)=1 :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hOrth
  have hDensity : (fun x=>hsNormSq (fun i=>e.symm (star (e (p x))*A x i*e (p x))))=ᵐ[
      volume.restrict (ball a r∩ball (0:Domain n) 1)]
      (fun x=>hsNormSq (fun i=>e.symm (A x i))) :=
    hO.mono fun x hx=>conjugated_density e hE (e (p x)) hx (A x)
  exact (integral_congr_ae hDensity).le.trans (hGrowth a ha r hr)

private theorem scalar_connection_raw_data {n q : ℕ}
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,
      ‖e.symm T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q))
    (hp : MemW12 (ballDomain (0:Domain n) 1) p Dp)
    (hOrth : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (e (p x))*e (p x)=1)
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q))
    (hA : ∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0:Domain n) 1)))
    (hSkew : ∀i,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (A x i)= -(A x i))
    (τ : ℝ) :
    let Zr := fun x i=>e.symm (star (e (p x))*e (Dp x i)+star (e (p x))*(τ • A x i)*e (p x))
    (∀i,MemLp (fun x=>Zr x i) 2 (volume.restrict (ball (0:Domain n) 1))) ∧
    (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,star (e (Zr x i))= -(e (Zr x i))) := by
  let Zr := fun x i=>e.symm (star (e (p x))*e (Dp x i)+star (e (p x))*(τ • A x i)*e (p x))
  have hScalarA (i : Fin n) : MemLp (fun x=>τ • A x i) 2 (volume.restrict (ball (0:Domain n) 1)) :=
    (hA i).const_smul τ
  have hScalarSkew (i : Fin n) : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (τ • A x i)= -(τ • A x i) := by
    filter_upwards [hSkew i] with x hx
    rw [star_smul,star_trivial,hx,smul_neg]
  have hRaw := frame_connection_memLp_and_skew e.symm.toContinuousLinearMap e.toContinuousLinearMap
    e.symm_apply_apply hE p Dp hp hOrth (fun x i=>τ • A x i) hScalarA hScalarSkew
  refine ⟨hRaw.2.1,?_⟩
  filter_upwards [hRaw.2.2] with x hx
  intro i
  exact (congrArg star (e.apply_symm_apply _)).trans ((hx i).trans (congrArg Neg.neg (e.apply_symm_apply _)).symm)

private theorem conjugated_raw_skew {n q : ℕ}
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (p : Domain n→Ambient (q*q))
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q))
    (hSkew : ∀i,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (A x i)= -(A x i)) :
    ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,
      star (e (e.symm (star (e (p x))*A x i*e (p x))))= -(e (e.symm (star (e (p x))*A x i*e (p x)))) := by
  filter_upwards [ae_all_iff.mpr hSkew] with x hx
  intro i
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact conjugated_skew (e (p x)) (A x i) (hx i)

private theorem raw_field_of_hs_class {n k : ℕ}
    (F : Domain n→Gradient n k)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0:Domain n) 1)))
    (U : HSUnitBallL2 n k) (hU : U=hsUnitBallL2Class F hF) :
    (fun x i=>WithLp.toLp 2 (fun j : Fin k=>U x (finProdFinEquiv (i,j))))=ᵐ[
      volume.restrict (ball (0:Domain n) 1)]F := by
  have hAE : (U : Domain n→Ambient (n*k))=ᵐ[volume.restrict (ball (0:Domain n) 1)]hsFlatten F := by
    rw [hU]
    exact hsUnitBallL2Class_ae F hF
  filter_upwards [hAE] with x hx
  exact (congrArg (fun v : Ambient (n*k)=>fun i : Fin n=>
    WithLp.toLp 2 (fun j : Fin k=>v (finProdFinEquiv (i,j)))) hx).trans (hs_unflatten_flatten (F x))

private theorem native_class_of_original_growth {n k : ℕ} (ν K : ℝ)
    (p : Domain n→Ambient k) (Dp : Domain n→Gradient n k)
    (hp : MemW12 (ballDomain (0:Domain n) 1) p Dp)
    (hGrowth : ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Dp x))≤K*r^ν) :
    ∃P : NativeMorreySobolevSpace n k ν,
      nativeMorreyMapClass (n:=n) (q:=k) ν P=hp.2.1.toLp p ∧
      nativeMorreyHSClass (n:=n) (q:=k) ν P=hsUnitBallL2Class Dp hp.2.2 ∧
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),(nativeMorreyMapClass (n:=n) (q:=k) ν P).val x=p x) ∧
      ((fun x i=>WithLp.toLp 2 (fun j : Fin k=>nativeMorreyHSClass (n:=n) (q:=k) ν P x
        (finProdFinEquiv (i,j))))=ᵐ[volume.restrict (ball (0:Domain n) 1)]Dp) := by
  have hData := (existsUnique_nativeMorreySobolev_iff_power_growth ν p Dp hp).mpr
    ⟨K,growth_constant_nonneg ν K Dp hGrowth,hGrowth⟩
  let P := hData.choose
  have hP := hData.choose_spec.1
  have hMapAE : (nativeMorreyMapClass (n:=n) (q:=k) ν P : Domain n→Ambient k)=ᵐ[
      volume.restrict (ball (0:Domain n) 1)]p := by
    rw [hP.1]
    exact hp.2.1.coeFn_toLp
  exact ⟨P,hP.1,hP.2,hMapAE,raw_field_of_hs_class Dp hp.2.2
    (nativeMorreyHSClass (n:=n) (q:=k) ν P) hP.2⟩

private theorem coefficient_class_of_original_growth {n k : ℕ} (ν K : ℝ)
    (F : Domain n→Gradient n k)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0:Domain n) 1)))
    (hGrowth : ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (F x))≤K*r^ν) :
    ∃Z : MorreyCoefficientSpace n k ν,
      morreyCoefficientRecover (n:=n) (q:=k) ν Z=hsUnitBallL2Class F hF ∧
      ((fun x i=>WithLp.toLp 2 (fun j : Fin k=>morreyCoefficientRecover (n:=n) (q:=k) ν Z x
        (finProdFinEquiv (i,j))))=ᵐ[volume.restrict (ball (0:Domain n) 1)]F) := by
  have hData := (existsUnique_morreyCoefficient_iff_power_growth ν F hF).mpr
    ⟨K,growth_constant_nonneg ν K F hGrowth,hGrowth⟩
  let Z := hData.choose
  have hZ := hData.choose_spec.1
  exact ⟨Z,hZ,raw_field_of_hs_class F hF (morreyCoefficientRecover (n:=n) (q:=k) ν Z) hZ⟩

/-- The original scalar-path frame and its original finite power bounds
construct the same genuine native frame and coefficient classes. Both
coefficient L2 proofs, exact recovery identities, original skew constraints
and the unchanged parameter-direction growth bound are produced internally. -/
theorem exists_scalar_coulomb_native_perturbation_data
    (n : ℕ) (_hn : 2≤n) (γ : ℝ) (_hγ : 0<γ) (_hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,
      ‖e.symm T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q))
    (hp : MemW12 (ballDomain (0:Domain n) 1) p Dp)
    (hOrth : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (e (p x))*e (p x)=1)
    (hDet : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),(e (p x)).det=1)
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q))
    (hA : ∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0:Domain n) 1)))
    (hAskew : ∀i,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (A x i)= -(A x i))
    (τ KA KD KZ : ℝ)
    (hGrowthA : ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>e.symm (A x i)))≤KA*r^((n:ℝ)-2+γ))
    (hGrowthD : ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Dp x))≤KD*r^((n:ℝ)-2+γ))
    (hGrowthZ : ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>e.symm
        (star (e (p x))*e (Dp x i)+star (e (p x))*(τ • A x i)*e (p x))))≤KZ*r^((n:ℝ)-2+γ)) :
    let ν : ℝ := (n:ℝ)-2+γ
    let Zr : Domain n→Gradient n (q*q) := fun x i=>e.symm
      (star (e (p x))*e (Dp x i)+star (e (p x))*(τ • A x i)*e (p x))
    let Yr : Domain n→Gradient n (q*q) := fun x i=>e.symm (star (e (p x))*A x i*e (p x))
    let field : MorreyCoefficientSpace n (q*q) ν→Domain n→Gradient n (q*q) :=
      fun F x i=>WithLp.toLp 2 (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
    ∃(P : NativeMorreySobolevSpace n (q*q) ν) (Z Y : MorreyCoefficientSpace n (q*q) ν)
      (hZ : ∀i,MemLp (fun x=>Zr x i) 2 (volume.restrict (ball (0:Domain n) 1)))
      (hY : ∀i,MemLp (fun x=>Yr x i) 2 (volume.restrict (ball (0:Domain n) 1))),
      nativeMorreyMapClass (n:=n) (q:=q*q) ν P=hp.2.1.toLp p ∧
      nativeMorreyHSClass (n:=n) (q:=q*q) ν P=hsUnitBallL2Class Dp hp.2.2 ∧
      morreyCoefficientRecover (n:=n) (q:=q*q) ν Z=hsUnitBallL2Class Zr hZ ∧
      morreyCoefficientRecover (n:=n) (q:=q*q) ν Y=hsUnitBallL2Class Yr hY ∧
      ((nativeMorreyMapClass (n:=n) (q:=q*q) ν P : Domain n→Ambient (q*q))=ᵐ[
        volume.restrict (ball (0:Domain n) 1)]p) ∧
      ((fun x i=>WithLp.toLp 2 (fun j : Fin (q*q)=>nativeMorreyHSClass (n:=n) (q:=q*q) ν P x
        (finProdFinEquiv (i,j))))=ᵐ[volume.restrict (ball (0:Domain n) 1)]Dp) ∧
      (field Z=ᵐ[volume.restrict (ball (0:Domain n) 1)]Zr) ∧
      (field Y=ᵐ[volume.restrict (ball (0:Domain n) 1)]Yr) ∧
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,star (e (Zr x i))= -(e (Zr x i))) ∧
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,star (e (Yr x i))= -(e (Yr x i))) ∧
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,star (e (field Z x i))= -(e (field Z x i))) ∧
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,star (e (field Y x i))= -(e (field Y x i))) ∧
      (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Yr x))≤KA*r^ν) ∧
      (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (field Y x))≤KA*r^ν) ∧
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
        star (e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν P).val x))*
          e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν P).val x)=1 ∧
        (e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν P).val x)).det=1) := by
  let ν : ℝ := (n:ℝ)-2+γ
  let Zr : Domain n→Gradient n (q*q) := fun x i=>e.symm
    (star (e (p x))*e (Dp x i)+star (e (p x))*(τ • A x i)*e (p x))
  let Yr : Domain n→Gradient n (q*q) := fun x i=>e.symm (star (e (p x))*A x i*e (p x))
  let field : MorreyCoefficientSpace n (q*q) ν→Domain n→Gradient n (q*q) :=
    fun F x i=>WithLp.toLp 2 (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
  have hRawZ := scalar_connection_raw_data e hE p Dp hp hOrth A hA hAskew τ
  have hYLp := conjugated_columns_memLp e p hp.2.1 hOrth A hA
  have hYSkew := conjugated_raw_skew e p A hAskew
  have hYGrowth := conjugated_power_growth ν KA e hE p hOrth A hGrowthA
  have hPData := native_class_of_original_growth ν KD p Dp hp hGrowthD
  let P := hPData.choose
  have hP := hPData.choose_spec
  have hZData := coefficient_class_of_original_growth ν KZ Zr hRawZ.1 hGrowthZ
  let Z := hZData.choose
  have hZ := hZData.choose_spec
  have hYData := coefficient_class_of_original_growth ν KA Yr hYLp hYGrowth
  let Y := hYData.choose
  have hY := hYData.choose_spec
  have hZCanonical : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,
      star (e (field Z x i))= -(e (field Z x i)) := by
    filter_upwards [hZ.2,hRawZ.2] with x hx hz
    change field Z x=Zr x at hx
    intro i
    rw [congrFun hx i]
    exact hz i
  have hYCanonical : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,
      star (e (field Y x i))= -(e (field Y x i)) := by
    filter_upwards [hY.2,hYSkew] with x hx hy
    change field Y x=Yr x at hx
    intro i
    rw [congrFun hx i]
    exact hy i
  have hYGrowthCanonical : ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (field Y x))≤KA*r^ν := by
    intro a ha r hr
    have hAE : field Y=ᵐ[volume.restrict (ball a r∩ball (0:Domain n) 1)]Yr :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right hY.2
    exact (integral_congr_ae (hAE.mono fun x hx=>congrArg hsNormSq hx)).le.trans (hYGrowth a ha r hr)
  have hSO : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
      star (e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν P).val x))*
        e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν P).val x)=1 ∧
      (e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν P).val x)).det=1 := by
    filter_upwards [hP.2.2.1,hOrth,hDet] with x hx hox hdx
    rw [hx]
    exact ⟨hox,hdx⟩
  exact ⟨P,Z,Y,hRawZ.1,hYLp,hP.1,hP.2.1,hZ.1,hY.1,hP.2.2.1,hP.2.2.2,
    hZ.2,hY.2,hRawZ.2,hYSkew,hZCanonical,hYCanonical,hYGrowth,hYGrowthCanonical,hSO⟩

end StationaryHarmonicMaps.Analysis
end
