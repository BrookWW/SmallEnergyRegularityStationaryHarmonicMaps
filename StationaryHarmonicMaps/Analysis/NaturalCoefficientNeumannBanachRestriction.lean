module

public import StationaryHarmonicMaps.Analysis.NaturalCoefficientNeumannBanachConstraint
public import StationaryHarmonicMaps.Analysis.MeanZeroNativeMorreyConstraint
public import Mathlib.Analysis.Normed.Ring.Units

/-!
# The actual natural Neumann operator on a fixed closed linear constraint

The original raw adjoint tests preserve the fixed coefficient kernel.
The same genuine operator restricts to the complete constrained native
space and retains its small norm, so its identity perturbation is invertible.
-/

public section
open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff
noncomputable section
namespace StationaryHarmonicMaps.Analysis

private abbrev mapValue {n q : ℕ} (ν : ℝ) (X : MeanZeroNativeMorreySpace n q ν) :
    Domain n → Ambient q := (nativeMorreyMapClass (n:=n) (q:=q) ν) X.val

private abbrev gradientValue {n q : ℕ} (ν : ℝ) (X : MeanZeroNativeMorreySpace n q ν) :
    Domain n → Gradient n q := fun x i=>WithLp.toLp 2
      (fun j : Fin q=>(nativeMorreyHSClass (n:=n) (q:=q) ν) X.val x (finProdFinEquiv (i,j)))

private theorem canonical_native {n q : ℕ} (ν : ℝ) (X : MeanZeroNativeMorreySpace n q ν) :
    MemW12 (ballDomain (0:Domain n) 1) (mapValue ν X) (gradientValue ν X) ∧
    (⨍x in ball (0:Domain n) 1,mapValue ν X x)=0 ∧
    ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (gradientValue ν X x))≤
        ‖meanZeroNativeMorreyGradientClass n q ν X‖^2*r^ν := by
  obtain ⟨u,Du,hu,hMean,hMap,hGrad,hGrowth⟩ := exists_raw_native_of_meanZeroNativeMorrey ν X
  have hUAE : mapValue ν X=ᵐ[volume.restrict (ball (0:Domain n) 1)] u := by
    change ((nativeMorreyMapClass (n:=n) (q:=q) ν) X.val : Domain n→Ambient q)=ᵐ[_]u
    rw [hMap]
    exact hu.2.1.coeFn_toLp
  have hDAE : gradientValue ν X=ᵐ[volume.restrict (ball (0:Domain n) 1)]Du := by
    have hHS := hsUnitBallL2Class_ae Du hu.2.2
    rw [←hGrad] at hHS
    filter_upwards [hHS] with x hx
    funext i
    ext j
    have H := congrArg (fun z : Ambient (n*q)=>z (finProdFinEquiv (i,j))) hx
    simpa only [hsFlatten,gradientValue,finProdFinEquiv.symm_apply_apply] using H
  refine ⟨hu.congr_ae hUAE.symm hDAE.symm,(average_congr hUAE).trans hMean,?_⟩
  intro a ha r hr
  have hDAE' : gradientValue ν X=ᵐ[volume.restrict (ball a r∩ball (0:Domain n) 1)]Du :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hDAE
  calc
    _=∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Du x) :=
      integral_congr_ae (hDAE'.mono fun x hx=>congrArg hsNormSq hx)
    _≤_ := hGrowth a ha r hr

private theorem canonical_integral_zero {n q : ℕ} (ν : ℝ)
    (X : MeanZeroNativeMorreySpace n q ν) :
    (∫x in ball (0:Domain n) 1,mapValue ν X x)=0 := by
  have hMean := (canonical_native ν X).2.1
  rw [average_eq] at hMean
  have hV : 0<(volume.restrict (ball (0:Domain n) 1)).real univ := by
    rw [measureReal_restrict_apply_univ]
    exact HolderToCK.ball_volume_real_pos 0 (by norm_num)
  exact (smul_eq_zero.mp hMean).resolve_left (inv_ne_zero hV.ne')


private theorem canonical_mem_constraint_iff {n q d : ℕ} (ν : ℝ)
    (J : Ambient q→L[ℝ]Ambient d) (X : MeanZeroNativeMorreySpace n q ν) :
    X∈constrainedMeanZeroNativeMorreySubmodule n q d ν J ↔
      (fun x=>J (mapValue ν X x))=ᵐ[volume.restrict (ball (0:Domain n) 1)](fun _=>0) := by
  let U := nativeMorreyMapClass (n:=n) (q:=q) ν X.val
  have hU : MemLp U 2 (volume.restrict (ball (0:Domain n) 1)) := Lp.memLp U
  exact mem_constrainedMeanZeroNativeMorreySubmodule_iff ν J U hU X
    (Lp.toLp_coeFn U hU).symm

/-- The complete original native Neumann tests imply invariance of an actual
fixed coefficient kernel; the constraint is imposed only on the input map. -/
theorem natural_neumann_operator_preserves_fixed_kernel {n m q d : ℕ} (ν : ℝ)
    (J : Ambient q→L[ℝ]Ambient d)
    (B : Ambient m→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (Z : Domain n→Gradient n m)
    (hB : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,∀w : Ambient q,
      J w=0 → J (B (Z x i) w)=0)
    (T : MeanZeroNativeMorreySpace n q ν→L[ℝ]MeanZeroNativeMorreySpace n q ν)
    (hTests : ∀(X : MeanZeroNativeMorreySpace n q ν)
      (ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      let u : Domain n→Ambient q := (nativeMorreyMapClass (n:=n) (q:=q) ν) X.val
      let Q : Domain n→Gradient n q := fun x i=>WithLp.toLp 2
        (fun j : Fin q=>(nativeMorreyHSClass (n:=n) (q:=q) ν) (T X).val x (finProdFinEquiv (i,j)))
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) :
    ∀X∈constrainedMeanZeroNativeMorreySubmodule n q d ν J,
      T X∈constrainedMeanZeroNativeMorreySubmodule n q d ν J := by
  intro X hX
  have hXAE := (canonical_mem_constraint_iff ν J X).mp hX
  have hForce : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,
      J (B (Z x i) (mapValue ν X x))=0 := by
    filter_upwards [hXAE,hB] with x hx hBx
    exact fun i=>hBx i (mapValue ν X x) hx
  have hConstraint := native_neumann_response_fixed_kernel_ae J
    (fun x i=>B (Z x i) (mapValue ν X x)) (gradientValue ν (T X)) (mapValue ν (T X))
    (canonical_native ν (T X)).1 (canonical_integral_zero ν (T X)) (hTests X) hForce
  exact (canonical_mem_constraint_iff ν J (T X)).mpr (hConstraint.mono fun _ hx=>hx.1)

private theorem small_add_identity_inverse {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (T : V→L[ℝ]V) (hT : ‖T‖≤(1/2:ℝ)) :
    ∃!A : V≃L[ℝ]V,(∀X : V,A X=X+T X) ∧ ‖(A.symm : V→L[ℝ]V)‖≤2 := by
  have hTOne : ‖-T‖<1 := by rw [norm_neg];exact hT.trans_lt (by norm_num)
  let U := Units.oneSub (-T) hTOne
  let A : V≃L[ℝ]V := ContinuousLinearEquiv.ofUnit U
  have hA (X : V) : A X=X+T X := by
    change ((1 : V→L[ℝ]V)-(-T)) X=X+T X
    simp only [sub_neg_eq_add,add_apply,one_apply_eq_self]
  have hInverse (Y : V) : ‖A.symm Y‖≤2*‖Y‖ := by
    have hEquation : A.symm Y+T (A.symm Y)=Y := (hA (A.symm Y)).symm.trans (A.apply_symm_apply Y)
    have hRearr : A.symm Y=Y-T (A.symm Y) := eq_sub_of_add_eq hEquation
    have hBound : ‖A.symm Y‖≤‖Y‖+(1/2:ℝ)*‖A.symm Y‖ := by
      calc
        _=‖Y-T (A.symm Y)‖ := congrArg norm hRearr
        _≤‖Y‖+‖T (A.symm Y)‖ := norm_sub_le _ _
        _≤‖Y‖+‖T‖*‖A.symm Y‖ := add_le_add le_rfl (T.le_opNorm _)
        _≤_ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hT (norm_nonneg (A.symm Y)))
    linarith only [hBound]
  have hNorm : ‖(A.symm : V→L[ℝ]V)‖≤2 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num) hInverse
  refine ⟨A,⟨hA,hNorm⟩,?_⟩
  intro D hD
  apply ContinuousLinearEquiv.ext
  funext X
  exact (hD.1 X).trans (hA X).symm


private theorem exists_submodule_identity_inverse {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (S : Submodule ℝ V) [CompleteSpace S]
    (T : V→L[ℝ]V) (hInvariant : ∀X∈S,T X∈S) (hSmall : ‖T‖≤(1/2:ℝ)) :
    ∃!A : S≃L[ℝ]S,(∀X : S,(A X).val=X.val+T X.val) ∧ ‖(A.symm : S→L[ℝ]S)‖≤2 := by
  let U : S→L[ℝ]S := T.restrict hInvariant
  have hUNorm : ‖U‖≤‖T‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro X
    change ‖T X.val‖≤‖T‖*‖X.val‖
    exact T.le_opNorm X.val
  obtain ⟨A,⟨hA,hInverse⟩,hUnique⟩ := small_add_identity_inverse U (hUNorm.trans hSmall)
  refine ⟨A,⟨fun X=>congrArg Subtype.val (hA X),hInverse⟩,?_⟩
  intro D hD
  apply hUnique
  refine ⟨?_,hD.2⟩
  intro X
  exact Subtype.ext (hD.1 X)

/-- The actual identity perturbation restricts to the genuine complete
fixed-kernel native space. Its inverse is produced internally and has
operator norm at most two in the same inherited norm. -/
theorem exists_natural_neumann_fixed_kernel_identity_inverse {n m q d : ℕ} (ν : ℝ)
    (J : Ambient q→L[ℝ]Ambient d)
    (B : Ambient m→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (Z : Domain n→Gradient n m)
    (hB : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,∀w : Ambient q,
      J w=0 → J (B (Z x i) w)=0)
    (T : MeanZeroNativeMorreySpace n q ν→L[ℝ]MeanZeroNativeMorreySpace n q ν)
    (hTests : ∀(X : MeanZeroNativeMorreySpace n q ν)
      (ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      let u : Domain n→Ambient q := (nativeMorreyMapClass (n:=n) (q:=q) ν) X.val
      let Q : Domain n→Gradient n q := fun x i=>WithLp.toLp 2
        (fun j : Fin q=>(nativeMorreyHSClass (n:=n) (q:=q) ν) (T X).val x (finProdFinEquiv (i,j)))
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i))
    (hSmall : ‖T‖≤(1/2:ℝ)) :
    ∃!A : ConstrainedMeanZeroNativeMorreySpace n q d ν J≃L[ℝ]
        ConstrainedMeanZeroNativeMorreySpace n q d ν J,
      (∀X : ConstrainedMeanZeroNativeMorreySpace n q d ν J,(A X).val=X.val+T X.val) ∧
      ‖(A.symm : ConstrainedMeanZeroNativeMorreySpace n q d ν J→L[ℝ]
        ConstrainedMeanZeroNativeMorreySpace n q d ν J)‖≤2 := by
  have hInvariant := natural_neumann_operator_preserves_fixed_kernel ν J B Z hB T hTests
  exact exists_submodule_identity_inverse (constrainedMeanZeroNativeMorreySubmodule n q d ν J)
    T hInvariant hSmall


end StationaryHarmonicMaps.Analysis
end
