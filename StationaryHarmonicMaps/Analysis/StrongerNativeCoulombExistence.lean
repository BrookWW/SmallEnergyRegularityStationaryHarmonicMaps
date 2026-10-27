module
public import StationaryHarmonicMaps.Analysis.ScalarCoulombPathInitialization
public import StationaryHarmonicMaps.Analysis.CoulombTwoExponentAbsorption
public import StationaryHarmonicMaps.Analysis.NativeMorreyCriticalPerturbationContinuity
public import StationaryHarmonicMaps.Analysis.NativeCoulombPerturbations
public import StationaryHarmonicMaps.Analysis.ScalarCoulombNativePerturbationData
public import StationaryHarmonicMaps.Analysis.ScalarCoulombFluxRealization
public import StationaryHarmonicMaps.Analysis.NativeCoulombThresholdArithmetic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.IntermediateValue
/-!
# Stronger Morrey native Coulomb frames

The scalar homotopy of the original skew connection admits a native special
orthogonal frame on the whole unit ball. Local solvability comes from the
actual matrix exponential and Neumann inverse; joint compactness closes the
bounded scalar path. Two-exponent absorption gives uniform critical and
stronger growth bounds for the same frame and transformed connection.
-/

public section
open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal
noncomputable section
namespace StationaryHarmonicMaps.Analysis

private theorem scalar_interval_covered_of_closed_local
    (S : Set ℝ) (hClosed : IsClosed S) (hZero : (0:ℝ)∈S)
    (hLocal : ∀τ∈Icc (0:ℝ) 1,τ∈S →
      ∀ᶠt in 𝓝 τ,t∈Icc (0:ℝ) 1 → t∈S) :
    ∀t∈Icc (0:ℝ) 1,t∈S := by
  let T : Set (Icc (0:ℝ) 1) := Subtype.val ⁻¹' S
  have hTClosed : IsClosed T := hClosed.preimage continuous_subtype_val
  have hTOpen : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro τ hτ
    have hLift := (continuous_subtype_val.tendsto τ).eventually (hLocal τ.val τ.property hτ)
    filter_upwards [hLift] with s hs
    exact hs s.property
  letI : PreconnectedSpace (Icc (0:ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  have hNonempty : T.Nonempty := ⟨⟨0,by norm_num⟩,hZero⟩
  have hAll : T=univ := (show IsClopen T from ⟨hTClosed,hTOpen⟩).eq_univ hNonempty
  intro t ht
  have hT : (⟨t,ht⟩ : Icc (0:ℝ) 1)∈T := by rw [hAll];trivial
  exact hT

private theorem critical_field_congr_ae {n q : ℕ} (D : Set (Domain n))
    (F G : Domain n→Gradient n q) (hFG : F=ᵐ[volume.restrict D]G) :
    criticalGradientMorreySquare F D=criticalGradientMorreySquare G D := by
  unfold criticalGradientMorreySquare
  apply iSup_congr
  intro a
  apply iSup_congr
  intro r
  congr 1
  exact dirichletEnergy_congr_ae
    (ae_restrict_of_ae_restrict_of_subset inter_subset_right hFG)

private theorem original_growth_constant_nonneg {n k : ℕ} (ν K : ℝ)
    (F : Domain n→Gradient n k)
    (hGrowth : ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (F x))≤K*r^ν) : 0≤K := by
  have H := hGrowth 0 (mem_ball_self zero_lt_one) 1 zero_lt_one
  rw [Real.one_rpow,mul_one] at H
  exact (integral_nonneg fun _=>hsNormSq_nonneg _).trans H

private theorem scalar_path_original_power_growth {n q k : ℕ}
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient k)
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q)) (ν K : ℝ) (hK : 0≤K)
    (hGrowth : ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>E (A x i)))≤K*r^ν) :
    ∀t∈Icc (0:ℝ) 1,∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>E (t • A x i)))≤K*r^ν := by
  intro t ht a ha r hr
  have hSquare : t^2≤1 := by nlinarith only [ht.1,ht.2]
  calc
    _=t^2*(∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>E (A x i))) := by
      simp_rw [E.map_smul,hsNormSq_const_smul]
      exact integral_const_mul _ _
    _≤t^2*(K*r^ν) := mul_le_mul_of_nonneg_left (hGrowth a ha r hr) (sq_nonneg t)
    _≤K*r^ν := (mul_le_mul_of_nonneg_right hSquare
      (mul_nonneg hK (Real.rpow_nonneg hr.le _))).trans_eq (one_mul _)

private theorem original_natural_tests_of_ae {n k : ℕ}
    (F G : Domain n→Gradient n k)
    (hFG : F=ᵐ[volume.restrict (ball (0:Domain n) 1)]G)
    (hTests : ∀(ψ : Domain n→Ambient k) (Dψ : Domain n→Gradient n k),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (G x i) (Dψ x i))=0) :
    ∀(ψ : Domain n→Ambient k) (Dψ : Domain n→Gradient n k),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (F x i) (Dψ x i))=0 := by
  intro ψ Dψ hψ
  have hAE : (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i))=ᵐ[
      volume.restrict (ball (0:Domain n) 1)](fun x=>∑i : Fin n,inner ℝ (G x i) (Dψ x i)) :=
    hFG.mono fun x hx=>congrArg (fun W : Gradient n k=>∑i : Fin n,inner ℝ (W i) (Dψ x i)) hx
  exact (integral_congr_ae hAE).trans (hTests ψ Dψ hψ)

private theorem native_gradient_critical_bound_of_difference {n k : ℕ} (ν : ℝ)
    (I : MorreyCoefficientSpace n k ν→L[ℝ]MorreyCoefficientSpace n k ((n:ℝ)-2))
    (hI : ∀F : MorreyCoefficientSpace n k ν,
      morreyCoefficientRecover (n:=n) (q:=k) ((n:ℝ)-2) (I F)=
        morreyCoefficientRecover (n:=n) (q:=k) ν F)
    (P W : NativeMorreySobolevSpace n k ν)
    (Dp Dw : Domain n→Gradient n k)
    (hDp : ∀i,MemLp (fun x=>Dp x i) 2 (volume.restrict (ball (0:Domain n) 1)))
    (hDw : ∀i,MemLp (fun x=>Dw x i) 2 (volume.restrict (ball (0:Domain n) 1)))
    (hP : nativeMorreyHSClass (n:=n) (q:=k) ν P=hsUnitBallL2Class Dp hDp)
    (hW : nativeMorreyHSClass (n:=n) (q:=k) ν W=hsUnitBallL2Class Dw hDw)
    (r M : ℝ) (hr : 0≤r) (hM : 0≤M)
    (hNorm : ‖I (nativeMorreyGradientClass (n:=n) (q:=k) ν W-
      nativeMorreyGradientClass (n:=n) (q:=k) ν P)‖≤r)
    (hCritical : criticalGradientMorreySquare Dp (ball (0:Domain n) 1)≤ENNReal.ofReal M) :
    criticalGradientMorreySquare Dw (ball (0:Domain n) 1)≤ENNReal.ofReal (2*M+2*r^2) := by
  let F := I (nativeMorreyGradientClass (n:=n) (q:=k) ν W)
  let G := I (nativeMorreyGradientClass (n:=n) (q:=k) ν P)
  have hF : morreyCoefficientRecover (n:=n) (q:=k) ((n:ℝ)-2) F=hsUnitBallL2Class Dw hDw :=
    (hI (nativeMorreyGradientClass (n:=n) (q:=k) ν W)).trans hW
  have hG : morreyCoefficientRecover (n:=n) (q:=k) ((n:ℝ)-2) G=hsUnitBallL2Class Dp hDp :=
    (hI (nativeMorreyGradientClass (n:=n) (q:=k) ν P)).trans hP
  have hDifference : F-G=I (nativeMorreyGradientClass (n:=n) (q:=k) ν W-
      nativeMorreyGradientClass (n:=n) (q:=k) ν P) :=
    (I.map_sub _ _).symm
  have hNorm' : ‖F-G‖≤r := (congrArg norm hDifference).le.trans hNorm
  exact critical_morrey_bound_of_coefficient_difference F G Dw Dp hDw hDp hF hG r M hr hM hNorm' hCritical

private def bounded_scalar_path_set {n q : ℕ}
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q))
    (MD MZ ν KD KZ : ℝ) : Set ℝ :=
  {t : ℝ | t∈Icc (0:ℝ) 1 ∧
    ∃(p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q)),
      MemW12 (ballDomain (0:Domain n) 1) p Dp ∧
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (e (p x))*e (p x)=1) ∧
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),(e (p x)).det=1) ∧
      criticalGradientMorreySquare Dp (ball (0:Domain n) 1)≤ENNReal.ofReal MD ∧
      (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Dp x))≤KD*r^ν) ∧
      let Z := fun x i=>e.symm (star (e (p x))*e (Dp x i)+star (e (p x))*(t • A x i)*e (p x))
      criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal MZ ∧
      (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Z x))≤KZ*r^ν) ∧
      ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0}

private theorem bounded_scalar_path_set_closed {n q : ℕ}
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,
      ‖e.symm T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q))
    (hA : ∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0:Domain n) 1)))
    (hAskew : ∀i,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (A x i)= -(A x i))
    (MA MD MZ ν KD KZ : ℝ) (hMA : 0≤MA) (hMD : 0≤MD) (hMZ : 0≤MZ)
    (hKD : 0≤KD) (hKZ : 0≤KZ)
    (hCritical : criticalGradientMorreySquare (fun x i=>e.symm (A x i)) (ball (0:Domain n) 1)≤ENNReal.ofReal MA) :
    IsClosed (bounded_scalar_path_set e A MD MZ ν KD KZ) := by
  exact isClosed_scalar_path_bounded_natural_coulomb_frames
    e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply e.symm_apply_apply hE
    A hA hAskew MA MD MZ ν KD KZ hMA hMD hMZ hKD hKZ hCritical

private theorem bounded_scalar_path_set_zero {n q : ℕ}
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q))
    (MD MZ ν KD KZ : ℝ) (hKD : 0≤KD) (hKZ : 0≤KZ) :
    (0:ℝ)∈bounded_scalar_path_set e A MD MZ ν KD KZ := by
  let p : Domain n→Ambient (q*q) := fun _=>e.symm 1
  let Dp : Domain n→Gradient n (q*q) := fun _ _=>0
  have hInit := identity_frame_zero_scalar_connection_unitBall
    e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply A
  have hp : MemW12 (ballDomain (0:Domain n) 1) p Dp := hInit.1
  have hSO : ∀x,star (e (p x))*e (p x)=1 ∧ (e (p x)).det=1 := hInit.2.1
  have hDZ : criticalGradientMorreySquare Dp (ball (0:Domain n) 1)=0 := hInit.2.2.1
  let Z := fun x i=>e.symm (star (e (p x))*e (Dp x i)+star (e (p x))*((0:ℝ) • A x i)*e (p x))
  have hZZ : criticalGradientMorreySquare Z (ball (0:Domain n) 1)=0 := hInit.2.2.2.1
  have hZPoint (x : Domain n) (i : Fin n) : Z x i=0 :=
    (congrArg e.symm (hInit.2.2.2.2.1 x i)).trans e.symm.map_zero
  change (0:ℝ)∈Icc 0 1 ∧ _
  refine ⟨by norm_num,p,Dp,hp,Eventually.of_forall fun x=>(hSO x).1,
    Eventually.of_forall fun x=>(hSO x).2,?_,?_,?_,?_,?_⟩
  · rw [hDZ]
    exact zero_le
  · intro a _ha r hr
    have hZero : (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Dp x))=0 := by
      simp [Dp,hsNormSq]
    exact hZero.le.trans (mul_nonneg hKD (Real.rpow_nonneg hr.le _))
  · rw [hZZ]
    exact zero_le
  · intro a _ha r hr
    have hZero : (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Z x))=0 := by
      simp only [hsNormSq,hZPoint,norm_zero,zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero,integral_zero]
    exact hZero.le.trans (mul_nonneg hKZ (Real.rpow_nonneg hr.le _))
  · intro ψ Dψ hψ
    exact (hInit.2.2.2.2.2 ψ Dψ hψ).2

private theorem exists_scalar_path_frame_improvement
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,
      ‖e.symm T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) :
    ∃δ C : ℝ,0<δ ∧ 0<C ∧
      ∀(A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q))
        (_hA : ∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0:Domain n) 1)))
        (_hAskew : ∀i,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (A x i)= -(A x i))
        (η KA : ℝ),
        criticalGradientMorreySquare (fun x i=>e.symm (A x i)) (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
        (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
          (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>e.symm (A x i)))≤KA*r^((n:ℝ)-2+γ)) →
        ∀τ∈Icc (0:ℝ) 1,
        ∀(p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q)) (J : ℝ),
          MemW12 (ballDomain (0:Domain n) 1) p Dp →
          (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (e (p x))*e (p x)=1) →
          (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),(e (p x)).det=1) →
          criticalGradientMorreySquare Dp (ball (0:Domain n) 1)≤ENNReal.ofReal (δ^2) →
          (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
            (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Dp x))≤J*r^((n:ℝ)-2+γ)) →
          (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
            MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
            (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ
              (e.symm (star (e (p x))*e (Dp x i)+star (e (p x))*(τ • A x i)*e (p x))) (Dψ x i))=0) →
          τ∈bounded_scalar_path_set e A (C*η^2) (C*η^2) ((n:ℝ)-2+γ) (C*KA) (C*KA) := by
  obtain ⟨δ,C,hδ,hC,H⟩ := exists_coulomb_critical_and_stronger_boundary_absorption n hn q
    e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply e.symm_apply_apply hE γ hγ hγTwo
  refine ⟨δ,C,hδ,hC,?_⟩
  intro A hA hAskew η KA hCritical hGrowth τ hτ p Dp J hp hOrth hDet hSmall hDGrowth hNatural
  have hKA : 0≤KA := original_growth_constant_nonneg ((n:ℝ)-2+γ) KA (fun x i=>e.symm (A x i)) hGrowth
  have hPath := skew_connection_scalar_critical_homotopy.{0,0} e.symm.toContinuousLinearMap
    (ball (0:Domain n) 1) A hA hAskew (η^2) (sq_nonneg η) hCritical
  have hScalar := hPath.1 τ
  have hSCrit := hPath.2.1 τ hτ
  have hSGrowth := scalar_path_original_power_growth e.symm.toContinuousLinearMap A
    ((n:ℝ)-2+γ) KA hKA hGrowth τ hτ
  have hImproved := H p Dp (fun x i=>τ • A x i) J (η^2) KA hp hOrth hScalar.1 hScalar.2.1
    hSmall hDGrowth (sq_nonneg η) hKA hSCrit hSGrowth hNatural
  let Z := fun x i=>e.symm (star (e (p x))*e (Dp x i)+star (e (p x))*(τ • A x i)*e (p x))
  have hSum : criticalGradientMorreySquare Dp (ball (0:Domain n) 1)+
      criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (C*η^2) := hImproved.1
  have hDC : criticalGradientMorreySquare Dp (ball (0:Domain n) 1)≤ENNReal.ofReal (C*η^2) :=
    (le_add_of_nonneg_right (zero_le : (0:ℝ≥0∞)≤criticalGradientMorreySquare Z (ball (0:Domain n) 1))).trans hSum
  have hZC : criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (C*η^2) :=
    (le_add_of_nonneg_left (zero_le : (0:ℝ≥0∞)≤criticalGradientMorreySquare Dp (ball (0:Domain n) 1))).trans hSum
  change τ∈Icc (0:ℝ) 1 ∧ _
  exact ⟨hτ,p,Dp,hp,hOrth,hDet,hDC,(fun a ha r hr=>(hImproved.2 a ha r hr).1),
    hZC,(fun a ha r hr=>(hImproved.2 a ha r hr).2),hNatural⟩

private theorem exists_original_scalar_baseline_flux
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (q : ℕ) (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,‖e.symm T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) :
    let ν : ℝ := (n:ℝ)-2+γ
    let S := NativeMorreySobolevSpace n (q*q) ν
    let M := MorreyCoefficientSpace n (q*q) ν
    let V := SkewMeanZeroNativeMorreySpace n q ν e
    letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
    letI : SeminormedAddCommGroup V :=
      (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
    letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
    let value : S→Domain n→Ambient (q*q) := fun H=>nativeMorreyMapClass (n:=n) (q:=q*q) ν H
    let field : M→Domain n→Gradient n (q*q) := fun F x i=>WithLp.toLp 2
      (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
    let D : S→L[ℝ]M := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    let Exp : S→S := matrixNativeMorreyExp n hn γ hγ hγTwo q
      e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply e.symm_apply_apply
    ∃ε : ℝ,0<ε ∧
      ∀(p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q))
        (hp : MemW12 (ballDomain (0:Domain n) 1) p Dp)
        (hOrth : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (e (p x))*e (p x)=1)
        (hDet : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),(e (p x)).det=1)
        (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q))
        (_hA : ∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0:Domain n) 1)))
        (_hAskew : ∀i,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (A x i)= -(A x i)) (τ : ℝ),
      let Zr := fun x i=>e.symm (star (e (p x))*e (Dp x i)+star (e (p x))*(τ • A x i)*e (p x))
      let Yr := fun x i=>e.symm (star (e (p x))*A x i*e (p x))
      ∀KA KD KZ : ℝ,
        (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
          (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>e.symm (A x i)))≤KA*r^ν) →
        (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
          (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Dp x))≤KD*r^ν) →
        (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
          (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Zr x))≤KZ*r^ν) →
      ∀η : ℝ,0≤η → η≤ε →
        criticalGradientMorreySquare Zr (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
        (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Zr x i) (Dψ x i))=0) →
      ∃(P : S) (Z Y : M),
        nativeMorreyMapClass (n:=n) (q:=q*q) ν P=hp.2.1.toLp p ∧
        nativeMorreyHSClass (n:=n) (q:=q*q) ν P=hsUnitBallL2Class Dp hp.2.2 ∧
        (field Z=ᵐ[volume.restrict (ball (0:Domain n) 1)]Zr) ∧
        (field Y=ᵐ[volume.restrict (ball (0:Domain n) 1)]Yr) ∧
      ∃Φ : S×ℝ→M,
        (∀p : S×ℝ,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
          field (Φ p) x=fun i=>e.symm
            (e (value (Exp (-p.1)) x)*e (field (D (Exp p.1)) x i)+
              (e (value (Exp (-p.1)) x)*(e (field Z x i)+p.2 • e (field Y x i)))*
                e (value (Exp p.1) x))) ∧
        (∀p : S×ℝ,AnalyticAt ℝ Φ p) ∧
        (∀t : ℝ,Φ (0,t)=Z+t • Y) ∧
        ∀U : Set (ℝ×V),U∈𝓝 (0 : ℝ×V) →
          ∀ᶠt in 𝓝 (0 : ℝ),∃u : V,(t,u)∈U ∧
            nativeNeumannMorreyResponse n hn ν
              (by
                have hnR : (2:ℝ)≤n := by exact_mod_cast hn
                dsimp only [ν]
                linarith)
              (by dsimp only [ν];linarith) (q*q) (Φ (u.val.val,t))=0 ∧
            ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
              MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
              IntegrableOn (fun x=>∑i : Fin n,inner ℝ (field (Φ (u.val.val,t)) x i) (Dψ x i))
                (ball (0:Domain n) 1) volume ∧
              (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (field (Φ (u.val.val,t)) x i) (Dψ x i))=0 := by
  let ν : ℝ := (n:ℝ)-2+γ
  let S := NativeMorreySobolevSpace n (q*q) ν
  let M := MorreyCoefficientSpace n (q*q) ν
  let V := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup V :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  let field : M→Domain n→Gradient n (q*q) := fun F x i=>WithLp.toLp 2
    (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
  have hLocal := exists_small_native_coulomb_perturbations n hn γ hγ hγTwo q e
  let ε := hLocal.choose
  have hε : 0<ε := hLocal.choose_spec.1
  refine ⟨ε,hε,?_⟩
  intro p Dp hp hOrth hDet A hA hAskew τ Zr Yr KA KD KZ hGA hGD hGZ η hη hSmall hCrit hNatural
  have hData := exists_scalar_coulomb_native_perturbation_data n hn γ hγ hγTwo q e hE
    p Dp hp hOrth hDet A hA hAskew τ KA KD KZ hGA hGD hGZ
  let P := hData.choose
  let Z := hData.choose_spec.choose
  let Y := hData.choose_spec.choose_spec.choose
  have hChar := hData.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hPMap : nativeMorreyMapClass (n:=n) (q:=q*q) ν P=hp.2.1.toLp p := hChar.1
  have hPGrad : nativeMorreyHSClass (n:=n) (q:=q*q) ν P=hsUnitBallL2Class Dp hp.2.2 := hChar.2.1
  have hZAE : field Z=ᵐ[volume.restrict (ball (0:Domain n) 1)]Zr := hChar.2.2.2.2.2.2.1
  have hYAE : field Y=ᵐ[volume.restrict (ball (0:Domain n) 1)]Yr := hChar.2.2.2.2.2.2.2.1
  have hZSk : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
      star (e (field Z x i))= -(e (field Z x i)) := hChar.2.2.2.2.2.2.2.2.2.2.1
  have hYSk : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
      star (e (field Y x i))= -(e (field Y x i)) := hChar.2.2.2.2.2.2.2.2.2.2.2.1
  have hCritCanonical : criticalGradientMorreySquare (field Z) (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) :=
    (critical_field_congr_ae (ball (0:Domain n) 1) (field Z) Zr hZAE).le.trans hCrit
  have hNaturalCanonical := original_natural_tests_of_ae (field Z) Zr hZAE hNatural
  have hPhiData := hLocal.choose_spec.2 Z Y η hNaturalCanonical hη hSmall hCritCanonical hZSk hYSk
  exact ⟨P,Z,Y,hPMap,hPGrad,hZAE,hYAE,hPhiData⟩

private theorem scalar_candidate_from_controlled_flux
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q))
    (hp : MemW12 (ballDomain (0 : Domain n) 1) p Dp)
    (P : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ))
    (hPMap : nativeMorreyMapClass (n:=n) (q:=q*q) ((n : ℝ)-2+γ) P=hp.2.1.toLp p)
    (hPSO : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (e (p x))*e (p x)=1 ∧ (e (p x)).det=1)
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q)) (τ : ℝ) :
    let ν := (n : ℝ)-2+γ
    let S := NativeMorreySobolevSpace n (q*q) ν
    let M := MorreyCoefficientSpace n (q*q) ν
    let E := e.symm.toContinuousLinearMap
    let R := e.toContinuousLinearMap
    let value : S→Domain n→Ambient (q*q) := fun H=>nativeMorreyMapClass (n:=n) (q:=q*q) ν H
    let field : M→Domain n→Gradient n (q*q) := fun F x i=>WithLp.toLp 2
      (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
    let D := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    let Exp := matrixNativeMorreyExp n hn γ hγ hγTwo q E R e.apply_symm_apply e.symm_apply_apply
    ∀(Z Y : M),
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
        field Z x i=e.symm (star (e (p x))*e (Dp x i)+star (e (p x))*(τ • A x i)*e (p x))) →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
        field Y x i=e.symm (star (e (p x))*A x i*e (p x))) →
      ∀(Φ : S×ℝ→M),
        (∀Q : S×ℝ,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),field (Φ Q) x=fun i=>e.symm
          (e (value (Exp (-Q.1)) x)*e (field (D (Exp Q.1)) x i)+
            (e (value (Exp (-Q.1)) x)*(e (field Z x i)+Q.2 • e (field Y x i)))*e (value (Exp Q.1) x))) →
      ∀(X : SkewMeanZeroNativeMorreySpace n q ν e) (t : ℝ),
      ∀(I : M→L[ℝ]MorreyCoefficientSpace n (q*q) ((n:ℝ)-2)),
        (∀F : M,morreyCoefficientRecover (n:=n) (q:=q*q) ((n:ℝ)-2) (I F)=
          morreyCoefficientRecover (n:=n) (q:=q*q) ν F) →
      ∀r MD : ℝ,0≤r → 0≤MD →
        ‖I (D (matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R P (Exp X.val.val))-D P)‖≤r →
        criticalGradientMorreySquare Dp (ball (0:Domain n) 1)≤ENNReal.ofReal MD →
        (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (field (Φ (X.val.val,t)) x i) (Dψ x i))=0) →
      ∃(w : Domain n→Ambient (q*q)) (Dw : Domain n→Gradient n (q*q)) (J : ℝ),
        MemW12 (ballDomain (0:Domain n) 1) w Dw ∧
        (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (e (w x))*e (w x)=1) ∧
        (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),(e (w x)).det=1) ∧
        criticalGradientMorreySquare Dw (ball (0:Domain n) 1)≤ENNReal.ofReal (2*MD+2*r^2) ∧
        (∀a∈ball (0:Domain n) 1,∀ρ : ℝ,0<ρ →
          (∫x in ball a ρ∩ball (0:Domain n) 1,hsNormSq (Dw x))≤J*ρ^ν) ∧
        ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ
            (e.symm (star (e (w x))*e (Dw x i)+star (e (w x))*((τ+t) • A x i)*e (w x))) (Dψ x i))=0
 := by
  intro ν S M E R value field D Exp Z Y hZ hY Φ hFormula X t I hI r MD hr hMD hNorm hCritical hNatural
  have hReal := scalar_native_coulomb_flux_realization n hn γ hγ hγTwo q e p Dp hp P hPMap hPSO A τ
    Z Y hZ hY Φ hFormula X t
  obtain ⟨v,Dv,hv,_hVMap,_hVGrad,hProd⟩ := hReal
  let B := matrixMorreyCoefficientProduct E R
  let W := fun x=>B (p x) (v x)
  let DW := fun x i=>B (Dp x i) (v x)+B (p x) (Dv x i)
  let Q := matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R P (Exp X.val.val)
  let Cw := fun x i=>e.symm (star (e (W x))*e (DW x i)+star (e (W x))*((τ+t) • A x i)*e (W x))
  obtain ⟨hW,_hWMap,hWGrad,hWSO,hFluxAE,_hCw,_hCwClass⟩ := hProd
  have hPGrad : nativeMorreyHSClass (n:=n) (q:=q*q) ν P=hsUnitBallL2Class Dp hp.2.2 :=
    nativeMorreyHSClass_eq_of_native_map ν p Dp hp P hPMap
  have hBound : criticalGradientMorreySquare DW (ball (0:Domain n) 1)≤ENNReal.ofReal (2*MD+2*r^2) :=
    native_gradient_critical_bound_of_difference ν I hI P Q Dp DW hp.2.2 hW.2.2 hPGrad hWGrad
      r MD hr hMD hNorm hCritical
  have hGrowth := morreyCoefficient_power_growth (n:=n) (q:=q*q) ν DW hW.2.2 (D Q) hWGrad
  have hNat := original_natural_tests_of_ae Cw (field (Φ (X.val.val,t))) hFluxAE.symm hNatural
  exact ⟨W,DW,‖D Q‖^2,hW,hWSO.mono (fun _ hx=>hx.1),hWSO.mono (fun _ hx=>hx.2),hBound,hGrowth,hNat⟩

private theorem scalar_path_local_from_flux
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q))
    (hp : MemW12 (ballDomain (0 : Domain n) 1) p Dp)
    (P : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ))
    (hPMap : nativeMorreyMapClass (n:=n) (q:=q*q) ((n : ℝ)-2+γ) P=hp.2.1.toLp p)
    (hPSO : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (e (p x))*e (p x)=1 ∧ (e (p x)).det=1)
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q)) (τ : ℝ)
    (δ C η KA : ℝ) (hδ : 0<δ) (hC : 0<C)
    (hEnergy : 2*C*η^2+2*(δ/4)^2≤δ^2) :
    let ν := (n : ℝ)-2+γ
    let S := NativeMorreySobolevSpace n (q*q) ν
    let M := MorreyCoefficientSpace n (q*q) ν
    let V := SkewMeanZeroNativeMorreySpace n q ν e
    letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
    letI : SeminormedAddCommGroup V :=
      (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
    letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
    let T := bounded_scalar_path_set e A (C*η^2) (C*η^2) ν (C*KA) (C*KA)
    let E := e.symm.toContinuousLinearMap
    let R := e.toContinuousLinearMap
    let value : S→Domain n→Ambient (q*q) := fun H=>nativeMorreyMapClass (n:=n) (q:=q*q) ν H
    let field : M→Domain n→Gradient n (q*q) := fun F x i=>WithLp.toLp 2
      (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
    let D := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    let Exp := matrixNativeMorreyExp n hn γ hγ hγTwo q E R e.apply_symm_apply e.symm_apply_apply
    ∀(Z Y : M),
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
        field Z x i=e.symm (star (e (p x))*e (Dp x i)+star (e (p x))*(τ • A x i)*e (p x))) →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
        field Y x i=e.symm (star (e (p x))*A x i*e (p x))) →
      ∀(Φ : S×ℝ→M),
        (∀Q : S×ℝ,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),field (Φ Q) x=fun i=>e.symm
          (e (value (Exp (-Q.1)) x)*e (field (D (Exp Q.1)) x i)+
            (e (value (Exp (-Q.1)) x)*(e (field Z x i)+Q.2 • e (field Y x i)))*e (value (Exp Q.1) x))) →
        (∀Q : S×ℝ,AnalyticAt ℝ Φ Q) → Φ (0,0)=Z →
        criticalGradientMorreySquare Dp (ball (0:Domain n) 1)≤ENNReal.ofReal (C*η^2) →
        (∀U : Set (ℝ×V),U∈𝓝 (0:ℝ×V) →
          ∀ᶠt in 𝓝 (0:ℝ),∃u : V,(t,u)∈U ∧
            ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
              MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
              (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (field (Φ (u.val.val,t)) x i) (Dψ x i))=0) →
        (∀s∈Icc (0:ℝ) 1,
          ∀(w : Domain n→Ambient (q*q)) (Dw : Domain n→Gradient n (q*q)) (J : ℝ),
            MemW12 (ballDomain (0:Domain n) 1) w Dw →
            (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (e (w x))*e (w x)=1) →
            (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),(e (w x)).det=1) →
            criticalGradientMorreySquare Dw (ball (0:Domain n) 1)≤ENNReal.ofReal (δ^2) →
            (∀a∈ball (0:Domain n) 1,∀ρ : ℝ,0<ρ →
              (∫x in ball a ρ∩ball (0:Domain n) 1,hsNormSq (Dw x))≤J*ρ^ν) →
            (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
              MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
              (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ
                (e.symm (star (e (w x))*e (Dw x i)+star (e (w x))*(s • A x i)*e (w x))) (Dψ x i))=0) → s∈T) →
        ∀ᶠs in 𝓝 τ,s∈Icc (0:ℝ) 1 → s∈T
 := by
  intro ν S M V T E R value field D Exp Z Y hZ hY Φ hFormula hAnalytic hBase hCritical hSolutions hImprove
  let r : ℝ := δ/4
  have hr : 0<r := div_pos hδ (by norm_num)
  have hNeighborhood := exists_native_matrix_critical_perturbation_neighborhood n hn γ hγ hγTwo q e
    P Z Φ hAnalytic hBase
  let I := hNeighborhood.choose
  have hI := hNeighborhood.choose_spec
  have hUData := hI.2.2 r hr
  let U := hUData.choose
  have hU := hUData.choose_spec
  have hSmallSolutions := hSolutions U hU.1
  have hShift : Tendsto (fun s : ℝ=>s-τ) (𝓝 τ) (𝓝 (0:ℝ)) :=
    (continuous_id.sub continuous_const).tendsto' τ 0 (sub_self τ)
  filter_upwards [hShift.eventually hSmallSolutions] with s hs
  intro hsIcc
  obtain ⟨u,hu,hNat⟩ := hs
  have hControl := (hU.2 (s-τ,u) hu).1.le
  have hMD : 0≤C*η^2 := mul_nonneg hC.le (sq_nonneg η)
  have hCandidate := scalar_candidate_from_controlled_flux n hn γ hγ hγTwo q e
    p Dp hp P hPMap hPSO A τ Z Y hZ hY Φ hFormula u (s-τ) I hI.2.1
    r (C*η^2) hr.le hMD hControl hCritical hNat
  obtain ⟨w,Dw,J,hw,hOrth,hDet,hNewCritical,hGrowth,hNewNatural⟩ := hCandidate
  have hEnergy' : 2*(C*η^2)+2*r^2≤δ^2 := by simpa only [r,mul_assoc] using hEnergy
  have hSmall : criticalGradientMorreySquare Dw (ball (0:Domain n) 1)≤ENNReal.ofReal (δ^2) :=
    hNewCritical.trans (ENNReal.ofReal_le_ofReal hEnergy')
  have hTime : τ+(s-τ)=s := by ring
  apply hImprove s hsIcc w Dw J hw hOrth hDet hSmall hGrowth
  intro ψ Dψ hψ
  simpa only [hTime] using hNewNatural ψ Dψ hψ

private theorem exists_uniform_scalar_path_coverage
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,
      ‖e.symm T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) :
    ∃ε C : ℝ,0<ε ∧ 0<C ∧
      ∀(A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q)) (η KA : ℝ),
        (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
        (∀i,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (A x i)= -(A x i)) →
        0≤η → η≤ε →
        criticalGradientMorreySquare (fun x i=>e.symm (A x i)) (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
        (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
          (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>e.symm (A x i)))≤KA*r^((n:ℝ)-2+γ)) →
        ∀τ∈Icc (0:ℝ) 1,
          τ∈bounded_scalar_path_set e A (C*η^2) (C*η^2) ((n:ℝ)-2+γ) (C*KA) (C*KA) := by
  obtain ⟨δ,C,hδ,hC,hImprove⟩ := exists_scalar_path_frame_improvement n hn γ hγ hγTwo q e hE
  obtain ⟨εIFT,hεIFT,hBase⟩ := exists_original_scalar_baseline_flux n hn γ hγ hγTwo q e hE
  obtain ⟨ε,hε,hThreshold⟩ := exists_uniform_coulomb_perturbation_threshold δ εIFT C hδ hεIFT hC
  refine ⟨ε,C,hε,hC,?_⟩
  intro A η KA hA hAskew hη hSmall hCritical hGrowth
  let ν : ℝ := (n:ℝ)-2+γ
  let T := bounded_scalar_path_set e A (C*η^2) (C*η^2) ν (C*KA) (C*KA)
  have hKA : 0≤KA := original_growth_constant_nonneg ν KA (fun x i=>e.symm (A x i)) hGrowth
  have hM : 0≤C*η^2 := mul_nonneg hC.le (sq_nonneg η)
  have hK : 0≤C*KA := mul_nonneg hC.le hKA
  have hClosed : IsClosed T := bounded_scalar_path_set_closed e hE A hA hAskew
    (η^2) (C*η^2) (C*η^2) ν (C*KA) (C*KA) (sq_nonneg η) hM hM hK hK hCritical
  have hZero : (0:ℝ)∈T := bounded_scalar_path_set_zero e A (C*η^2) (C*η^2) ν (C*KA) (C*KA) hK hK
  apply scalar_interval_covered_of_closed_local T hClosed hZero
  intro τ _hτIcc hτ
  obtain ⟨_hIcc,p,Dp,hp,hOrth,hDet,hDCrit,hDGrow,hZCrit,hZGrow,hNatural⟩ := hτ
  have hBounds := hThreshold η hη hSmall
  have hZSmall := hBounds.2.2.2.2 _ hZCrit
  have hFluxData := hBase p Dp hp hOrth hDet A hA hAskew τ KA (C*KA) (C*KA)
    hGrowth hDGrow hZGrow ((1+C)*η) hBounds.1 hBounds.2.1 hZSmall hNatural
  obtain ⟨P,Z,Y,hPMap,_hPGrad,hZAE,hYAE,Φ,hFormula,hAnalytic,hBaseEq,hSolutions⟩ := hFluxData
  let V := SkewMeanZeroNativeMorreySpace n q ν e
  let field : MorreyCoefficientSpace n (q*q) ν→Domain n→Gradient n (q*q) := fun F x i=>WithLp.toLp 2
    (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
  have hSolNat : ∀U : Set (ℝ×V),U∈𝓝 (0:ℝ×V) →
      ∀ᶠt in 𝓝 (0:ℝ),∃u : V,(t,u)∈U ∧
        ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (field (Φ (u.val.val,t)) x i) (Dψ x i))=0 := by
    intro U hU
    filter_upwards [hSolutions U hU] with t ht
    obtain ⟨u,hu,_hResponse,hTests⟩ := ht
    exact ⟨u,hu,fun ψ Dψ hψ=>(hTests ψ Dψ hψ).2⟩
  have hPhi0 : Φ (0,0)=Z := by
    simpa only [zero_smul,add_zero] using hBaseEq 0
  have hPSO := hOrth.and hDet
  exact scalar_path_local_from_flux n hn γ hγ hγTwo q e p Dp hp P hPMap hPSO A τ δ C η KA
    hδ hC hBounds.2.2.1 Z Y
    (hZAE.mono fun x hx i=>congrFun hx i) (hYAE.mono fun x hx i=>congrFun hx i)
    Φ hFormula hAnalytic hPhi0 hDCrit hSolNat (hImprove A hA hAskew η KA hCritical hGrowth)

/-- Original small critical skew connections with finite stronger growth
have an actual native SO natural Coulomb frame with uniform bounds. -/
theorem exists_small_stronger_native_coulomb_frame
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,
      ‖e.symm T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) :
    ∃ε C : ℝ,0<ε ∧ 0<C ∧
      ∀(A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q)) (η KA : ℝ),
        (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
        (∀i,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (A x i)= -(A x i)) →
        0≤η → η≤ε →
        criticalGradientMorreySquare (fun x i=>e.symm (A x i)) (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
        (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
          (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>e.symm (A x i)))≤KA*r^((n:ℝ)-2+γ)) →
        ∃(p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) p Dp ∧
          (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (e (p x))*e (p x)=1) ∧
          (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),(e (p x)).det=1) ∧
          let Z := fun x i=>e.symm (star (e (p x))*e (Dp x i)+star (e (p x))*A x i*e (p x))
          (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0:Domain n) 1))) ∧
          (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,star (e (Z x i))= -(e (Z x i))) ∧
          (criticalGradientMorreySquare Dp (ball (0:Domain n) 1)+
            criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (C*η^2)) ∧
          (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
            ((∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Dp x))≤C*KA*r^((n:ℝ)-2+γ)) ∧
            ((∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Z x))≤C*KA*r^((n:ℝ)-2+γ))) ∧
          ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
            MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
            IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Z x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
            (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0
 := by
  obtain ⟨ε,C,hε,hC,H⟩ := exists_uniform_scalar_path_coverage n hn γ hγ hγTwo q e hE
  refine ⟨ε,2*C,hε,mul_pos (by norm_num) hC,?_⟩
  intro A η KA hA hAskew hη hSmall hCritical hGrowth
  have hCoverage := H A η KA hA hAskew hη hSmall hCritical hGrowth
  have hOne := hCoverage 1 (by norm_num)
  obtain ⟨_hIcc,p,Dp,hp,hOrth,hDet,hDCrit,hDGrow,hZCritOne,hZGrowOne,hNaturalOne⟩ := hOne
  let Z := fun x i=>e.symm (star (e (p x))*e (Dp x i)+star (e (p x))*A x i*e (p x))
  have hZCrit : criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (C*η^2) := by
    simpa only [one_smul] using hZCritOne
  have hKA : 0≤KA := original_growth_constant_nonneg ((n:ℝ)-2+γ) KA (fun x i=>e.symm (A x i)) hGrowth
  have hM : 0≤C*η^2 := mul_nonneg hC.le (sq_nonneg η)
  have hSum : criticalGradientMorreySquare Dp (ball (0:Domain n) 1)+
      criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal ((2*C)*η^2) := by
    calc
      _≤ENNReal.ofReal (C*η^2)+ENNReal.ofReal (C*η^2) := add_le_add hDCrit hZCrit
      _=ENNReal.ofReal ((2*C)*η^2) := by
        rw [←ENNReal.ofReal_add hM hM]
        congr 1
        ring
  have hRaw := frame_connection_memLp_and_skew e.symm.toContinuousLinearMap e.toContinuousLinearMap
    e.symm_apply_apply hE p Dp hp hOrth A hA hAskew
  have hZLp : ∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0:Domain n) 1)) := hRaw.2.1
  have hZSkew : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,star (e (Z x i))= -(e (Z x i)) := by
    filter_upwards [hRaw.2.2] with x hx
    intro i
    have hPoint : e (Z x i)=star (e (p x))*e (Dp x i)+star (e (p x))*A x i*e (p x) :=
      e.apply_symm_apply _
    rw [hPoint]
    exact hx i
  have hCoeff (r : ℝ) (hr : 0<r) : C*KA*r^((n:ℝ)-2+γ)≤(2*C)*KA*r^((n:ℝ)-2+γ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hC] : C≤2*C) hKA)
      (Real.rpow_nonneg hr.le _)
  refine ⟨p,Dp,hp,hOrth,hDet,hZLp,hZSkew,hSum,?_,?_⟩
  · intro a ha r hr
    have hZGrow : (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Z x))≤C*KA*r^((n:ℝ)-2+γ) := by
      simpa only [one_smul] using hZGrowOne a ha r hr
    exact ⟨(hDGrow a ha r hr).trans (hCoeff r hr),hZGrow.trans (hCoeff r hr)⟩
  · intro ψ Dψ hψ
    refine ⟨integrable_column_pairing (volume.restrict (ball (0:Domain n) 1)) Z Dψ hZLp hψ.2.2,?_⟩
    simpa only [one_smul] using hNaturalOne ψ Dψ hψ

end StationaryHarmonicMaps.Analysis
end
