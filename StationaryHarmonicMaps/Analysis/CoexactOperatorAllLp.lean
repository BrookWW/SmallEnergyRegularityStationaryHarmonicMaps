module

public import StationaryHarmonicMaps.Analysis.NeumannOperatorAllLp
public import StationaryHarmonicMaps.Analysis.RelativeCoexactPotential
public import StationaryHarmonicMaps.Analysis.ClosedNormalTensorNatural

/-!
# One actual relative coexact projection with all Lp bounds

The complement of the same native Neumann projection retains the original
input decomposition into a native gradient and an actual closed normal H1
tensor divergence, including every original coexact core pairing.
The response one-form has every Lp bound, with one operator before all
original inputs and exponents. No Lp estimate for the full derivative
tensor of the potential is asserted.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem norm_sub_rpow_le {m : ℕ} (v w : Ambient m) (p : ℝ) (hp : 0≤p) :
    ‖v-w‖^p≤(2 : ℝ)^p*(‖v‖^p+‖w‖^p) := by
  by_cases h : ‖v‖≤‖w‖
  · have hTwo : ‖v-w‖≤2*‖w‖ := (norm_sub_le v w).trans (by linarith only [h])
    calc
      _≤(2*‖w‖)^p := Real.rpow_le_rpow (norm_nonneg _) hTwo hp
      _=(2 : ℝ)^p*‖w‖^p := Real.mul_rpow (by norm_num) (norm_nonneg _)
      _≤_ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _))
        (Real.rpow_nonneg (by norm_num) _)
  · have hTwo : ‖v-w‖≤2*‖v‖ := (norm_sub_le v w).trans (by linarith only [not_le.mp h])
    calc
      _≤(2*‖v‖)^p := Real.rpow_le_rpow (norm_nonneg _) hTwo hp
      _=(2 : ℝ)^p*‖v‖^p := Real.mul_rpow (by norm_num) (norm_nonneg _)
      _≤_ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
        (Real.rpow_nonneg (by norm_num) _)

private theorem complement_projection_data {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H) (hSelfN : IsSelfAdjoint N) (hIdemN : ∀W,N (N W)=N W) :
    ‖(1-N : H →L[ℝ] H)‖≤1 ∧ IsSelfAdjoint (1-N : H →L[ℝ] H) ∧
      (∀W,(1-N : H →L[ℝ] H) ((1-N) W)=(1-N) W) ∧
      ∀W : H,‖(1-N : H →L[ℝ] H) W‖≤‖W‖ := by
  let T : H →L[ℝ] H := 1-N
  have hTApply (W : H) : T W=W-N W := rfl
  have hAdj : N.adjoint=N := by simpa only [IsSelfAdjoint,ContinuousLinearMap.star_eq_adjoint] using hSelfN
  have hPointNorm (W : H) : ‖T W‖≤‖W‖ := by
    have H := ContinuousLinearMap.adjoint_inner_right N W (N W)
    rw [hAdj,hIdemN,real_inner_self_eq_norm_sq] at H
    have hSquare : ‖T W‖^2≤‖W‖^2 := by
      rw [hTApply,norm_sub_sq_real,H]
      nlinarith only [sq_nonneg ‖N W‖]
    nlinarith only [hSquare,norm_nonneg (T W),norm_nonneg W]
  have hNormT : ‖T‖≤1 := T.opNorm_le_bound (by norm_num) fun W=>by
    simpa only [one_mul] using hPointNorm W
  have hSelfT : IsSelfAdjoint T := by
    change star (1-N)=1-N
    rw [star_sub,star_one]
    exact congrArg (fun z=>1-z) hSelfN
  have hIdemT (W : H) : T (T W)=T W := by
    simp only [hTApply,map_sub,hIdemN,sub_self,sub_zero]
  exact ⟨hNormT,hSelfT,hIdemT,hPointNorm⟩

private theorem difference_lp_moment_bound {X : Type*} [MeasurableSpace X] {m : ℕ}
    (μ : Measure X) (W P : Lp (Ambient m) 2 μ) (p : {p : ℝ //1<p}) (C : ℝ)
    (hW : MemLp (fun x=>W x) (ENNReal.ofReal p.val) μ)
    (hP : MemLp (fun x=>P x) (ENNReal.ofReal p.val) μ)
    (hMoment : (∫x,‖P x‖^p.val ∂μ)≤C*(∫x,‖W x‖^p.val ∂μ)) :
    MemLp (fun x=>(W-P) x) (ENNReal.ofReal p.val) μ ∧
      (∫x,‖(W-P) x‖^p.val ∂μ)≤((2 : ℝ)^p.val*(1+C))*(∫x,‖W x‖^p.val ∂μ) := by
  have hSub : (fun x=>(W-P) x)=ᵐ[μ](fun x=>W x-P x) := Lp.coeFn_sub W P
  have hDifference : MemLp (fun x=>W x-P x) (ENNReal.ofReal p.val) μ := hW.sub hP
  have hOut : MemLp (fun x=>(W-P) x) (ENNReal.ofReal p.val) μ := MemLp.ae_eq hSub.symm hDifference
  have hp0 : 0<p.val := zero_lt_one.trans p.property
  have hExponent : ENNReal.ofReal p.val≠0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hWI : Integrable (fun x=>‖W x‖^p.val) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hW.integrable_norm_rpow hExponent ENNReal.ofReal_ne_top
  have hPI : Integrable (fun x=>‖P x‖^p.val) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hP.integrable_norm_rpow hExponent ENNReal.ofReal_ne_top
  have hOI : Integrable (fun x=>‖(W-P) x‖^p.val) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hOut.integrable_norm_rpow hExponent ENNReal.ofReal_ne_top
  have hBound : ∀ᵐx∂μ,‖(W-P) x‖^p.val≤(2 : ℝ)^p.val*(‖W x‖^p.val+‖P x‖^p.val) := by
    filter_upwards [hSub] with x hx
    rw [hx]
    exact norm_sub_rpow_le (W x) (P x) p.val hp0.le
  refine ⟨hOut,?_⟩
  calc
    _≤∫x,(2 : ℝ)^p.val*(‖W x‖^p.val+‖P x‖^p.val) ∂μ :=
      integral_mono_ae hOI ((hWI.add hPI).const_mul _) hBound
    _=(2 : ℝ)^p.val*((∫x,‖W x‖^p.val ∂μ)+(∫x,‖P x‖^p.val ∂μ)) := by
      rw [integral_const_mul,integral_add hWI hPI]
    _≤(2 : ℝ)^p.val*((∫x,‖W x‖^p.val ∂μ)+C*(∫x,‖W x‖^p.val ∂μ)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hMoment) (Real.rpow_nonneg (by norm_num) _)
    _=_ := by ring

private theorem core_pairing_of_native_complement {n q : ℕ}
    (F P : Domain n → Gradient n q)
    (hF : ∀j,MemLp (fun x=>F x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hP : ∀j,MemLp (fun x=>P x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (u : Domain n → Ambient q)
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u (fun x i=>F x i-P x i))
    (C : Fin n → Fin n → Domain n → Ambient q)
    (hC : ∀i j,ContDiff ℝ ∞ (C i j)) (hSkew : ∀i j x,C i j x= -C j i x)
    (hNormal : ∀j (x : Domain n),‖x‖=1 → (∑i : Fin n,x i • C i j x)=0) :
    let μ := volume.restrict (ball (0 : Domain n) 1)
    let Z := fun x j=>∑i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)
    Integrable (fun x=>∑j : Fin n,inner ℝ (P x j) (Z x j)) μ ∧
    Integrable (fun x=>∑j : Fin n,inner ℝ (F x j) (Z x j)) μ ∧
    (∫x,∑j : Fin n,inner ℝ (P x j) (Z x j) ∂μ)=
      ∫x,∑j : Fin n,inner ℝ (F x j) (Z x j) ∂μ := by
  intro μ Z
  obtain ⟨hZ,hNatural⟩ := smooth_skew_normal_tensor_divergence_native_tests C hC hSkew hNormal
  have hPI : Integrable (fun x=>∑j : Fin n,inner ℝ (P x j) (Z x j)) μ :=
    integrable_finsetSum _ (fun j _=>HolderToCK.integrable_inner_of_memLp_two (hP j) (hZ j))
  have hFI : Integrable (fun x=>∑j : Fin n,inner ℝ (F x j) (Z x j)) μ :=
    integrable_finsetSum _ (fun j _=>HolderToCK.integrable_inner_of_memLp_two (hF j) (hZ j))
  have H := (hNatural u _ hu).2
  have hPoint (x : Domain n) : (∑j : Fin n,inner ℝ (Z x j) (F x j-P x j))=
      (∑j : Fin n,inner ℝ (F x j) (Z x j))-(∑j : Fin n,inner ℝ (P x j) (Z x j)) := by
    simp only [inner_sub_right,Finset.sum_sub_distrib]
    congr 1 <;> exact Finset.sum_congr rfl fun j _=>real_inner_comm _ _
  change (∫x,∑j : Fin n,inner ℝ (Z x j) (F x j-P x j) ∂μ)=0 at H
  rw [integral_congr_ae (Eventually.of_forall hPoint),integral_sub hFI hPI] at H
  exact ⟨hPI,hFI,(sub_eq_zero.mp H).symm⟩

/-- One actual relative coexact L2 projection has all Lp estimates for its same response one-form and internally constructs its exact native closed normal H1 potential. -/
theorem exists_same_coexact_operator_all_lp_unitBall (n : ℕ) (hn : 2≤n) :
    ∃ Cp : {p : ℝ //1<p} → ℝ,(∀p,0<Cp p) ∧ ∀q : ℕ,
      let μ := volume.restrict (ball (0 : Domain n) 1)
      let D := fun (W : Domain n → Ambient (n*q)) x i=>WithLp.toLp 2
        (fun j : Fin q=>W x (finProdFinEquiv (i,j)))
      ∃ T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
        ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀W,T (T W)=T W) ∧
        ∀W : Lp (Ambient (n*q)) 2 μ,
          ∃ (u : Domain n → Ambient q) (b : Fin n → Fin n → Domain n → Ambient q)
            (Db : Fin n → Fin n → Domain n → Gradient n q),
            MemW12 (ballDomain (0 : Domain n) 1) u (fun x i=>D W x i-D (T W) x i) ∧
            (∀i j,MemW12 (ballDomain (0 : Domain n) 1) (b i j) (Db i j)) ∧
            (∀ᵐx∂μ,∀i j,b i j x= -b j i x) ∧
            (∀ᵐx∂μ,∀i j k,Db i j x k+Db j k x i+Db k i x j=0) ∧
            (∀ᵐx∂μ,∀j,(∑i : Fin n,Db i j x i)=D (T W) x j) ∧
            (∀ (j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
              MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
              Integrable (fun x=>∑i : Fin n,inner ℝ (b i j x) (Dψ x i)) μ ∧
              Integrable (fun x=>inner ℝ (D (T W) x j) (ψ x)) μ ∧
              (∫x,∑i : Fin n,inner ℝ (b i j x) (Dψ x i) ∂μ)=
                -(∫x,inner ℝ (D (T W) x j) (ψ x) ∂μ)) ∧
            (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
              MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
              Integrable (fun x=>∑i : Fin n,inner ℝ (D (T W) x i) (Dψ x i)) μ ∧
              (∫x,∑i : Fin n,inner ℝ (D (T W) x i) (Dψ x i) ∂μ)=0) ∧
            ((∫x,∑j : Fin n,∑i : Fin n,‖b i j x‖^2 ∂μ)+
              (∫x,∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Db i j x k‖^2 ∂μ)≤
                (4*(2 : ℝ)^(n+1)+2*(n : ℝ)+2)*(∫x,hsNormSq (D (T W) x) ∂μ)) ∧
            ((∫x,hsNormSq (D (T W) x) ∂μ)≤∫x,hsNormSq (D W x) ∂μ) ∧
            (∀ C : Fin n → Fin n → Domain n → Ambient q,
              (∀i j,ContDiff ℝ ∞ (C i j)) → (∀i j x,C i j x= -C j i x) →
              (∀i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
                fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0) →
              (∀j (x : Domain n),‖x‖=1 → (∑i : Fin n,x i • C i j x)=0) →
              let Z := fun x j=>∑i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)
              Integrable (fun x=>∑j : Fin n,inner ℝ (D (T W) x j) (Z x j)) μ ∧
              Integrable (fun x=>∑j : Fin n,inner ℝ (D W x j) (Z x j)) μ ∧
              (∫x,∑j : Fin n,inner ℝ (D (T W) x j) (Z x j) ∂μ)=
                ∫x,∑j : Fin n,inner ℝ (D W x j) (Z x j) ∂μ) ∧
            ∀p : {p : ℝ //1<p},MemLp (fun x=>W x) (ENNReal.ofReal p.val) μ →
              MemLp (fun x=>(T W) x) (ENNReal.ofReal p.val) μ ∧
              (∫x,‖(T W) x‖^p.val ∂μ)≤Cp p*(∫x,‖W x‖^p.val ∂μ) := by
  obtain ⟨CN,hCN,HN⟩ := exists_same_neumann_operator_all_lp_unitBall n hn
  let Cp := fun p : {p : ℝ //1<p}=>(2 : ℝ)^p.val*(1+CN p)
  have hCp (p : {p : ℝ //1<p}) : 0<Cp p :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith only [hCN p])
  refine ⟨Cp,hCp,?_⟩
  intro q μ D
  obtain ⟨N,_hN,hSelfN,hIdemN,hResponse⟩ := HN q
  let T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ := 1-N
  have hTApply (W : Lp (Ambient (n*q)) 2 μ) : T W=W-N W := rfl
  obtain ⟨hNormT,hSelfT,hIdemT,hPointNorm⟩ := complement_projection_data N hSelfN hIdemN
  have hNorm (W : Lp (Ambient (n*q)) 2 μ) : ‖W‖^2=∫x,hsNormSq (D W x) ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    exact integral_congr_ae (Eventually.of_forall fun x=>by
      change inner ℝ (W x) (W x)=hsNormSq (D W x)
      rw [real_inner_self_eq_norm_sq]
      exact (hs_unflatten_hsNormSq (W x)).symm)
  refine ⟨T,hNormT,hSelfT,hIdemT,?_⟩
  intro W
  obtain ⟨u,hu,hTests,_hEquation,_hEnergyN,hLpN⟩ := hResponse W
  have hTW : (fun x=>(T W) x)=ᵐ[μ](fun x=>W x-(N W) x) := by
    rw [hTApply]
    exact Lp.coeFn_sub W (N W)
  have hDecoded : D (T W)=ᵐ[μ](fun x j=>D W x j-D (N W) x j) := by
    filter_upwards [hTW] with x hx
    funext j
    change WithLp.toLp 2 (fun a : Fin q=>(T W) x (finProdFinEquiv (j,a)))=D W x j-D (N W) x j
    ext a
    have H := congrArg (fun z : Ambient (n*q)=>z (finProdFinEquiv (j,a))) hx
    simpa only [PiLp.sub_apply] using H
  have hQLp (j : Fin n) : MemLp (fun x=>D (T W) x j) 2 μ :=
    memLp_hs_unflatten (T W) (Lp.memLp (T W)) j
  have hWLp (j : Fin n) : MemLp (fun x=>D W x j) 2 μ :=
    memLp_hs_unflatten W (Lp.memLp W) j
  have hComplement : D (N W)=ᵐ[μ](fun x i=>D W x i-D (T W) x i) := by
    filter_upwards [hDecoded] with x hx
    funext i
    rw [hx]
    change D (N W) x i=D W x i-(D W x i-D (N W) x i)
    abel
  have huComplement : MemW12 (ballDomain (0 : Domain n) 1) u (fun x i=>D W x i-D (T W) x i) :=
    hu.congr_ae (Eventually.of_forall fun _=>rfl) hComplement
  have hNatural (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
      Integrable (fun x=>∑i : Fin n,inner ℝ (D (T W) x i) (Dψ x i)) μ ∧
      (∫x,∑i : Fin n,inner ℝ (D (T W) x i) (Dψ x i) ∂μ)=0 := by
    obtain ⟨hNI,hWI,hEq⟩ := hTests ψ Dψ hψ
    have hPair : (fun x=>∑i : Fin n,inner ℝ (D (T W) x i) (Dψ x i))=ᵐ[μ]
        (fun x=>(∑i : Fin n,inner ℝ (D W x i) (Dψ x i))-
          ∑i : Fin n,inner ℝ (D (N W) x i) (Dψ x i)) := by
      filter_upwards [hDecoded] with x hx
      simp only [hx,inner_sub_left,Finset.sum_sub_distrib]
    refine ⟨(hWI.sub hNI).congr hPair.symm,?_⟩
    rw [integral_congr_ae hPair,integral_sub hWI hNI,← hEq,sub_self]
  obtain ⟨b,Db,hb,hSkew,hClosed,hDiv,hNormal,hH1⟩ :=
    exists_native_relative_coexact_potential_unitBall (by omega : 1≤n) (D (T W)) hQLp
      (fun ψ Dψ hψ=>(hNatural ψ Dψ hψ).2)
  have hEnergy : (∫x,hsNormSq (D (T W) x) ∂μ)≤∫x,hsNormSq (D W x) ∂μ := by
    rw [← hNorm (T W),← hNorm W]
    exact pow_le_pow_left₀ (norm_nonneg _) (hPointNorm W) 2
  refine ⟨u,b,Db,huComplement,hb,hSkew,hClosed,hDiv,hNormal,hNatural,hH1,hEnergy,?_,?_⟩
  · intro C hC hCS _hClosed hCN
    exact core_pairing_of_native_complement (D W) (D (T W)) hWLp hQLp u huComplement C hC hCS hCN
  · intro p hW
    obtain ⟨hNW,hMomentN⟩ := hLpN p hW
    have H := difference_lp_moment_bound μ W (N W) p (CN p) hW hNW hMomentN
    simpa only [hTApply,Cp] using H

end StationaryHarmonicMaps.Analysis

end
