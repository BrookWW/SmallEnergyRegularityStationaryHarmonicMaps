module

public import StationaryHarmonicMaps.Analysis.ClosedNormalTensorSpace
public import StationaryHarmonicMaps.Analysis.ClosedNormalTensorLimitEnergy
public import StationaryHarmonicMaps.Analysis.ClosedNormalTensorNatural
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtDecoding
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Actual native closed normal coexact projection

A raw L2 one-form is genuinely projected onto the closed Hilbert range of
smooth closed normal tensor divergences. Actual range approximants and
coercivity recover a native H1 potential with the original weak normal
boundary identity, energy bounds and actual variational tests. No image
surjectivity or full Hodge decomposition is assumed.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Every original raw L2 one-form has a genuine native closed normal tensor projection, with actual potentials, weak boundary, full-HS energy bounds and all smooth core variational tests produced. -/
theorem exists_closed_normal_tensor_projection_unitBall {n q : ℕ}
    (F : Domain n → Gradient n q)
    (hF : ∀ j,MemLp (fun x=>F x j) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    ∃ (b : Fin n → Fin n → Domain n → Ambient q)
      (Db : Fin n → Fin n → Domain n → Gradient n q) (P : Domain n → Gradient n q),
      (∀ i j,MemW12 (ballDomain (0 : Domain n) 1) (b i j) (Db i j)) ∧
      (∀ j,MemLp (fun x=>P x j) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ i j,b i j x = -b j i x) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ i j k,Db i j x k+Db j k x i+Db k i x j=0) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ j,(∑ i : Fin n,Db i j x i)=P x j) ∧
      (∀ (j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑ i : Fin n,inner ℝ (b i j x) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
        IntegrableOn (fun x=>inner ℝ (P x j) (ψ x)) (ball (0 : Domain n) 1) volume ∧
        (∫ x in ball (0 : Domain n) 1,∑ i : Fin n,inner ℝ (b i j x) (Dψ x i)) =
          -(∫ x in ball (0 : Domain n) 1,inner ℝ (P x j) (ψ x))) ∧
      (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑ j : Fin n,inner ℝ (P x j) (Dψ x j)) (ball (0 : Domain n) 1) volume ∧
        (∫ x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (P x j) (Dψ x j))=0) ∧
      (IntegrableOn (fun x=>∑ j : Fin n,inner ℝ (F x j) (P x j)) (ball (0 : Domain n) 1) volume ∧
        (∫ x in ball (0 : Domain n) 1,hsNormSq (P x)) =
          (∫ x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (F x j) (P x j))) ∧
      ((∫ x in ball (0 : Domain n) 1,hsNormSq (P x)) ≤ ∫ x in ball (0 : Domain n) 1,hsNormSq (F x)) ∧
      ((∫ x in ball (0 : Domain n) 1,∑ j : Fin n,∑ i : Fin n,‖b i j x‖^2)+
        (∫ x in ball (0 : Domain n) 1,∑ j : Fin n,∑ k : Fin n,∑ i : Fin n,‖Db i j x k‖^2) ≤
        (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)*(∫ x in ball (0 : Domain n) 1,hsNormSq (F x))) ∧
      ∀ C : Fin n → Fin n → Domain n → Ambient q,
        (∀ i j,ContDiff ℝ ∞ (C i j)) →
        (∀ i j x,C i j x = -C j i x) →
        (∀ i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
          fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0) →
        (∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • C i j x)=0) →
        IntegrableOn (fun x=>∑ j : Fin n,inner ℝ (P x j)
          (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1))) (ball (0 : Domain n) 1) volume ∧
        IntegrableOn (fun x=>∑ j : Fin n,inner ℝ (F x j)
          (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1))) (ball (0 : Domain n) 1) volume ∧
        (∫ x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (P x j)
          (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1))) =
        ∫ x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (F x j)
          (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)) := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let E : Gradient n q → Ambient (n*q) := fun A=>WithLp.toLp 2
    (fun k=>A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  obtain ⟨S,hS⟩ := exists_smooth_closed_normal_divergence_submodule_unitBall n q
  let A : Lp (Ambient (n*q)) 2 μ := (memLp_hs_flatten F hF).toLp (fun x=>E (F x))
  let Z : Lp (Ambient (n*q)) 2 μ := S.topologicalClosure.starProjection A
  have hA : (A : Domain n → Ambient (n*q)) =ᵐ[μ] (fun x=>E (F x)) :=
    (memLp_hs_flatten F hF).coeFn_toLp
  have hZmem : Z∈S.topologicalClosure := S.topologicalClosure.starProjection_apply_mem A
  have hSeq : ∃ V : ℕ → Lp (Ambient (n*q)) 2 μ,(∀ s,V s∈S) ∧ Tendsto V atTop (𝓝 Z) := by
    apply mem_closure_iff_seq_limit.mp
    rw [← Submodule.topologicalClosure_coe]
    exact hZmem
  obtain ⟨V,hV,hVConv⟩ := hSeq
  choose B hB hSkew hClosed hNormal hRep using (fun s=>(hS (V s)).mp (hV s))
  let P := fun (x : Domain n) (j : Fin n)=>WithLp.toLp 2
    (fun a : Fin q=>Z x (finProdFinEquiv (j,a)))
  have hP (j : Fin n) : MemLp (fun x=>P x j) 2 μ := memLp_hs_unflatten Z (Lp.memLp Z) j
  have hEncConv : Tendsto (fun s=>eLpNorm (fun x=>E (fun j=>∑ i : Fin n,
      fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))-Z x) 2 μ) atTop (𝓝 0) := by
    have H := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' V Z).mp hVConv
    apply H.congr
    intro s
    apply eLpNorm_congr_ae
    filter_upwards [hRep s] with x hx
    change V s x-Z x=E (fun j=>∑ i : Fin n,fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))-Z x
    rw [hx]
  have hConv (j : Fin n) : Tendsto (fun s=>eLpNorm (fun x=>(∑ i : Fin n,
      fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))-P x j) 2 μ) atTop (𝓝 0) := by
    have H := hs_unflatten_column_l2_limit hEncConv j
    apply H.congr
    intro s
    apply eLpNorm_congr_ae
    exact Eventually.of_forall (fun x=>by
      change (WithLp.toLp 2 (fun a : Fin q=>(E (fun j=>∑ i : Fin n,
        fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))) (finProdFinEquiv (j,a))))-P x j =
          (∑ i : Fin n,fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))-P x j
      congr 1
      exact congrFun (hs_unflatten_flatten (fun j=>∑ i : Fin n,
        fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))) j)
  obtain ⟨b,Db,hb,hMap,hGrad,hs,hc,hd,hn⟩ :=
    exists_closed_normal_native_tensor_of_divergence_strong_limit B hB hSkew hClosed hNormal P hP hConv
  have hNorm (W : Lp (Ambient (n*q)) 2 μ) : ‖W‖^2=∫ x,‖W x‖^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    exact integral_congr_ae (Eventually.of_forall (fun x=>real_inner_self_eq_norm_sq (W x)))
  have hANorm : ‖A‖^2=∫ x,hsNormSq (F x) ∂μ := by
    rw [hNorm]
    apply integral_congr_ae
    filter_upwards [hA] with x hx
    rw [hx]
    exact hs_flatten_norm_sq (F x)
  have hEnergy : (∫ x,hsNormSq (P x) ∂μ) ≤ ∫ x,hsNormSq (F x) ∂μ := by
    calc
      _ = ∫ x,‖Z x‖^2 ∂μ := integral_congr_ae
        (Eventually.of_forall (fun x=>hs_unflatten_hsNormSq (Z x)))
      _ = ‖Z‖^2 := (hNorm Z).symm
      _ ≤ ‖A‖^2 := pow_le_pow_left₀ (norm_nonneg _) (S.topologicalClosure.norm_starProjection_apply_le A) 2
      _ = _ := hANorm
  have hFPInt : Integrable (fun x=>∑ j : Fin n,inner ℝ (F x j) (P x j)) μ :=
    integrable_finsetSum _ (fun j _=>HolderToCK.integrable_inner_of_memLp_two (hF j) (hP j))
  have hFPIdentity : (∫ x,hsNormSq (P x) ∂μ)=∫ x,∑ j : Fin n,inner ℝ (F x j) (P x j) ∂μ := by
    have hSelf := S.topologicalClosure.starProjection_inner_eq_zero A Z hZmem
    change inner ℝ (A-Z) Z=0 at hSelf
    rw [inner_sub_left] at hSelf
    have hEq : inner ℝ A Z=inner ℝ Z Z := sub_eq_zero.mp hSelf
    calc
      _ = ∫ x,‖Z x‖^2 ∂μ := integral_congr_ae
        (Eventually.of_forall (fun x=>hs_unflatten_hsNormSq (Z x)))
      _ = ‖Z‖^2 := (hNorm Z).symm
      _ = inner ℝ Z Z := (real_inner_self_eq_norm_sq Z).symm
      _ = inner ℝ A Z := hEq.symm
      _ = _ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hA] with x hx
        change inner ℝ (A x) (Z x)=_
        have hEnc : E (P x)=Z x := hs_flatten_unflatten (Z x)
        rw [hx,← hEnc]
        exact hs_flatten_inner (F x) (P x)
  have hBEnergy := (closed_normal_tensor_strong_limit_energy_bound
    B hB hSkew hClosed hNormal b Db hb hMap hGrad P hP hConv).2.2.2
  have hBControl : (∫ x,∑ j : Fin n,∑ i : Fin n,‖b i j x‖^2 ∂μ)+
      (∫ x,∑ j : Fin n,∑ k : Fin n,∑ i : Fin n,‖Db i j x k‖^2 ∂μ) ≤
        (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)*(∫ x,hsNormSq (F x) ∂μ) :=
    hBEnergy.trans (mul_le_mul_of_nonneg_left hEnergy (by positivity))
  have hNatural := skew_normal_tensor_divergence_limit_native_tests B hB hSkew hNormal P hP hConv
  refine ⟨b,Db,P,hb,hP,hs,hc,hd,hn,hNatural,⟨hFPInt,hFPIdentity⟩,hEnergy,hBControl,?_⟩
  intro C hC hCS hCD hCN
  let dC := fun (x : Domain n) (j : Fin n)=>∑ i : Fin n,
    fderiv ℝ (C i j) x (EuclideanSpace.single i 1)
  have hCLp (j : Fin n) : MemLp (fun x=>dC x j) 2 μ := memLp_finsetSum _ (fun i _=>
    (memW12_ball_of_ambient_c1 (0 : Domain n) 1 _ ((hC i j).of_le (by simp))).2.2 i)
  have hEC : MemLp (fun x=>E (dC x)) 2 μ := memLp_hs_flatten dC hCLp
  let W : Lp (Ambient (n*q)) 2 μ := hEC.toLp (fun x=>E (dC x))
  have hW : (W : Domain n → Ambient (n*q)) =ᵐ[μ] (fun x=>E (dC x)) := hEC.coeFn_toLp
  have hWmem : W∈S := (hS W).mpr ⟨C,hC,hCS,hCD,hCN,hW⟩
  have hOrth : inner ℝ Z W=inner ℝ A W := by
    have H := S.topologicalClosure.starProjection_inner_eq_zero A W (S.le_topologicalClosure hWmem)
    change inner ℝ (A-Z) W=0 at H
    rw [inner_sub_left] at H
    exact (sub_eq_zero.mp H).symm
  have hPI : Integrable (fun x=>∑ j : Fin n,inner ℝ (P x j) (dC x j)) μ :=
    integrable_finsetSum _ (fun j _=>HolderToCK.integrable_inner_of_memLp_two (hP j) (hCLp j))
  have hFI : Integrable (fun x=>∑ j : Fin n,inner ℝ (F x j) (dC x j)) μ :=
    integrable_finsetSum _ (fun j _=>HolderToCK.integrable_inner_of_memLp_two (hF j) (hCLp j))
  have hZW : inner ℝ Z W=∫ x,∑ j : Fin n,inner ℝ (P x j) (dC x j) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hW] with x hx
    change inner ℝ (Z x) (W x)=_
    have hEnc : E (P x)=Z x := hs_flatten_unflatten (Z x)
    rw [hx,← hEnc]
    exact hs_flatten_inner (P x) (dC x)
  have hAW : inner ℝ A W=∫ x,∑ j : Fin n,inner ℝ (F x j) (dC x j) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hA,hW] with x ha hw
    change inner ℝ (A x) (W x)=_
    rw [ha,hw]
    exact hs_flatten_inner (F x) (dC x)
  exact ⟨hPI,hFI,hZW.symm.trans (hOrth.trans hAW)⟩

end StationaryHarmonicMaps.Analysis

end
