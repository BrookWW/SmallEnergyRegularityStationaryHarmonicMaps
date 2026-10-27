/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.CoexactOperatorAllLp
public import StationaryHarmonicMaps.Analysis.NeumannFullPowerGrowth

/-!
# The same relative coexact projection has all Lp and power-growth bounds

The original input retains its native gradient complement and exact closed
normal H1 potential. The same response one-form has every finite Lp bound
above one and every nonnegative power-growth bound below dimension, on all
balls truncated by the unit ball. No estimate for the full derivative of
the tensor potential in Lp is asserted.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The same actual coexact one-form projection retains the original native
Hodge decomposition and has all Lp and full power-growth bounds. -/
theorem exists_same_coexact_operator_all_lp_and_power_growth_unitBall (n : ℕ) (hn : 2≤n) :
    ∃ (Cp : {p : ℝ //1<p} → ℝ) (Cm : {ν : ℝ //0≤ν ∧ ν<(n:ℝ)} → ℝ),
      (∀p,0<Cp p) ∧ (∀ν,0<Cm ν) ∧ ∀q : ℕ,
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
            (∀p : {p : ℝ //1<p},MemLp (fun x=>W x) (ENNReal.ofReal p.val) μ →
              MemLp (fun x=>(T W) x) (ENNReal.ofReal p.val) μ ∧
              (∫x,‖(T W) x‖^p.val ∂μ)≤Cp p*(∫x,‖W x‖^p.val ∂μ)) ∧
            (∀(ν : {ν : ℝ //0≤ν ∧ ν<(n:ℝ)}) (K : ℝ),0≤K →
              (∀a : Domain n,a∈ball (0:Domain n) 1 → ∀r : ℝ,0<r →
                (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (D W x))≤K*r^ν.val) →
              ∀a : Domain n,a∈ball (0:Domain n) 1 → ∀r : ℝ,0<r →
                (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (D (T W) x))≤Cm ν*K*r^ν.val) := by
  classical
  obtain ⟨Cp,hCp,HT⟩ := exists_same_coexact_operator_all_lp_unitBall n hn
  choose L hL Hgrowth using fun ν : {ν : ℝ //0≤ν ∧ ν<(n:ℝ)}=>
    exists_native_neumann_full_real_power_growth n hn ν.val ν.property.1 ν.property.2
  let Cm := fun ν : {ν : ℝ //0≤ν ∧ ν<(n:ℝ)}=>2*(1+L ν)
  have hCm (ν : {ν : ℝ //0≤ν ∧ ν<(n:ℝ)}) : 0<Cm ν := by
    dsimp only [Cm]
    exact mul_pos (by norm_num) (by linarith only [hL ν])
  refine ⟨Cp,Cm,hCp,hCm,?_⟩
  intro q μ D
  obtain ⟨T,hT,hSelf,hIdem,Hresponse⟩ := HT q
  refine ⟨T,hT,hSelf,hIdem,?_⟩
  intro W
  obtain ⟨u,b,Db,hu,hb,hSkew,hClosed,hDiv,hNormal,hNatural,hH1,hEnergy,hCore,hLp⟩ := Hresponse W
  refine ⟨u,b,Db,hu,hb,hSkew,hClosed,hDiv,hNormal,hNatural,hH1,hEnergy,hCore,hLp,?_⟩
  intro ν K hK hForcing
  have hF (i : Fin n) : MemLp (fun x=>D W x i) 2 μ := memLp_hs_unflatten W (Lp.memLp W) i
  have hP (i : Fin n) : MemLp (fun x=>D (T W) x i) 2 μ := memLp_hs_unflatten (T W) (Lp.memLp (T W)) i
  have hNat (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
      (hψ : MemW12 (ballDomain (0:Domain n) 1) ψ Dψ) :
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (D W x i-D (T W) x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (D W x i) (Dψ x i) := by
    have hFI : Integrable (fun x=>∑i : Fin n,inner ℝ (D W x i) (Dψ x i)) μ :=
      integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hF i) (hψ.2.2 i))
    obtain ⟨hPI,hZero⟩ := hNatural ψ Dψ hψ
    simp only [inner_sub_left,Finset.sum_sub_distrib]
    rw [integral_sub hFI hPI,hZero,sub_zero]
  have hDuGrowth := Hgrowth ν q u (fun x i=>D W x i-D (T W) x i) (D W) K hu hF hK hForcing hNat
  intro a ha r hr
  have hFIB : IntegrableOn (fun x=>hsNormSq (D W x)) (ball (0:Domain n) 1) volume :=
    integrable_hsNormSq_of_columns (D W) hF
  have hPIB : IntegrableOn (fun x=>hsNormSq (D (T W) x)) (ball (0:Domain n) 1) volume :=
    integrable_hsNormSq_of_columns (D (T W)) hP
  have hFI : IntegrableOn (fun x=>hsNormSq (D W x)) (ball a r∩ball (0:Domain n) 1) volume :=
    hFIB.mono_set inter_subset_right
  have hPI : IntegrableOn (fun x=>hsNormSq (D (T W) x)) (ball a r∩ball (0:Domain n) 1) volume :=
    hPIB.mono_set inter_subset_right
  have hDI := hu.integrable_hsNormSq.mono_set (inter_subset_right (s:=ball a r))
  have hPoint (x : Domain n) : hsNormSq (D (T W) x)≤
      2*hsNormSq (D W x)+2*hsNormSq (fun i=>D W x i-D (T W) x i) := by
    have H := HolderToCK.hsNormSq_add_le (D W x) (fun i=>-(D W x i-D (T W) x i))
    have hId : D W x+(fun i=>-(D W x i-D (T W) x i))=D (T W) x := by funext i;dsimp;abel
    rw [hId] at H
    simpa only [hsNormSq,Pi.neg_apply,norm_neg] using H
  calc
    _≤∫x in ball a r∩ball (0:Domain n) 1,
        2*hsNormSq (D W x)+2*hsNormSq (fun i=>D W x i-D (T W) x i) :=
      integral_mono hPI ((hFI.const_mul 2).add (hDI.const_mul 2)) hPoint
    _=2*(∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (D W x))+
        2*(∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>D W x i-D (T W) x i)) := by
      rw [integral_add (hFI.const_mul 2) (hDI.const_mul 2),integral_const_mul,integral_const_mul]
    _≤2*(K*r^ν.val)+2*(L ν*K*r^ν.val) := add_le_add
      (mul_le_mul_of_nonneg_left (hForcing a ha r hr) (by norm_num))
      (mul_le_mul_of_nonneg_left (hDuGrowth a ha r hr) (by norm_num))
    _=Cm ν*K*r^ν.val := by dsimp only [Cm];ring

@[expose] def effectiveCoexactPowerConstant (n : ℕ) : ℚ :=
  2 * (1 + effectiveNativeNeumannPowerConstant n)

theorem effectiveCoexactPowerConstant_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < effectiveCoexactPowerConstant n := by
  have H := effectiveNativeNeumannPowerConstant_pos n hn
  unfold effectiveCoexactPowerConstant
  positivity

/-- The same actual coexact one-form projection retains the original native
Hodge decomposition and has all Lp and full power-growth bounds. -/
theorem effective_same_coexact_operator_all_lp_and_power_growth_unitBall (n : ℕ) (hn : 2≤n) :
    ∃ Cp : {p : ℝ //1<p} → ℝ,
      (∀p,0<Cp p) ∧ ∀q : ℕ,
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
            (∀p : {p : ℝ //1<p},MemLp (fun x=>W x) (ENNReal.ofReal p.val) μ →
              MemLp (fun x=>(T W) x) (ENNReal.ofReal p.val) μ ∧
              (∫x,‖(T W) x‖^p.val ∂μ)≤Cp p*(∫x,‖W x‖^p.val ∂μ)) ∧
            (∀(ν : {ν : ℝ //0≤ν ∧ ν≤(n:ℝ)-1}) (K : ℝ),0≤K →
              (∀a : Domain n,a∈ball (0:Domain n) 1 → ∀r : ℝ,0<r →
                (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (D W x))≤K*r^ν.val) →
              ∀a : Domain n,a∈ball (0:Domain n) 1 → ∀r : ℝ,0<r →
                (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (D (T W) x))≤(effectiveCoexactPowerConstant n : ℝ)*K*r^ν.val) := by
  classical
  obtain ⟨Cp,hCp,HT⟩ := exists_same_coexact_operator_all_lp_unitBall n hn
  refine ⟨Cp,hCp,?_⟩
  intro q μ D
  obtain ⟨T,hT,hSelf,hIdem,Hresponse⟩ := HT q
  refine ⟨T,hT,hSelf,hIdem,?_⟩
  intro W
  obtain ⟨u,b,Db,hu,hb,hSkew,hClosed,hDiv,hNormal,hNatural,hH1,hEnergy,hCore,hLp⟩ := Hresponse W
  refine ⟨u,b,Db,hu,hb,hSkew,hClosed,hDiv,hNormal,hNatural,hH1,hEnergy,hCore,hLp,?_⟩
  intro ν K hK hForcing
  have hF (i : Fin n) : MemLp (fun x=>D W x i) 2 μ := memLp_hs_unflatten W (Lp.memLp W) i
  have hP (i : Fin n) : MemLp (fun x=>D (T W) x i) 2 μ := memLp_hs_unflatten (T W) (Lp.memLp (T W)) i
  have hNat (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
      (hψ : MemW12 (ballDomain (0:Domain n) 1) ψ Dψ) :
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (D W x i-D (T W) x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (D W x i) (Dψ x i) := by
    have hFI : Integrable (fun x=>∑i : Fin n,inner ℝ (D W x i) (Dψ x i)) μ :=
      integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hF i) (hψ.2.2 i))
    obtain ⟨hPI,hZero⟩ := hNatural ψ Dψ hψ
    simp only [inner_sub_left,Finset.sum_sub_distrib]
    rw [integral_sub hFI hPI,hZero,sub_zero]
  have hDuGrowth := effective_native_neumann_full_power_growth_of_exponent_le n hn ν.val ν.property.1 ν.property.2 q u (fun x i=>D W x i-D (T W) x i) (D W) K hu hF hK hForcing hNat
  intro a ha r hr
  have hFIB : IntegrableOn (fun x=>hsNormSq (D W x)) (ball (0:Domain n) 1) volume :=
    integrable_hsNormSq_of_columns (D W) hF
  have hPIB : IntegrableOn (fun x=>hsNormSq (D (T W) x)) (ball (0:Domain n) 1) volume :=
    integrable_hsNormSq_of_columns (D (T W)) hP
  have hFI : IntegrableOn (fun x=>hsNormSq (D W x)) (ball a r∩ball (0:Domain n) 1) volume :=
    hFIB.mono_set inter_subset_right
  have hPI : IntegrableOn (fun x=>hsNormSq (D (T W) x)) (ball a r∩ball (0:Domain n) 1) volume :=
    hPIB.mono_set inter_subset_right
  have hDI := hu.integrable_hsNormSq.mono_set (inter_subset_right (s:=ball a r))
  have hPoint (x : Domain n) : hsNormSq (D (T W) x)≤
      2*hsNormSq (D W x)+2*hsNormSq (fun i=>D W x i-D (T W) x i) := by
    have H := HolderToCK.hsNormSq_add_le (D W x) (fun i=>-(D W x i-D (T W) x i))
    have hId : D W x+(fun i=>-(D W x i-D (T W) x i))=D (T W) x := by funext i;dsimp;abel
    rw [hId] at H
    simpa only [hsNormSq,Pi.neg_apply,norm_neg] using H
  calc
    _≤∫x in ball a r∩ball (0:Domain n) 1,
        2*hsNormSq (D W x)+2*hsNormSq (fun i=>D W x i-D (T W) x i) :=
      integral_mono hPI ((hFI.const_mul 2).add (hDI.const_mul 2)) hPoint
    _=2*(∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (D W x))+
        2*(∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>D W x i-D (T W) x i)) := by
      rw [integral_add (hFI.const_mul 2) (hDI.const_mul 2),integral_const_mul,integral_const_mul]
    _≤2*(K*r^ν.val)+2*((effectiveNativeNeumannPowerConstant n : ℝ)*K*r^ν.val) := add_le_add
      (mul_le_mul_of_nonneg_left (hForcing a ha r hr) (by norm_num))
      (mul_le_mul_of_nonneg_left (hDuGrowth a ha r hr) (by norm_num))
    _=(effectiveCoexactPowerConstant n : ℝ)*K*r^ν.val := by
      simp only [effectiveCoexactPowerConstant, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_add, Rat.cast_one]
      ring

end StationaryHarmonicMaps.Analysis

end
