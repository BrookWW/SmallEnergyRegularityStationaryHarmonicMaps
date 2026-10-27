module

public import StationaryHarmonicMaps.Analysis.SystemCutoffDirichletResponse
public import StationaryHarmonicMaps.Analysis.SystemCoexactCompensation
public import StationaryHarmonicMaps.Analysis.RelativeHodgeDecompositionBall
public import StationaryHarmonicMaps.Analysis.HodgeDirichletUniqueness

/-!
# Compensated estimates for one same actual full Hodge decomposition

Raw transformed cutoff data produce one full relative Hodge decomposition.
Native Dirichlet uniqueness transfers the constructed projection estimate
onto its same f. The actual native gradient complement lets the coexact
estimate act directly on its same Q. Its original harmonic remainder and
exact energy identity are retained.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Original compact-target system data and a given critical native
Coulomb frame produce one actual Hodge decomposition whose same exact
and coexact fields satisfy both compensated bounds. -/
theorem exists_compact_target_same_compensated_hodge_fields
    (n : ℕ) (hn : 2≤n) (p : ℝ) (hpOne : 1<p) (hpTwo : p<2)
    (hpConj : (n : ℝ)<p/(p-1)) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (δ A B L : ℝ) (hδ : 0<δ) (hδOne : δ<1) (hA : 0≤A) (hB : 0≤B) (hL : 0≤L) :
    ∃C : ℝ,0<C ∧ ∀(N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),u x∈N.carrierSet) → 0≤η → η≤1 →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀(P : Domain n → Ambient (q*q)) (DP : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) P DP →
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (P x))*R (P x)=1) →
        criticalGradientMorreySquare DP (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
        ∀Ω : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
          (∀i,MemLp (fun x=>Ω x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) Du (fun x=>-(∑i : Fin n,Ω x i (Du x i))) →
          let Z := fun x i=>star (R (P x))*R (DP x i)+star (R (P x))*Ω x i*R (P x)
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) (fun x i=>E (Z x i)) (fun _=>0) →
          criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
          ∀χ : Domain n → ℝ,ContDiff ℝ ∞ χ → HasCompactSupport χ →
            tsupport χ⊆closedBall (0 : Domain n) (3/4 : ℝ) →
            (∀x,|χ x|≤A) → (∀(x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) →
            (∀x,|Laplacian.laplacian χ x|≤L) →
            let c := ⨍y in ball (0 : Domain n) 1,u y
            let v := fun x=>χ x • (u x-c)
            let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
            let Fv := fun x i=>star (R (P x)) (Dv x i)
            let Φ := fun (x : Domain n) (r : ℝ)=>r^(p-(n : ℝ))*∫y in ball x r,(Real.sqrt (hsNormSq (Dv y)))^p
            let Ψ := fun t : ℝ=>sSup {z : ℝ | ∃x r,0<r ∧ r≤t ∧ z=Φ x r}
            MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv ∧
            ∀(a : Domain n) (t : ℝ),0<t → t≤1/128 → closedBall a (t/2)⊆ball (0 : Domain n) 1 →
              ∃(f : Domain n → Ambient q) (Df Q h : Domain n → Gradient n q) (g : Domain n → Ambient q),
                HasZeroBoundaryValues (ballDomain a (t/2)) f Df ∧
                MemW12 (ballDomain a (t/2)) g h ∧
                (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball a (t/2)))) ∧
                (∀ᵐx∂volume.restrict (ball a (t/2)),∀i,Fv x i=Df x i+Q x i+h x i) ∧
                (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
                  MemW12 (ballDomain a (t/2)) ψ Dψ →
                  (∫x in ball a (t/2),∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) ∧
                HolderToCK.WeakPoissonOn (ballDomain a (t/2)) h (fun _=>0) ∧
                (∀(i : Fin n) (ψ : Domain n → Ambient q),ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
                  tsupport ψ⊆ball a (t/2) →
                  (∫x in ball a (t/2),inner ℝ (h x i) (Laplacian.laplacian ψ x))=0) ∧
                IntegrableOn (fun x=>(hsNormSq (Df x))^(p/2)) (ball a (t/2)) volume ∧
                IntegrableOn (fun x=>(hsNormSq (Q x))^(p/2)) (ball a (t/2)) volume ∧
                ((∫x in ball a (t/2),(hsNormSq (Df x))^(p/2))^(1/p)≤
                  C*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+C*η*t^((n : ℝ)/p-δ)) ∧
                ((∫x in ball a (t/2),(hsNormSq (Q x))^(p/2))^(1/p)≤
                  C*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)) ∧
                ((∫x in ball a (t/2),hsNormSq (Df x))+(∫x in ball a (t/2),hsNormSq (Q x))+
                  (∫x in ball a (t/2),hsNormSq (h x))=∫x in ball a (t/2),hsNormSq (Fv x)) := by
  obtain ⟨D,hD,HDir⟩ := exists_compact_target_cutoff_dirichlet_compensated_response
    n hn p hpOne hpTwo hpConj q E R hRE hER hE δ A B L hδ hδOne hA hB hL
  obtain ⟨K,hK,HCoexact⟩ := exists_same_system_coexact_compensated_bound n hn p hpOne hpTwo q E R hER hE
  let C := 1+D+K
  have hC : 0<C := by dsimp only [C];linarith only [hD,hK]
  have hDC : D≤C := by dsimp only [C];linarith only [hK]
  have hKC : K≤C := by dsimp only [C];linarith only [hD]
  refine ⟨C,hC,?_⟩
  intro N u Du η hu hTarget hη hηOne hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
    χ hχ hcχ hsχ hχA hDχ hLap c v Dv Fv Φ Ψ
  obtain ⟨hV,HQuery⟩ := HDir N u Du η hu hTarget hη hηOne hCritical P DP hP hOrth hDPCritical
    Ω hΩ hEq hDiv hZCritical χ hχ hcχ hsχ hχA hDχ hLap
  refine ⟨hV,?_⟩
  intro a t ht htCap hClosed
  let r := t/2
  have hr : 0<r := half_pos ht
  let μ := volume.restrict (ball a r)
  have hSub : ball a r⊆ball (0 : Domain n) 1 := ball_subset_closedBall.trans hClosed
  let Λ : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q) :=
    (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).toContinuousLinearMap.comp R
  have hΛ (z : Ambient (q*q)) : Λ z=star (R z) := rfl
  have hPBound : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖P x‖≤Real.sqrt (q : ℝ) :=
    ae_orthogonal_coordinates_bound (Ω:=ballDomain (0 : Domain n) 1) E R hER hE P hOrth
  have hVParent : MemW12 (ballDomain (0 : Domain n) 1) v Dv := memW12_of_openDomain_subset hV (subset_univ _)
  have hF (i : Fin n) : MemLp (fun x=>Fv x i) 2 μ := by
    have H := (memLp_bounded_native_frame_columns (ballDomain (0 : Domain n) 1) P DP hP
      (Real.sqrt (q : ℝ)) hPBound Λ Dv hVParent.2.2 i).mono_measure
      (Measure.restrict_mono_set volume hSub)
    simpa only [hΛ] using H
  obtain ⟨f,Df,b,Db,Q,h,g,hf,hg,_hgMean,_hb,hQ,_hSkew,_hClosedB,_hDivB,_hNormal,hNatural,
    hDecomp,hHDiv,hHarm,_hFE,_hQE,_hBE,hFG,hProjection,_hPair,hPyth,_hHE⟩ :=
    exists_L2_relative_hodge_decomposition_ball hn a r hr Fv hF
  obtain ⟨f₀,Df₀,hf₀,_hEq₀,_hEnergy₀,hPI₀,hBound₀,hProjection₀⟩ := HQuery a t ht htCap hClosed
  have hTest (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
      (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆ball a r) :
      HasZeroBoundaryValues (ballDomain a r) ψ
        (fun x i=>fderiv ℝ ψ x (EuclideanSpace.single i 1)) :=
    (memW12_ball_of_ambient_c1 a r ψ (hψ.of_le (by simp))).zeroBoundary_of_compactSupport_ball hr hc hs
  have hUnique := dirichlet_gradient_response_unique_ae (by omega : 1≤n) a hr Fv hF hf hf₀
    (fun ψ hψ hc hs=>(hProjection ψ _ (hTest ψ hψ hc hs)).2.2)
    (fun ψ hψ hc hs=>hProjection₀ ψ _ (hTest ψ hψ hc hs))
  have hDensity : (fun x=>(hsNormSq (Df x))^(p/2))=ᵐ[μ](fun x=>(hsNormSq (Df₀ x))^(p/2)) :=
    hUnique.2.mono fun x hx=>by
      change (hsNormSq (Df x))^(p/2)=(hsNormSq (Df₀ x))^(p/2)
      rw [hx]
  have hPI : Integrable (fun x=>(hsNormSq (Df x))^(p/2)) μ := hPI₀.congr hDensity.symm
  have hDfBound : (∫x,(hsNormSq (Df x))^(p/2) ∂μ)^(1/p)≤
      D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+D*η*t^((n : ℝ)/p-δ) := by
    rw [integral_congr_ae hDensity]
    exact hBound₀
  have hComplement : ∀ᵐx∂μ,∀i,star (R (P x)) (Dv x i)=(Df x i+h x i)+Q x i := by
    filter_upwards [hDecomp] with x hx i
    change Fv x i=(Df x i+h x i)+Q x i
    rw [hx i]
    abel_nf
  obtain ⟨_hVZero,hQI,hQBound⟩ := HCoexact A B hA hB N u Du η hu hTarget hη hCritical χ hχ hcχ hsχ hχA hDχ
    P DP η hP hη hOrth hDPCritical a t ht htCap hSub Q (f+g) (fun x i=>Df x i+h x i) hFG hQ
    (fun ψ Dψ hψ=>(hNatural ψ Dψ hψ).2) hComplement
  obtain ⟨_hV',hPsi,_hGrowth⟩ := cutoff_capped_envelope_lp_growth n hn p hpOne.le hpTwo.le A B hA hB
    q u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ t ht htCap
  have hPsiPower : 0≤(Ψ (8*t))^(1/p) := Real.rpow_nonneg hPsi _
  have hDfFinal : (∫x,(hsNormSq (Df x))^(p/2) ∂μ)^(1/p)≤
      C*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+C*η*t^((n : ℝ)/p-δ) := hDfBound.trans (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC hη)
      (Real.rpow_nonneg ht.le _)) hPsiPower)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC hη) (Real.rpow_nonneg ht.le _)))
  have hQFinal : (∫x,(hsNormSq (Q x))^(p/2) ∂μ)^(1/p)≤C*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p) :=
    hQBound.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC hη)
      (Real.rpow_nonneg ht.le _)) hPsiPower)
  exact ⟨f,Df,Q,h,g,hf,hg,hQ,hDecomp,(fun ψ Dψ hψ=>(hNatural ψ Dψ hψ).2),hHDiv,
    (fun i ψ hψ hc hs=>(hHarm i ψ hψ hc hs).2),hPI,hQI,hDfFinal,hQFinal,hPyth⟩

@[expose] def effectiveSystemCompensatedHodgeConstant (n q B L : ℕ) : ℚ :=
  1+effectiveSystemCutoffDirichletConstant n q B L+(effectiveSystemCoexactConstant n : ℚ)

theorem effective_compact_target_same_compensated_hodge_fields
    (n : ℕ) (hn : 2≤n) (p : ℝ) (hpOne : 1<p) (hpTwo : p<2)
    (hpConj : (n : ℝ)<p/(p-1)) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (A : ℝ) (B L : ℕ) (hA : 0≤A)
    (hConjugate : p/(p-1)=((2*n+1 : ℕ) : ℝ)) :
    ∃C : ℝ,0<C ∧ C = (effectiveSystemCompensatedHodgeConstant n q B L : ℝ) ∧ ∀(N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),u x∈N.carrierSet) → 0≤η → η≤1 →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀(P : Domain n → Ambient (q*q)) (DP : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) P DP →
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (P x))*R (P x)=1) →
        criticalGradientMorreySquare DP (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
        ∀Ω : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
          (∀i,MemLp (fun x=>Ω x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) Du (fun x=>-(∑i : Fin n,Ω x i (Du x i))) →
          let Z := fun x i=>star (R (P x))*R (DP x i)+star (R (P x))*Ω x i*R (P x)
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) (fun x i=>E (Z x i)) (fun _=>0) →
          criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
          ∀χ : Domain n → ℝ,ContDiff ℝ ∞ χ → HasCompactSupport χ →
            tsupport χ⊆closedBall (0 : Domain n) (3/4 : ℝ) →
            (∀x,|χ x|≤A) → (∀(x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) →
            (∀x,|Laplacian.laplacian χ x|≤L) →
            let c := ⨍y in ball (0 : Domain n) 1,u y
            let v := fun x=>χ x • (u x-c)
            let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
            let Fv := fun x i=>star (R (P x)) (Dv x i)
            let Φ := fun (x : Domain n) (r : ℝ)=>r^(p-(n : ℝ))*∫y in ball x r,(Real.sqrt (hsNormSq (Dv y)))^p
            let Ψ := fun t : ℝ=>sSup {z : ℝ | ∃x r,0<r ∧ r≤t ∧ z=Φ x r}
            MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv ∧
            ∀(a : Domain n) (t : ℝ),0<t → t≤1/128 → closedBall a (t/2)⊆ball (0 : Domain n) 1 →
              ∃(f : Domain n → Ambient q) (Df Q h : Domain n → Gradient n q) (g : Domain n → Ambient q),
                HasZeroBoundaryValues (ballDomain a (t/2)) f Df ∧
                MemW12 (ballDomain a (t/2)) g h ∧
                (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball a (t/2)))) ∧
                (∀ᵐx∂volume.restrict (ball a (t/2)),∀i,Fv x i=Df x i+Q x i+h x i) ∧
                (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
                  MemW12 (ballDomain a (t/2)) ψ Dψ →
                  (∫x in ball a (t/2),∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) ∧
                HolderToCK.WeakPoissonOn (ballDomain a (t/2)) h (fun _=>0) ∧
                (∀(i : Fin n) (ψ : Domain n → Ambient q),ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
                  tsupport ψ⊆ball a (t/2) →
                  (∫x in ball a (t/2),inner ℝ (h x i) (Laplacian.laplacian ψ x))=0) ∧
                IntegrableOn (fun x=>(hsNormSq (Df x))^(p/2)) (ball a (t/2)) volume ∧
                IntegrableOn (fun x=>(hsNormSq (Q x))^(p/2)) (ball a (t/2)) volume ∧
                ((∫x in ball a (t/2),(hsNormSq (Df x))^(p/2))^(1/p)≤
                  C*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+C*η*t^((n : ℝ)/p-(1/2 : ℝ))) ∧
                ((∫x in ball a (t/2),(hsNormSq (Q x))^(p/2))^(1/p)≤
                  C*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)) ∧
                ((∫x in ball a (t/2),hsNormSq (Df x))+(∫x in ball a (t/2),hsNormSq (Q x))+
                  (∫x in ball a (t/2),hsNormSq (h x))=∫x in ball a (t/2),hsNormSq (Fv x)) := by
  have hB : (0 : ℝ)≤B := Nat.cast_nonneg B
  obtain ⟨D,hD,hDF,HDir⟩ := exists_compact_target_cutoff_dirichlet_compensated_response_effective
    n hn p hpOne hpTwo hpConj q E R hRE hER hE A B L hA hConjugate
  let K : ℝ := effectiveSystemCoexactConstant n
  have hK : 0<K := effectiveSystemCoexactConstant_pos n
  have HCoexact := effective_same_system_coexact_compensated_bound n hn p hpOne hpTwo q E R hER hE hConjugate
  let C := 1+D+K
  have hC : 0<C := by dsimp only [C];linarith only [hD,hK]
  have hDC : D≤C := by dsimp only [C];linarith only [hK]
  have hKC : K≤C := by dsimp only [C];linarith only [hD]
  refine ⟨C,hC,?_,?_⟩
  · dsimp only [C,K,effectiveSystemCompensatedHodgeConstant]
    simp only [Rat.cast_add,Rat.cast_one,Rat.cast_natCast]
    rw [hDF]
  intro N u Du η hu hTarget hη hηOne hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
    χ hχ hcχ hsχ hχA hDχ hLap c v Dv Fv Φ Ψ
  obtain ⟨hV,HQuery⟩ := HDir N u Du η hu hTarget hη hηOne hCritical P DP hP hOrth hDPCritical
    Ω hΩ hEq hDiv hZCritical χ hχ hcχ hsχ hχA hDχ hLap
  refine ⟨hV,?_⟩
  intro a t ht htCap hClosed
  let r := t/2
  have hr : 0<r := half_pos ht
  let μ := volume.restrict (ball a r)
  have hSub : ball a r⊆ball (0 : Domain n) 1 := ball_subset_closedBall.trans hClosed
  let Λ : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q) :=
    (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).toContinuousLinearMap.comp R
  have hΛ (z : Ambient (q*q)) : Λ z=star (R z) := rfl
  have hPBound : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖P x‖≤Real.sqrt (q : ℝ) :=
    ae_orthogonal_coordinates_bound (Ω:=ballDomain (0 : Domain n) 1) E R hER hE P hOrth
  have hVParent : MemW12 (ballDomain (0 : Domain n) 1) v Dv := memW12_of_openDomain_subset hV (subset_univ _)
  have hF (i : Fin n) : MemLp (fun x=>Fv x i) 2 μ := by
    have H := (memLp_bounded_native_frame_columns (ballDomain (0 : Domain n) 1) P DP hP
      (Real.sqrt (q : ℝ)) hPBound Λ Dv hVParent.2.2 i).mono_measure
      (Measure.restrict_mono_set volume hSub)
    simpa only [hΛ] using H
  obtain ⟨f,Df,b,Db,Q,h,g,hf,hg,_hgMean,_hb,hQ,_hSkew,_hClosedB,_hDivB,_hNormal,hNatural,
    hDecomp,hHDiv,hHarm,_hFE,_hQE,_hBE,hFG,hProjection,_hPair,hPyth,_hHE⟩ :=
    exists_L2_relative_hodge_decomposition_ball hn a r hr Fv hF
  obtain ⟨f₀,Df₀,hf₀,_hEq₀,_hEnergy₀,hPI₀,hBound₀,hProjection₀⟩ := HQuery a t ht htCap hClosed
  have hTest (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
      (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆ball a r) :
      HasZeroBoundaryValues (ballDomain a r) ψ
        (fun x i=>fderiv ℝ ψ x (EuclideanSpace.single i 1)) :=
    (memW12_ball_of_ambient_c1 a r ψ (hψ.of_le (by simp))).zeroBoundary_of_compactSupport_ball hr hc hs
  have hUnique := dirichlet_gradient_response_unique_ae (by omega : 1≤n) a hr Fv hF hf hf₀
    (fun ψ hψ hc hs=>(hProjection ψ _ (hTest ψ hψ hc hs)).2.2)
    (fun ψ hψ hc hs=>hProjection₀ ψ _ (hTest ψ hψ hc hs))
  have hDensity : (fun x=>(hsNormSq (Df x))^(p/2))=ᵐ[μ](fun x=>(hsNormSq (Df₀ x))^(p/2)) :=
    hUnique.2.mono fun x hx=>by
      change (hsNormSq (Df x))^(p/2)=(hsNormSq (Df₀ x))^(p/2)
      rw [hx]
  have hPI : Integrable (fun x=>(hsNormSq (Df x))^(p/2)) μ := hPI₀.congr hDensity.symm
  have hDfBound : (∫x,(hsNormSq (Df x))^(p/2) ∂μ)^(1/p)≤
      D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+D*η*t^((n : ℝ)/p-(1/2 : ℝ)) := by
    rw [integral_congr_ae hDensity]
    exact hBound₀
  have hComplement : ∀ᵐx∂μ,∀i,star (R (P x)) (Dv x i)=(Df x i+h x i)+Q x i := by
    filter_upwards [hDecomp] with x hx i
    change Fv x i=(Df x i+h x i)+Q x i
    rw [hx i]
    abel_nf
  obtain ⟨_hVZero,hQI,hQBound⟩ := HCoexact A B hA hB N u Du η hu hTarget hη hCritical χ hχ hcχ hsχ hχA hDχ
    P DP η hP hη hOrth hDPCritical a t ht htCap hSub Q (f+g) (fun x i=>Df x i+h x i) hFG hQ
    (fun ψ Dψ hψ=>(hNatural ψ Dψ hψ).2) hComplement
  obtain ⟨_hV',hPsi,_hGrowth⟩ := cutoff_capped_envelope_lp_growth n hn p hpOne.le hpTwo.le A B hA hB
    q u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ t ht htCap
  have hPsiPower : 0≤(Ψ (8*t))^(1/p) := Real.rpow_nonneg hPsi _
  have hDfFinal : (∫x,(hsNormSq (Df x))^(p/2) ∂μ)^(1/p)≤
      C*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+C*η*t^((n : ℝ)/p-(1/2 : ℝ)) := hDfBound.trans (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC hη)
      (Real.rpow_nonneg ht.le _)) hPsiPower)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC hη) (Real.rpow_nonneg ht.le _)))
  have hQFinal : (∫x,(hsNormSq (Q x))^(p/2) ∂μ)^(1/p)≤C*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p) :=
    hQBound.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC hη)
      (Real.rpow_nonneg ht.le _)) hPsiPower)
  exact ⟨f,Df,Q,h,g,hf,hg,hQ,hDecomp,(fun ψ Dψ hψ=>(hNatural ψ Dψ hψ).2),hHDiv,
    (fun i ψ hψ hc hs=>(hHarm i ψ hψ hc hs).2),hPI,hQI,hDfFinal,hQFinal,hPyth⟩

end StationaryHarmonicMaps.Analysis

end
