module

public import StationaryHarmonicMaps.Analysis.SystemDirichletCompensation
public import StationaryHarmonicMaps.Analysis.SystemCutoffDirichletEquation
public import StationaryHarmonicMaps.Analysis.CutoffErrorIntegralEstimate

/-!
# The actual cutoff Dirichlet response and its complete compensated bound

Original map and connection data produce the original transformed cutoff
equation. The actual Dirichlet projection is constructed from that flux.
The original four-term error is controlled internally and the same
projection receives both the compensated envelope term and error scale.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Original compact-target system data and a given critical native
Coulomb frame construct the actual Dirichlet cutoff projection and its
scale-correct estimate. No component equation or error bound is an input. -/
theorem exists_compact_target_cutoff_dirichlet_compensated_response
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
            let W := fun x=>∑i : Fin n,Z x i (star (R (P x)) (Dv x i))
            let e := fun x=>
              (∑i : Fin n,fderiv ℝ χ x (EuclideanSpace.single i 1) • star (R (DP x i)) (u x-c))+
              (2 : ℝ) • (∑i : Fin n,fderiv ℝ χ x (EuclideanSpace.single i 1) • star (R (P x)) (Du x i))+
              Laplacian.laplacian χ x • star (R (P x)) (u x-c)+
              ∑i : Fin n,fderiv ℝ χ x (EuclideanSpace.single i 1) • Z x i (star (R (P x)) (u x-c))
            let Φ := fun (x : Domain n) (r : ℝ)=>r^(p-(n : ℝ))*∫y in ball x r,(Real.sqrt (hsNormSq (Dv y)))^p
            let Ψ := fun t : ℝ=>sSup {z : ℝ | ∃x r,0<r ∧ r≤t ∧ z=Φ x r}
            MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv ∧
            ∀(a : Domain n) (t : ℝ),0<t → t≤1/128 → closedBall a (t/2)⊆ball (0 : Domain n) 1 →
              ∃(f : Domain n → Ambient q) (Df : Domain n → Gradient n q),
                HasZeroBoundaryValues (ballDomain a (t/2)) f Df ∧
                HolderToCK.WeakPoissonOn (ballDomain a (t/2)) Df (fun x=>e x-W x) ∧
                (∫x in ball a (t/2),hsNormSq (Df x))≤∫x in ball a (t/2),hsNormSq (Fv x) ∧
                IntegrableOn (fun x=>(hsNormSq (Df x))^(p/2)) (ball a (t/2)) volume ∧
                (∫x in ball a (t/2),(hsNormSq (Df x))^(p/2))^(1/p)≤
                  C*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+C*η*t^((n : ℝ)/p-δ) ∧
                ∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
                  HasZeroBoundaryValues (ballDomain a (t/2)) ψ Dψ →
                  (∫x in ball a (t/2),∑i : Fin n,inner ℝ (Df x i) (Dψ x i))=
                    ∫x in ball a (t/2),∑i : Fin n,inner ℝ (Fv x i) (Dψ x i) := by
  have hp : 0<p := zero_lt_one.trans hpOne
  let s := p/(p-1)
  have hs : 0<s := div_pos hp (sub_pos.mpr hpOne)
  obtain ⟨D,hD,HD⟩ := exists_compact_target_system_dirichlet_compensated_bound n hn p hpOne hpTwo hpConj q E R hRE hER hE A B hA hB
  obtain ⟨G,hG,HErr⟩ := exists_cutoff_error_integral_bound n (q*q) q hn R hδ hδOne hB hL
  let C := 1+D+D*G
  have hC : 0<C := by dsimp only [C];positivity
  have hDC : D≤C := by dsimp only [C];nlinarith only [hD,hG]
  have hDGC : D*G≤C := by dsimp only [C];linarith only [hD]
  refine ⟨C,hC,?_⟩
  intro N u Du η hu hTarget hη hηOne hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
    χ hχ hcχ hsχ hχA hDχ hLap c v Dv Fv W e Φ Ψ
  let U := ballDomain (0 : Domain n) 1
  let μ := volume.restrict (ball (0 : Domain n) 1)
  have hPBound : ∀ᵐx∂μ,‖P x‖≤Real.sqrt (q : ℝ) :=
    ae_orthogonal_coordinates_bound (Ω:=U) E R hER hE P hOrth
  have hΩLocal (i : Fin n) : LocallyMemL2 U (fun x=>Ω x i) := by
    intro S _hS hSU
    exact (hΩ i).mono_measure (Measure.restrict_mono_set volume hSU)
  have hZOp (i : Fin n) : MemLp (fun x=>Z x i) 2 μ := by
    have hRP := R.continuous.comp_aestronglyMeasurable hP.2.1.aestronglyMeasurable
    have hStarP := (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).continuous.comp_aestronglyMeasurable hRP
    have hRPBound : ∀ᵐx∂μ,‖R (P x)‖≤‖R‖*Real.sqrt (q : ℝ) := by
      filter_upwards [hPBound] with x hx
      exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg R))
    have hStarBound : ∀ᵐx∂μ,‖star (R (P x))‖≤‖R‖*Real.sqrt (q : ℝ) := by
      filter_upwards [hRPBound] with x hx
      simpa only [ContinuousLinearMap.star_eq_adjoint,LinearIsometryEquiv.norm_map] using hx
    have hD := R.lipschitz.comp_memLp (map_zero R) (hP.2.2 i)
    exact memLp_two_bounded_connection hRP hRPBound hStarP hStarBound hD (hΩ i)
  have hZ (i : Fin n) : MemLp (fun x=>E (Z x i)) 2 μ :=
    E.lipschitz.comp_memLp (map_zero E) (hZOp i)
  have hZLocal (i : Fin n) : LocallyMemL2 U (fun x=>E (Z x i)) := by
    intro S _hS hSU
    exact (hZ i).mono_measure (Measure.restrict_mono_set volume hSU)
  have hsInside : tsupport χ⊆U.val := hsχ.trans (closedBall_subset_ball (by norm_num))
  obtain ⟨hV,_hWLocal,_heLocal,_hRaw,Hquery⟩ := exists_system_cutoff_dirichlet_equation (by omega : 1≤n)
    hP.to_memW12Loc hPBound R hOrth hu.to_memW12Loc Ω hΩLocal hEq c χ hχ hcχ hsInside
  refine ⟨hV,?_⟩
  intro a t ht htCap hClosed
  let r := t/2
  have hr : 0<r := half_pos ht
  obtain ⟨_hF,_hWI,heI,f,Df,hf,hEquation,hEnergy,hProjection⟩ := Hquery a r hr hClosed
  obtain ⟨_hV,hPI,hBound⟩ := HD N u Du η hu hTarget hη hηOne hCritical χ hχ hcχ hsχ hχA hDχ
    U P DP hP.to_memW12Loc hOrth hDPCritical Z hZ hDiv hZCritical a t ht htCap hClosed e heI f Df hf hEquation
  have hrCap : r≤1/16 := by dsimp only [r];linarith only [htCap]
  have hError : (∫x in ball a r,‖e x‖)≤G*η*r^((n : ℝ)-1-δ) := by
    have H := (HErr u Du P DP (fun x i=>E (Z x i)) χ η hu hP.to_memW12Loc hZLocal hOrth
      hη hηOne hCritical hDPCritical hZCritical hχ hcχ hsχ hDχ hLap a r hr hrCap).2
    simpa only [hRE] using H
  have hnReal : (2 : ℝ)≤n := by exact_mod_cast hn
  have hErrExponent : 0≤(n : ℝ)-1-δ := by linarith only [hnReal,hδOne]
  have hErrRadius : r^((n : ℝ)-1-δ)≤t^((n : ℝ)-1-δ) :=
    Real.rpow_le_rpow hr.le (by dsimp only [r];linarith only [ht]) hErrExponent
  have hError' : (∫x in ball a r,‖e x‖)≤G*η*t^((n : ℝ)-1-δ) := hError.trans
    (mul_le_mul_of_nonneg_left hErrRadius (mul_nonneg hG.le hη))
  have hConj : 1/s=1-1/p := by
    dsimp only [s]
    field_simp [hp.ne',(sub_pos.mpr hpOne).ne']
  have hScale : t^(1-(n : ℝ)/s)*t^((n : ℝ)-1-δ)=t^((n : ℝ)/p-δ) := by
    rw [←Real.rpow_add ht]
    have hDiv : (n : ℝ)/s=(n : ℝ)*(1-1/p) := by rw [div_eq_mul_inv,←one_div,hConj]
    congr 1
    rw [hDiv]
    ring
  obtain ⟨_hV',hPsi,_hGrowth⟩ := cutoff_capped_envelope_lp_growth n hn p hpOne.le hpTwo.le A B hA hB
    q u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ t ht htCap
  have hPsiPower : 0≤(Ψ (8*t))^(1/p) := Real.rpow_nonneg hPsi _
  refine ⟨f,Df,hf,hEquation,hEnergy,hPI,hBound.trans ?_,?_⟩
  · calc
      _≤D*(η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+t^(1-(n : ℝ)/s)*(G*η*t^((n : ℝ)-1-δ))) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hError' (Real.rpow_nonneg ht.le _))) hD.le
      _=D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+(D*G)*η*(t^(1-(n : ℝ)/s)*t^((n : ℝ)-1-δ)) := by ring
      _=D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+(D*G)*η*t^((n : ℝ)/p-δ) := by rw [hScale]
      _≤_ := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC hη)
          (Real.rpow_nonneg ht.le _)) hPsiPower)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDGC hη) (Real.rpow_nonneg ht.le _))
  · intro ψ Dψ hψ
    exact (hProjection ψ Dψ hψ).2.2

end StationaryHarmonicMaps.Analysis

end
