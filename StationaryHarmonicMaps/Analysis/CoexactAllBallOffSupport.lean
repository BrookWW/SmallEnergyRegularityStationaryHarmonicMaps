module

public import StationaryHarmonicMaps.Analysis.SameNeumannOperatorOffSupport
public import StationaryHarmonicMaps.Analysis.NeumannGradientUniqueness

/-!
# Off-support bounds for the same native relative coexact response

Native gradient-complement uniqueness identifies the original response
with the complement of the true Neumann projection. Wherever the original
forcing vanishes, its zero extension is the negative Neumann gradient.
The boundary harmonic estimate therefore controls that same response.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Every actual natural relative response has the same all-ball essential
bound off the original forcing, including boundary and exterior queries. -/
theorem exists_native_coexact_all_ball_offSupport_bounds (n : ℕ) (hn : 2≤n) :
    ∃C : ℝ,0<C ∧ ∀ (q : ℕ) (F Q : Domain n → Gradient n q)
      (v : Domain n → Ambient q),
      (∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      MemW12 (ballDomain (0 : Domain n) 1) v (fun x i=>F x i-Q x i) →
      (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) →
      ∀ (a : Domain n) (r : ℝ),0<r →
        F=ᵐ[volume.restrict (ball (0 : Domain n) 1∩ball a (256*r))] (fun _=>0) →
        let Q₀ := (ball (0 : Domain n) 1).indicator Q
        ∀ᵐx∂volume.restrict (ball a r),hsNormSq (Q₀ x)≤
          C*(volume.real (ball a (256*r)))⁻¹*(∫y in ball a (256*r),hsNormSq (Q₀ y)) := by
  obtain ⟨C,hC,HC⟩ := exists_same_neumann_operator_all_ball_offSupport_bounds n hn
  refine ⟨C,hC,?_⟩
  intro q F Q v hF hQ hv hNatural a r hr hZero Q₀
  let μ := volume.restrict (ball (0 : Domain n) 1)
  obtain ⟨T,_hNorm,_hSelf,_hIdem,Hresponse⟩ := HC q
  obtain ⟨f,hf,_hEnergy,hNat,_hWeak,_hN₀,Hbound⟩ := Hresponse F hF
  let N : Domain n → Gradient n q := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2 (fun j : Fin q=>
    (T ((memLp_hs_flatten F hF).toLp (fun x=>WithLp.toLp 2
      (fun k : Fin (n*q)=>F x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)))) x
        (finProdFinEquiv (i,j)))
  let N₀ : Domain n → Gradient n q := fun x i=>(ball (0 : Domain n) 1).indicator (fun y=>N y i) x
  change MemW12 (ballDomain (0 : Domain n) 1) f N at hf
  change ∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
    MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
    Integrable (fun x=>∑i : Fin n,inner ℝ (N x i) (Dψ x i)) μ ∧
    Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i)) μ ∧
    (∫x,∑i : Fin n,inner ℝ (N x i) (Dψ x i) ∂μ)=
      ∫x,∑i : Fin n,inner ℝ (F x i) (Dψ x i) ∂μ at hNat
  change ∀ (a : Domain n) (r : ℝ),0<r →
    F=ᵐ[volume.restrict (ball (0 : Domain n) 1∩ball a (256*r))] (fun _=>0) →
    ∀ᵐx∂volume.restrict (ball a r),hsNormSq (N₀ x)≤
      C*(volume.real (ball a (256*r)))⁻¹*(∫y in ball a (256*r),hsNormSq (N₀ y)) at Hbound
  clear_value N
  have hEq : (fun x i=>F x i-Q x i)=ᵐ[μ]N := by
    apply native_neumann_gradient_response_unique_ae (ballDomain (0 : Domain n) 1) v f _ N hv hf
    intro ψ Dψ hψ
    have hFI : Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i)) μ :=
      integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hF i) (hψ.2.2 i))
    have hQI : Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ :=
      integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hQ i) (hψ.2.2 i))
    simp only [inner_sub_left,Finset.sum_sub_distrib]
    change (∫x,(∑i : Fin n,inner ℝ (F x i) (Dψ x i))-
      (∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) ∂μ)=_
    rw [integral_sub hFI hQI,hNatural ψ Dψ hψ,sub_zero]
    exact (hNat ψ Dψ hψ).2.2.symm
  have hHS : (fun x=>hsNormSq (Q₀ x))=ᵐ[volume.restrict (ball a (256*r))]
      (fun x=>hsNormSq (N₀ x)) := by
    have hZero' : ∀ᵐx∂volume,x∈ball (0 : Domain n) 1∩ball a (256*r) → F x=0 :=
      (ae_restrict_iff' (measurableSet_ball.inter measurableSet_ball)).mp hZero
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae hZero',
      ae_restrict_of_ae ((ae_restrict_iff' measurableSet_ball).mp hEq)] with x hx hFx hNx
    by_cases hxB : x∈ball (0 : Domain n) 1
    · have hFx0 : F x=0 := hFx ⟨hxB,hx⟩
      have hNx' := hNx hxB
      have hNeg (i : Fin n) : Q x i= -N x i := by
        have H := congrFun hNx' i
        simpa only [hFx0,Pi.zero_apply,zero_sub,neg_eq_iff_eq_neg] using H
      simp only [Q₀,N₀,indicator_of_mem hxB,hsNormSq,hNeg,norm_neg]
    · simp only [Q₀,N₀,indicator_of_notMem hxB,hsNormSq,Pi.zero_apply]
  have hSmall : (fun x=>hsNormSq (Q₀ x))=ᵐ[volume.restrict (ball a r)]
      (fun x=>hsNormSq (N₀ x)) := hHS.filter_mono
    (ae_mono (Measure.restrict_mono_set volume (ball_subset_ball (by linarith only [hr] : r≤256*r))))
  have H := Hbound a r hr hZero
  rw [←integral_congr_ae hHS] at H
  exact hSmall.le.trans H

end StationaryHarmonicMaps.Analysis

end
