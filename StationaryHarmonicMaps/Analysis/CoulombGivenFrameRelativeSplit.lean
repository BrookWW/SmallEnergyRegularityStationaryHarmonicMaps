/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.SkewCoulombLinearMorrey
public import StationaryHarmonicMaps.Analysis.SkewConnectionAndTests

/-!
# Relative fields for one given native Coulomb frame

The same given orthogonal frame and original skew connection produce an
actual linear relative tensor and response. Subtracting that response
from the original full natural Coulomb connection gives its nonlinear
relative field, with the literal logarithmic native gradient complement.
No minimizing frame is selected in this construction.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- One given native orthogonal Coulomb frame has actual linear and
nonlinear natural relative fields; its same linear tensor retains every
original subdimensional power-growth bound of A. -/
theorem exists_given_frame_coulomb_relative_fields_unitBall (n : ℕ) (hn : 2≤n) :
    ∃L : {ν : ℝ //0≤ν ∧ ν<(n:ℝ)} → ℝ,
      (∀ν,0<L ν) ∧ ∀(q : ℕ)
      (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
      (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q)),
      (∀T,R (E T)=T) → (∀z,E (R z)=z) →
      (∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) →
      ∀(p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
        (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q)),
        MemW12 (ballDomain (0:Domain n) 1) p Dp →
        (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (R (p x))*R (p x)=1) →
        (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
        (∀i,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (A x i)= -A x i) →
        let F := fun x i=>E (star (R (p x))*R (Dp x i))
        let G := fun x i=>E (star (R (p x))*A x i*R (p x))
        let Z := fun x i=>star (R (p x))*R (Dp x i)+star (R (p x))*A x i*R (p x)
        let μ := volume.restrict (ball (0:Domain n) 1)
        (∀(ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x,∑i : Fin n,inner ℝ (E (Z x i)) (Dψ x i) ∂μ)=0) →
        ∃(Qc Qb : Domain n → Gradient n (q*q))
          (v w : Domain n → Ambient (q*q))
          (c : Fin n → Fin n → Domain n → Ambient (q*q))
          (Dc : Fin n → Fin n → Domain n → Gradient n (q*q)),
          (∀i,MemLp (fun x=>Qc x i) 2 μ) ∧
          (∀i,MemLp (fun x=>Qb x i) 2 μ) ∧
          MemW12 (ballDomain (0:Domain n) 1) w (fun x i=>G x i-Qc x i) ∧
          MemW12 (ballDomain (0:Domain n) 1) v (fun x i=>F x i-Qb x i) ∧
          (∀x i,star (R (Qc x i))= -R (Qc x i)) ∧
          (∀ᵐx∂μ,∀i,star (R (Qb x i))= -R (Qb x i)) ∧
          (∀x i,Qb x i+Qc x i=E (Z x i)) ∧
          (∀(ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
            MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (Qb x i) (Dψ x i)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (Qb x i) (Dψ x i) ∂μ)=0) ∧
          (∀(ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
            MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (Qc x i) (Dψ x i)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (Qc x i) (Dψ x i) ∂μ)=0) ∧
          (∀i j,MemW12 (ballDomain (0:Domain n) 1) (c i j) (Dc i j)) ∧
          (∀i j x,star (R (c i j x))= -R (c i j x)) ∧
          (∀i j x k,star (R (Dc i j x k))= -R (Dc i j x k)) ∧
          (∀ᵐx∂μ,∀i j,c i j x= -c j i x) ∧
          (∀ᵐx∂μ,∀i j k,Dc i j x k+Dc j k x i+Dc k i x j=0) ∧
          (∀ᵐx∂μ,∀j,(∑i : Fin n,Dc i j x i)=Qc x j) ∧
          (∀(j : Fin n) (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
            MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (c i j x) (Dψ x i)) μ ∧
            Integrable (fun x=>inner ℝ (Qc x j) (ψ x)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (c i j x) (Dψ x i) ∂μ)=
              -(∫x,inner ℝ (Qc x j) (ψ x) ∂μ)) ∧
          ∀(ν : {ν : ℝ //0≤ν ∧ ν<(n:ℝ)}) (K : ℝ),0≤K →
            (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
              (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>E (A x i)))≤K*r^ν.val) →
            ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
              (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Qc x))≤L ν*K*r^ν.val := by
  obtain ⟨L,hL,Hlinear⟩ := exists_skew_coulomb_linear_relative_power_growth n hn
  refine ⟨L,hL,?_⟩
  intro q E R hRE hER hE p Dp A hp hOrth hA hAskew F G Z μ hZN
  obtain ⟨_hZ,hEZ,hZSkew⟩ := frame_connection_memLp_and_skew E R hER hE p Dp hp hOrth A hA hAskew
  obtain ⟨w,c,Dc,Qc,hw,_hwSkew,hc,hct,hDct,hQcSkew,hQc,hCS,hCC,hCD,hCN,hQcN,hGrowth⟩ :=
    Hlinear q E R hRE hER hE p Dp A hp hOrth hA hAskew
  let Qb := fun x i=>E (Z x i)-Qc x i
  have hQb (i : Fin n) : MemLp (fun x=>Qb x i) 2 μ := (hEZ i).sub (hQc i)
  have hv : MemW12 (ballDomain (0:Domain n) 1) (fun x=> -w x) (fun x i=>F x i-Qb x i) := by
    let S : Ambient (q*q) →L[ℝ] Ambient (q*q) := -ContinuousLinearMap.id ℝ _
    have hwNeg : MemW12 (ballDomain (0:Domain n) 1) (fun x=> -w x)
        (fun x i=> -(G x i-Qc x i)) :=
      ⟨(memW12Loc_continuousLinearMap hw.to_memW12Loc S).1,
        hw.2.1.neg,fun i=>(hw.2.2 i).neg⟩
    apply hwNeg.congr_ae (Eventually.of_forall fun _=>rfl)
    exact Eventually.of_forall fun x=>by
      funext i
      dsimp only [F,G,Z,Qb]
      rw [map_add]
      abel
  have hQbSkew : ∀ᵐx∂μ,∀i,star (R (Qb x i))= -R (Qb x i) := by
    filter_upwards [hZSkew] with x hx i
    change star (R (E (Z x i)-Qc x i))= -R (E (Z x i)-Qc x i)
    rw [map_sub,hRE]
    change ContinuousLinearMap.adjoint (Z x i-R (Qc x i))= -(Z x i-R (Qc x i))
    rw [map_sub]
    change star (Z x i)-star (R (Qc x i))= -(Z x i-R (Qc x i))
    have hZi : star (Z x i)= -Z x i := hx i
    rw [hZi,hQcSkew]
    abel
  have hTotal (x : Domain n) (i : Fin n) : Qb x i+Qc x i=E (Z x i) := sub_add_cancel _ _
  have hQbN (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q))
      (hψ : MemW12 (ballDomain (0:Domain n) 1) ψ Dψ) :
      Integrable (fun x=>∑i : Fin n,inner ℝ (Qb x i) (Dψ x i)) μ ∧
      (∫x,∑i : Fin n,inner ℝ (Qb x i) (Dψ x i) ∂μ)=0 := by
    have hZI : Integrable (fun x=>∑i : Fin n,inner ℝ (E (Z x i)) (Dψ x i)) μ :=
      integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hEZ i) (hψ.2.2 i))
    obtain ⟨hCI,hCZero⟩ := hQcN ψ Dψ hψ
    refine ⟨?_,?_⟩
    · apply (hZI.sub hCI).congr
      exact Eventually.of_forall fun x=>by
        change (∑i : Fin n,inner ℝ (E (Z x i)) (Dψ x i))-
          (∑i : Fin n,inner ℝ (Qc x i) (Dψ x i))=∑i : Fin n,inner ℝ (Qb x i) (Dψ x i)
        simp only [Qb,inner_sub_left,Finset.sum_sub_distrib]
    · simp only [Qb,inner_sub_left,Finset.sum_sub_distrib]
      rw [integral_sub hZI hCI,hZN ψ Dψ hψ,hCZero,sub_self]
  exact ⟨Qc,Qb,fun x=> -w x,w,c,Dc,hQc,hQb,hw,hv,hQcSkew,hQbSkew,hTotal,hQbN,
    hQcN,hc,hct,hDct,hCS,hCC,hCD,hCN,hGrowth⟩

end StationaryHarmonicMaps.Analysis

end
