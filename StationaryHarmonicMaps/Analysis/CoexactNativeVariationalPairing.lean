module

public import StationaryHarmonicMaps.Analysis.RelativeHodgeDecomposition
public import StationaryHarmonicMaps.Analysis.SobolevLinearOperations

/-!
# Native variational pairings of the actual relative coexact component

The two native gradient terms in the relative Hodge decomposition combine
to one native gradient. Every natural solenoidal L2 field annihilates that
gradient, so the same coexact component has the original field's pairing.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The displayed divergence of a finite native H1 tensor has L2 columns. -/
theorem memLp_native_tensor_divergence {n q : ℕ} (Ω : OpenDomain n)
    (b : Fin n → Fin n → Domain n → Ambient q)
    (Db : Fin n → Fin n → Domain n → Gradient n q)
    (hb : ∀i j,MemW12 Ω (b i j) (Db i j))
    (P : Domain n → Gradient n q)
    (hDiv : ∀ᵐx∂volume.restrict Ω.val,∀j,(∑i : Fin n,Db i j x i)=P x j) :
    ∀j,MemLp (fun x=>P x j) 2 (volume.restrict Ω.val) := by
  intro j
  exact (memLp_finsetSum Finset.univ (fun i _=>(hb i j).2.2 i)).ae_eq
    (hDiv.mono fun x hx=>hx j)

/-- A native gradient complement vanishes against every natural solenoidal
L2 field, with all original pairings integrable. -/
theorem native_coexact_pairing_of_gradient_complement {n q : ℕ}
    (Ω : OpenDomain n) (F P : Domain n → Gradient n q)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12 Ω u Du)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict Ω.val))
    (hP : ∀i,MemLp (fun x=>P x i) 2 (volume.restrict Ω.val))
    (hDecomp : ∀ᵐx∂volume.restrict Ω.val,∀i,F x i=Du x i+P x i)
    (Q : Domain n → Gradient n q)
    (hQ : ∀i,MemLp (fun x=>Q x i) 2 (volume.restrict Ω.val))
    (hNatural : ∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 Ω ψ Dψ →
      (∫x in Ω.val,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) :
    IntegrableOn (fun x=>∑i : Fin n,inner ℝ (P x i) (Q x i)) Ω.val volume ∧
    IntegrableOn (fun x=>∑i : Fin n,inner ℝ (F x i) (Q x i)) Ω.val volume ∧
    (∫x in Ω.val,∑i : Fin n,inner ℝ (P x i) (Q x i))=
      ∫x in Ω.val,∑i : Fin n,inner ℝ (F x i) (Q x i) := by
  have hPI := integrable_finsetSum Finset.univ (fun i _=>
    HolderToCK.integrable_inner_of_memLp_two (hP i) (hQ i))
  have hFI := integrable_finsetSum Finset.univ (fun i _=>
    HolderToCK.integrable_inner_of_memLp_two (hF i) (hQ i))
  have hDI := integrable_finsetSum Finset.univ (fun i _=>
    HolderToCK.integrable_inner_of_memLp_two (hu.2.2 i) (hQ i))
  have hDZero : (∫x in Ω.val,∑i : Fin n,inner ℝ (Du x i) (Q x i))=0 := by
    calc
      _=∫x in Ω.val,∑i : Fin n,inner ℝ (Q x i) (Du x i) :=
        integral_congr_ae (Eventually.of_forall fun x=>
          Finset.sum_congr rfl fun i _=>real_inner_comm _ _)
      _=0 := hNatural u Du hu
  refine ⟨hPI,hFI,?_⟩
  symm
  calc
    _=∫x in Ω.val,(∑i : Fin n,inner ℝ (Du x i) (Q x i))+
        ∑i : Fin n,inner ℝ (P x i) (Q x i) := by
      apply integral_congr_ae
      filter_upwards [hDecomp] with x hx
      simp only [hx,inner_add_left,Finset.sum_add_distrib]
    _=(∫x in Ω.val,∑i : Fin n,inner ℝ (Du x i) (Q x i))+
        ∫x in Ω.val,∑i : Fin n,inner ℝ (P x i) (Q x i) := integral_add hDI hPI
    _=_ := by rw [hDZero,zero_add]

/-- Original L2 data produce the actual closed normal relative coexact
component, its native gradient complement, and the pairing against every
natural solenoidal native L2 field. -/
theorem exists_relative_coexact_native_pairing_unitBall {n q : ℕ} (hn : 2≤n)
    (F : Domain n → Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0:Domain n) 1))) :
    ∃(b : Fin n → Fin n → Domain n → Ambient q)
      (Db : Fin n → Fin n → Domain n → Gradient n q)
      (P : Domain n → Gradient n q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) u Du ∧
      (∀i j,MemW12 (ballDomain (0:Domain n) 1) (b i j) (Db i j)) ∧
      (∀i,MemLp (fun x=>P x i) 2 (volume.restrict (ball (0:Domain n) 1))) ∧
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i j,b i j x= -b j i x) ∧
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i j k,
        Db i j x k+Db j k x i+Db k i x j=0) ∧
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀j,(∑i : Fin n,Db i j x i)=P x j) ∧
      (∀(j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (b i j x) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
        IntegrableOn (fun x=>inner ℝ (P x j) (ψ x)) (ball (0:Domain n) 1) volume ∧
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (b i j x) (Dψ x i))=
          -(∫x in ball (0:Domain n) 1,inner ℝ (P x j) (ψ x))) ∧
      (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (P x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (P x i) (Dψ x i))=0) ∧
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,F x i=Du x i+P x i) ∧
      ((∫x in ball (0:Domain n) 1,hsNormSq (P x))≤
        ∫x in ball (0:Domain n) 1,hsNormSq (F x)) ∧
      ∀Q : Domain n → Gradient n q,
        (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
        (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (P x i) (Q x i)) (ball (0:Domain n) 1) volume ∧
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (F x i) (Q x i)) (ball (0:Domain n) 1) volume ∧
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (P x i) (Q x i))=
          ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (F x i) (Q x i) := by
  obtain ⟨f,Df,b,Db,P,h,g,hf,hg,_hgMean,hb,hP,hSkew,hClosed,hDiv,
    hNormal,hNatural,hDecomp,_hHLp,_hHDiv,_hHarm,_hfEnergy,hPEnergy,_hbEnergy,_hCore⟩ :=
    exists_L2_relative_hodge_decomposition_unitBall hn F hF
  have hu : MemW12 (ballDomain (0:Domain n) 1) (f+g)
      (fun x i=>Df x i+h x i) :=
    ⟨hasWeakGradient_add hf.1.1 hg.1,hf.1.2.1.add hg.2.1,
      fun i=>(hf.1.2.2 i).add (hg.2.2 i)⟩
  have hFull : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,
      F x i=(Df x i+h x i)+P x i := by
    filter_upwards [hDecomp,hDiv] with x hx hd i
    rw [hx i,hd i]
    abel
  refine ⟨b,Db,P,f+g,fun x i=>Df x i+h x i,hu,hb,hP,hSkew,hClosed,hDiv,
    hNormal,hNatural,hFull,hPEnergy,?_⟩
  intro Q hQ hQN
  exact native_coexact_pairing_of_gradient_complement (ballDomain (0:Domain n) 1)
    F P (f+g) _ hu hF hP hFull Q hQ hQN

end StationaryHarmonicMaps.Analysis

end
