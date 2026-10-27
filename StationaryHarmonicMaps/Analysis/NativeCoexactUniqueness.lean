module

public import StationaryHarmonicMaps.Analysis.NeumannGradientUniqueness

/-!
# Uniqueness of a natural coexact response of the original field

Natural response fields with native gradient complements have the same
Neumann gradient response. Native self-testing identifies the displayed
response fields almost everywhere on the original domain.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

/-- Two natural L2 fields whose complements in the same raw field are
native gradients coincide almost everywhere, without a value normalization. -/
theorem native_coexact_response_unique_ae {n q : ℕ} (Ω : OpenDomain n)
    (F P Q : Domain n → Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict Ω.val))
    (hP : ∀i,MemLp (fun x=>P x i) 2 (volume.restrict Ω.val))
    (hQ : ∀i,MemLp (fun x=>Q x i) 2 (volume.restrict Ω.val))
    (f g : Domain n → Ambient q)
    (hf : MemW12 Ω f (fun x i=>F x i-P x i))
    (hg : MemW12 Ω g (fun x i=>F x i-Q x i))
    (hPN : ∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 Ω ψ Dψ → (∫x in Ω.val,∑i : Fin n,inner ℝ (P x i) (Dψ x i))=0)
    (hQN : ∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 Ω ψ Dψ → (∫x in Ω.val,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) :
    P=ᵐ[volume.restrict Ω.val]Q := by
  let μ := volume.restrict Ω.val
  have hEq (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
      (hψ : MemW12 Ω ψ Dψ) :
      (∫x in Ω.val,∑i : Fin n,inner ℝ (F x i-P x i) (Dψ x i))=
        ∫x in Ω.val,∑i : Fin n,inner ℝ (F x i-Q x i) (Dψ x i) := by
    have hFI : Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i)) μ :=
      integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hF i) (hψ.2.2 i))
    have hPI : Integrable (fun x=>∑i : Fin n,inner ℝ (P x i) (Dψ x i)) μ :=
      integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hP i) (hψ.2.2 i))
    have hQI : Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ :=
      integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hQ i) (hψ.2.2 i))
    simp only [inner_sub_left,Finset.sum_sub_distrib]
    rw [integral_sub hFI hPI,integral_sub hFI hQI,hPN ψ Dψ hψ,hQN ψ Dψ hψ]
  have H := native_neumann_gradient_response_unique_ae Ω f g
    (fun x i=>F x i-P x i) (fun x i=>F x i-Q x i) hf hg hEq
  filter_upwards [H] with x hx
  funext i
  have Hi := congrFun hx i
  exact sub_right_inj.mp Hi

end StationaryHarmonicMaps.Analysis

end
