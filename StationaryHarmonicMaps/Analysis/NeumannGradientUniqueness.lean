module

public import StationaryHarmonicMaps.Analysis.NeumannGradientProjection

/-!
# Uniqueness of the original native Neumann gradient

Testing the two original responses against their actual native difference
annihilates its complete HS energy. No normalization of their map values
is needed to identify their displayed gradients.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

/-- Two native graphs with identical unrestricted-boundary gradient tests have the same explicit gradient almost everywhere. -/
theorem native_neumann_gradient_response_unique_ae {n q : ℕ} (Ω : OpenDomain n)
    (f g : Domain n → Ambient q) (Df Dg : Domain n → Gradient n q)
    (hf : MemW12 Ω f Df) (hg : MemW12 Ω g Dg)
    (hEq : ∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),MemW12 Ω ψ Dψ →
      (∫x in Ω.val,∑i : Fin n,inner ℝ (Df x i) (Dψ x i))=
        ∫x in Ω.val,∑i : Fin n,inner ℝ (Dg x i) (Dψ x i)) :
    Df=ᵐ[volume.restrict Ω.val]Dg := by
  let μ := volume.restrict Ω.val
  have hDiff := hf.sub hg
  have hIF := integrable_column_pairing μ Df (fun x i=>Df x i-Dg x i) hf.2.2 hDiff.2.2
  have hIG := integrable_column_pairing μ Dg (fun x i=>Df x i-Dg x i) hg.2.2 hDiff.2.2
  have hEnergy : (∫x,hsNormSq (fun i=>Df x i-Dg x i) ∂μ)=0 := by
    calc
      _=(∫x,∑i : Fin n,inner ℝ (Df x i) (Df x i-Dg x i) ∂μ)-
          ∫x,∑i : Fin n,inner ℝ (Dg x i) (Df x i-Dg x i) ∂μ := by
        rw [← integral_sub hIF hIG]
        apply integral_congr_ae
        exact Eventually.of_forall fun x=>by
          simp only [hsNormSq,← real_inner_self_eq_norm_sq,inner_sub_left,Finset.sum_sub_distrib]
      _=0 := by rw [hEq (f-g) _ hDiff,sub_self]
  have hAE := (integral_eq_zero_iff_of_nonneg (fun x=>hsNormSq_nonneg (fun i=>Df x i-Dg x i))
    hDiff.integrable_hsNormSq).mp hEnergy
  filter_upwards [hAE] with x hx
  funext i
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  have H := Finset.single_le_sum (fun j _=>sq_nonneg ‖Df x j-Dg x j‖) (Finset.mem_univ i)
  change ‖Df x i-Dg x i‖^2≤hsNormSq (fun j=>Df x j-Dg x j) at H
  rw [hx] at H
  exact le_antisymm H (sq_nonneg _)

end StationaryHarmonicMaps.Analysis

end
