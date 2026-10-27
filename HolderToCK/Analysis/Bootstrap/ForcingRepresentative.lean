module

public import HolderToCK.Analysis.ClassicalWeakGradient
public import HolderToCK.Analysis.WeakPoissonLocality
public import HarmonicMaps.SobolevLemmas

/-! # The classical quadratic forcing of the same map

The original weak columns agree almost everywhere with the actual C1
derivative. Replacing them in the original formula gives one continuous
quadratic forcing and preserves the signed weak equation.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK

theorem classical_quadratic_forcing_representative {n q : ℕ} (Ω : OpenDomain n)
    {u F : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    (hA : Continuous A) (hu : ContDiffOn ℝ 1 u Ω.val)
    (hWeak : HasWeakGradient Ω u Du) (hEq : WeakPoissonOn Ω Du F)
    (hFormula : ∀ᵐ x ∂volume.restrict Ω.val, F x = ∑ i : Fin n, A (u x) (Du x i) (Du x i)) :
    ContinuousOn (fun x => ∑ i : Fin n,
      A (u x) (fderiv ℝ u x (EuclideanSpace.single i 1))
        (fderiv ℝ u x (EuclideanSpace.single i 1))) Ω.val ∧
    F =ᵐ[volume.restrict Ω.val] (fun x => ∑ i : Fin n,
      A (u x) (fderiv ℝ u x (EuclideanSpace.single i 1))
        (fderiv ℝ u x (EuclideanSpace.single i 1))) ∧
    WeakPoissonOn Ω (fun x i => fderiv ℝ u x (EuclideanSpace.single i 1))
      (fun x => ∑ i : Fin n,
        A (u x) (fderiv ℝ u x (EuclideanSpace.single i 1))
          (fderiv ℝ u x (EuclideanSpace.single i 1))) := by
  have hDu : Du =ᵐ[volume.restrict Ω.val]
      (fun x i => fderiv ℝ u x (EuclideanSpace.single i 1)) :=
    hWeak.ae_eq (hasWeakGradient_of_contDiffOn_one Ω hu)
  have hforce : F =ᵐ[volume.restrict Ω.val] (fun x => ∑ i : Fin n,
      A (u x) (fderiv ℝ u x (EuclideanSpace.single i 1))
        (fderiv ℝ u x (EuclideanSpace.single i 1))) := by
    filter_upwards [hFormula, hDu] with x hx hdx
    rw [hx, hdx]
  have hcolumn (i : Fin n) : ContinuousOn
      (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) Ω.val :=
    (hu.continuousOn_fderiv_of_isOpen Ω.property le_rfl).clm_apply continuousOn_const
  refine ⟨?_, hforce, hEq.congr hDu hforce⟩
  apply continuousOn_finsetSum Finset.univ
  intro i _
  exact ((hA.comp_continuousOn hu.continuousOn).clm_apply (hcolumn i)).clm_apply (hcolumn i)

end HolderToCK
end
