module

public import HolderToCK.Analysis.ClassicalPoisson
public import HolderToCK.Analysis.WeakPoissonLocality
public import HarmonicMaps.SobolevLemmas
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Classical equations from the same weak Poisson data

Uniqueness of the native weak gradient identifies the actual classical columns.
The forcing is then unique almost everywhere. Continuity upgrades that equality
to the pointwise equation on the original open domain.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK

theorem WeakPoissonOn.laplacian_ae_eq_of_contDiffOn_two {n q : ℕ} {Ω : OpenDomain n}
    {u F : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hEq : WeakPoissonOn Ω Du F) (hWeak : HasWeakGradient Ω u Du)
    (hu : ContDiffOn ℝ 2 u Ω.val) :
    Laplacian.laplacian u =ᵐ[volume.restrict Ω.val] F := by
  have hClassical : HasWeakGradient Ω u
      (fun x i => fderiv ℝ u x (EuclideanSpace.single i 1)) :=
    hasWeakGradient_of_contDiffOn_one Ω (hu.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))
  have hEqClassical := hEq.congr (hWeak.ae_eq hClassical) (Filter.Eventually.of_forall fun _ => rfl)
  exact (weakPoissonOn_of_contDiffOn_two Ω hu).ae_eq_forcing hEqClassical

theorem WeakPoissonOn.laplacian_eq_of_contDiffOn_two {n q : ℕ} {Ω : OpenDomain n}
    {u F : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hEq : WeakPoissonOn Ω Du F) (hWeak : HasWeakGradient Ω u Du)
    (hu : ContDiffOn ℝ 2 u Ω.val) (hF : ContinuousOn F Ω.val) :
    ∀ x ∈ Ω.val, Laplacian.laplacian u x = F x := by
  have hEqOn := Measure.eqOn_open_of_ae_eq (hEq.laplacian_ae_eq_of_contDiffOn_two hWeak hu)
    Ω.property (continuousOn_laplacian_of_contDiffOn_two Ω hu) hF
  exact fun _ hx => hEqOn hx

theorem weakPoissonOn_of_contDiffOn_two_of_laplacian_eq {n q : ℕ} (Ω : OpenDomain n)
    {u F : Domain n → Ambient q} (hu : ContDiffOn ℝ 2 u Ω.val)
    (hEq : ∀ x ∈ Ω.val, Laplacian.laplacian u x = F x) :
    WeakPoissonOn Ω (fun x i => fderiv ℝ u x (EuclideanSpace.single i 1)) F := by
  apply (weakPoissonOn_of_contDiffOn_two Ω hu).congr (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [ae_restrict_mem Ω.property.measurableSet] with x hx
  exact hEq x hx

end HolderToCK
end
