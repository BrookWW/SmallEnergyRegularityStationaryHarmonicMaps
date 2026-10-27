module

public import HolderToCK.Foundation.WeakPoisson
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Reconstructing vector tests from scalar tests

Finite Euclidean coordinate expansion turns separated scalar and constant-vector
identities into the full vector-test identity. Both pairings retain their
integrability. The signed Poisson predicate uses the convention `Δu = F`.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem sum_coordinate_single {q : ℕ} (v : Ambient q) :
    (∑ j : Fin q, v j • EuclideanSpace.single j 1) = v := by
  simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun (Fin q) ℝ).sum_repr v

/-- Scalar tests paired with all constant vectors give every compact smooth vector test. -/
theorem vector_test_identity_of_separated {n q : ℕ} (Ω : OpenDomain n)
    (Du : Domain n → Gradient n q) (B : Domain n → Ambient q)
    (hsep : ∀ (η : Domain n → ℝ), ContDiff ℝ ∞ η →
      HasCompactSupport η → tsupport η ⊆ Ω.val → ∀ v : Ambient q,
      IntegrableOn (fun x => ∑ i : Fin n,
        inner ℝ (Du x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) Ω.val volume ∧
      IntegrableOn (fun x => η x * inner ℝ (B x) v) Ω.val volume ∧
      (∫ x in Ω.val, ∑ i : Fin n,
        inner ℝ (Du x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) =
        ∫ x in Ω.val, η x * inner ℝ (B x) v)
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Ω.val) :
    IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) Ω.val volume ∧
    IntegrableOn (fun x => inner ℝ (B x) (ψ x)) Ω.val volume ∧
    (∫ x in Ω.val, ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      ∫ x in Ω.val, inner ℝ (B x) (ψ x) := by
  let η (j : Fin q) (x : Domain n) : ℝ := ψ x j
  have hη (j : Fin q) : ContDiff ℝ ∞ (η j) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).contDiff.comp hψ
  have hcη (j : Fin q) : HasCompactSupport (η j) :=
    hcψ.comp_left (g := fun y : Ambient q => y j) rfl
  have htη (j : Fin q) : tsupport (η j) ⊆ tsupport ψ := by
    apply closure_mono
    intro x hx hz
    exact hx (by change ψ x j = 0; rw [hz]; rfl)
  have hsη (j : Fin q) : tsupport (η j) ⊆ Ω.val := (htη j).trans hsψ
  have hDη (j : Fin q) (x : Domain n) (a : Domain n) :
      fderiv ℝ (η j) x a = (fderiv ℝ ψ x a) j := by
    have H := ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).hasFDerivAt.comp x
      (hψ.differentiable (by simp) x).hasFDerivAt).fderiv
    exact congrArg (fun D : Domain n →L[ℝ] ℝ => D a) H
  let A (j : Fin q) (x : Domain n) := ∑ i : Fin n,
    inner ℝ (Du x i) (fderiv ℝ (η j) x (EuclideanSpace.single i 1) •
      EuclideanSpace.single j 1)
  let C (j : Fin q) (x : Domain n) := η j x * inner ℝ (B x) (EuclideanSpace.single j 1)
  have H (j : Fin q) := hsep (η j) (hη j) (hcη j) (hsη j) (EuclideanSpace.single j 1)
  have hA : IntegrableOn (fun x => ∑ j : Fin q, A j x) Ω.val volume :=
    integrable_finsetSum _ (fun j _ => (H j).1)
  have hC : IntegrableOn (fun x => ∑ j : Fin q, C j x) Ω.val volume :=
    integrable_finsetSum _ (fun j _ => (H j).2.1)
  have hAeq (x : Domain n) : (∑ j : Fin q, A j x) =
      ∑ i : Fin n, inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    dsimp only [A]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    simp_rw [hDη]
    rw [← inner_sum, sum_coordinate_single]
  have hCeq (x : Domain n) : (∑ j : Fin q, C j x) = inner ℝ (B x) (ψ x) := by
    dsimp only [C, η]
    simp_rw [← real_inner_smul_right]
    rw [← inner_sum, sum_coordinate_single]
  refine ⟨hA.congr (Filter.Eventually.of_forall hAeq),
    hC.congr (Filter.Eventually.of_forall hCeq), ?_⟩
  calc
    _ = ∫ x in Ω.val, ∑ j : Fin q, A j x :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => (hAeq x).symm)
    _ = ∑ j : Fin q, ∫ x in Ω.val, A j x :=
      integral_finsetSum _ (fun j _ => (H j).1)
    _ = ∑ j : Fin q, ∫ x in Ω.val, C j x :=
      Finset.sum_congr rfl (fun j _ => (H j).2.2)
    _ = ∫ x in Ω.val, ∑ j : Fin q, C j x :=
      (integral_finsetSum _ (fun j _ => (H j).2.1)).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hCeq)

/-- A positive-forcing separated identity is the signed equation `Δu = -B`. -/
theorem weakPoissonOn_neg_of_separated {n q : ℕ} (Ω : OpenDomain n)
    (Du : Domain n → Gradient n q) (B : Domain n → Ambient q)
    (hB : LocallyIntegrableOn B Ω.val volume)
    (hsep : ∀ (η : Domain n → ℝ), ContDiff ℝ ∞ η →
      HasCompactSupport η → tsupport η ⊆ Ω.val → ∀ v : Ambient q,
      IntegrableOn (fun x => ∑ i : Fin n,
        inner ℝ (Du x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) Ω.val volume ∧
      IntegrableOn (fun x => η x * inner ℝ (B x) v) Ω.val volume ∧
      (∫ x in Ω.val, ∑ i : Fin n,
        inner ℝ (Du x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) =
        ∫ x in Ω.val, η x * inner ℝ (B x) v) :
    HolderToCK.WeakPoissonOn Ω Du (fun x => -(B x)) := by
  refine ⟨hB.neg, ?_⟩
  intro ψ hψ hcψ hsψ
  obtain ⟨hA, hC, heq⟩ := vector_test_identity_of_separated Ω Du B hsep ψ hψ hcψ hsψ
  refine ⟨hA, ?_, ?_⟩
  · have hn : IntegrableOn (fun x => -(inner ℝ (B x) (ψ x))) Ω.val volume := hC.neg
    exact hn.congr (Filter.Eventually.of_forall fun x => (inner_neg_left (B x) (ψ x)).symm)
  · simpa only [inner_neg_left, integral_neg, neg_neg] using heq

end StationaryHarmonicMaps.Analysis

end
