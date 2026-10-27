module

public import StationaryHarmonicMaps.Analysis.DivCurlKernelCancellation
public import StationaryHarmonicMaps.Analysis.SobolevLinearOperations
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Native zero-boundary tests for physical divergence-free vectors

The original scalar compact-test divergence equation is encoded in the
one-dimensional Euclidean target. The actual finite L2 pairing extends
that equation to the literal W0 graph, retaining the original vector field
and the original displayed test columns.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual scalar divergence tests extend to the first coordinate of every real native W0 graph. -/
theorem physical_divergence_free_zeroBoundary_test {n : ℕ} (Ω : OpenDomain n)
    (Z : Domain n → Domain n) (hZ : MemLp Z 2 (volume.restrict Ω.val))
    (hdiv : ∀ (η : Domain n → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ω.val →
      (∫ x in Ω.val,∑ i : Fin n,Z x i*fderiv ℝ η x (EuclideanSpace.single i 1))=0)
    {φ : Domain n → Ambient 1} {Dφ : Domain n → Gradient n 1}
    (hφ : HasZeroBoundaryValues Ω φ Dφ) :
    IntegrableOn (fun x => ∑ i : Fin n,Z x i*(Dφ x i) 0) Ω.val volume ∧
    (∫ x in Ω.val,∑ i : Fin n,Z x i*(Dφ x i) 0)=0 := by
  let e : Ambient 1 := EuclideanSpace.single 0 1
  let F : Domain n → Gradient n 1 := fun x i => Z x i • e
  let L (i : Fin n) : Domain n →ₗ[ℝ] Ambient 1 :=
    { toFun := fun z => z i • e
      map_add' := fun z w => by simp only [PiLp.add_apply,add_smul]
      map_smul' := fun c z => by simp only [PiLp.smul_apply,smul_smul]; rfl }
  have hF (i : Fin n) : MemLp (fun x => F x i) 2 (volume.restrict Ω.val) :=
    (L i).toContinuousLinearMap.lipschitz.comp_memLp (map_zero _) hZ
  have hInner (z : ℝ) (v : Ambient 1) : inner ℝ (z • e) v=z*v 0 := by
    simp only [real_inner_smul_left,e,EuclideanSpace.inner_single_left,map_one,one_mul]
  let l : Ambient 1 →ₗ[ℝ] ℝ :=
    { toFun := fun z => z 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let P : Ambient 1 →L[ℝ] ℝ := l.toContinuousLinearMap
  have hEq : ∀ (ψ : Domain n → Ambient 1),ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Ω.val →
      (∫ x in Ω.val,∑ i : Fin n,inner ℝ (F x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=0 := by
    intro ψ hψ hcψ hsψ
    let η : Domain n → ℝ := fun x => P (ψ x)
    have hη : ContDiff ℝ ∞ η := P.contDiff.comp hψ
    have hcη : HasCompactSupport η := hcψ.comp_left (map_zero P)
    have hsη : tsupport η ⊆ Ω.val := by
      apply Subset.trans _ hsψ
      apply closure_mono
      intro x hx hz
      exact hx (by change P (ψ x)=0; rw [hz,map_zero])
    have hDη (x : Domain n) (i : Fin n) :
        fderiv ℝ η x (EuclideanSpace.single i 1)=P (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
      have H := P.hasFDerivAt.comp x (hψ.differentiable (by simp) x).hasFDerivAt
      have hηEq : η=P ∘ ψ := by funext y; rfl
      rw [hηEq,H.fderiv]
      rfl
    have hPoint (x : Domain n) : (∑ i : Fin n,inner ℝ (F x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=
        ∑ i : Fin n,Z x i*fderiv ℝ η x (EuclideanSpace.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show F x i=Z x i • e from rfl,hInner,hDη]
      rfl
    rw [integral_congr_ae (Eventually.of_forall hPoint)]
    exact hdiv η hη hcη hsη
  have H := gradient_pairing_eq_on_zeroBoundary_of_smooth Ω F (fun _ _ => 0) hF
    (fun _ => MemLp.zero) (fun ψ hψ hc hs => by
      simpa only [inner_zero_left,Finset.sum_const_zero,integral_zero] using hEq ψ hψ hc hs) hφ
  have hPoint (x : Domain n) : (∑ i : Fin n,inner ℝ (F x i) (Dφ x i))=
      ∑ i : Fin n,Z x i*(Dφ x i) 0 := by
    apply Finset.sum_congr rfl
    intro i _
    exact hInner _ _
  refine ⟨H.1.congr (Eventually.of_forall hPoint),?_⟩
  rw [← integral_congr_ae (Eventually.of_forall hPoint),H.2.2]
  simp only [inner_zero_left,Finset.sum_const_zero,integral_zero]

end StationaryHarmonicMaps.Analysis

end
