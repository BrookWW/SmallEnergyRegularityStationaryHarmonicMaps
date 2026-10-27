module

public import StationaryHarmonicMaps.Analysis.SobolevOrthogonalFrame
public import StationaryHarmonicMaps.Analysis.WeakOperatorFluxTransform
public import StationaryHarmonicMaps.Geometry.OrthogonalFluxAlgebra

/-!
# The weak system in a genuine Sobolev orthogonal frame

The differentiated orthogonality identity is proved from the actual frame
map. Its product test then gives the transformed equation with the explicit
connection `P* dP + P* A P`. Existence of a Coulomb frame and identification
of this connection with a coexact field are separate obligations.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Actual Sobolev orthogonality and bounded product tests give the transformed signed system. -/
theorem weak_orthogonal_frame_system {n m q : ℕ} {Ω : OpenDomain n}
    {p : Domain n → Ambient m} {Dp : Domain n → Gradient n m}
    (hp : MemW12Loc Ω p Dp) {M : ℝ}
    (hb : ∀ᵐ x ∂volume.restrict Ω.val, ‖p x‖ ≤ M)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (horth : ∀ᵐ x ∂volume.restrict Ω.val, star (R (p x)) * R (p x) = 1)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (A : Domain n → Fin n → Ambient q →L[ℝ] Ambient q)
    (hEq : HolderToCK.WeakPoissonOn Ω Du (fun x => -(∑ i : Fin n, A x i (Du x i)))) :
    let E (x : Domain n) (i : Fin n) := star (R (p x)) (Du x i)
    let Z (x : Domain n) (i : Fin n) :=
      star (R (p x)) * R (Dp x i) + star (R (p x)) * A x i * R (p x)
    LocallyIntegrableOn (fun x => ∑ i : Fin n, Z x i (E x i)) Ω.val volume ∧
    ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Ω.val →
      IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (E x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) Ω.val volume ∧
      IntegrableOn (fun x => inner ℝ (∑ i : Fin n, Z x i (E x i)) (ψ x)) Ω.val volume ∧
      (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (E x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        ∫ x in Ω.val, inner ℝ (∑ i : Fin n, Z x i (E x i)) (ψ x) := by
  let J (x : Domain n) := star (R (p x)) (-(∑ i : Fin n, A x i (Du x i))) +
    ∑ i : Fin n, star (R (Dp x i)) (Du x i)
  let W (x : Domain n) := ∑ i : Fin n,
    (star (R (p x)) * R (Dp x i) + star (R (p x)) * A x i * R (p x))
      (star (R (p x)) (Du x i))
  have hdorth := ae_orthogonal_frame_derivative hp R M hb horth
  have hJ : J =ᵐ[volume.restrict Ω.val] (fun x => -(W x)) := by
    filter_upwards [horth, hdorth] with x hx hdx
    exact orthogonal_flux_forcing_identity (R (p x)) (fun i => R (Dp x i)) (A x)
      (Du x) (mul_star_eq_one_of_star_mul_eq_one _ hx) hdx
  have hnegJ : (fun x => -(J x)) =ᵐ[volume.restrict Ω.val] W := by
    filter_upwards [hJ] with x hx
    rw [hx, neg_neg]
  have hflux := weak_operator_flux_transform hp hb R hu hEq
  refine ⟨LocallyIntegrableOn.congr hnegJ hflux.1.neg, ?_⟩
  intro ψ hψ hcψ hsψ
  obtain ⟨hleft, hright, heq⟩ := hflux.2 ψ hψ hcψ hsψ
  have hinner : (fun x => inner ℝ (J x) (ψ x)) =ᵐ[volume.restrict Ω.val]
      (fun x => -(inner ℝ (W x) (ψ x))) := by
    filter_upwards [hJ] with x hx
    rw [hx, inner_neg_left]
  have hinnerNeg : (fun x => -(inner ℝ (J x) (ψ x))) =ᵐ[volume.restrict Ω.val]
      (fun x => inner ℝ (W x) (ψ x)) := by
    filter_upwards [hinner] with x hx
    rw [hx, neg_neg]
  refine ⟨hleft, hright.neg.congr hinnerNeg, ?_⟩
  calc
    _ = -(∫ x in Ω.val, inner ℝ (J x) (ψ x)) := heq
    _ = -(∫ x in Ω.val, -(inner ℝ (W x) (ψ x))) :=
      congrArg Neg.neg (integral_congr_ae hinner)
    _ = _ := by rw [integral_neg, neg_neg]

end StationaryHarmonicMaps.Analysis

end
