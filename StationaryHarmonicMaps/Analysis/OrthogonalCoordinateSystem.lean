module

public import StationaryHarmonicMaps.Analysis.OrthogonalCoefficientBounds
public import StationaryHarmonicMaps.Analysis.SobolevOrthogonalFlux

/-!
# Weak frame systems in faithful matrix coordinates

Orthogonality itself supplies the essential bound through the genuine
coefficient encoder and decoder. The transformed equation therefore needs
no separate boundedness premise for the Sobolev frame coordinates.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Faithful HS coordinates turn an actual Sobolev orthogonal frame into the transformed system. -/
theorem weak_orthogonal_coordinate_system {n q : ℕ} {Ω : OpenDomain n}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q))
    (R : Ambient (q * q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀ z, E (R z) = z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    {p : Domain n → Ambient (q * q)} {Dp : Domain n → Gradient n (q * q)}
    (hp : MemW12Loc Ω p Dp)
    (horth : ∀ᵐ x ∂volume.restrict Ω.val, star (R (p x)) * R (p x) = 1)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (A : Domain n → Fin n → Ambient q →L[ℝ] Ambient q)
    (hEq : HolderToCK.WeakPoissonOn Ω Du (fun x => -(∑ i : Fin n, A x i (Du x i)))) :
    let F (x : Domain n) (i : Fin n) := star (R (p x)) (Du x i)
    let Z (x : Domain n) (i : Fin n) :=
      star (R (p x)) * R (Dp x i) + star (R (p x)) * A x i * R (p x)
    LocallyIntegrableOn (fun x => ∑ i : Fin n, Z x i (F x i)) Ω.val volume ∧
    ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Ω.val →
      IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (F x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) Ω.val volume ∧
      IntegrableOn (fun x => inner ℝ (∑ i : Fin n, Z x i (F x i)) (ψ x)) Ω.val volume ∧
      (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (F x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        ∫ x in Ω.val, inner ℝ (∑ i : Fin n, Z x i (F x i)) (ψ x) :=
  weak_orthogonal_frame_system hp (ae_orthogonal_coordinates_bound E R hER hE p horth)
    R horth hu A hEq

end StationaryHarmonicMaps.Analysis

end
