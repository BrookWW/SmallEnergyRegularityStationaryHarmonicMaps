module

public import StationaryHarmonicMaps.Foundation.TangentImage
public import HarmonicMaps.Sobolev

/-! # Weak harmonicity through map variations

The first variation pairs the same explicit weak gradient with compactly
supported C¹ ambient fields tangent along the target. Each pairing requires
integrability as well as a vanishing integral.
-/

@[expose] public section

open scoped Manifold ContDiff
open HarmonicMaps MeasureTheory Set

namespace StationaryHarmonicMaps

/-- The first-variation identity against compactly supported C¹ ambient tangent fields. -/
noncomputable def IsWeaklyHarmonicByTangentVariations {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) : Prop :=
  ∀ (V : Domain n × Ambient q → Ambient q) (_hV : ContDiff ℝ 1 V),
    HasCompactSupport V → tsupport V ⊆ Ω.val ×ˢ (Set.univ : Set (Ambient q)) →
    (∀ (x : Domain n) (p : N.Carrier), V (x, p.val) ∈ N.tangentImage p) →
      IntegrableOn (fun x =>
        ∑ i : Fin n, inner ℝ (Du x i)
          (fderiv ℝ V (x, u x) (EuclideanSpace.single i 1, Du x i))) Ω.val volume ∧
      (∫ x in Ω.val,
        ∑ i : Fin n, inner ℝ (Du x i)
          (fderiv ℝ V (x, u x) (EuclideanSpace.single i 1, Du x i))) = 0


end StationaryHarmonicMaps

end
