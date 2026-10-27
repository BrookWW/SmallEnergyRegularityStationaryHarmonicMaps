/- Copyright (c) 2026. All rights reserved. -/
module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Alternating coefficients for the logarithmic derivative of a frame

The literal skew part of the encoded logarithmic product is a genuine
continuous bilinear map. It is alternating on its whole carrier and its
decoded values are skew. Differentiated orthogonality identifies it with
the original logarithmic derivative without a separate skew premise.
-/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps.Geometry

/-- The actual alternating continuous bilinear coefficient of the encoded
logarithmic product. -/
@[expose] noncomputable def skewLogarithmicAlternation {m k q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient k)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q)) :
    Ambient m →L[ℝ] (Ambient m →L[ℝ] Ambient k) := by
  let J := (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).toContinuousLinearMap.comp R
  let M := ContinuousLinearMap.compL ℝ (Ambient q) (Ambient q) (Ambient q)
  let L₀ : Ambient m →ₗ[ℝ] (Ambient m →L[ℝ] Ambient k) :=
    { toFun := fun z=>E.comp ((M (J z)).comp R)
      map_add' := by
        intro z w
        apply ContinuousLinearMap.ext
        intro v
        change E (J (z+w)*R v)=E (J z*R v)+E (J w*R v)
        rw [map_add,add_mul,map_add]
      map_smul' := by
        intro c z
        apply ContinuousLinearMap.ext
        intro v
        change E (J (c • z)*R v)=c • E (J z*R v)
        rw [map_smul]
        change E ((c • J z).comp (R v))=c • E ((J z).comp (R v))
        rw [ContinuousLinearMap.smul_comp,map_smul] }
  let L := L₀.toContinuousLinearMap
  exact (1/2:ℝ) • (L-L.flip)

/-- The coefficient acts by the literal half-difference of the two
adjoint products. -/
theorem skewLogarithmicAlternation_apply {m k q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient k)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (z w : Ambient m) :
    skewLogarithmicAlternation E R z w=
      E ((1/2:ℝ) • (star (R z)*R w-star (R w)*R z)) := by
  change (1/2:ℝ) • (E (star (R z)*R w)-E (star (R w)*R z))=_
  rw [map_smul,map_sub]

/-- The genuine bilinear coefficient is alternating for every vector. -/
theorem skewLogarithmicAlternation_self {m k q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient k)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q)) (z : Ambient m) :
    skewLogarithmicAlternation E R z z=0 := by
  rw [skewLogarithmicAlternation_apply,sub_self,smul_zero,map_zero]

/-- Exchanging the two coefficient arguments reverses its sign. -/
theorem skewLogarithmicAlternation_swap {m k q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient k)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q)) (z w : Ambient m) :
    skewLogarithmicAlternation E R z w= -skewLogarithmicAlternation E R w z := by
  rw [skewLogarithmicAlternation_apply,skewLogarithmicAlternation_apply,← map_neg]
  congr 1
  module

/-- Every decoded value lies in the actual skew operator space. -/
theorem skewLogarithmicAlternation_range_skew {m q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient m)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (z w : Ambient m) :
    star (R (skewLogarithmicAlternation E R z w))=
      -R (skewLogarithmicAlternation E R z w) := by
  have hStarSub (T U : Ambient q →L[ℝ] Ambient q) : star (T-U)=star T-star U := by
    change ContinuousLinearMap.adjoint (T-U)=star T-star U
    rw [map_sub]
    rfl
  rw [skewLogarithmicAlternation_apply,hRE,star_smul,star_trivial,
    hStarSub,star_mul,star_mul,star_star,star_star]
  module

/-- Differentiated orthogonality identifies the alternating coefficient
with the original encoded logarithmic product. -/
theorem skewLogarithmicAlternation_eq_logarithmic_of_constraint {m k q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient k)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q)) (z w : Ambient m)
    (hDerivative : star (R w)*R z+star (R z)*R w=0) :
    skewLogarithmicAlternation E R z w=E (star (R z)*R w) := by
  have H : star (R w)*R z= -(star (R z)*R w) := eq_neg_of_add_eq_zero_left hDerivative
  rw [skewLogarithmicAlternation_apply,H]
  congr 1
  module

/-- At the encoded identity, every genuine skew direction is recovered
exactly by the alternating coefficient. -/
theorem skewLogarithmicAlternation_identity_left {m q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient m)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T)
    (S : Ambient q →L[ℝ] Ambient q) (hS : star S= -S) :
    skewLogarithmicAlternation E R (E 1) (E S)=E S := by
  rw [skewLogarithmicAlternation_apply,hRE,hRE,star_one,one_mul,mul_one,hS]
  congr 1
  module

end StationaryHarmonicMaps.Geometry

end
