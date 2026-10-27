module

public import StationaryHarmonicMaps.Geometry.GaugedEnergyAlgebra
public import StationaryHarmonicMaps.Analysis.OrthogonalOperatorBounds
public import HarmonicMaps.Analysis.VariableMollificationMatrix

/-!
# Full HS invariance under an actual orthogonal right factor

The true sharp right-composition HS estimate and the actual operator norm
bound one give one inequality. The actual orthogonal inverse gives the
reverse inequality on the same complete coefficient carrier.
-/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps

/-- Right multiplication by an actual orthogonal operator preserves the genuine full encoded HS square, including zero dimension. -/
theorem encoded_norm_sq_mul_right_orthogonal {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖^2=∑ j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (T P : Ambient q →L[ℝ] Ambient q) (hP : star P*P=1) :
    ‖E (T*P)‖^2=‖E T‖^2 := by
  have hRight (A Q : Ambient q →L[ℝ] Ambient q) (hQ : star Q*Q=1) :
      ‖E (A*Q)‖^2≤‖E A‖^2 := by
    have hCols (i : Fin q) :
        (∑ j : Fin q,(Q (EuclideanSpace.single i 1)) j • A (EuclideanSpace.single j 1))=
        (A*Q) (EuclideanSpace.single i 1) := by
      have H := congrArg A ((EuclideanSpace.basisFun (Fin q) ℝ).sum_repr (Q (EuclideanSpace.single i 1)))
      simpa only [map_sum,map_smul,EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,mul_apply_eq_comp] using H
    have H := hsNormSq_right_comp_le_of_norm_le
      (fun j => A (EuclideanSpace.single j 1)) Q (Analysis.orthogonal_opNorm_le_one Q hQ)
    simpa only [hCols,hsNormSq,← hE (A*Q),← hE A,one_pow,one_mul] using H
  have hPInverse : P*star P=1 := mul_star_eq_one_of_star_mul_eq_one P hP
  have hStarOrth : star (star P)*star P=1 := by rw [star_star];exact hPInverse
  apply le_antisymm (hRight T P hP)
  have H := hRight (T*P) (star P) hStarOrth
  simpa only [mul_assoc,hPInverse,mul_one] using H

end StationaryHarmonicMaps

end
