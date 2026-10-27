module

public import HarmonicMaps.Geometry.TargetNearestPoint
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Normality of actual nearest points

The squared ambient distance has a minimum in the true target chart. Its
derivative vanishes in every intrinsic tangent direction, so the displacement
from a nearest point is orthogonal to the differential of the actual inclusion.
-/

public section

open Filter Topology
open scoped Manifold ContDiff

namespace HarmonicMaps.CompactSmoothEmbeddedTarget

/-- Actual distance minimizers have normal displacement in every tangent direction. -/
theorem nearest_point_normal {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (z : EuclideanSpace ℝ (Fin q)) (p : N.Carrier)
    (hp : ∀ r : N.Carrier, dist z p.val ≤ dist z r.val)
    (v : EuclideanSpace ℝ (Fin N.dimension)) :
    inner ℝ (z - p.val)
      ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
        𝓘(ℝ, EuclideanSpace ℝ (Fin q))
        (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p) v) = 0 := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin q))
  let e := extChartAt I p
  let a := e p
  let g : EuclideanSpace ℝ (Fin N.dimension) → EuclideanSpace ℝ (Fin q) :=
    fun x => (e.symm x).val
  let A := mfderiv I J (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p
  have hgp : g a = p.val := by
    exact congrArg Subtype.val (extChartAt_to_inv (I := I) p)
  have hm : MDifferentiableAt I J
      (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p :=
    N.isSmoothEmbedding.contMDiff.mdifferentiableAt (by simp)
  have hg : HasFDerivAt g A a := by
    have h := hm.hasMFDerivAt.2
    simpa only [I, J, g, A, a, e, writtenInExtChartAt, mfld_simps,
      hasFDerivWithinAt_univ, Function.comp_def] using h
  have hmin : IsLocalMin (fun x => ‖z - g x‖ ^ 2) a := by
    apply Filter.Eventually.of_forall
    intro x
    change ‖z - g a‖ ^ 2 ≤ ‖z - g x‖ ^ 2
    rw [hgp]
    exact pow_le_pow_left₀ (norm_nonneg _) (by
      simpa only [dist_eq_norm, g] using hp (e.symm x)) 2
  have hsq := ((hasFDerivAt_const z a).sub hg).norm_sq
  have hz := congrArg (fun L => L v) (hmin.hasFDerivAt_eq_zero hsq)
  simp only [smul_apply, ContinuousLinearMap.comp_apply, zero_apply,
    Pi.sub_apply, innerSL_apply_apply, neg_apply, zero_sub, inner_neg_right,
    hgp, nsmul_eq_mul, Nat.cast_ofNat] at hz
  exact neg_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left two_ne_zero)

/-- Compactness produces a genuine nearest point and its full normality condition. -/
theorem exists_nearest_point_normal {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (z : EuclideanSpace ℝ (Fin q)) :
    ∃ p : N.Carrier, dist z p.val = Metric.infDist z N.carrierSet ∧
      (∀ r : N.Carrier, dist z p.val ≤ dist z r.val) ∧
      ∀ v : EuclideanSpace ℝ (Fin N.dimension),
        inner ℝ (z - p.val)
          ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
            𝓘(ℝ, EuclideanSpace ℝ (Fin q))
            (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p) v) = 0 := by
  obtain ⟨p, heq, hp⟩ := N.exists_nearest_point z
  exact ⟨p, heq, hp, fun v => N.nearest_point_normal z p hp v⟩

end HarmonicMaps.CompactSmoothEmbeddedTarget

end
