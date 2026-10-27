module

public import StationaryHarmonicMaps.Geometry.OrientationDeterminant
public import StationaryHarmonicMaps.Geometry.SkewMatrixPairing
public import StationaryHarmonicMaps.Geometry.OrthogonalFluxAlgebra
public import StationaryHarmonicMaps.Analysis.NaturalCoulombTests
public import StationaryHarmonicMaps.Analysis.SobolevLinearOperations
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Fixed right orthogonal corrections of native frames

Right multiplication preserves the actual gauged HS energy and conjugates
the actual connection. The reflection used for orientation has determinant
minus one when the target dimension is positive.
-/

public section

open HarmonicMaps MeasureTheory Filter
open scoped ContDiff Topology

namespace StationaryHarmonicMaps

/-- The actual encoded HS square is invariant under the real adjoint. -/
theorem encoded_norm_sq_star {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (T : Ambient q →L[ℝ] Ambient q) : ‖E (star T)‖ ^ 2 = ‖E T‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  rw [encoded_inner_star_right_eq_star_left E hE, star_star]

/-- A true orthogonal right factor preserves the full HS energy, not merely an operator-norm bound. -/
theorem encoded_norm_sq_mul_right_orthogonal {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (T H : Ambient q →L[ℝ] Ambient q) (hH : star H * H = 1) :
    ‖E (T * H)‖ ^ 2 = ‖E T‖ ^ 2 := by
  have hH' : star (star H) * star H = 1 := by
    rw [star_star]
    exact mul_star_eq_one_of_star_mul_eq_one H hH
  calc
    _ = ‖E (star (T * H))‖ ^ 2 := (encoded_norm_sq_star E hE _).symm
    _ = ‖E (star H * star T)‖ ^ 2 := by rw [star_mul]
    _ = ‖E (star T)‖ ^ 2 := encoded_norm_sq_mul_left_orthogonal E hE _ _ hH'
    _ = _ := encoded_norm_sq_star E hE _

/-- Positive-dimensional Euclidean space has an actual orthogonal reflection of determinant minus one. -/
theorem exists_orthogonal_reflection_det_neg_one {q : ℕ} (hq : 0 < q) :
    ∃ H : Ambient q →L[ℝ] Ambient q, star H * H = 1 ∧ H.det = -1 := by
  let j : Fin q := ⟨0, hq⟩
  let e : Ambient q := EuclideanSpace.single j 1
  have he : e ≠ 0 := by
    intro h
    have H : ‖e‖ = 1 := by simp only [e, PiLp.norm_single, norm_one]
    rw [h, norm_zero] at H
    norm_num at H
  let K : Submodule ℝ (Ambient q) := (Submodule.span ℝ {e})ᗮ
  let H : Ambient q →L[ℝ] Ambient q := K.reflection.toContinuousLinearMap
  have horth : star H * H = 1 :=
    H.isometry_iff_adjoint_comp_self.mp K.reflection.isometry
  refine ⟨H, horth, ?_⟩
  change LinearMap.det K.reflection.toLinearMap = -1
  rw [Submodule.det_reflection]
  have hspan : (Submodule.span ℝ {e})ᗮᗮ = Submodule.span ℝ {e} :=
    (Submodule.span ℝ {e}).orthogonal_orthogonal
  change (-1 : ℝ) ^ Module.finrank ℝ ((Submodule.span ℝ {e})ᗮᗮ) = -1
  rw [hspan, finrank_span_singleton he, pow_one]


/-- Moving a true right factor across the actual HS pairing introduces its adjoint. -/
theorem encoded_inner_mul_right_eq_adjoint {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (B T H : Ambient q →L[ℝ] Ambient q) :
    inner ℝ (E B) (E (T * H)) = inner ℝ (E (B * star H)) (E T) := by
  have hboth (U V : Ambient q →L[ℝ] Ambient q) :
      inner ℝ (E (star U)) (E (star V)) = inner ℝ (E U) (E V) := by
    rw [encoded_inner_star_right_eq_star_left E hE, star_star]
  calc
    _ = inner ℝ (E (star B)) (E (star (T * H))) := (hboth _ _).symm
    _ = inner ℝ (E (star B)) (E (star H * star T)) := by rw [star_mul]
    _ = inner ℝ (E (H * star B)) (E (star T)) := by
      rw [encoded_inner_mul_left_eq_adjoint E hE, star_star]
    _ = inner ℝ (E (star (H * star B))) (E T) :=
      encoded_inner_star_right_eq_star_left E hE _ _
    _ = _ := by rw [star_mul, star_star]

/-- Constant conjugation of a connection is dual to the inverse conjugation of the true test. -/
theorem encoded_inner_conjugate_eq {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (Z H T : Ambient q →L[ℝ] Ambient q) :
    inner ℝ (E (star H * Z * H)) (E T) = inner ℝ (E Z) (E (H * T * star H)) := by
  calc
    _ = inner ℝ (E T) (E ((star H * Z) * H)) := real_inner_comm _ _
    _ = inner ℝ (E (T * star H)) (E (star H * Z)) :=
      encoded_inner_mul_right_eq_adjoint E hE _ _ _
    _ = inner ℝ (E (H * (T * star H))) (E Z) := by
      rw [encoded_inner_mul_left_eq_adjoint E hE, star_star]
    _ = _ := by rw [real_inner_comm]; simp only [mul_assoc]

/-- Fixed actual right multiplication preserves the native graph, its original HS gradient and gauged energy. -/
theorem native_right_orthogonal_correction {n q : ℕ} {Ω : OpenDomain n}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀ T, R (E T) = T) (hER : ∀ z, E (R z) = z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
    (hp : MemW12 Ω p Dp)
    (horth : ∀ᵐ x ∂volume.restrict Ω.val, star (R (p x)) * R (p x) = 1)
    (H : Ambient q →L[ℝ] Ambient q) (hH : star H * H = 1) :
    let pH := fun x => E (R (p x) * H)
    let DpH := fun x i => E (R (Dp x i) * H)
    MemW12 Ω pH DpH ∧
      (∀ x, R (pH x) = R (p x) * H) ∧
      (∀ x i, R (DpH x i) = R (Dp x i) * H) ∧
      (∀ᵐ x ∂volume.restrict Ω.val, star (R (pH x)) * R (pH x) = 1) ∧
      (∀ x, hsNormSq (DpH x) = hsNormSq (Dp x)) ∧
      ∀ (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q)) (x : Domain n),
        hsNormSq (fun i => DpH x i + E (A x i * R (pH x))) =
          hsNormSq (fun i => Dp x i + E (A x i * R (p x))) := by
  intro pH DpH
  let M := ContinuousLinearMap.compL ℝ (Ambient q) (Ambient q) (Ambient q)
  let L : Ambient (q*q) →L[ℝ] Ambient (q*q) := E.comp ((M.flip H).comp R)
  have hL (z : Ambient (q*q)) : L z = E (R z * H) := rfl
  have hloc := Analysis.memW12Loc_continuousLinearMap hp.to_memW12Loc L
  have hW : MemW12 Ω pH DpH :=
    ⟨hloc.1, L.lipschitz.comp_memLp (map_zero L) hp.2.1,
      fun i => L.lipschitz.comp_memLp (map_zero L) (hp.2.2 i)⟩
  refine ⟨hW, fun x => hRE _, fun x i => hRE _, ?_, ?_, ?_⟩
  · filter_upwards [horth] with x hx
    change star (R (E (R (p x) * H))) * R (E (R (p x) * H)) = 1
    rw [hRE, star_mul]
    calc
      _ = star H * (star (R (p x)) * R (p x)) * H := by simp only [mul_assoc]
      _ = _ := by rw [hx, mul_one]; exact hH
  · intro x
    apply Finset.sum_congr rfl
    intro i _
    change ‖E (R (Dp x i) * H)‖ ^ 2 = ‖Dp x i‖ ^ 2
    rw [encoded_norm_sq_mul_right_orthogonal E hE _ _ hH, hER]
  · intro A x
    apply Finset.sum_congr rfl
    intro i _
    change ‖E (R (Dp x i) * H) + E (A x i * R (E (R (p x) * H)))‖ ^ 2 = _
    rw [hRE]
    have heq : E (R (Dp x i) * H) + E (A x i * (R (p x) * H)) =
        E ((R (Dp x i) + A x i * R (p x)) * H) := by
      rw [add_mul, map_add, mul_assoc]
    rw [heq, encoded_norm_sq_mul_right_orthogonal E hE _ _ hH, map_add, hER]


/-- Fixed right multiplication preserves every actual native natural-connection test through a genuine conjugate test graph. -/
theorem native_connection_tests_right_multiplication {n q : ℕ} {Ω : OpenDomain n}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀ T, R (E T) = T) (hER : ∀ z, E (R z) = z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
    (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q))
    (H : Ambient q →L[ℝ] Ambient q)
    (hNat : ∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
      MemW12 Ω ψ Dψ →
      IntegrableOn (fun x => ∑ i : Fin n, inner ℝ
        (E (star (R (p x)) * R (Dp x i) + star (R (p x)) * A x i * R (p x))) (Dψ x i)) Ω.val volume ∧
      (∫ x in Ω.val, ∑ i : Fin n, inner ℝ
        (E (star (R (p x)) * R (Dp x i) + star (R (p x)) * A x i * R (p x))) (Dψ x i)) = 0)
    (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)) (hψ : MemW12 Ω ψ Dψ) :
    let pH := fun x => E (R (p x) * H)
    let DpH := fun x i => E (R (Dp x i) * H)
    IntegrableOn (fun x => ∑ i : Fin n, inner ℝ
      (E (star (R (pH x)) * R (DpH x i) + star (R (pH x)) * A x i * R (pH x))) (Dψ x i)) Ω.val volume ∧
    (∫ x in Ω.val, ∑ i : Fin n, inner ℝ
      (E (star (R (pH x)) * R (DpH x i) + star (R (pH x)) * A x i * R (pH x))) (Dψ x i)) = 0 := by
  intro pH DpH
  let M := ContinuousLinearMap.compL ℝ (Ambient q) (Ambient q) (Ambient q)
  let K : Ambient (q*q) →L[ℝ] Ambient (q*q) := E.comp ((M.flip (star H)).comp ((M H).comp R))
  have hK (z : Ambient (q*q)) : K z = E (H * R z * star H) := rfl
  have hloc := Analysis.memW12Loc_continuousLinearMap hψ.to_memW12Loc K
  have hW : MemW12 Ω (fun x => K (ψ x)) (fun x i => K (Dψ x i)) :=
    ⟨hloc.1, K.lipschitz.comp_memLp (map_zero K) hψ.2.1,
      fun i => K.lipschitz.comp_memLp (map_zero K) (hψ.2.2 i)⟩
  obtain ⟨hI, hzero⟩ := hNat _ _ hW
  have hpair (x : Domain n) : (∑ i : Fin n, inner ℝ
      (E (star (R (pH x)) * R (DpH x i) + star (R (pH x)) * A x i * R (pH x))) (Dψ x i)) =
      ∑ i : Fin n, inner ℝ
        (E (star (R (p x)) * R (Dp x i) + star (R (p x)) * A x i * R (p x))) (K (Dψ x i)) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [pH, DpH]
    simp only [hRE, hK]
    have heq : star (R (p x) * H) * (R (Dp x i) * H) +
        star (R (p x) * H) * A x i * (R (p x) * H) =
        star H * (star (R (p x)) * R (Dp x i) + star (R (p x)) * A x i * R (p x)) * H := by
      simp only [star_mul, mul_add, add_mul, mul_assoc]
    rw [heq]
    simpa only [hER] using encoded_inner_conjugate_eq E hE
      (star (R (p x)) * R (Dp x i) + star (R (p x)) * A x i * R (p x)) H (R (Dψ x i))
  refine ⟨hI.congr (Eventually.of_forall fun x => (hpair x).symm), ?_⟩
  exact (integral_congr_ae (Eventually.of_forall hpair)).trans hzero

end StationaryHarmonicMaps

end
