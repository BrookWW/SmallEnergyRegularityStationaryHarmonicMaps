module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual exponentials of skew-adjoint real operators

The Banach-algebra exponential is smooth on the entire operator carrier.
Its star identity and the actual inverse exponential give orthogonality
for every real parameter, including the zero-dimensional target. Spatial
bounds use the true Frechet derivative on a compact closed ball.
-/

public section

open HarmonicMaps Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps

/-- Exponentiating a true skew-adjoint operator gives both orthogonality identities. -/
theorem operator_exp_orthogonal_of_skew {q : ℕ}
    (S : Ambient q →L[ℝ] Ambient q) (hS : star S = -S) (t : ℝ) :
    star (NormedSpace.exp (t • S)) * NormedSpace.exp (t • S) = 1 ∧
      NormedSpace.exp (t • S) * star (NormedSpace.exp (t • S)) = 1 := by
  letI : NormedAlgebra ℚ (Ambient q →L[ℝ] Ambient q) :=
    .restrictScalars ℚ ℝ (Ambient q →L[ℝ] Ambient q)
  have hskew : t • S ∈ skewAdjoint (Ambient q →L[ℝ] Ambient q) := by
    rw [skewAdjoint.mem_iff]
    simp only [star_smul, star_trivial, hS, smul_neg]
  exact Unitary.mem_iff.mp (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hskew)

/-- The genuine noncommutative operator exponential is globally smooth. -/
theorem contDiff_operator_exp (q : ℕ) :
    ContDiff ℝ ∞ (NormedSpace.exp : (Ambient q →L[ℝ] Ambient q) → (Ambient q →L[ℝ] Ambient q)) := by
  have H : AnalyticOnNhd ℝ (NormedSpace.exp :
      (Ambient q →L[ℝ] Ambient q) → (Ambient q →L[ℝ] Ambient q)) univ :=
    fun x _ => NormedSpace.exp_analytic (𝕂 := ℝ) x
  exact H.contDiff

/-- The actual exponential field of a smooth operator field is smooth. -/
theorem contDiff_operator_exp_field {n q : ℕ}
    (S : Domain n → (Ambient q →L[ℝ] Ambient q)) (hS : ContDiff ℝ ∞ S) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => NormedSpace.exp (t • S x)) :=
  (contDiff_operator_exp q).comp (by
    convert (contDiff_const (c := t)).smul hS using 1
    funext x
    rfl)

/-- The time and domain variables form one actual smooth exponential field. -/
theorem contDiff_joint_operator_exp_field {n q : ℕ}
    (S : Domain n → (Ambient q →L[ℝ] Ambient q)) (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (fun z : ℝ × Domain n => NormedSpace.exp (z.1 • S z.2)) := by
  have ht : ContDiff ℝ ∞ (fun z : ℝ × Domain n => z.1) := contDiff_fst
  have hSz : ContDiff ℝ ∞ (fun z : ℝ × Domain n => S z.2) := hS.comp contDiff_snd
  apply (contDiff_operator_exp q).comp
  convert ht.smul hSz using 1
  funext z
  rfl

/-- A fixed operator generates a true differentiable exponential path. -/
theorem operator_exp_time_hasDerivAt {q : ℕ} (S : Ambient q →L[ℝ] Ambient q) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • S)) (NormedSpace.exp (t • S) * S) t :=
  hasDerivAt_exp_smul_const S t

/-- At zero the full noncommutative Frechet derivative is the identity. -/
theorem operator_exp_hasFDerivAt_zero (q : ℕ) :
    HasFDerivAt (NormedSpace.exp : (Ambient q →L[ℝ] Ambient q) → (Ambient q →L[ℝ] Ambient q))
      (ContinuousLinearMap.id ℝ (Ambient q →L[ℝ] Ambient q)) 0 :=
  hasFDerivAt_exp_zero

/-- The actual spatial derivative of a smooth exponential field is bounded on the closed unit ball. -/
theorem exists_operator_exp_field_derivative_bound {n q : ℕ}
    (S : Domain n → (Ambient q →L[ℝ] Ambient q)) (hS : ContDiff ℝ ∞ S) (t : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ Metric.closedBall (0 : Domain n) 1,
      ‖fderiv ℝ (fun y => NormedSpace.exp (t • S y)) x‖ ≤ K := by
  have hQ := contDiff_operator_exp_field S hS t
  have hD : ContDiff ℝ ∞ (fderiv ℝ (fun y => NormedSpace.exp (t • S y))) :=
    hQ.fderiv_right (m := ∞) (by simp)
  have hc : IsCompact (Metric.closedBall (0 : Domain n) 1) := isCompact_closedBall _ _
  letI : SeminormedAddGroup (Domain n →L[ℝ] (Ambient q →L[ℝ] Ambient q)) :=
    @SeminormedAddCommGroup.toSeminormedAddGroup _
      (@NormedAddCommGroup.toSeminormedAddCommGroup _ inferInstance)
  obtain ⟨K, hK⟩ := hc.exists_bound_of_continuousOn
    (f := fderiv ℝ (fun y => NormedSpace.exp (t • S y))) (by
      convert hD.continuous.continuousOn using 1)
  refine ⟨1 + |K|, by positivity, ?_⟩
  intro x hx
  have hKbound : K ≤ 1 + |K| := by linarith only [le_abs_self K]
  exact (hK x hx).trans hKbound

end StationaryHarmonicMaps

end
