module

public import HarmonicMaps.Analysis.VariableMollificationWeak
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Finite classical data for smooth boundary input

Smoothness on an open neighborhood of the closed source ball produces finite
L2 map, coordinate derivative and Laplacian data on the closed ball. The same
coordinate derivatives are the weak columns on the open ball.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff BigOperators

namespace HarmonicMaps

private theorem continuousOn_closedBall_memLp {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {f : Domain n → E} {R : ℝ}
    (hf : ContinuousOn f (Metric.closedBall (0 : Domain n) R)) :
    MemLp f 2 (volume.restrict (Metric.closedBall (0 : Domain n) R)) := by
  let K := Metric.closedBall (0 : Domain n) R
  have hK : IsCompact K := isCompact_closedBall _ _
  letI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hf).isBounded.exists_norm_le
  apply MemLp.of_bound
    (hf.aestronglyMeasurable_of_subset_isCompact hK hK.measurableSet Subset.rfl) C
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC _ (mem_image_of_mem f hx)

/-- The actual smooth input has finite classical graph and Laplacian data on
the closed source ball. No global smoothness assumption is used. -/
theorem dirichlet_smoothData_closedBall {n q : ℕ} (R : PositiveRadius)
    (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U) :
    MemLp m 2 (volume.restrict (Metric.closedBall 0 R.val)) ∧
    (∀ i : Fin n, MemLp (fun x => fderiv ℝ m x (EuclideanSpace.single i 1))
      2 (volume.restrict (Metric.closedBall 0 R.val))) ∧
    MemLp (fun x => ∑ i : Fin n,
      fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) 2
      (volume.restrict (Metric.closedBall 0 R.val)) ∧
    IntegrableOn (fun x => ∑ i : Fin n,
      fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) (Metric.closedBall 0 R.val) volume := by
  have hDm : ContDiffOn ℝ ∞ (fderiv ℝ m) U :=
    hm.fderiv_of_isOpen hU (by simp)
  have hcolumn (i : Fin n) :
      ContDiffOn ℝ ∞ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) U :=
    hDm.clm_apply contDiffOn_const
  have hsecond (i : Fin n) : ContinuousOn
      (fun x => fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) U :=
    ((hcolumn i).continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hLap : ContinuousOn (fun x => ∑ i : Fin n,
      fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) (Metric.closedBall 0 R.val) :=
    (continuousOn_finsetSum Finset.univ (fun i _ => hsecond i)).mono hclosed
  exact ⟨continuousOn_closedBall_memLp (hm.continuousOn.mono hclosed),
    fun i => continuousOn_closedBall_memLp ((hcolumn i).continuousOn.mono hclosed),
    continuousOn_closedBall_memLp hLap,
    hLap.integrableOn_compact (isCompact_closedBall _ _)⟩

/-- The actual classical coordinate columns of the smooth source input satisfy
the existing weak Sobolev definition on the open source ball. -/
theorem dirichlet_smoothData_memW12 {n q : ℕ} (R : PositiveRadius)
    (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U) :
    MemW12 (ballDomain (0 : Domain n) R.val) m
      (fun x i => fderiv ℝ m x (EuclideanSpace.single i 1)) := by
  obtain ⟨hm2, hDm2, _, _⟩ := dirichlet_smoothData_closedBall R U hU hclosed m hm
  have hmeasure : volume.restrict (Metric.ball (0 : Domain n) R.val) ≤
      volume.restrict (Metric.closedBall (0 : Domain n) R.val) :=
    Measure.restrict_mono_set volume Metric.ball_subset_closedBall
  apply memW12_ball_of_differentiableAt _ (fun _ _ _ => rfl)
    (hm2.mono_measure hmeasure) (fun i => (hDm2 i).mono_measure hmeasure)
  intro x hx
  exact (hm.contDiffAt (hU.mem_nhds (hclosed (Metric.ball_subset_closedBall hx)))).differentiableAt
    (by simp)

/-- The native Euclidean Laplacian is the sum of the same coordinate-column
second derivatives used in the finite classical data. -/
theorem dirichlet_smoothData_laplacian {n q : ℕ} (R : PositiveRadius)
    (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (x : Domain n) (hx : x ∈ Metric.closedBall (0 : Domain n) R.val) :
    Laplacian.laplacian m x = ∑ i : Fin n,
      fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  have hDm : ContDiffOn ℝ ∞ (fderiv ℝ m) U :=
    hm.fderiv_of_isOpen hU (by simp)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ m) x :=
    (hDm.contDiffAt (hU.mem_nhds (hclosed hx))).differentiableAt (by simp)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis m
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
    fderiv_clm_apply hdiff (differentiableAt_const _)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

end HarmonicMaps
