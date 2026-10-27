module

public import StationaryHarmonicMaps.Geometry.SphereTangentialDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The genuine sphere boundary term for normal one-forms

Differentiating the actual normal contraction along sphere tangents retains
the curvature contribution in the Gaffney divergence identity.
-/

public section

open HarmonicMaps Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps

/-- The derivative of the actual normal contraction is the ordinary finite product rule. -/
theorem normal_contraction_hasFDerivAt {n q : ℕ}
    (A : Fin n → Domain n → Ambient q) (x : Domain n)
    (hA : ∀ i, DifferentiableAt ℝ (A i) x) :
    HasFDerivAt (fun y : Domain n => ∑ i : Fin n, y i • A i y)
      (∑ i : Fin n, (x i • fderiv ℝ (A i) x +
        (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).smulRight (A i x))) x := by
  apply HasFDerivAt.fun_sum
  intro i _
  exact (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).hasFDerivAt.smul (hA i).hasFDerivAt

/-- Vanishing actual normal contraction gives the exact nonpositive Gaffney sphere flux. -/
theorem normal_oneForm_sphere_flux {n q : ℕ}
    (A : Fin n → Domain n → Ambient q)
    (hNormal : ∀ y : Domain n, ‖y‖=1 → (∑ i : Fin n, y i • A i y)=0)
    (x : Domain n) (hx : ‖x‖=1) (hA : ∀ i, DifferentiableAt ℝ (A i) x) :
    (∑ i : Fin n, x i * ∑ j : Fin n,
      (inner ℝ (A j x) (fderiv ℝ (A i) x (EuclideanSpace.single j 1)) -
        inner ℝ (A i x) (fderiv ℝ (A j) x (EuclideanSpace.single j 1)))) =
      -(∑ i : Fin n, ‖A i x‖^2) := by
  let H := fun y : Domain n => ∑ i : Fin n, y i • A i y
  let L := fderiv ℝ H x
  have hdH := normal_contraction_hasFDerivAt A x hA
  have hHL (v : Domain n) : L v = ∑ i : Fin n,
      (x i • fderiv ℝ (A i) x v + v i • A i x) := by
    have hh := congrArg (fun D : Domain n →L[ℝ] Ambient q => D v) hdH.fderiv
    simpa only [L,H,sum_apply,add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply] using hh
  have hLj (j : Fin n) : L (EuclideanSpace.single j 1) =
      (∑ i : Fin n, x i • fderiv ℝ (A i) x (EuclideanSpace.single j 1)) + A j x := by
    rw [hHL,Finset.sum_add_distrib]
    congr 1
    simp only [PiLp.single_apply,ite_smul,zero_smul,one_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hZeroSphere : ∀ y∈sphere (0 : Domain n) 1, H y=0 := by
    intro y hy
    exact hNormal y (by simpa only [mem_sphere,dist_zero_right] using hy)
  have hTang (j : Fin n) : L (EuclideanSpace.single j 1) = x j • L x := by
    have horth : inner ℝ x (EuclideanSpace.single j 1 - x j • x)=0 := by
      rw [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hx]
      simp only [EuclideanSpace.inner_single_right,conj_trivial,one_mul,one_pow,mul_one,sub_self]
    have hh := fderiv_eq_zero_of_zero_on_unitSphere H hZeroSphere x
      (EuclideanSpace.single j 1 - x j • x) hx horth hdH.differentiableAt
    change L (EuclideanSpace.single j 1 - x j • x)=0 at hh
    rw [map_sub,map_smul] at hh
    exact sub_eq_zero.mp hh
  have hFirst : (∑ i : Fin n, x i * ∑ j : Fin n,
      inner ℝ (A j x) (fderiv ℝ (A i) x (EuclideanSpace.single j 1))) =
      -(∑ i : Fin n, ‖A i x‖^2) := by
    calc
      _ = ∑ j : Fin n, inner ℝ (A j x)
          (∑ i : Fin n, x i • fderiv ℝ (A i) x (EuclideanSpace.single j 1)) := by
        simp only [inner_sum,inner_smul_right,Finset.mul_sum]
        exact Finset.sum_comm
      _ = ∑ j : Fin n, inner ℝ (A j x) (x j • L x - A j x) := by
        apply Finset.sum_congr rfl
        intro j _
        have hh := hLj j
        rw [hTang] at hh
        rw [eq_sub_iff_add_eq.mpr hh.symm]
      _ = inner ℝ (∑ j : Fin n, x j • A j x) (L x) - ∑ j : Fin n, ‖A j x‖^2 := by
        simp only [inner_sub_right,inner_smul_right,sum_inner,inner_smul_left,
          real_inner_self_eq_norm_sq,Finset.sum_sub_distrib,conj_trivial]
      _ = _ := by rw [hNormal x hx,inner_zero_left,zero_sub]
  have hSecond : (∑ i : Fin n, x i * ∑ j : Fin n,
      inner ℝ (A i x) (fderiv ℝ (A j) x (EuclideanSpace.single j 1))) = 0 := by
    calc
      _ = inner ℝ (∑ i : Fin n, x i • A i x)
          (∑ j : Fin n, fderiv ℝ (A j) x (EuclideanSpace.single j 1)) := by
        simp only [sum_inner,inner_smul_left,inner_sum,Finset.mul_sum,conj_trivial]
        exact Finset.sum_comm
      _ = 0 := by rw [hNormal x hx,inner_zero_left]
  simp only [Finset.sum_sub_distrib,mul_sub]
  rw [hFirst,hSecond,sub_zero]

end StationaryHarmonicMaps

end
