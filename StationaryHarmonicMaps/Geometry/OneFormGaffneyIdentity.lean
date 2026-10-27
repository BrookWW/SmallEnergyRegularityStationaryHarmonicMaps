module

public import StationaryHarmonicMaps.Geometry.NormalOneFormBoundary
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Actual one-form divergence identities

The Hessian of each smooth coefficient is symmetric. The resulting
coordinate divergence cancels its second derivatives exactly. All sums use
the genuine Euclidean inner products and the full coefficient HS energy.
-/

public section

open HarmonicMaps Filter Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps

/-- The complete antisymmetric coefficient energy is the exact difference between full gradient energy and the transpose pairing. -/
theorem oneForm_curl_energy_identity {n q : ℕ} (D : Fin n → Fin n → Ambient q) :
    (∑ i : Fin n, ∑ j : Fin n, ‖D i j‖^2) -
      (1/2:ℝ)*(∑ i : Fin n, ∑ j : Fin n, ‖D i j-D j i‖^2) =
      ∑ i : Fin n, ∑ j : Fin n, inner ℝ (D i j) (D j i) := by
  simp only [norm_sub_sq_real,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  have hswap : (∑ i : Fin n, ∑ j : Fin n, ‖D j i‖^2) = ∑ i : Fin n, ∑ j : Fin n, ‖D i j‖^2 :=
    Finset.sum_comm
  rw [hswap]
  ring

/-- Actual mixed derivatives of a smooth vector-valued coefficient agree in the two coordinate orders. -/
theorem smooth_vector_mixed_fderiv {n q : ℕ} (f : Domain n → Ambient q)
    (hf : ContDiff ℝ ∞ f) (x : Domain n) (i j : Fin n) :
    fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) =
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  have hcol (k : Fin n) : fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single k 1)) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (EuclideanSpace.single k 1) := by
    simpa using ((hd.differentiable (by simp) x).hasFDerivAt.clm_apply
      (hasFDerivAt_const (EuclideanSpace.single k 1) x)).fderiv
  rw [hcol i,hcol j,ContinuousLinearMap.flip_apply,ContinuousLinearMap.flip_apply]
  have hs : IsSymmSndFDerivAt ℝ f x := hf.contDiffAt.isSymmSndFDerivAt (by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (by simpa only [Nat.cast_ofNat] using
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2) : (2:ℕ∞ω)≤∞))
  exact hs.eq _ _

/-- The true Gaffney coordinate field is smooth and has the exact full-gradient/curl/divergence identity. -/
theorem oneForm_gaffney_divergence_identity {n q : ℕ}
    (A : Fin n → Domain n → Ambient q) (hA : ∀ i, ContDiff ℝ ∞ (A i)) :
    let V := fun x : Domain n => WithLp.toLp 2 (fun i : Fin n => ∑ j : Fin n,
      (inner ℝ (A j x) (fderiv ℝ (A i) x (EuclideanSpace.single j 1)) -
        inner ℝ (A i x) (fderiv ℝ (A j) x (EuclideanSpace.single j 1))))
    ContDiff ℝ ∞ V ∧ ∀ x : Domain n,
      (∑ i : Fin n, (fderiv ℝ V x (EuclideanSpace.single i 1)) i) =
        (∑ i : Fin n, ∑ j : Fin n, ‖fderiv ℝ (A j) x (EuclideanSpace.single i 1)‖^2) -
        (1/2:ℝ)*(∑ i : Fin n, ∑ j : Fin n,
          ‖fderiv ℝ (A j) x (EuclideanSpace.single i 1)-
            fderiv ℝ (A i) x (EuclideanSpace.single j 1)‖^2) -
        ‖∑ i : Fin n, fderiv ℝ (A i) x (EuclideanSpace.single i 1)‖^2 := by
  intro V
  let D := fun (i j : Fin n) (x : Domain n) => fderiv ℝ (A j) x (EuclideanSpace.single i 1)
  have hD (i j : Fin n) : ContDiff ℝ ∞ (D i j) :=
    ((hA j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  let W := fun (i : Fin n) (x : Domain n) => ∑ j : Fin n,
    (inner ℝ (A j x) (D j i x)-inner ℝ (A i x) (D j j x))
  have hW (i : Fin n) : ContDiff ℝ ∞ (W i) :=
    ContDiff.sum (fun j _ => ((hA j).inner ℝ (hD j i)).sub ((hA i).inner ℝ (hD j j)))
  have hV : ContDiff ℝ ∞ V := by
    change ContDiff ℝ ∞ (fun x => WithLp.toLp 2 (fun i => W i x))
    exact ((contDiff_piLp 2).2 hW)
  refine ⟨hV,?_⟩
  intro x
  have hderW (i : Fin n) : fderiv ℝ (W i) x (EuclideanSpace.single i 1) =
      ∑ j : Fin n,
        ((inner ℝ (D i j x) (D j i x) +
          inner ℝ (A j x) (fderiv ℝ (D j i) x (EuclideanSpace.single i 1))) -
          (inner ℝ (D i i x) (D j j x) +
            inner ℝ (A i x) (fderiv ℝ (D j j) x (EuclideanSpace.single i 1)))) := by
    have hh := (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (((hA j).differentiable (by simp) x).hasFDerivAt.inner ℝ
        ((hD j i).differentiable (by simp) x).hasFDerivAt).sub
      (((hA i).differentiable (by simp) x).hasFDerivAt.inner ℝ
        ((hD j j).differentiable (by simp) x).hasFDerivAt))).fderiv
    have hhe := congrArg (fun L : Domain n →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hh
    simp only [W,D,Pi.sub_apply,sum_apply,sub_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,fderivInnerCLM_apply] at hhe ⊢
    convert hhe using 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hderV (i : Fin n) : (fderiv ℝ V x (EuclideanSpace.single i 1)) i =
      fderiv ℝ (W i) x (EuclideanSpace.single i 1) := by
    let π := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i
    have heq : W i = π ∘ V := rfl
    rw [heq,fderiv_comp x π.differentiableAt (hV.differentiable (by simp) x),π.fderiv]
    rfl
  have hcancel : (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ (A j x) (fderiv ℝ (D j i) x (EuclideanSpace.single i 1))) =
      ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (A i x) (fderiv ℝ (D j j) x (EuclideanSpace.single i 1)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [show fderiv ℝ (D j i) x (EuclideanSpace.single i 1) =
      fderiv ℝ (D i i) x (EuclideanSpace.single j 1) from smooth_vector_mixed_fderiv (A i) (hA i) x j i]
  have hdiv : (∑ i : Fin n, ∑ j : Fin n, inner ℝ (D i i x) (D j j x)) =
      ‖∑ i : Fin n, D i i x‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner,inner_sum]
    exact Finset.sum_comm
  simp_rw [hderV,hderW]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [hcancel,hdiv,← oneForm_curl_energy_identity (fun i j => D i j x)]
  dsimp only [D]
  ring

end StationaryHarmonicMaps

end
