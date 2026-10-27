module

public import StationaryHarmonicMaps.Analysis.OneFormGaffney

/-!
# Closed normal two-tensor Gaffney estimate

The dual of a relative (n-2)-form is a closed antisymmetric two-tensor
with zero normal contraction. Closedness identifies the complete column
curl energy with the full coefficient gradient energy. Absorbing its exact
one-half factor gives the dimension-independent coefficient estimate.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual smooth closed antisymmetric normal two-tensors have full coefficient-gradient energy at most twice their codifferential energy. -/
theorem smooth_closed_normal_twoTensor_gaffney {n q : ℕ}
    (B : Fin n → Fin n → Domain n → Ambient q)
    (hB : ∀ i j, ContDiff ℝ ∞ (B i j))
    (hSkew : ∀ i j x, B i j x = -B j i x)
    (hClosed : ∀ i j k x,
      fderiv ℝ (B i j) x (EuclideanSpace.single k 1) +
        fderiv ℝ (B j k) x (EuclideanSpace.single i 1) +
        fderiv ℝ (B k i) x (EuclideanSpace.single j 1) = 0)
    (hNormal : ∀ j (x : Domain n), ‖x‖=1 → (∑ i : Fin n, x i • B i j x)=0) :
    let g := fun x : Domain n => ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n,
      ‖fderiv ℝ (B i j) x (EuclideanSpace.single k 1)‖^2
    let d := fun x : Domain n => ∑ j : Fin n,
      ‖∑ i : Fin n, fderiv ℝ (B i j) x (EuclideanSpace.single i 1)‖^2
    IntegrableOn g (ball (0 : Domain n) 1) volume ∧
      IntegrableOn d (ball (0 : Domain n) 1) volume ∧
      (∫ x in ball (0 : Domain n) 1, g x) ≤
        2*(∫ x in ball (0 : Domain n) 1, d x) := by
  intro g d
  let gj := fun (j : Fin n) (x : Domain n) => ∑ k : Fin n, ∑ i : Fin n,
    ‖fderiv ℝ (B i j) x (EuclideanSpace.single k 1)‖^2
  let cj := fun (j : Fin n) (x : Domain n) => ∑ k : Fin n, ∑ i : Fin n,
    ‖fderiv ℝ (B i j) x (EuclideanSpace.single k 1)-
      fderiv ℝ (B k j) x (EuclideanSpace.single i 1)‖^2
  let dj := fun (j : Fin n) (x : Domain n) =>
    ‖∑ i : Fin n, fderiv ℝ (B i j) x (EuclideanSpace.single i 1)‖^2
  have hG (j : Fin n) := smooth_normal_oneForm_gaffney (fun i=>B i j)
    (fun i=>hB i j) (hNormal j)
  have hgI : IntegrableOn g (ball (0 : Domain n) 1) volume :=
    integrable_finsetSum _ (fun j _=>(hG j).1)
  have hdI : IntegrableOn d (ball (0 : Domain n) 1) volume :=
    integrable_finsetSum _ (fun j _=>(hG j).2.2.1)
  have hDskew (i j : Fin n) (x v : Domain n) :
      fderiv ℝ (B i j) x v = -fderiv ℝ (B j i) x v := by
    have heq : B i j = fun y=> -B j i y := funext (hSkew i j)
    rw [heq]
    exact congrArg (fun L : Domain n →L[ℝ] Ambient q=>L v)
      (((hB j i).differentiable (by simp) x).hasFDerivAt.neg.fderiv)
  have hCurl (i j k : Fin n) (x : Domain n) :
      fderiv ℝ (B i j) x (EuclideanSpace.single k 1)-
        fderiv ℝ (B k j) x (EuclideanSpace.single i 1) =
          fderiv ℝ (B i k) x (EuclideanSpace.single j 1) := by
    have H := hClosed i j k x
    rw [hDskew j k,hDskew k i] at H
    exact sub_eq_zero.mp (show
      (fderiv ℝ (B i j) x (EuclideanSpace.single k 1)-
        fderiv ℝ (B k j) x (EuclideanSpace.single i 1)) -
          fderiv ℝ (B i k) x (EuclideanSpace.single j 1)=0 from by
      simpa only [sub_eq_add_neg] using H)
  have hCurlSum (x : Domain n) : (∑ j : Fin n, cj j x)=g x := by
    dsimp only [cj,g]
    simp_rw [hCurl]
    exact Finset.sum_comm
  have hsum : (∑ j : Fin n, ∫ x in ball (0 : Domain n) 1, gj j x) ≤
      (1/2:ℝ)*(∑ j : Fin n, ∫ x in ball (0 : Domain n) 1, cj j x) +
        ∑ j : Fin n, ∫ x in ball (0 : Domain n) 1, dj j x := by
    have H := Finset.sum_le_sum (s := Finset.univ) (fun j _=>(hG j).2.2.2)
    simpa only [Finset.sum_add_distrib,← Finset.mul_sum] using H
  have hIntG : (∑ j : Fin n, ∫ x in ball (0 : Domain n) 1, gj j x) =
      ∫ x in ball (0 : Domain n) 1, g x :=
    (integral_finsetSum _ (fun j _=>(hG j).1)).symm
  have hIntD : (∑ j : Fin n, ∫ x in ball (0 : Domain n) 1, dj j x) =
      ∫ x in ball (0 : Domain n) 1, d x :=
    (integral_finsetSum _ (fun j _=>(hG j).2.2.1)).symm
  have hIntC : (∑ j : Fin n, ∫ x in ball (0 : Domain n) 1, cj j x) =
      ∫ x in ball (0 : Domain n) 1, g x := by
    rw [← integral_finsetSum _ (fun j _=>(hG j).2.1)]
    exact integral_congr_ae (Eventually.of_forall hCurlSum)
  rw [hIntG,hIntC,hIntD] at hsum
  exact ⟨hgI,hdI,by linarith only [hsum]⟩

end StationaryHarmonicMaps.Analysis

end
