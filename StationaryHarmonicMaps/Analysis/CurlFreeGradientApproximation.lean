module

public import HolderToCK.Analysis.GradientLinearAlgebra
public import HolderToCK.Analysis.ClassicalWeakGradient
public import HarmonicMaps.SobolevRestriction
public import HarmonicMaps.Analysis.SobolevAECongruence
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Actual primitives of smooth curl-free column fields

The literal finite column-linear-map field has symmetric Frechet derivative
when its original coordinate columns have zero curl. The convex-domain
Poincare theorem constructs an actual primitive. Its genuine derivative
recovers all original columns, and classical local Sobolev membership gives
actual finite native Sobolev graphs on every strictly interior ball.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- A smooth curl-free field has one actual smooth primitive and its genuine native Sobolev graph on every interior ball. -/
theorem exists_primitive_of_smooth_curl_free_ball {n q : ℕ}
    (a : Domain n) (R : ℝ) (G : Domain n → Gradient n q)
    (hG : ∀ i, ContDiff ℝ ∞ (fun x => G x i))
    (hcurl : ∀ x ∈ Metric.ball a R, ∀ i j : Fin n,
      fderiv ℝ (fun y => G y j) x (EuclideanSpace.single i 1) =
        fderiv ℝ (fun y => G y i) x (EuclideanSpace.single j 1)) :
    ∃ φ : Domain n → Ambient q,
      ContDiffOn ℝ ∞ φ (Metric.ball a R) ∧
      (∀ x ∈ Metric.ball a R, ∀ i : Fin n,
        fderiv ℝ φ x (EuclideanSpace.single i 1) = G x i) ∧
      ∀ r : ℝ, r < R → MemW12 (ballDomain a r) φ G := by
  let L (i : Fin n) : Ambient q →L[ℝ] (Domain n →L[ℝ] Ambient q) :=
    (ContinuousLinearMap.smulRightL ℝ (Domain n) (Ambient q))
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i)
  let W := fun x => ∑ i : Fin n, L i (G x i)
  have hW : ContDiff ℝ ∞ W := ContDiff.sum
    (fun i _ => (L i).contDiff.comp (hG i))
  have hsingle (x : Domain n) (j : Fin n) : W x (EuclideanSpace.single j 1) = G x j :=
    HolderToCK.columnLinearMap_single (G x) j
  have hcolumn (x : Domain n) (i j : Fin n) :
      fderiv ℝ W x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        fderiv ℝ (fun y => G y j) x (EuclideanSpace.single i 1) := by
    let E : (Domain n →L[ℝ] Ambient q) →L[ℝ] Ambient q :=
      ContinuousLinearMap.apply ℝ (Ambient q) (EuclideanSpace.single j 1)
    have hEq : E ∘ W = (fun y => G y j) := funext fun y => hsingle y j
    have H := (E.hasFDerivAt.comp x (hW.differentiable (by simp) x).hasFDerivAt).fderiv
    rw [hEq] at H
    exact (congrArg (fun T : Domain n →L[ℝ] Ambient q => T (EuclideanSpace.single i 1)) H).symm
  have hsymm (x : Domain n) (hx : x ∈ Metric.ball a R) (v w : Domain n) :
      fderiv ℝ W x v w = fderiv ℝ W x w v := by
    let B := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    have hb (i : Fin n) : B i = EuclideanSpace.single i 1 := by
      simp only [B,OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
    have H : fderiv ℝ W x = (fderiv ℝ W x).flip := by
      apply ContinuousLinearMap.coe_injective
      apply B.ext
      intro i
      apply ContinuousLinearMap.coe_injective
      apply B.ext
      intro j
      simp only [hb,ContinuousLinearMap.coe_coe,ContinuousLinearMap.flip_apply]
      rw [hcolumn,hcolumn]
      exact hcurl x hx i j
    exact congrArg (fun T : Domain n →L[ℝ] (Domain n →L[ℝ] Ambient q) => T v w) H
  obtain ⟨φ,hφ⟩ := (convex_ball a R).exists_forall_hasFDerivAt_of_fderiv_symmetric
    Metric.isOpen_ball (hW.differentiable (by simp)).differentiableOn hsymm
  have hderiv : EqOn (fderiv ℝ φ) W (Metric.ball a R) := fun x hx => (hφ x hx).fderiv
  have hsmooth : ContDiffOn ℝ ∞ φ (Metric.ball a R) := by
    apply (contDiffOn_infty_iff_fderiv_of_isOpen Metric.isOpen_ball).mpr
    refine ⟨fun x hx => (hφ x hx).differentiableAt.differentiableWithinAt,?_⟩
    exact hW.contDiffOn.congr hderiv
  have hcols (x : Domain n) (hx : x ∈ Metric.ball a R) (i : Fin n) :
      fderiv ℝ φ x (EuclideanSpace.single i 1) = G x i := by
    rw [hderiv hx]
    exact hsingle x i
  refine ⟨φ,hsmooth,hcols,?_⟩
  intro r hr
  have hlocal := HolderToCK.memW12Loc_of_contDiffOn_one (ballDomain a R)
    (hsmooth.of_le (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤)))
  have hfinite := hlocal.memW12_ball (Metric.closedBall_subset_ball hr)
  apply hfinite.congr_ae (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  funext i
  exact hcols x ((Metric.ball_subset_ball hr.le) hx) i

end StationaryHarmonicMaps.Analysis

end
