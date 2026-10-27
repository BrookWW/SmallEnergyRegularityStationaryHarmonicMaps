module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Derivatives of smooth harmonic maps

The Laplacian commutes with a classical coordinate derivative on an open
smoothness carrier. Third derivative symmetry supplies the commutation.
-/

public section

open Set Filter
open scoped ContDiff BigOperators Topology

namespace HarmonicMaps

private theorem two_le_infty : (2 : ℕ∞ω) ≤ ∞ :=
  le_of_lt (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top (2 : ℕ)))

private theorem init_vec3 {E : Type*} (a b c : E) :
    Fin.init ![a, b, c] = ![a, b] := by
  funext i
  fin_cases i <;> rfl

private theorem last_vec3 {E : Type*} (a b c : E) :
    (![a, b, c] : Fin 3 → E) (Fin.last 2) = c := rfl

private theorem tail_vec3 {E : Type*} (a b c : E) :
    Fin.tail ![a, b, c] = ![b, c] := by
  funext i
  fin_cases i <;> rfl

private theorem thirdDerivative_swap_last {n q : ℕ}
    (W : Set (Domain n)) (hW : IsOpen W)
    (f : Domain n → Ambient q) (hf : ContDiffOn ℝ ∞ f W)
    (x : Domain n) (hx : x ∈ W) (a b c : Domain n) :
    iteratedFDeriv ℝ 3 f x ![a, b, c] =
      iteratedFDeriv ℝ 3 f x ![a, c, b] := by
  have hAt : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hW.mem_nhds hx)
  have hD2 : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 f) x :=
    hAt.differentiableAt_iteratedFDeriv
      (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top (2 : ℕ)))
  have hsym (y : Domain n) (hy : y ∈ W) :
      iteratedFDeriv ℝ 2 f y ![b, c] =
        iteratedFDeriv ℝ 2 f y ![c, b] :=
    ((hf.contDiffAt (hW.mem_nhds hy)).isSymmSndFDerivAt
      (by simpa only [minSmoothness_of_isRCLikeNormedField] using two_le_infty)).iteratedFDeriv_cons
  have hev : (fun y => iteratedFDeriv ℝ 2 f y ![b, c]) =ᶠ[𝓝 x]
      (fun y => iteratedFDeriv ℝ 2 f y ![c, b]) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact hsym y hy
  have hleft := hD2.iteratedFDeriv_succ_apply_left'
    (m := ![a, b, c])
  have hright := hD2.iteratedFDeriv_succ_apply_left'
    (m := ![a, c, b])
  simpa only [Fin.tail_cons, Matrix.cons_val_zero] using
    hleft.trans ((congrArg (fun L : Domain n →L[ℝ] Ambient q => L a)
      hev.fderiv_eq).trans hright.symm)

private theorem thirdDerivative_swap_first {n q : ℕ}
    (W : Set (Domain n)) (hW : IsOpen W)
    (f : Domain n → Ambient q) (hf : ContDiffOn ℝ ∞ f W)
    (x : Domain n) (hx : x ∈ W) (a b c : Domain n) :
    iteratedFDeriv ℝ 3 f x ![a, b, c] =
      iteratedFDeriv ℝ 3 f x ![b, a, c] := by
  have hDfOn : ContDiffOn ℝ ∞ (fderiv ℝ f) W :=
    hf.fderiv_of_isOpen hW (by simp)
  have hDfAt : ContDiffAt ℝ ∞ (fderiv ℝ f) x :=
    hDfOn.contDiffAt (hW.mem_nhds hx)
  have hsym := (hDfAt.isSymmSndFDerivAt
    (by simpa only [minSmoothness_of_isRCLikeNormedField] using two_le_infty)).iteratedFDeriv_cons
    (v := a) (w := b)
  have h := congrArg (fun L : Domain n →L[ℝ] Ambient q => L c) hsym
  have hleft := iteratedFDeriv_succ_apply_right
    (𝕜 := ℝ)
    (f := f) (x := x) (n := 2) (m := ![a, b, c])
  have hright := iteratedFDeriv_succ_apply_right
    (𝕜 := ℝ)
    (f := f) (x := x) (n := 2) (m := ![b, a, c])
  simp only [init_vec3, last_vec3, Nat.reduceAdd] at hleft hright
  exact hleft.trans (h.trans hright.symm)

private theorem laplacian_fderiv_apply {n q : ℕ}
    (W : Set (Domain n)) (hW : IsOpen W)
    (f : Domain n → Ambient q) (hf : ContDiffOn ℝ ∞ f W)
    (x : Domain n) (hx : x ∈ W) (v : Domain n) :
    Laplacian.laplacian (fun z => fderiv ℝ f z v) x =
      fderiv ℝ (Laplacian.laplacian f) x v := by
  let basis := EuclideanSpace.basisFun (Fin n) ℝ
  let L : (Domain n →L[ℝ] Ambient q) →L[ℝ] Ambient q :=
    ContinuousLinearMap.apply ℝ (Ambient q) v
  have hAt : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hW.mem_nhds hx)
  have hDfOn : ContDiffOn ℝ ∞ (fderiv ℝ f) W :=
    hf.fderiv_of_isOpen hW (by simp)
  have hDfAt : ContDiffAt ℝ ∞ (fderiv ℝ f) x :=
    hDfOn.contDiffAt (hW.mem_nhds hx)
  have hDiff2 : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 f) x :=
    hAt.differentiableAt_iteratedFDeriv
      (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top (2 : ℕ)))
  have hleft : Laplacian.laplacian (fun z => fderiv ℝ f z v) x =
      ∑ j : Fin n, iteratedFDeriv ℝ 3 f x
        ![basis j, basis j, v] := by
    have hLap := (hDfAt.of_le two_le_infty).laplacian_CLM_comp_left (l := L)
    change Laplacian.laplacian (fun z => fderiv ℝ f z v) x =
      L (Laplacian.laplacian (fderiv ℝ f) x) at hLap
    rw [hLap, InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (fderiv ℝ f) basis]
    simp only [L, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hright := iteratedFDeriv_succ_apply_right
      (𝕜 := ℝ)
      (f := f) (x := x) (n := 2)
      (m := ![basis j, basis j, v])
    simpa only [L, ContinuousLinearMap.apply_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      init_vec3, last_vec3, Nat.reduceAdd] using hright.symm
  have hright : fderiv ℝ (Laplacian.laplacian f) x v =
      ∑ j : Fin n, iteratedFDeriv ℝ 3 f x
        ![v, basis j, basis j] := by
    have hrep : Laplacian.laplacian f =
        fun z => ∑ j : Fin n, iteratedFDeriv ℝ 2 f z
          ![basis j, basis j] :=
      InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f basis
    rw [hrep, fderiv_fun_sum]
    · have hsum :
          (∑ j : Fin n, fderiv ℝ
            (fun z => iteratedFDeriv ℝ 2 f z ![basis j, basis j]) x) v =
          ∑ j : Fin n, (fderiv ℝ
            (fun z => iteratedFDeriv ℝ 2 f z ![basis j, basis j]) x) v := by
          let ev : (Domain n →L[ℝ] Ambient q) →L[ℝ] Ambient q :=
            ContinuousLinearMap.apply ℝ (Ambient q) v
          change ev (∑ j : Fin n, fderiv ℝ
            (fun z => iteratedFDeriv ℝ 2 f z ![basis j, basis j]) x) = _
          rw [map_sum]
          rfl
      rw [hsum]
      apply Finset.sum_congr rfl
      intro j _
      have hleft3 := hDiff2.iteratedFDeriv_succ_apply_left'
        (m := ![v, basis j, basis j])
      simpa only [tail_vec3, Matrix.cons_val_zero, Nat.reduceAdd] using
        hleft3.symm
    · intro j _
      exact hDiff2.continuousMultilinear_apply_const ![basis j, basis j]
  rw [hleft, hright]
  apply Finset.sum_congr rfl
  intro j _
  exact (thirdDerivative_swap_last W hW f hf x hx
    (basis j) (basis j) v).trans
      (thirdDerivative_swap_first W hW f hf x hx
        (basis j) v (basis j))

/-- Each classical coordinate derivative of a smooth harmonic map is smooth
and harmonic on the same open carrier. -/
theorem harmonic_fderiv_column {n q : ℕ}
    (W : Set (Domain n)) (hW : IsOpen W)
    (f : Domain n → Ambient q) (hf : ContDiffOn ℝ ∞ f W)
    (hh : ∀ x ∈ W, Laplacian.laplacian f x = 0)
    (i : Fin n) :
    ContDiffOn ℝ ∞
      (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) W ∧
    ∀ x ∈ W, Laplacian.laplacian
      (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x = 0 := by
  have hsmooth : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) W :=
    (hf.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
  refine ⟨hsmooth, ?_⟩
  intro x hx
  rw [laplacian_fderiv_apply W hW f hf x hx]
  have hlocal : Laplacian.laplacian f =ᶠ[𝓝 x]
      (fun _ : Domain n => 0) := by
    filter_upwards [hW.mem_nhds hx] with z hz
    exact hh z hz
  rw [hlocal.fderiv_eq]
  rw [fderiv_const_apply, zero_apply]

end HarmonicMaps
end
