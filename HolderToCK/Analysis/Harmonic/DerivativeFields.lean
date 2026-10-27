module

public import HarmonicMaps.Analysis.HarmonicDerivative
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-! # Harmonicity of actual higher derivative fields

Directional derivatives are finite linear combinations of the proved harmonic
coordinate columns. Induction identifies their successive evaluations with
the native iterated Fréchet derivative on the same open smoothness carrier.
-/

public section

open HarmonicMaps InnerProductSpace Set
open scoped ContDiff Topology

namespace HolderToCK

theorem harmonicOnNhd_of_smooth_laplacian_zero {n q : ℕ}
    {W : Set (Domain n)} (hW : IsOpen W) {f : Domain n → Ambient q}
    (hf : ContDiffOn ℝ ∞ f W) (hh : ∀ x ∈ W, Laplacian.laplacian f x = 0) :
    HarmonicOnNhd f W := by
  intro x hx
  refine ⟨(hf.contDiffAt (hW.mem_nhds hx)).of_le
    (le_of_lt (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top (2 : ℕ)))), ?_⟩
  filter_upwards [hW.mem_nhds hx] with y hy
  exact hh y hy

theorem harmonicOnNhd_finset_sum {n q : ℕ} {ι : Type*}
    (s : Finset ι) {W : Set (Domain n)} (f : ι → Domain n → Ambient q)
    (hf : ∀ i ∈ s, HarmonicOnNhd (f i) W) :
    HarmonicOnNhd (fun x => ∑ i ∈ s, f i x) W := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (harmonicOnNhd_const (c := (0 : Ambient q)) (s := W))
  | @insert i s hi ih =>
      have hs : ∀ j ∈ s, HarmonicOnNhd (f j) W :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have heq : (fun x => ∑ j ∈ insert i s, f j x) =
          f i + (fun x => ∑ j ∈ s, f j x) := by
        funext x
        simp only [Finset.sum_insert hi, Pi.add_apply]
      rw [heq]
      exact (hf i (Finset.mem_insert_self i s)).add (ih hs)

theorem harmonic_fderiv_direction {n q : ℕ}
    (W : Set (Domain n)) (hW : IsOpen W) (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f W) (hh : ∀ x ∈ W, Laplacian.laplacian f x = 0)
    (v : Domain n) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) W ∧
    ∀ x ∈ W, Laplacian.laplacian (fun x => fderiv ℝ f x v) x = 0 := by
  have hsmooth : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) W :=
    (hf.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
  have hcolumn (i : Fin n) := harmonic_fderiv_column W hW f hf hh i
  have hrep (x : Domain n) : fderiv ℝ f x v =
      ∑ i : Fin n, v i • fderiv ℝ f x (EuclideanSpace.single i 1) := by
    nth_rw 1 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
    rw [map_sum]
    simp only [map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have hsum : HarmonicOnNhd
      (fun x => ∑ i : Fin n, v i • fderiv ℝ f x (EuclideanSpace.single i 1)) W := by
    apply harmonicOnNhd_finset_sum Finset.univ
    intro i _
    exact (harmonicOnNhd_of_smooth_laplacian_zero hW (hcolumn i).1 (hcolumn i).2).const_smul
  refine ⟨hsmooth, ?_⟩
  intro x hx
  rw [funext hrep]
  exact (hsum x hx).2.eq_of_nhds

theorem harmonic_iteratedFDeriv_apply {n q : ℕ}
    (W : Set (Domain n)) (hW : IsOpen W) (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f W) (hh : ∀ x ∈ W, Laplacian.laplacian f x = 0)
    (k : ℕ) (v : Fin k → Domain n) :
    ContDiffOn ℝ ∞ (fun x => iteratedFDeriv ℝ k f x v) W ∧
    ∀ x ∈ W, Laplacian.laplacian (fun x => iteratedFDeriv ℝ k f x v) x = 0 := by
  induction k with
  | zero => simpa only [iteratedFDeriv_zero_apply] using And.intro hf hh
  | succ k ih =>
      have hprev := ih (Fin.tail v)
      have hdir := harmonic_fderiv_direction W hW
        (fun x => iteratedFDeriv ℝ k f x (Fin.tail v)) hprev.1 hprev.2 (v 0)
      have heq : EqOn (fun x => iteratedFDeriv ℝ (k + 1) f x v)
          (fun x => fderiv ℝ (fun y => iteratedFDeriv ℝ k f y (Fin.tail v)) x (v 0)) W := by
        intro x hx
        have hdiff := (hf.contDiffAt (hW.mem_nhds hx)).differentiableAt_iteratedFDeriv
          (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top k))
        exact hdiff.iteratedFDeriv_succ_apply_left'
      refine ⟨hdir.1.congr heq, ?_⟩
      intro x hx
      have hlocal : (fun x => iteratedFDeriv ℝ (k + 1) f x v) =ᶠ[𝓝 x]
          (fun x => fderiv ℝ (fun y => iteratedFDeriv ℝ k f y (Fin.tail v)) x (v 0)) := by
        filter_upwards [hW.mem_nhds hx] with y hy
        exact heq hy
      rw [(InnerProductSpace.laplacian_congr_nhds hlocal).eq_of_nhds]
      exact hdir.2 x hx

end HolderToCK
end
