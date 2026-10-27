module

public import HolderToCK.Foundation.HolderBounds
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! # Holder control from the same C1 derivative bound on a bounded convex domain -/

public section

open HarmonicMaps Set
open scoped ContDiff

namespace HolderToCK

theorem HolderBoundOn.clm_apply_const {n q : ℕ} {s : Set (Domain n)}
    {P : Domain n → Domain n →L[ℝ] Ambient q} {γ H : ℝ}
    (hP : HolderBoundOn s P γ H) (v : Domain n) :
    HolderBoundOn s (fun x => P x v) γ (H * ‖v‖) := by
  intro x hx y hy
  rw [← sub_apply]
  calc
    _ ≤ ‖P x - P y‖ * ‖v‖ := (P x - P y).le_opNorm v
    _ ≤ (H * Real.rpow (dist x y) γ) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (hP x hx y hy) (norm_nonneg _)
    _ = _ := by ring

theorem fderiv_column_holderBoundOn {n q : ℕ} {s : Set (Domain n)}
    {u : Domain n → Ambient q} {γ H : ℝ}
    (hDerivative : HolderBoundOn s (fderiv ℝ u) γ H) (i : Fin n) :
    HolderBoundOn s (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) γ H := by
  simpa only [EuclideanSpace.single, PiLp.norm_single, norm_one, mul_one] using
    hDerivative.clm_apply_const (EuclideanSpace.single i 1)

theorem fderiv_column_norm_bound {n q : ℕ} {s : Set (Domain n)}
    {u : Domain n → Ambient q} {M : ℝ}
    (hDerivative : ∀ x ∈ s, ‖fderiv ℝ u x‖ ≤ M) :
    ∀ x ∈ s, ∀ i : Fin n, ‖fderiv ℝ u x (EuclideanSpace.single i 1)‖ ≤ M := by
  intro x hx i
  have h := (fderiv ℝ u x).le_opNorm (EuclideanSpace.single i 1)
  simp only [EuclideanSpace.single, PiLp.norm_single, norm_one, mul_one] at h
  exact h.trans (hDerivative x hx)

theorem dist_le_diameter_factor_rpow {n : ℕ} (x y : Domain n) {D γ : ℝ}
    (hD : dist x y ≤ D) (hγ : 0 ≤ γ) (hγone : γ ≤ 1) :
    dist x y ≤ Real.rpow D (1 - γ) * Real.rpow (dist x y) γ := by
  have hproduct : Real.rpow (dist x y) γ * Real.rpow (dist x y) (1 - γ) = dist x y := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add_of_nonneg dist_nonneg hγ (sub_nonneg.mpr hγone),
      show γ + (1 - γ) = 1 by ring, Real.rpow_one]
  have hpower := Real.rpow_le_rpow (dist_nonneg : 0 ≤ dist x y) hD (sub_nonneg.mpr hγone)
  calc
    _ = Real.rpow (dist x y) γ * Real.rpow (dist x y) (1 - γ) := hproduct.symm
    _ ≤ Real.rpow (dist x y) γ * Real.rpow D (1 - γ) :=
      mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg dist_nonneg _)
    _ = _ := mul_comm _ _

theorem c1_holderBoundOn_of_diameter {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} (hu : ContDiffOn ℝ 1 u Ω.val) (hConvex : Convex ℝ Ω.val)
    {C D γ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hγone : γ ≤ 1)
    (hDerivative : ∀ x ∈ Ω.val, ‖fderiv ℝ u x‖ ≤ C)
    (hDiameter : ∀ x ∈ Ω.val, ∀ y ∈ Ω.val, dist x y ≤ D) :
    HolderBoundOn Ω.val u γ (C * Real.rpow D (1 - γ)) := by
  intro x hx y hy
  have hLip := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hu.contDiffAt (Ω.property.mem_nhds hz)).differentiableAt one_ne_zero)
    hDerivative hConvex hy hx
  have hpower := dist_le_diameter_factor_rpow x y (hDiameter x hx y hy) hγ hγone
  calc
    ‖u x - u y‖ ≤ C * dist x y := by simpa only [dist_eq_norm] using hLip
    _ ≤ C * (Real.rpow D (1 - γ) * Real.rpow (dist x y) γ) :=
      mul_le_mul_of_nonneg_left hpower hC
    _ = _ := (mul_assoc _ _ _).symm

end HolderToCK
end
