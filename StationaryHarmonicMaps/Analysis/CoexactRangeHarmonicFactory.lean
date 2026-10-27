module

public import StationaryHarmonicMaps.Analysis.CoexactRangeEulerHarmonic
public import StationaryHarmonicMaps.Analysis.CoexactDualPotentialEquation

/-!
# Actual closed normal test tensors from harmonic solenoidal fields

Two genuine radial Euler inverses construct the corrected one-form and its
exterior derivative. The resulting tensor is smooth, closed and normal on
the unit sphere. Its divergence equals the original harmonic solenoidal
field with the displayed negative sign, up to an actual smooth gradient.
-/

public section

open HarmonicMaps MeasureTheory Set Filter Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Every original smooth harmonic solenoidal field near the closed unit ball gives an actual smooth closed normal tensor whose divergence differs from its negative by an actual smooth gradient. -/
theorem exists_smooth_closed_normal_potential_mod_gradient {n q : ℕ} (hn : 1 ≤ n)
    (G : Domain n → Gradient n q) (hG : ∀ j, ContDiff ℝ ∞ (fun x => G x j))
    (ρ : ℝ) (hρ : 1 < ρ)
    (hDiv : ∀ x ∈ ball (0 : Domain n) ρ,
      (∑ i : Fin n, fderiv ℝ (fun y => G y i) x (EuclideanSpace.single i 1)) = 0)
    (hHarm : ∀ j x, x ∈ ball (0 : Domain n) ρ →
      Laplacian.laplacian (fun y => G y j) x = 0) :
    ∃ (C : Fin n → Fin n → Domain n → Ambient q) (g : Domain n → Ambient q),
      (∀ i j, ContDiff ℝ ∞ (C i j)) ∧
      (∀ i j x, C i j x = -C j i x) ∧
      (∀ i j k x, fderiv ℝ (C i j) x (EuclideanSpace.single k 1) +
        fderiv ℝ (C j k) x (EuclideanSpace.single i 1) +
        fderiv ℝ (C k i) x (EuclideanSpace.single j 1) = 0) ∧
      (∀ j (x : Domain n), ‖x‖ = 1 → (∑ i : Fin n, x i • C i j x) = 0) ∧
      ContDiff ℝ ∞ g ∧
      ∀ x ∈ ball (0 : Domain n) 1, ∀ j,
        (∑ i : Fin n, fderiv ℝ (C i j) x (EuclideanSpace.single i 1)) =
          -G x j + fderiv ℝ g x (EuclideanSpace.single j 1) := by
  let H := fun j x => (1/2 : ℝ) • radialEulerResolvent (n-1) 2 (fun y => G y j) x
  let K := fun j => radialEulerResolvent 0 1 (H j)
  obtain ⟨hH, hK, hEuler, hForce, hDivH, hDivK, hLH, hLK⟩ :=
    radial_hodge_resolvents hn (fun j x => G x j) hG ρ hDiv hHarm
  let S := fun x : Domain n => ∑ i : Fin n, x i • K i x
  let φ := fun j (x : Domain n) => (1-‖x‖^2) • H j x + (2 : ℝ) • K j x +
    ‖x‖^2 • fderiv ℝ S x (EuclideanSpace.single j 1)
  let C := fun i j (x : Domain n) => fderiv ℝ (φ j) x (EuclideanSpace.single i 1) -
    fderiv ℝ (φ i) x (EuclideanSpace.single j 1)
  let g := fun x : Domain n => (2 * ((n : ℝ)-2)) • S x + (4 : ℝ) • fderiv ℝ S x x
  obtain ⟨hC, hSkew, hClosed, hNormal⟩ := euler_primitive_closed_normal_twoTensor H K hH hK hEuler
  obtain ⟨hg, _hDivφ, hEquation⟩ := euler_primitive_relative_tensor_equation
    (ball (0 : Domain n) ρ) isOpen_ball H K hH hK hEuler hLH hLK hDivH hDivK
  refine ⟨C, g, hC, hSkew, hClosed, hNormal, hg, ?_⟩
  intro x hx j
  have hxρ : x ∈ ball (0 : Domain n) ρ := ball_subset_ball hρ.le hx
  have hE := hEquation j x hxρ
  change (∑ i : Fin n, fderiv ℝ (C i j) x (EuclideanSpace.single i 1)) =
    -(2 : ℝ) • ((n : ℝ) • H j x + (2 : ℝ) • fderiv ℝ (H j) x x) +
      fderiv ℝ g x (EuclideanSpace.single j 1) at hE
  rw [hE, hForce j x]
  module

end StationaryHarmonicMaps.Analysis

end
