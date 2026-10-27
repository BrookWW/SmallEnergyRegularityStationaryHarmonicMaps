module

public import HarmonicMaps.Energy
public import HarmonicMaps.Analysis.PoissonAngularGeometry
public import HarmonicMaps.Analysis.ClosedBallDerivativeSystem
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Module

/-!
# Closed-ball smoothness from angular and Euler identities

Continuous families indexed by angular words are smooth on the closed ball when
interior angular and Euler derivatives satisfy the coordinate harmonic system.
The Cartesian derivative formula has coefficients smooth away from the origin;
interior smoothness supplies regularity at the origin.
-/

public section

open Set Metric
open scoped ContDiff BigOperators

namespace HarmonicMaps

private theorem poisson_column_of_radial_angular {n q : ℕ}
    (A : Fin n → Fin n → (Domain n →L[ℝ] Domain n))
    (hA : ∀ i j (x : Domain n), A i j x =
      x i • EuclideanSpace.single j 1 - x j • EuclideanSpace.single i 1)
    (B : Domain n →L[ℝ] Ambient q) (x : Domain n) (hx : x ≠ 0) (k : Fin n) :
    B (EuclideanSpace.single k 1) =
      (‖x‖ ^ 2)⁻¹ • (x k • B x + ∑ j : Fin n, x j • B (A j k x)) := by
  have h := poisson_cartesian_column_from_radial_angular B x k
  have hs : ‖x‖ ^ 2 • B (EuclideanSpace.single k 1) =
      x k • B x + ∑ j : Fin n, x j • B (A j k x) := by
    simpa only [hA] using h
  rw [← hs, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)), one_smul]

/-- Continuous angular-word and Euler families satisfying the actual interior
coordinate harmonic identities are infinitely smooth within the closed ball. -/
theorem poisson_angular_euler_closed_smooth {n q : ℕ}
    (R : PositiveRadius)
    (A : Fin n → Fin n → (Domain n →L[ℝ] Domain n))
    (hA : ∀ i j (x : Domain n), A i j x =
      x i • EuclideanSpace.single j 1 - x j • EuclideanSpace.single i 1)
    (F E : List (Fin n × Fin n) → Domain n → Ambient q)
    (hFc : ∀ w, ContinuousOn (F w) (closedBall 0 R.val))
    (hEc : ∀ w, ContinuousOn (E w) (closedBall 0 R.val))
    (hFs : ∀ w, ContDiffOn ℝ ∞ (F w) (ball 0 R.val))
    (hEs : ∀ w, ContDiffOn ℝ ∞ (E w) (ball 0 R.val))
    (hFr : ∀ w x, x ∈ ball 0 R.val → fderiv ℝ (F w) x x = E w x)
    (hFa : ∀ w i j x, x ∈ ball 0 R.val →
      fderiv ℝ (F w) x (A i j x) = F ((i, j) :: w) x)
    (hEa : ∀ w i j x, x ∈ ball 0 R.val →
      fderiv ℝ (E w) x (A i j x) = E ((i, j) :: w) x)
    (hEr : ∀ w x, x ∈ ball 0 R.val →
      fderiv ℝ (E w) x x = -((n : ℝ) - 2) • E w x -
        (1 / 2 : ℝ) • (∑ i : Fin n, ∑ j : Fin n, F ((i, j) :: (i, j) :: w) x)) :
    ∀ w, ContDiffOn ℝ ∞ (F w) (closedBall 0 R.val) ∧
      ContDiffOn ℝ ∞ (E w) (closedBall 0 R.val) := by
  classical
  let I := Bool × List (Fin n × Fin n)
  let J := Sum Unit (Sum (Fin n) (Fin n × Fin n))
  let f : I → Domain n → Ambient q := fun p => if p.1 then E p.2 else F p.2
  let σ : I → Fin n → J → I := fun p k t =>
    match t with
    | Sum.inl _ => (true, p.2)
    | Sum.inr (Sum.inl j) => (p.1, (j, k) :: p.2)
    | Sum.inr (Sum.inr ij) => (false, ij :: ij :: p.2)
  let c : I → Fin n → J → Domain n → ℝ := fun p k t x =>
    match t with
    | Sum.inl _ => if p.1 then (‖x‖ ^ 2)⁻¹ * x k * (-((n : ℝ) - 2))
      else (‖x‖ ^ 2)⁻¹ * x k
    | Sum.inr (Sum.inl j) => (‖x‖ ^ 2)⁻¹ * x j
    | Sum.inr (Sum.inr _) => if p.1 then (‖x‖ ^ 2)⁻¹ * x k * (-(1 / 2 : ℝ))
      else 0
  have hinv : ContDiffOn ℝ ∞ (fun x : Domain n => (‖x‖ ^ 2)⁻¹) ({0}ᶜ : Set (Domain n)) :=
    (contDiff_norm_sq ℝ).contDiffOn.inv (fun x hx =>
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  have hcoeff (k : Fin n) : ContDiffOn ℝ ∞
      (fun x : Domain n => (‖x‖ ^ 2)⁻¹ * x k) ({0}ᶜ : Set (Domain n)) :=
    hinv.mul (by
      simpa only [EuclideanSpace.coe_proj] using
        (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffOn)
  have hfc (i : I) : ContinuousOn (f i) (closedBall 0 R.val) := by
    rcases i with ⟨b, w⟩
    cases b
    · exact hFc w
    · exact hEc w
  have hfs (i : I) : ContDiffOn ℝ ∞ (f i) (ball 0 R.val) := by
    rcases i with ⟨b, w⟩
    cases b
    · exact hFs w
    · exact hEs w
  have hc (i : I) (k : Fin n) (j : J) :
      ContDiffOn ℝ ∞ (c i k j) ({0}ᶜ : Set (Domain n)) := by
    rcases i with ⟨b, w⟩
    rcases j with _ | j
    · cases b
      · exact hcoeff k
      · exact (hcoeff k).mul contDiffOn_const
    · rcases j with j | ij
      · exact hcoeff j
      · cases b
        · exact contDiffOn_const
        · exact (hcoeff k).mul contDiffOn_const
  have hsystem (i : I) (k : Fin n) (x : Domain n) (hx : x ∈ ball 0 R.val) (hx0 : x ≠ 0) :
      fderiv ℝ (f i) x (EuclideanSpace.single k 1) =
        ∑ j : J, c i k j x • f (σ i k j) x := by
    rcases i with ⟨b, w⟩
    cases b
    · change fderiv ℝ (F w) x (EuclideanSpace.single k 1) = _
      rw [poisson_column_of_radial_angular A hA _ x hx0 k]
      simp only [hFr w x hx, hFa w _ _ x hx, J, Fintype.sum_sum_type,
        Fintype.sum_unique, c, σ, f, Bool.false_eq_true,
        ↓reduceIte, zero_smul,
        Finset.sum_const_zero, add_zero, smul_add, Finset.smul_sum, smul_smul]
    · change fderiv ℝ (E w) x (EuclideanSpace.single k 1) = _
      rw [poisson_column_of_radial_angular A hA _ x hx0 k]
      simp only [hEr w x hx, hEa w _ _ x hx, J, Fintype.sum_sum_type,
        Fintype.sum_unique, Fintype.sum_prod_type, c, σ, f, Bool.false_eq_true,
        ↓reduceIte, smul_add, smul_sub,
        Finset.smul_sum, smul_smul]
      simp only [← mul_assoc, mul_neg, neg_smul, Finset.sum_neg_distrib]
      module
  have hs := contDiffOn_closedBall_family_of_finite_derivative_system R.property
    f σ c hfc hfs hc hsystem
  intro w
  exact ⟨hs (false, w), hs (true, w)⟩

end HarmonicMaps
end
