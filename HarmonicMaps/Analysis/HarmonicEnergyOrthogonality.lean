module

public import HarmonicMaps.Analysis.HarmonicEnergyAlgebra
public import HarmonicMaps.Analysis.DirichletClosedGreen
public import HarmonicMaps.Analysis.DirichletSmoothData
public import HarmonicMaps.Analysis.SobolevDifference

/-!
# Energy orthogonality of a harmonic replacement

The actual zero-boundary difference tests the harmonic solution in the native
signed Green identity. The resulting vanishing mixed term and the exact
Hilbert--Schmidt expansion give an equality with coefficient one.
-/

public section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace HarmonicMaps

/-- A conditional calculus result for a smooth harmonic map and its genuine
zero-boundary difference. Source applications produce all these premises. -/
theorem closedBall_harmonic_energy_orthogonality {n q : ℕ}
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m w : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (hw : ContDiffOn ℝ ∞ w (Metric.closedBall (0 : Domain n) R.val))
    (hharm : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian w x = 0)
    (hzero : HasZeroBoundaryValues (ballDomain (0 : Domain n) R.val) (m - w)
      (fun x i => fderiv ℝ m x (EuclideanSpace.single i 1) -
        fderiv ℝ w x (EuclideanSpace.single i 1))) :
    let Dm : Domain n → Gradient n q := fun x i =>
      fderiv ℝ m x (EuclideanSpace.single i 1)
    let Dw : Domain n → Gradient n q := fun x i =>
      fderiv ℝ w x (EuclideanSpace.single i 1)
    let Ddiff := Dm - Dw
    (∫ x in Metric.ball (0 : Domain n) R.val, hsNormSq (Dm x)) =
      (∫ x in Metric.ball (0 : Domain n) R.val, hsNormSq (Dw x)) +
      (∫ x in Metric.ball (0 : Domain n) R.val, hsNormSq (Ddiff x)) ∧
    dirichletEnergy Dw (Metric.ball (0 : Domain n) R.val) ≤
      dirichletEnergy Dm (Metric.ball (0 : Domain n) R.val) := by
  let B : Set (Domain n) := Metric.ball 0 R.val
  let Dm : Domain n → Gradient n q := fun x i => fderiv ℝ m x (EuclideanSpace.single i 1)
  let Dw : Domain n → Gradient n q := fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)
  let Ddiff : Domain n → Gradient n q := Dm - Dw
  have hmW := dirichlet_smoothData_memW12 R U hU hclosed m hm
  have hwW : MemW12 (ballDomain (0 : Domain n) R.val) w Dw := by
    simpa only [sub_sub_cancel] using hmW.sub hzero.1
  have hmInt : IntegrableOn (fun x => hsNormSq (Dm x)) B volume := hmW.integrable_hsNormSq
  have hwInt : IntegrableOn (fun x => hsNormSq (Dw x)) B volume := hwW.integrable_hsNormSq
  have hdInt : IntegrableOn (fun x => hsNormSq (Ddiff x)) B volume := hzero.1.integrable_hsNormSq
  obtain ⟨hcrossInt, _, hgreen⟩ :=
    closed_dirichlet_zeroBoundary_green_laplacian R w hw (m - w) Ddiff hzero
  have hzeroLap (x : Domain n) (hx : x ∈ B) :
      inner ℝ (Laplacian.laplacian w x) ((m - w) x) = 0 := by
    rw [hharm x hx, inner_zero_left]
  have hcrosszero :
      (∫ x in B, ∑ i : Fin n, inner ℝ (Dw x i) (Ddiff x i)) = 0 := by
    calc
      _ = -(∫ x in B, inner ℝ (Laplacian.laplacian w x) ((m - w) x)) := hgreen
      _ = 0 := by
        rw [setIntegral_congr_fun measurableSet_ball hzeroLap]
        simp
  have hpoint (x : Domain n) :
      hsNormSq (Dm x) = hsNormSq (Dw x) + hsNormSq (Ddiff x) +
        2 * ∑ i : Fin n, inner ℝ (Dw x i) (Ddiff x i) :=
    hsNormSq_sub_orthogonality (Dm x) (Dw x)
  have hidentity : (∫ x in B, hsNormSq (Dm x)) =
      (∫ x in B, hsNormSq (Dw x)) +
      (∫ x in B, hsNormSq (Ddiff x)) := by
    calc
      _ = ∫ x in B, hsNormSq (Dw x) +
          (hsNormSq (Ddiff x) + 2 * ∑ i : Fin n, inner ℝ (Dw x i) (Ddiff x i)) := by
        apply setIntegral_congr_fun measurableSet_ball
        intro x _
        change hsNormSq (Dm x) = hsNormSq (Dw x) +
          (hsNormSq (Ddiff x) + 2 * ∑ i : Fin n, inner ℝ (Dw x i) (Ddiff x i))
        rw [hpoint x]
        ring
      _ = (∫ x in B, hsNormSq (Dw x)) +
          ((∫ x in B, hsNormSq (Ddiff x)) +
            2 * (∫ x in B, ∑ i : Fin n, inner ℝ (Dw x i) (Ddiff x i))) := by
        calc
          _ = (∫ x in B, hsNormSq (Dw x)) +
              (∫ x in B, hsNormSq (Ddiff x) +
                2 * ∑ i : Fin n, inner ℝ (Dw x i) (Ddiff x i)) :=
            integral_add hwInt (hdInt.add (hcrossInt.const_mul 2))
          _ = (∫ x in B, hsNormSq (Dw x)) +
              ((∫ x in B, hsNormSq (Ddiff x)) +
                (∫ x in B, 2 * ∑ i : Fin n, inner ℝ (Dw x i) (Ddiff x i))) := by
            rw [integral_add hdInt (hcrossInt.const_mul 2)]
          _ = _ := by rw [integral_const_mul]
      _ = _ := by rw [hcrosszero]; ring
  have hle : (∫ x in B, hsNormSq (Dw x)) ≤ (∫ x in B, hsNormSq (Dm x)) := by
    have hn : 0 ≤ ∫ x in B, hsNormSq (Ddiff x) :=
      integral_nonneg (fun x => hsNormSq_nonneg (Ddiff x))
    linarith only [hidentity, hn]
  refine ⟨hidentity, ?_⟩
  rw [dirichletEnergy_eq_ofReal_integral hwInt, dirichletEnergy_eq_ofReal_integral hmInt]
  exact ENNReal.ofReal_le_ofReal hle

end HarmonicMaps
end
