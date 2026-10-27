module

public import StationaryHarmonicMaps.Analysis.BallDivergenceIntegral

/-! # Actual zero sphere flux gives a zero ball divergence integral -/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Applying the actual sphere sign inequality to both signs retains the genuine zero-flux divergence identity. -/
theorem unitBall_integral_divergence_eq_zero {n : ℕ}
    (V : Domain n → Domain n) (hV : ContDiff ℝ 1 V)
    (hSphere : ∀ x : Domain n, ‖x‖=1 → inner ℝ x (V x)=0) :
    IntegrableOn (fun x=>∑ i : Fin n,
      (fderiv ℝ V x (EuclideanSpace.single i 1)) i) (ball (0 : Domain n) 1) volume ∧
      (∫ x in ball (0 : Domain n) 1,∑ i : Fin n,
        (fderiv ℝ V x (EuclideanSpace.single i 1)) i)=0 := by
  have hPos := unitBall_integral_divergence_nonpos V hV (fun x hx=>(hSphere x hx).le)
  have hNeg := unitBall_integral_divergence_nonpos (fun x=> -V x) hV.neg (fun x hx=>by
    rw [inner_neg_right,hSphere x hx,neg_zero])
  have hDer (x : Domain n) (i : Fin n) :
      (fderiv ℝ (fun y=> -V y) x (EuclideanSpace.single i 1)) i =
        -((fderiv ℝ V x (EuclideanSpace.single i 1)) i) := by
    have H := congrArg (fun L : Domain n →L[ℝ] Domain n=> (L (EuclideanSpace.single i 1)) i)
      ((hV.differentiable (by norm_num) x).hasFDerivAt.neg.fderiv)
    have heq : (-V : Domain n → Domain n) = (fun y=> -V y) := rfl
    rw [heq] at H
    simpa only [neg_apply,PiLp.neg_apply] using H
  have heq : (∫ x in ball (0 : Domain n) 1,∑ i : Fin n,
      (fderiv ℝ (fun y=> -V y) x (EuclideanSpace.single i 1)) i) =
        -(∫ x in ball (0 : Domain n) 1,∑ i : Fin n,
          (fderiv ℝ V x (EuclideanSpace.single i 1)) i) := by
    simp_rw [hDer,Finset.sum_neg_distrib]
    exact integral_neg _
  rw [heq] at hNeg
  exact ⟨hPos.1,le_antisymm hPos.2 (by linarith only [hNeg.2])⟩

end StationaryHarmonicMaps.Analysis

end
