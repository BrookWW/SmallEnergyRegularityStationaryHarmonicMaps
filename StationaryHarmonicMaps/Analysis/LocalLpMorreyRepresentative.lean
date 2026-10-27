module

public import StationaryHarmonicMaps.Analysis.LocalCampanatoRepresentative
public import StationaryHarmonicMaps.Analysis.LpMorreyRepresentative
public import HarmonicMaps.SobolevRestriction

/-!
# Half-ball representatives from local Lp HS-gradient growth

Every gradient-growth ball has its closure inside the original Sobolev
domain. The actual local Sobolev data give its mean-oscillation estimate;
the local Campanato theorem supplies the same-map representative and a
full pairwise Holder bound without extending the Sobolev map.
-/

public section

open HarmonicMaps MeasureTheory Set Metric

namespace StationaryHarmonicMaps

/-- Local all-center Lp growth gives the unique continuous half-ball representative.
The uniform constant precedes every ambient dimension, map, amplitude and ball. -/
theorem existsUnique_local_representative_of_lp_gradient_growth
    (n : ℕ) (p α : ℝ) (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2)
    (hα : 0 < α) (_hαOne : α < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) (Ω : OpenDomain n) (u : Domain n → Ambient q)
        (Du : Domain n → Gradient n q) (K : ℝ) (a : Domain n) (R : ℝ),
        MemW12Loc Ω u Du → 0 < R → Metric.closedBall a R ⊆ Ω.val → 0 ≤ K →
        (∀ (x : Domain n), x ∈ Metric.ball a (3 * R / 4) →
          ∀ r : ℝ, 0 < r → r ≤ R / 4 →
            (∫ y in Metric.ball x r, (Real.sqrt (hsNormSq (Du y))) ^ p) ≤
              K ^ p * r ^ ((n : ℝ) - p + p * α)) →
        ∃! w : Metric.ball a (R / 2) → Ambient q,
          IsContinuousRepresentative (ballDomain a (R / 2)) u w ∧
          ∀ x y : Metric.ball a (R / 2),
            ‖w x - w y‖ ≤ C * K * (dist (x : Domain n) (y : Domain n)) ^ α := by
  obtain ⟨C₀, hC₀, hcampanato⟩ :=
    existsUnique_local_representative_of_meanOscillation n α hα
  let D : ℝ := ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) *
    (volume.real (Metric.ball (0 : Domain n) 1)) ^ (-(1 / p))
  let C : ℝ := 1 + C₀ * D
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hcoefficient : C₀ * D ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro q Ω u Du K a R hu hR hball hK hgrowth
  letI : IsFiniteMeasure (volume.restrict (ballDomain a R).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have houter : MemW12 (ballDomain a R) u Du := hu.memW12_ball hball
  have hf : IntegrableOn u (Metric.ball a R) volume := houter.2.1.integrable (by norm_num)
  have hosc : ∀ (x : Domain n), x ∈ Metric.ball a (3 * R / 4) →
      ∀ r : ℝ, 0 < r → r ≤ R / 4 →
        (⨍ y in Metric.ball x r, ‖u y - (⨍ z in Metric.ball x r, u z)‖) ≤
          (D * K) * r ^ α := by
    intro x hx r hr hcap
    have hclosed : Metric.closedBall x r ⊆ Ω.val :=
      (closedBall_quarter_subset_outer hx hcap).trans
        (Metric.ball_subset_closedBall.trans hball)
    have hW : MemW12 (ballDomain x r) u Du := hu.memW12_ball hclosed
    exact sobolev_meanOscillation_of_lp_growth x hr hp₁ hp₂ hK hW (hgrowth x hx r hr hcap)
  obtain ⟨w, hw, _⟩ := hcampanato q u a R (D * K) hR (mul_nonneg hD hK) hf hosc
  refine ⟨w, ⟨hw.1, ?_⟩, ?_⟩
  · intro x y
    calc
      _ ≤ C₀ * (D * K) * (dist (x : Domain n) (y : Domain n)) ^ α := hw.2.2.2 x y
      _ = (C₀ * D) * K * (dist (x : Domain n) (y : Domain n)) ^ α := by ring
      _ ≤ C * K * (dist (x : Domain n) (y : Domain n)) ^ α := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoefficient hK) (Real.rpow_nonneg dist_nonneg _)
  · intro v hv
    exact hv.1.unique hw.1

end StationaryHarmonicMaps

end
