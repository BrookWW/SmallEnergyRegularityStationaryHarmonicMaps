module

public import HarmonicMaps.Analysis.BallAverageDifferentiation
public import HarmonicMaps.Analysis.MorreyBallEstimates
public import HarmonicMaps.Analysis.MorreyGeometricMeans
public import HarmonicMaps.Energy

/-! # The actual all-radius Sobolev ball-mean limit

Poincare supplies comparable-scale control. Completeness then produces a
unique limit of the literal means, with every-radius error and AE agreement.
-/

public section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace HarmonicMaps

/-- The ball means of the original map have a unique all-radius limit at every inner point. -/
theorem MemW12.morrey_ballAverage_existsUnique {n q : ℕ}
    {f : Domain n → Ambient q} {Df : Domain n → Gradient n q}
    (hf : MemW12 (ballDomain 0 1) f Df) {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    (hgrowth : ∀ (x : Domain n), x ∈ Metric.ball (0 : Domain n) (1 / 2) →
      ∀ (r : PositiveRadius), r.val ≤ (1 / 2 : ℝ) →
        (∫ y in Metric.ball x r.val, hsNormSq (Df y)) ≤
          M * Real.rpow r.val ((n : ℝ) - 2 + 2 * α))
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2)) :
    ∃! w : Ambient q,
      Tendsto (fun r : ℝ => (volume (Metric.ball x r)).toReal⁻¹ •
        (∫ y in Metric.ball x r, f y)) (𝓝[>] (0 : ℝ)) (𝓝 w) ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
        ‖(⨍ y in Metric.ball x r, f y) - w‖ ≤
          (Real.sqrt ((2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n /
            volume.real (Metric.ball (0 : Domain n) 1)) /
            (1 - (1 / 2 : ℝ) ^ α)) * Real.sqrt M * Real.rpow r α := by
  let F : ℝ → Ambient q := fun r => ⨍ y in Metric.ball x r, f y
  let K := Real.sqrt ((2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n /
    volume.real (Metric.ball (0 : Domain n) 1)) * Real.sqrt M
  have hK : 0 ≤ K := by positivity
  have hcomp : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ 1 / 2 → t ≤ 2 * s →
      dist (F s) (F t) ≤ K * t ^ α := by
    intro s t hs hst ht hratio
    have ht0 : 0 < t := hs.trans_le hst
    have h := hf.morrey_ballAverage_compare hM (by norm_num : (0 : ℝ) ≤ 2)
      hs ht0 hx ht (Metric.ball_subset_ball hst) hratio (hgrowth x hx ⟨t, ht0⟩ ht)
    simpa only [F, K, dist_eq_norm, Real.rpow_eq_pow] using h
  obtain ⟨w, hw, _hunique⟩ := existsUnique_allRadius_limit_of_comparable F hα hK hcomp
  refine ⟨w, ⟨?_, ?_⟩, ?_⟩
  · simpa only [F, setAverage_eq, measureReal_def] using hw.1
  · intro r hr hrhalf
    have h := hw.2 r hr hrhalf
    simp only [F, K, dist_eq_norm] at h
    simp only [Real.rpow_eq_pow]
    convert h using 1
    ring
  · intro v hv
    have hvF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 v) := by
      simpa only [F, setAverage_eq, measureReal_def] using hv.1
    exact tendsto_nhds_unique hvF hw.1

/-- One subtype function is the all-radius mean limit and agrees AE with the original map. -/
theorem MemW12.morrey_means {n q : ℕ} {f : Domain n → Ambient q}
    {Df : Domain n → Gradient n q} (hf : MemW12 (ballDomain 0 1) f Df)
    {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    (hgrowth : ∀ (x : Domain n), x ∈ Metric.ball (0 : Domain n) (1 / 2) →
      ∀ (r : PositiveRadius), r.val ≤ (1 / 2 : ℝ) →
        (∫ y in Metric.ball x r.val, hsNormSq (Df y)) ≤
          M * Real.rpow r.val ((n : ℝ) - 2 + 2 * α)) :
    ∃ w : Metric.ball (0 : Domain n) (1 / 2) → Ambient q,
      (∀ (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2)),
        Tendsto (fun r : ℝ => (volume (Metric.ball x r)).toReal⁻¹ •
          (∫ y in Metric.ball x r, f y)) (𝓝[>] (0 : ℝ)) (𝓝 (w ⟨x, hx⟩))) ∧
      (∀ (x : Metric.ball (0 : Domain n) (1 / 2)) (r : ℝ), 0 < r → r ≤ 1 / 2 →
        ‖(⨍ y in Metric.ball (x : Domain n) r, f y) - w x‖ ≤
          (Real.sqrt ((2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n /
            volume.real (Metric.ball (0 : Domain n) 1)) /
            (1 - (1 / 2 : ℝ) ^ α)) * Real.sqrt M * Real.rpow r α) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) (1 / 2)),
        ∀ hx : x ∈ Metric.ball (0 : Domain n) (1 / 2), w ⟨x, hx⟩ = f x) := by
  classical
  have hex (x : Metric.ball (0 : Domain n) (1 / 2)) :=
    hf.morrey_ballAverage_existsUnique hα hM hgrowth x x.2
  let w : Metric.ball (0 : Domain n) (1 / 2) → Ambient q := fun x => (hex x).exists.choose
  have hw (x : Metric.ball (0 : Domain n) (1 / 2)) := (hex x).exists.choose_spec
  refine ⟨w, (fun x hx => (hw ⟨x, hx⟩).1), (fun x => (hw x).2), ?_⟩
  filter_upwards [locallyIntegrableOn_ae_tendsto_ballAverage f hf.1.1] with x hx hxin
  exact tendsto_nhds_unique (hw ⟨x, hxin⟩).1 hx

end HarmonicMaps
