module

public import StationaryHarmonicMaps.Analysis.BoundedSobolevL2Compactness
public import StationaryHarmonicMaps.Analysis.SobolevWeakGradientClosure
public import StationaryHarmonicMaps.Analysis.HSWeakL2Subsequence
public import StationaryHarmonicMaps.Analysis.L2ClosedRange

/-!
# Actual simultaneous bounded Sobolev limits on the whole unit ball

Whole-ball strong compactness and one further full-HS weak subsequence
preserve the original map limit. Native weak-gradient closure and the
closed norm constraint produce the same bounded Sobolev limit graph.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual bounded native Sobolev graphs have one whole-ball strong/weak native limit. -/
theorem exists_bounded_strong_weak_sobolev_L2_limit_unitBall {n q : ℕ}
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (hu : ∀ k, MemW12 (ballDomain (0 : Domain n) 1) (u k) (Du k))
    (B Mgrad : ℝ) (hB : 0 ≤ B) (hMgrad : 0 ≤ Mgrad)
    (hbound : ∀ k, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), ‖u k x‖ ≤ B)
    (hgrad : ∀ k, (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du k x)) ≤ Mgrad) :
    ∃ (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) v Dv ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), ‖v x‖ ≤ B) ∧
      (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Dv x)) ≤ Mgrad ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun k => eLpNorm (u (σ k) - v) 2
          (volume.restrict (Metric.ball (0 : Domain n) 1))) atTop (𝓝 0) ∧
        ∀ (i : Fin n) (g : Domain n → Ambient q), MemLp g 2
          (volume.restrict (Metric.ball (0 : Domain n) 1)) →
          Tendsto (fun k => ∫ x in Metric.ball (0 : Domain n) 1, inner ℝ (Du (σ k) x i) (g x)) atTop
            (𝓝 (∫ x in Metric.ball (0 : Domain n) 1, inner ℝ (Dv x i) (g x))) := by
  let Ω := ballDomain (0 : Domain n) 1
  let μ := volume.restrict Ω.val
  obtain ⟨hMap, _hTB, v, hv, s, hs, hstrong⟩ :=
    bounded_sobolev_L2_compactness_unitBall u Du hu B Mgrad hB hMgrad hbound hgrad
  obtain ⟨Dv, hDv, hEDv, t, ht, hweak⟩ := exists_weak_HS_L2_subsequence μ
    (fun k => Du (s k)) (fun k i => (hu (s k)).2.2 i) hMgrad (fun k => hgrad (s k))
  let σ := s ∘ t
  have hσ : StrictMono σ := hs.comp ht
  have hstrongσ : Tendsto (fun k => eLpNorm (u (σ k) - v) 2 μ) atTop (𝓝 0) :=
    hstrong.comp ht.tendsto_atTop
  have hW : MemW12 Ω v Dv := memW12_of_strong_map_weak_gradient_L2 Ω
    (fun k => u (σ k)) (fun k => Du (σ k)) (fun k => hu (σ k))
    v Dv hv hDv hstrongσ hweak
  have hVbound : ∀ᵐ x ∂μ, ‖v x‖ ≤ B := ae_mem_closed_of_L2_limit μ
    (fun k => u (σ k)) v (fun k => hMap (σ k)) hv hstrongσ
    {z | ‖z‖ ≤ B} (isClosed_le continuous_norm continuous_const) (fun k => hbound (σ k))
  exact ⟨v, Dv, hW, hVbound, hEDv, σ, hσ, hstrongσ, hweak⟩

end StationaryHarmonicMaps.Analysis

end
