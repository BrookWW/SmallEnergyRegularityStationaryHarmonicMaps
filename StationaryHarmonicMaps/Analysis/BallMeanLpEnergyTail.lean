module

public import StationaryHarmonicMaps.Analysis.LpMorreyRepresentative
public import StationaryHarmonicMaps.Analysis.BallMeanEnergyTail

/-!
# Actual Lebesgue-point tails from lower-power gradient averages

The forward Lp Poincare inequality controls the original mean oscillation.
Linear-radius oscillation gives a genuine limit of means, identified with
the same original value at its actual Lebesgue point.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Genuine bounded Lp gradient averages control the original ball-mean
tail at an actual Lebesgue point, including p=1 and p=2. -/
theorem ballMean_value_tail_of_lp_energy_average {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (p : ℝ) (hpOne : 1≤p) (hpTwo : p≤2)
    (hu : MemW12Loc Ω u Du) (x : Domain n) {r₀ L : ℝ}
    (hr₀ : 0<r₀) (hL : 0≤L) (hClosed : closedBall x r₀⊆Ω.val)
    (hLebesgue : Tendsto (fun r : ℝ=>⨍y in ball x r,u y) (𝓝[>] (0 : ℝ)) (𝓝 (u x)))
    (hEnergy : ∀r : ℝ,0<r → r≤r₀ →
      (∫y in ball x r,(Real.sqrt (hsNormSq (Du y)))^p)≤L^p*volume.real (ball x r)) :
    ‖(⨍y in ball x r₀,u y)-u x‖≤
      ((2 : ℝ)^(n+1)*((2 : ℝ)^(n+1)*Real.sqrt (n : ℝ)))*L*r₀ := by
  have hp : 0<p := zero_lt_one.trans_le hpOne
  let D := (2 : ℝ)^(n+1)*Real.sqrt (n : ℝ)
  have hK : 0≤D*L := mul_nonneg (by dsimp only [D];positivity) hL
  let μ := volume.restrict (ball x r₀)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hW := hu.memW12_ball hClosed
  have hULp : MemLp u 2 μ := hW.2.1
  have hI : IntegrableOn u (ball x r₀) volume := hULp.integrable (by norm_num)
  have hOsc (r : ℝ) (hr : 0<r) (hCap : r≤r₀) :
      (⨍y in ball x r,‖u y-(⨍z in ball x r,u z)‖)≤(D*L)*r^(1 : ℝ) := by
    have hSmall := hu.memW12_ball ((closedBall_subset_closedBall hCap).trans hClosed)
    have hV : 0<volume.real (ball x r) := HolderToCK.ball_volume_real_pos x hr
    have hMean : (⨍y in ball x r,(Real.sqrt (hsNormSq (Du y)))^p)≤L^p := by
      rw [setAverage_eq,smul_eq_mul]
      exact (mul_le_mul_of_nonneg_left (hEnergy r hr hCap) (inv_nonneg.mpr hV.le)).trans_eq (by
        field_simp)
    have hMeanNonneg : 0≤(⨍y in ball x r,(Real.sqrt (hsNormSq (Du y)))^p) :=
      integral_nonneg fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hRoot := Real.rpow_le_rpow hMeanNonneg hMean (one_div_nonneg.mpr hp.le)
    rw [one_div,Real.rpow_rpow_inv hL hp.ne'] at hRoot
    have H := sobolev_ballAverage_oscillation_le_lp_hs x hr hpOne hpTwo hSmall
    rw [one_div] at H
    have H' : (⨍y in ball x r,‖u y-(⨍z in ball x r,u z)‖)≤
        ((2 : ℝ)^(n+1)*Real.sqrt (n : ℝ))*r*L :=
      H.trans (mul_le_mul_of_nonneg_left hRoot (by positivity))
    exact H'.trans_eq (by rw [Real.rpow_one];dsimp only [D];ring)
  obtain ⟨w,hw,_hUnique⟩ := existsUnique_ballAverage_limit_of_meanOscillation_radius u x
    (by norm_num : (0 : ℝ)<1) hK hr₀ hI hOsc
  have hwx : w=u x := tendsto_nhds_unique hw.1 hLebesgue
  have H := hw.2 r₀ hr₀ le_rfl
  rw [hwx,Real.rpow_one,Real.rpow_one] at H
  exact H.trans_eq (by dsimp only [D];rw [pow_succ];ring)

end StationaryHarmonicMaps.Analysis

end
