module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Module

/-!
# Quantitative central coordinates on the unit sphere

Central projection of the affine tangent plane has distortion tending to one
on shrinking tangent balls. The literal normalization formula is used on its
whole domain; no chosen chart or selected surface measure is introduced.
-/

public section

open Set
open scoped RealInnerProductSpace

namespace HarmonicMaps

/-- Orthogonality controls the radial variation in a small tangent ball. -/
theorem sphereSurface_chart_radial_bound {n : ℕ} (e : Domain n) (he : ‖e‖ = 1)
    (ε : ℝ) (u v : (ℝ ∙ e)ᗮ) (hu : ‖u‖ ≤ ε) (hv : ‖v‖ ≤ ε) :
    |‖e + (u : Domain n)‖ - ‖e + (v : Domain n)‖| ≤ ε * ‖u - v‖ := by
  have hsq (w : (ℝ ∙ e)ᗮ) : ‖e + (w : Domain n)‖ ^ 2 = 1 + ‖w‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero e (w : Domain n)
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property)
    rw [he] at h
    change ‖e + (w : Domain n)‖ ^ 2 = 1 + ‖(w : Domain n)‖ ^ 2
    nlinarith only [h]
  have hge (w : (ℝ ∙ e)ᗮ) : 1 ≤ ‖e + (w : Domain n)‖ := by
    have h := hsq w
    nlinarith only [h, sq_nonneg ‖w‖, norm_nonneg (e + (w : Domain n))]
  have hab : |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ (2 * ε) * ‖u - v‖ := by
    calc
      |‖u‖ ^ 2 - ‖v‖ ^ 2| = |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖) := by
        rw [← abs_of_nonneg (add_nonneg (norm_nonneg u) (norm_nonneg v)), ← abs_mul]
        congr 1
        ring
      _ ≤ ‖u - v‖ * (2 * ε) :=
        mul_le_mul (abs_norm_sub_norm_le u v) (by linarith only [hu, hv])
          (add_nonneg (norm_nonneg u) (norm_nonneg v)) (norm_nonneg _)
      _ = (2 * ε) * ‖u - v‖ := mul_comm _ _
  have hid : |‖e + (u : Domain n)‖ - ‖e + (v : Domain n)‖| *
      (‖e + (u : Domain n)‖ + ‖e + (v : Domain n)‖) = |‖u‖ ^ 2 - ‖v‖ ^ 2| := by
    rw [← abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), ← abs_mul]
    congr 1
    nlinarith only [hsq u, hsq v]
  have hsum : 2 ≤ ‖e + (u : Domain n)‖ + ‖e + (v : Domain n)‖ := by
    linarith only [hge u, hge v]
  have hmul := mul_le_mul_of_nonneg_left hsum
    (abs_nonneg (‖e + (u : Domain n)‖ - ‖e + (v : Domain n)‖))
  rw [hid] at hmul
  linarith only [hmul, hab]

/-- The central chart has explicit upper and lower distance bounds whose
constants tend to one with the radius of the tangent ball. -/
theorem sphereSurface_chart_distortion {n : ℕ} (e : Domain n) (he : ‖e‖ = 1)
    (ε : ℝ) (hε1 : ε < 1)
    (u v : (ℝ ∙ e)ᗮ) (hu : ‖u‖ ≤ ε) (hv : ‖v‖ ≤ ε) :
    let ψ : (ℝ ∙ e)ᗮ → Domain n := fun w => ‖e + (w : Domain n)‖⁻¹ • (e + w)
    ‖ψ u - ψ v‖ ≤ (1 + ε) * ‖u - v‖ ∧
      ‖u - v‖ ≤ ((1 + ε) / (1 - ε)) * ‖ψ u - ψ v‖ := by
  let ψ : (ℝ ∙ e)ᗮ → Domain n := fun w => ‖e + (w : Domain n)‖⁻¹ • (e + w)
  have hge (w : (ℝ ∙ e)ᗮ) : 1 ≤ ‖e + (w : Domain n)‖ := by
    have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero e (w : Domain n)
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property)
    rw [he] at hsq
    nlinarith only [hsq, sq_nonneg ‖(w : Domain n)‖, norm_nonneg (e + (w : Domain n))]
  have hpos (w : (ℝ ∙ e)ᗮ) : 0 < ‖e + (w : Domain n)‖ := lt_of_lt_of_le zero_lt_one (hge w)
  have hnorm (w : (ℝ ∙ e)ᗮ) : ‖ψ w‖ = 1 := by
    dsimp only [ψ]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (hpos w).ne']
  have hrec (w : (ℝ ∙ e)ᗮ) : ‖e + (w : Domain n)‖ • ψ w = e + w := by
    dsimp only [ψ]
    rw [smul_smul, mul_inv_cancel₀ (hpos w).ne', one_smul]
  have hrad := sphereSurface_chart_radial_bound e he ε u v hu hv
  have hradu : |‖e + (v : Domain n)‖ - ‖e + (u : Domain n)‖| ≤ ε * ‖u - v‖ := by
    rwa [abs_sub_comm]
  have hup : ‖e + (u : Domain n)‖ ≤ 1 + ε :=
    (norm_add_le e (u : Domain n)).trans (by
      rw [he]
      exact add_le_add le_rfl hu)
  have hforward : ‖e + (u : Domain n)‖ • (ψ u - ψ v) =
      ((u : Domain n) - v) + (‖e + (v : Domain n)‖ - ‖e + (u : Domain n)‖) • ψ v := by
    rw [smul_sub, hrec u, sub_smul, hrec v]
    module
  have hback : ((u : Domain n) - v) =
      ‖e + (u : Domain n)‖ • (ψ u - ψ v) +
        (‖e + (u : Domain n)‖ - ‖e + (v : Domain n)‖) • ψ v := by
    rw [smul_sub, hrec u, sub_smul, hrec v]
    module
  have hfbound : ‖e + (u : Domain n)‖ * ‖ψ u - ψ v‖ ≤ ‖u - v‖ + ε * ‖u - v‖ := by
    calc
      _ = ‖‖e + (u : Domain n)‖ • (ψ u - ψ v)‖ := by rw [norm_smul, norm_norm]
      _ = ‖((u : Domain n) - v) +
          (‖e + (v : Domain n)‖ - ‖e + (u : Domain n)‖) • ψ v‖ := congrArg norm hforward
      _ ≤ ‖(u : Domain n) - v‖ +
          ‖(‖e + (v : Domain n)‖ - ‖e + (u : Domain n)‖) • ψ v‖ := norm_add_le _ _
      _ = ‖u - v‖ + |‖e + (v : Domain n)‖ - ‖e + (u : Domain n)‖| := by
        rw [norm_smul, Real.norm_eq_abs, hnorm, mul_one]
        rfl
      _ ≤ _ := add_le_add le_rfl hradu
  have hb : ‖u - v‖ ≤ (1 + ε) * ‖ψ u - ψ v‖ + ε * ‖u - v‖ := by
    calc
      ‖u - v‖ = ‖((u : Domain n) - v)‖ := rfl
      _ = ‖‖e + (u : Domain n)‖ • (ψ u - ψ v) +
          (‖e + (u : Domain n)‖ - ‖e + (v : Domain n)‖) • ψ v‖ := congrArg norm hback
      _ ≤ ‖‖e + (u : Domain n)‖ • (ψ u - ψ v)‖ +
          ‖(‖e + (u : Domain n)‖ - ‖e + (v : Domain n)‖) • ψ v‖ := norm_add_le _ _
      _ = ‖e + (u : Domain n)‖ * ‖ψ u - ψ v‖ +
          |‖e + (u : Domain n)‖ - ‖e + (v : Domain n)‖| := by
        rw [norm_smul, norm_norm, norm_smul, Real.norm_eq_abs, hnorm, mul_one]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hup (norm_nonneg _)) hrad
  constructor
  · have hmono := mul_le_mul_of_nonneg_right (hge u) (norm_nonneg (ψ u - ψ v))
    nlinarith only [hfbound, hmono]
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sub_pos.mpr hε1)).mpr
    nlinarith only [hb]

/-- The central projection is a genuine sphere point and has the literal
inverse obtained by dividing by its positive normal coordinate. -/
theorem sphereSurface_chart_geometry {n : ℕ} (e : Domain n) (he : ‖e‖ = 1)
    (u : (ℝ ∙ e)ᗮ) :
    let ψ : Domain n := ‖e + (u : Domain n)‖⁻¹ • (e + u)
    1 ≤ ‖e + (u : Domain n)‖ ∧ ‖ψ‖ = 1 ∧
      inner ℝ e ψ = ‖e + (u : Domain n)‖⁻¹ ∧
      (inner ℝ e ψ)⁻¹ • ψ - e = (u : Domain n) := by
  have horth : inner ℝ e (u : Domain n) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp u.property
  have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero e (u : Domain n) horth
  rw [he] at hsq
  have hge : 1 ≤ ‖e + (u : Domain n)‖ := by
    nlinarith only [hsq, sq_nonneg ‖(u : Domain n)‖, norm_nonneg (e + (u : Domain n))]
  have hpos : 0 < ‖e + (u : Domain n)‖ := lt_of_lt_of_le zero_lt_one hge
  have hpair : inner ℝ e (e + (u : Domain n)) = 1 := by
    rw [inner_add_right, horth, add_zero, real_inner_self_eq_norm_sq, he, one_pow]
  have hin : inner ℝ e (‖e + (u : Domain n)‖⁻¹ • (e + u)) = ‖e + (u : Domain n)‖⁻¹ := by
    rw [inner_smul_right, hpair, mul_one]
  refine ⟨hge, ?_, hin, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hpos.ne']
  · rw [hin, inv_inv, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    abel

/-- The literal central chart is continuous on its entire tangent space. -/
theorem sphereSurface_chart_continuous {n : ℕ} (e : Domain n) (he : ‖e‖ = 1) :
    Continuous (fun u : (ℝ ∙ e)ᗮ => ‖e + (u : Domain n)‖⁻¹ • (e + u)) := by
  have h : Continuous (fun u : (ℝ ∙ e)ᗮ => e + (u : Domain n)) :=
    continuous_const.add continuous_subtype_val
  exact (h.norm.inv₀ (fun u => (lt_of_lt_of_le zero_lt_one
    (sphereSurface_chart_geometry e he u).1).ne')).smul h

/-- On a tangent ball of radius less than one, the actual chart has finite
Lipschitz and inverse Lipschitz constants tending to one with that radius. -/
theorem sphereSurface_chart_lipschitz {n : ℕ} (e : Domain n) (he : ‖e‖ = 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1) :
    let ψ : (ℝ ∙ e)ᗮ → Domain n := fun u => ‖e + (u : Domain n)‖⁻¹ • (e + u)
    LipschitzOnWith (Real.toNNReal (1 + ε)) ψ (Metric.closedBall 0 ε) ∧
      AntilipschitzWith (Real.toNNReal ((1 + ε) / (1 - ε)))
        (fun u : Metric.closedBall (0 : (ℝ ∙ e)ᗮ) ε => ψ u.val) := by
  dsimp only
  constructor
  · apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    have hub : ‖u‖ ≤ ε := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
    have hvb : ‖v‖ ≤ ε := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    simpa only [dist_eq_norm, Real.coe_toNNReal _ (by linarith only [hε] : 0 ≤ 1 + ε)] using
      (sphereSurface_chart_distortion e he ε hε1 u v hub hvb).1
  · apply AntilipschitzWith.of_le_mul_dist
    intro u v
    have hub : ‖u.val‖ ≤ ε := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using u.property
    have hvb : ‖v.val‖ ≤ ε := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using v.property
    have hK : 0 ≤ (1 + ε) / (1 - ε) :=
      div_nonneg (by linarith only [hε]) (sub_pos.mpr hε1).le
    simpa only [Subtype.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hK] using
      (sphereSurface_chart_distortion e he ε hε1 u.val v.val hub hvb).2

end HarmonicMaps
end
