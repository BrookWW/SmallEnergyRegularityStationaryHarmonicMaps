module

public import HarmonicMaps.Energy
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Joint continuity of positive-collar radial primitives

Continuous closed-ball data give a jointly continuous radial integrand on a
positive collar. The interval integral is continuous jointly in direction and
upper radius, including the outer radius. Radius projection supplies a proof
local continuous integrand beyond the integration interval.
-/

public section

open MeasureTheory Set Filter
open scoped Topology Interval

namespace HarmonicMaps

/-- A continuous closed-ball datum has a genuine weighted radial primitive
which is jointly continuous in direction and radius on every positive collar.
The integrand agrees with the literal weight and datum throughout the collar. -/
theorem closedBall_radial_primitive_joint_continuous {n q : ℕ}
    (R : PositiveRadius) (a : ℝ) (ha : 0 < a) (haR : a ≤ R.val)
    (k : ℤ) (w : Metric.closedBall (0 : Domain n) R.val → Ambient q)
    (hw : Continuous w) :
    ∃ J : Metric.sphere (0 : Domain n) 1 → ℝ → Ambient q,
      Continuous (fun p : Metric.sphere (0 : Domain n) 1 × ℝ => J p.1 p.2) ∧
      (∀ (θ : Metric.sphere (0 : Domain n) 1) (s : ℝ) (_hs : s ∈ Icc a R.val),
        ∃ hball : s • θ.val ∈ Metric.closedBall (0 : Domain n) R.val,
          J θ s = s ^ k • w ⟨s • θ.val, hball⟩) ∧
      Continuous (fun p : Metric.sphere (0 : Domain n) 1 × Icc a R.val =>
        ∫ s in a..p.2.val, J p.1 s) := by
  let S := Metric.sphere (0 : Domain n) 1
  let c : ℝ → ℝ := fun s => (projIcc a R.val haR s).val
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hcnonzero (s : ℝ) : c s ≠ 0 :=
    (ha.trans_le (projIcc a R.val haR s).property.1).ne'
  have htheta (θ : S) : ‖θ.val‖ = 1 := by
    simpa only [S, Metric.mem_sphere, dist_zero_right] using θ.property
  have hball (θ : S) (s : ℝ) : c s • θ.val ∈ Metric.closedBall (0 : Domain n) R.val := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (ha.le.trans (projIcc a R.val haR s).property.1), htheta, mul_one]
    exact (projIcc a R.val haR s).property.2
  let β : S × ℝ → Metric.closedBall (0 : Domain n) R.val := fun p =>
    ⟨c p.2 • p.1.val, hball p.1 p.2⟩
  have hβ : Continuous β :=
    Continuous.subtype_mk ((hc.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)) _
  let J : S → ℝ → Ambient q := fun θ s => (c s) ^ k • w (β (θ, s))
  have hJ : Continuous (fun p : S × ℝ => J p.1 p.2) :=
    ((hc.comp continuous_snd).zpow₀ k (fun p => Or.inl (hcnonzero p.2))).smul
      (hw.comp hβ)
  have hK : IsCompact ((univ : Set S) ×ˢ Icc (a - 1) (R.val + 1)) :=
    isCompact_univ.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hJ.continuousOn
  have hbig : a - 1 ≤ R.val + 1 := by linarith only [haR]
  have hmeas (θ : S) : AEStronglyMeasurable (J θ)
      (volume.restrict (Ι (a - 1) (R.val + 1))) :=
    (hJ.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbound (θ : S) : ∀ᵐ s ∂volume.restrict (Ι (a - 1) (R.val + 1)), ‖J θ s‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le hbig] at hs
    exact hC (θ, s) ⟨mem_univ _, hs.1.le, hs.2⟩
  have hcontinuous : Continuous (fun p : S × Icc a R.val => ∫ s in a..p.2.val, J p.1 s) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hAt : ContinuousAt (fun z : S × ℝ => ∫ s in a..z.2, J z.1 s) (p.1, p.2.val) := by
      apply intervalIntegral.continuousAt_parametric_primitive_of_dominated
        (fun _ : ℝ => C) (a - 1) (R.val + 1) hmeas
        (Eventually.of_forall hbound) intervalIntegrable_const
      · filter_upwards with s
        exact (hJ.comp (continuous_id.prodMk continuous_const)).continuousAt
      · constructor <;> linarith only [haR]
      · constructor
        · linarith only [p.2.property.1]
        · linarith only [p.2.property.2]
      · exact measure_singleton _
    exact hAt.comp (f := fun z : S × Icc a R.val => (z.1, z.2.val))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousAt
  refine ⟨J, hJ, ?_, hcontinuous⟩
  intro θ s hs
  have hcs : c s = s := congrArg Subtype.val (projIcc_of_mem haR hs)
  have hsball : s • θ.val ∈ Metric.closedBall (0 : Domain n) R.val := by
    simpa only [hcs] using hball θ s
  refine ⟨hsball, ?_⟩
  change (c s) ^ k • w ⟨c s • θ.val, hball θ s⟩ = s ^ k • w ⟨s • θ.val, hsball⟩
  simp only [hcs]

end HarmonicMaps
end
