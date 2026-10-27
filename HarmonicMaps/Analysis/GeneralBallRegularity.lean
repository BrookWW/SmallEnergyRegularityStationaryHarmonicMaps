module

public import HarmonicMaps.Analysis.UnitBallRegularity
public import HarmonicMaps.Analysis.AffineMinimizerTransport

/-!
# Regularity on arbitrary compactly contained balls

The actual affine minimizer transport supplies the same unit-ball energy.
The unit representative is transported to the open inner-ball subtype by
its inverse affine map. Restricted-volume transport gives AE equality;
exact distance scaling gives the source radius power and full uniqueness.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace HarmonicMaps

/-- Original locally minimizing Sobolev data give the full target-valued
representative and exact radius-scaled Hölder estimate on every source ball. -/
theorem generalBallRegularity_complete
    {n q : ℕ} (hn : 2 ≤ n) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ε α : ℝ, ∃ C : ℝ≥0,
      0 < ε ∧ 0 < α ∧ α < 1 ∧
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q)
        (Du : Domain n → Gradient n q),
        MemW12Loc Ω u Du →
        TakesValuesIn N Ω u →
        IsLocallyEnergyMinimizing N Ω u Du →
        ∀ (a : Domain n) (R : PositiveRadius),
          Metric.closedBall a R.val ⊆ Ω.val →
          normalizedEnergy Du a R ≤ ENNReal.ofReal ε →
          ∃ w : Metric.ball a (R.val / 2) → Ambient q,
            IsContinuousRepresentative (ballDomain a (R.val / 2)) u w ∧
            (∀ x, w x ∈ N.carrierSet) ∧
            (∀ x y : Metric.ball a (R.val / 2),
              ‖w x - w y‖ ≤
                (C : ℝ) * Real.rpow R.val (-α) *
                  Real.sqrt (normalizedEnergy Du a R).toReal *
                  Real.rpow (dist (x : Domain n) (y : Domain n)) α) ∧
            ∀ v : Metric.ball a (R.val / 2) → Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val / 2)) u v →
              v = w := by
  obtain ⟨ε, α, C, hε, hα, hαOne, hUnit⟩ := unitBallRegularity_complete n hn q N
  refine ⟨ε, α, C, hε, hα, hαOne, ?_⟩
  intro Ω u Du hu hN hmin a R hclosed hsmall
  obtain ⟨hv, hNv, hMinV, hEnergy⟩ :=
    affineBall_minimizer_transport N Ω a R u Du hclosed hu hN hmin
  have hSmallV : dirichletEnergy (fun z i => R.val • Du (a + R.val • z) i)
      (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal ε := hEnergy.trans_le hsmall
  obtain ⟨w0, hw0, hTarget, hHolder, _hUniqueUnit⟩ :=
    hUnit _ _ hv hNv hMinV hSmallV
  let Q : Domain n → Domain n := fun x => R.val⁻¹ • (x - a)
  have hRadius : (1 / 2 : ℝ) / R.val⁻¹ = R.val / 2 := by
    rw [div_inv_eq_mul]
    ring
  have hQmem (x : Metric.ball a (R.val / 2)) : Q x.val ∈ Metric.ball (0 : Domain n) (1 / 2) := by
    have h := (affineBall_mem_ball_iff (0 : Domain n) a (inv_pos.mpr R.property)
      (1 / 2) x.val).mpr (by rw [hRadius]; exact x.property)
    simpa only [zero_add] using h
  let F : Metric.ball a (R.val / 2) → Metric.ball (0 : Domain n) (1 / 2) :=
    fun x => ⟨Q x.val, hQmem x⟩
  let w : Metric.ball a (R.val / 2) → Ambient q := fun x => w0 (F x)
  have hPQ (x : Domain n) : a + R.val • Q x = x := by
    dsimp only [Q]
    rw [smul_smul, mul_inv_cancel₀ R.property.ne', one_smul]
    exact add_sub_cancel _ _
  have hContinuousF : Continuous F := by
    apply Continuous.subtype_mk
    change Continuous (fun x : Metric.ball a (R.val / 2) => R.val⁻¹ • (x.val - a))
    have hSub : Continuous (fun x : Metric.ball a (R.val / 2) => x.val - a) :=
      continuous_subtype_val.sub continuous_const
    exact hSub.const_smul R.val⁻¹
  have hAE : ∀ᵐ x ∂volume.restrict (Metric.ball a (R.val / 2)),
      ∀ hx : x ∈ Metric.ball a (R.val / 2), w ⟨x, hx⟩ = u x := by
    have h := ae_affineBall (0 : Domain n) a (inv_pos.mpr R.property) (1 / 2) hw0.2
    rw [hRadius] at h
    simp only [zero_add] at h
    filter_upwards [h] with x hx
    intro hball
    change w0 ⟨Q x, hQmem ⟨x, hball⟩⟩ = u x
    have hh := hx (hQmem ⟨x, hball⟩)
    rw [hPQ] at hh
    exact hh
  have hRep : IsContinuousRepresentative (ballDomain a (R.val / 2)) u w :=
    ⟨hw0.1.comp hContinuousF, hAE⟩
  refine ⟨w, hRep, fun x => hTarget (F x), ?_, ?_⟩
  · intro x y
    have hDistance : dist (Q x.val) (Q y.val) = R.val⁻¹ * dist x.val y.val := by
      dsimp only [Q]
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr R.property)]
      congr 1
      rw [sub_sub_sub_cancel_right, ← dist_eq_norm]
    have hPower : Real.rpow (dist (Q x.val) (Q y.val)) α =
        Real.rpow R.val (-α) * Real.rpow (dist x.val y.val) α := by
      simp only [Real.rpow_eq_pow]
      rw [hDistance, Real.mul_rpow (inv_pos.mpr R.property).le dist_nonneg,
        ← Real.rpow_neg_eq_inv_rpow]
    have hBound := hHolder (F x) (F y)
    change ‖w x - w y‖ ≤ (C : ℝ) *
      Real.sqrt (dirichletEnergy (fun z i => R.val • Du (a + R.val • z) i)
        (Metric.ball (0 : Domain n) 1)).toReal *
      Real.rpow (dist (Q x.val) (Q y.val)) α at hBound
    rw [hEnergy, hPower] at hBound
    exact hBound.trans_eq (by ring)
  · intro v hRepV
    exact hRepV.unique hRep

end HarmonicMaps
end
