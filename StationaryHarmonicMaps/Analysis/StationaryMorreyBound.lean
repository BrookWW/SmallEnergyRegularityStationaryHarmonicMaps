module

public import StationaryHarmonicMaps.Frozen.Monotonicity

/-!
# Interior truncated-ball energy bounds

Domain stationarity controls every truncated ball in the inner three-quarter
ball. The constant is exactly the manuscript's `4^(n-2)`, including `n = 2`.
-/

public section

open HarmonicMaps MeasureTheory Set Metric

namespace StationaryHarmonicMaps.Analysis

/-- Extended Dirichlet energy is monotone under set inclusion. -/
theorem dirichletEnergy_mono_set {n q : ℕ} (Du : Domain n → Gradient n q)
    {U V : Set (Domain n)} (hUV : U ⊆ V) :
    dirichletEnergy Du U ≤ dirichletEnergy Du V :=
  lintegral_mono_set hUV

/-- The negative normalization power decreases with the positive radius. -/
theorem normalization_power_antitone {n : ℕ} (hn : 2 ≤ n)
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    s ^ (2 - (n : ℤ)) ≤ r ^ (2 - (n : ℤ)) := by
  have hexp : 2 - (n : ℤ) = -((n - 2 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  exact (inv_le_inv₀ (pow_pos (hr.trans_le hrs) _) (pow_pos hr _)).2
    (pow_le_pow_left₀ hr.le hrs _)

/-- Changing the reference radius by four gives the exact normalization factor. -/
theorem quarter_radius_normalization {n : ℕ} (hn : 2 ≤ n) (R : ℝ) :
    (R / 4) ^ (2 - (n : ℤ)) = (4 : ℝ) ^ (n - 2) * R ^ (2 - (n : ℤ)) := by
  have hexp : 2 - (n : ℤ) = -((n - 2 : ℕ) : ℤ) := by omega
  simp only [hexp, zpow_neg, zpow_natCast, div_pow, inv_div]
  ring

/-- Stationarity gives the source bound on each positive-radius truncated ball. -/
theorem stationary_truncated_ball_energy_bound {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hstationary : IsDomainStationary Ω Du) (hu : MemW12Loc Ω u Du)
    {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val)
    {x : Domain n} (hx : x ∈ Metric.ball a (3 * R / 4))
    {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (r ^ (2 - (n : ℤ))) *
      dirichletEnergy Du (Metric.ball x r ∩ Metric.ball a (3 * R / 4)) ≤
      ENNReal.ofReal ((4 : ℝ) ^ (n - 2)) * normalizedEnergy Du a ⟨R, hR⟩ := by
  have hquarter : 0 < R / 4 := by positivity
  have hxR : Metric.closedBall x (R / 4) ⊆ Metric.ball a R := by
    intro y hy
    have hd := dist_triangle y x a
    have hy' : dist y x ≤ R / 4 := hy
    have hx' : dist x a < 3 * R / 4 := hx
    change dist y a < R
    linarith only [hd, hy', hx']
  have hclosedx : Metric.closedBall x (R / 4) ⊆ Ω.val :=
    hxR.trans (Metric.ball_subset_closedBall.trans hball)
  have hquarter_bound : normalizedEnergy Du x ⟨R / 4, hquarter⟩ ≤
      ENNReal.ofReal ((4 : ℝ) ^ (n - 2)) * normalizedEnergy Du a ⟨R, hR⟩ := by
    unfold normalizedEnergy
    calc
      _ ≤ ENNReal.ofReal ((R / 4) ^ (2 - (n : ℤ))) *
          dirichletEnergy Du (Metric.ball a R) :=
        mul_le_mul_right (dirichletEnergy_mono_set Du
          (Metric.ball_subset_closedBall.trans hxR)) _
      _ = _ := by
        rw [quarter_radius_normalization hn, ENNReal.ofReal_mul (by positivity)]
        exact mul_assoc _ _ _
  by_cases hsmall : r ≤ R / 4
  · have hnorm : normalizedEnergy Du x ⟨r, hr⟩ ≤
        normalizedEnergy Du x ⟨R / 4, hquarter⟩ := by
      rcases lt_or_eq_of_le hsmall with hlt | rfl
      · exact (hstationary.monotonicity hn hu hquarter hclosedx hr hlt le_rfl).2.2
      · exact le_rfl
    exact (mul_le_mul_right (dirichletEnergy_mono_set Du inter_subset_left) _).trans
      (hnorm.trans hquarter_bound)
  · have hsub : Metric.ball x r ∩ Metric.ball a (3 * R / 4) ⊆ Metric.ball a R :=
      inter_subset_right.trans (Metric.ball_subset_ball (by linarith only [hR]))
    calc
      _ ≤ ENNReal.ofReal ((R / 4) ^ (2 - (n : ℤ))) *
          dirichletEnergy Du (Metric.ball a R) :=
        mul_le_mul (ENNReal.ofReal_le_ofReal (normalization_power_antitone hn
          hquarter (le_of_not_ge hsmall))) (dirichletEnergy_mono_set Du hsub) zero_le zero_le
      _ = _ := by
        rw [quarter_radius_normalization hn, normalizedEnergy,
          ENNReal.ofReal_mul (by positivity)]
        exact mul_assoc _ _ _

end StationaryHarmonicMaps.Analysis

end
