module

public import HarmonicMaps.EnergyLemmas
public import StationaryHarmonicMaps.Foundation.CriticalGradientMorrey
public import StationaryHarmonicMaps.Frozen.StationaryMorreyBound
public import StationaryHarmonicMaps.Analysis.AntisymmetricPotential
public import StationaryHarmonicMaps.Analysis.OperatorHSCoefficientBounds

/-!
# Hilbert--Schmidt control of the actual antisymmetric potential

The coefficient norm includes every domain, input and output index. A
uniform ambient derivative bound supplies one target-dependent constant.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The true coefficient square sum is controlled by the given gradient's HS density. -/
theorem ae_normal_projection_potential_hs_sq_le {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    {G : Ambient q → Ambient q →L[ℝ] Ambient q} (_hG : ContDiff ℝ 1 G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L) :
    ∀ᵐ x ∂volume.restrict Ω.val,
      (∑ i : Fin n, ∑ j : Fin q,
        ‖projectionCommutator (G (u x)) (fderiv ℝ G (u x) (Du x i))
          (EuclideanSpace.single j 1)‖ ^ 2) ≤
        (q : ℝ) * (2 * L) ^ 2 * hsNormSq (Du x) := by
  filter_upwards [hN] with x hx
  have hP : ‖G (u x)‖ ≤ 1 := by
    rw [hGN ⟨u x, hx⟩]
    exact N.normalProjection_norm_le_one _
  exact commutator_hs_sq_le (G (u x)) (fun i => fderiv ℝ G (u x) (Du x i))
    (Du x) hP hL (fun i => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hDG (u x)) (norm_nonneg _)))

/-- The genuine matrix one-form norm is bounded by the same map's HS gradient norm. -/
theorem ae_normal_projection_potential_hsNorm_le {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    {G : Ambient q → Ambient q →L[ℝ] Ambient q} (_hG : ContDiff ℝ 1 G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L) :
    ∀ᵐ x ∂volume.restrict Ω.val,
      Real.sqrt (∑ i : Fin n, ∑ j : Fin q,
        ‖projectionCommutator (G (u x)) (fderiv ℝ G (u x) (Du x i))
          (EuclideanSpace.single j 1)‖ ^ 2) ≤
        (2 * Real.sqrt (q : ℝ) * L) * Real.sqrt (hsNormSq (Du x)) := by
  filter_upwards [hN] with x hx
  have hP : ‖G (u x)‖ ≤ 1 := by
    rw [hGN ⟨u x, hx⟩]
    exact N.normalProjection_norm_le_one _
  exact commutator_hsNorm_le (G (u x)) (fun i => fderiv ℝ G (u x) (Du x i))
    (Du x) hP hL (fun i => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hDG (u x)) (norm_nonneg _)))

/-- The actual Hilbert--Schmidt norm of the potential belongs to local L². -/
theorem locallyMemL2_normal_projection_potential_hsNorm {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    {G : Ambient q → Ambient q →L[ℝ] Ambient q} (hG : ContDiff ℝ 1 G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L) :
    LocallyMemL2 Ω (fun x => Real.sqrt (∑ i : Fin n, ∑ j : Fin q,
      ‖projectionCommutator (G (u x)) (fderiv ℝ G (u x) (Du x i))
        (EuclideanSpace.single j 1)‖ ^ 2)) := by
  intro K hK hs
  have hm := (hu.2.1 K hK hs).aestronglyMeasurable
  have hPmeas := hG.continuous.comp_aestronglyMeasurable hm
  have hDmeas (i : Fin n) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (((hG.continuous_fderiv (by simp)).comp_aestronglyMeasurable hm).prodMk
        (hu.2.2 i K hK hs).aestronglyMeasurable)
  have hP : ∀ᵐ x ∂volume.restrict K, ‖G (u x)‖ ≤ 1 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hN] with x hx
    rw [hGN ⟨u x, hx⟩]
    exact N.normalProjection_norm_le_one _
  apply memLp_commutator_hsNorm (fun x => G (u x))
    (fun x i => fderiv ℝ G (u x) (Du x i)) Du hL hPmeas hDmeas hP
  · filter_upwards [] with x
    intro i
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hDG (u x)) (norm_nonneg _))
  · exact fun i => hu.2.2 i K hK hs

/-- The coefficient square energy on any subset is bounded by the actual gradient energy. -/
theorem normal_projection_potential_energy_le {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    {G : Ambient q → Ambient q →L[ℝ] Ambient q} (hG : ContDiff ℝ 1 G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L)
    {S : Set (Domain n)} (hS : S ⊆ Ω.val) :
    (∫⁻ x in S, ENNReal.ofReal (∑ i : Fin n, ∑ j : Fin q,
      ‖projectionCommutator (G (u x)) (fderiv ℝ G (u x) (Du x i))
        (EuclideanSpace.single j 1)‖ ^ 2)) ≤
      ENNReal.ofReal ((q : ℝ) * (2 * L) ^ 2) * dirichletEnergy Du S := by
  have hsq := ae_restrict_of_ae_restrict_of_subset hS
    (ae_normal_projection_potential_hs_sq_le N (Du := Du) hN hG hGN hL hDG)
  calc
    _ ≤ ∫⁻ x in S, ENNReal.ofReal ((q : ℝ) * (2 * L) ^ 2 * hsNormSq (Du x)) :=
      lintegral_mono_ae (hsq.mono (fun _ h => ENNReal.ofReal_le_ofReal h))
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (q : ℝ) * (2 * L) ^ 2)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Every truncated-ball term of the potential is controlled by the gradient Morrey square. -/
theorem normal_projection_potential_truncated_morrey_le {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    {G : Ambient q → Ambient q →L[ℝ] Ambient q} (hG : ContDiff ℝ 1 G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L)
    {D : Set (Domain n)} (hD : D ⊆ Ω.val) {x : Domain n} (hx : x ∈ D)
    (r : PositiveRadius) :
    ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) *
      (∫⁻ y in Metric.ball x r.val ∩ D, ENNReal.ofReal (∑ i : Fin n, ∑ j : Fin q,
        ‖projectionCommutator (G (u y)) (fderiv ℝ G (u y) (Du y i))
          (EuclideanSpace.single j 1)‖ ^ 2)) ≤
      ENNReal.ofReal ((q : ℝ) * (2 * L) ^ 2) * criticalGradientMorreySquare Du D := by
  have henergy := normal_projection_potential_energy_le N (Du := Du) hN hG hGN hL hDG
    (inter_subset_right.trans hD : Metric.ball x r.val ∩ D ⊆ Ω.val)
  have hterm : ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) *
      dirichletEnergy Du (Metric.ball x r.val ∩ D) ≤ criticalGradientMorreySquare Du D :=
    le_iSup_of_le ⟨x, hx⟩ (le_iSup_of_le r le_rfl)
  calc
    _ ≤ ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) *
        (ENNReal.ofReal ((q : ℝ) * (2 * L) ^ 2) *
          dirichletEnergy Du (Metric.ball x r.val ∩ D)) := mul_le_mul_right henergy _
    _ = ENNReal.ofReal ((q : ℝ) * (2 * L) ^ 2) *
        (ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) *
          dirichletEnergy Du (Metric.ball x r.val ∩ D)) := by ac_rfl
    _ ≤ _ := mul_le_mul_right hterm _

/-- Stationarity bounds the gradient and potential on every interior truncated ball. -/
theorem stationary_joint_truncated_morrey_bound {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hstationary : IsDomainStationary Ω Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    {G : Ambient q → Ambient q →L[ℝ] Ambient q} (hG : ContDiff ℝ 1 G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L)
    {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val)
    {x : Domain n} (hx : x ∈ Metric.ball a (3 * R / 4)) (r : PositiveRadius) :
    ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) *
      (dirichletEnergy Du (Metric.ball x r.val ∩ Metric.ball a (3 * R / 4)) +
        ∫⁻ y in Metric.ball x r.val ∩ Metric.ball a (3 * R / 4),
          ENNReal.ofReal (∑ i : Fin n, ∑ j : Fin q,
            ‖projectionCommutator (G (u y)) (fderiv ℝ G (u y) (Du y i))
              (EuclideanSpace.single j 1)‖ ^ 2)) ≤
      (1 + ENNReal.ofReal ((q : ℝ) * (2 * L) ^ 2)) *
        ENNReal.ofReal ((4 : ℝ) ^ (n - 2)) * normalizedEnergy Du a ⟨R, hR⟩ := by
  have hD : Metric.ball a (3 * R / 4) ⊆ Ω.val :=
    (Metric.ball_subset_ball (by linarith only [hR])).trans
      (Metric.ball_subset_closedBall.trans hball)
  have hM := stationary_morrey_bound hn hstationary hu hR hball
  have hA := normal_projection_potential_truncated_morrey_le N (Du := Du) hN hG hGN hL hDG hD hx r
  have hDu := stationary_truncated_ball_energy_bound hn hstationary hu hR hball hx r.property
  rw [mul_add]
  calc
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ (n - 2)) * normalizedEnergy Du a ⟨R, hR⟩ +
        ENNReal.ofReal ((q : ℝ) * (2 * L) ^ 2) *
          (ENNReal.ofReal ((4 : ℝ) ^ (n - 2)) * normalizedEnergy Du a ⟨R, hR⟩) :=
      add_le_add hDu (hA.trans (mul_le_mul_right hM _))
    _ = _ := by ring


end StationaryHarmonicMaps.Analysis

end
