module

public import HolderToCK.Analysis.Poisson.PotentialDerivatives

/-! # Actual first derivatives of compact-data Newtonian potentials -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace HolderToCK

@[expose] noncomputable def potentialGradientColumn {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (g : Domain n → E) (x : Domain n) : E :=
  ∫ z, ((euclideanSphereArea n)⁻¹ * ‖z‖ ^ (-(n : ℝ)) * z i) • g (x - z)

theorem potentialGradientColumn_integrable {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i : Fin n) {g : Domain n → E}
    (hg : Continuous g) (hcg : HasCompactSupport g) (x : Domain n) :
    Integrable (fun z => ((euclideanSphereArea n)⁻¹ * ‖z‖ ^ (-(n : ℝ)) * z i) •
      g (x - z)) volume :=
  (normalizedRadialColumn_locallyIntegrable hn i).integrable_smul_right_of_hasCompactSupport
    (hg.comp (continuous_const.sub continuous_id)) (hcg.comp_homeomorph (Homeomorph.subLeft x))

theorem potentialGradientColumn_applyCLM {n : ℕ}
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hn : 0 < n) (i : Fin n) (L : E →L[ℝ] F) {g : Domain n → E}
    (hg : Continuous g) (hcg : HasCompactSupport g) (x : Domain n) :
    L (potentialGradientColumn i g x) = potentialGradientColumn i (fun z => L (g z)) x := by
  rw [potentialGradientColumn, potentialGradientColumn,
    ← L.integral_comp_comm (potentialGradientColumn_integrable hn i hg hcg x)]
  apply integral_congr_ae
  filter_upwards with z
  exact L.map_smul _ _

theorem compactData_clm_column {n : ℕ}
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {g : Domain n → E} (hg : ContDiff ℝ 1 g) (x : Domain n) (i : Fin n) :
    fderiv ℝ (fun z => L (g z)) x (EuclideanSpace.single i 1) =
      L (fderiv ℝ g x (EuclideanSpace.single i 1)) := by
  have hd := L.hasFDerivAt.comp x (hg.differentiable one_ne_zero x).hasFDerivAt
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  rfl

theorem newtonianPotential_column_eq_gradient_scalar {n : ℕ}
    (hn : 2 ≤ n) (i : Fin n) {g : Domain n → ℝ} (hg : ContDiff ℝ 1 g)
    (hcg : HasCompactSupport g) (x : Domain n) :
    fderiv ℝ (newtonianPotential hn g) x (EuclideanSpace.single i 1) =
      potentialGradientColumn i g x := by
  let φ : Domain n → ℝ := fun z => g (x - z)
  have hφ : ContDiff ℝ 1 φ := hg.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := hcg.comp_homeomorph (Homeomorph.subLeft x)
  have hcol (z : Domain n) : fderiv ℝ φ z (EuclideanSpace.single i 1) =
      -(fderiv ℝ g (x - z) (EuclideanSpace.single i 1)) := by
    rw [(compactData_sub_hasFDerivAt hg x z).fderiv]
    rfl
  rw [newtonianPotential_fderiv_data hn hg hcg]
  by_cases hn2 : n = 2
  · subst n
    rw [newtonianPotential_eq_log, potentialGradientColumn]
    have hweak := fundamentalLog_testDerivative hφ hcφ i
    simp_rw [hcol, mul_neg] at hweak
    rw [integral_neg] at hweak
    exact neg_injective hweak
  · have hn3 : 3 ≤ n := by omega
    rw [newtonianPotential_eq_power hn3, potentialGradientColumn]
    have hweak := fundamentalPower_testDerivative hn3 hφ hcφ i
    simp_rw [hcol, mul_neg] at hweak
    rw [integral_neg] at hweak
    exact neg_injective hweak

theorem newtonianPotential_column_eq_gradient {n q : ℕ}
    (hn : 2 ≤ n) (i : Fin n) {g : Domain n → Ambient q} (hg : ContDiff ℝ 1 g)
    (hcg : HasCompactSupport g) (x : Domain n) :
    fderiv ℝ (newtonianPotential hn g) x (EuclideanSpace.single i 1) =
      potentialGradientColumn i g x := by
  ext a
  let L : Ambient q →L[ℝ] ℝ := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) a
  change L (fderiv ℝ (newtonianPotential hn g) x (EuclideanSpace.single i 1)) =
    L (potentialGradientColumn i g x)
  have hD : Continuous (fun z => fderiv ℝ g z (EuclideanSpace.single i 1)) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [newtonianPotential_fderiv_data hn hg hcg,
    newtonianPotential_applyCLM hn L hD (hcg.fderiv_apply ℝ _) x,
    potentialGradientColumn_applyCLM (by omega : 0 < n) i L hg.continuous hcg x]
  have hgL : ContDiff ℝ 1 (fun z => L (g z)) := L.contDiff.comp hg
  have hcgL : HasCompactSupport (fun z => L (g z)) := hcg.comp_left L.map_zero
  have hs := newtonianPotential_column_eq_gradient_scalar hn i hgL hcgL x
  rw [newtonianPotential_fderiv_data hn hgL hcgL] at hs
  have heq : (fun z => fderiv ℝ (fun w => L (g w)) z (EuclideanSpace.single i 1)) =
      (fun z => L (fderiv ℝ g z (EuclideanSpace.single i 1))) :=
    funext (fun z => compactData_clm_column L hg z i)
  rw [heq] at hs
  exact hs

end HolderToCK
end
