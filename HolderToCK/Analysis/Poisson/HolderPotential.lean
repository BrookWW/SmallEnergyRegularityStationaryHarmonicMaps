module

public import HolderToCK.Analysis.Poisson.DistributionIdentity
public import HolderToCK.Analysis.ConvolutionDerivatives
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! # The Newtonian potential on the punctured integration carrier -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology Convolution

namespace HolderToCK

@[expose] noncomputable def newtonianPotential {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 2 ≤ n) (g : Domain n → E) (x : Domain n) : E :=
  ∫ z : {z : Domain n // z ≠ 0}, fundamentalSolution n hn z • g (x - z.val)
    ∂(volume : Measure (Domain n)).comap (Subtype.val : {z : Domain n // z ≠ 0} → Domain n)

theorem newtonianPotential_eq_power {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 3 ≤ n) (g : Domain n → E) (x : Domain n) :
    newtonianPotential (by omega : 2 ≤ n) g x =
      ∫ z, fundamentalPowerExpression z • g (x - z) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega : 0 < n)
  have hs : MeasurableSet {z : Domain n | z ≠ 0} :=
    (isClosed_singleton (x := (0 : Domain n))).isOpen_compl.measurableSet
  rw [newtonianPotential]
  simp_rw [fundamentalSolution_power hn]
  calc
    _ = ∫ z in {z : Domain n | z ≠ 0}, fundamentalPowerExpression z • g (x - z) :=
      integral_subtype_comap hs (fun z => fundamentalPowerExpression z • g (x - z))
    _ = _ := by
      change (∫ z in ({(0 : Domain n)}ᶜ : Set (Domain n)),
        fundamentalPowerExpression z • g (x - z)) = _
      rw [restrict_compl_singleton]

theorem newtonianPotential_eq_log
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Domain 2 → E) (x : Domain 2) :
    newtonianPotential (by omega : 2 ≤ 2) g x =
      ∫ z, fundamentalLogExpression z • g (x - z) := by
  have hs : MeasurableSet {z : Domain 2 | z ≠ 0} :=
    (isClosed_singleton (x := (0 : Domain 2))).isOpen_compl.measurableSet
  rw [newtonianPotential]
  simp_rw [fundamentalSolution_log]
  calc
    _ = ∫ z in {z : Domain 2 | z ≠ 0}, fundamentalLogExpression z • g (x - z) :=
      integral_subtype_comap hs (fun z => fundamentalLogExpression z • g (x - z))
    _ = _ := by
      change (∫ z in ({(0 : Domain 2)}ᶜ : Set (Domain 2)),
        fundamentalLogExpression z • g (x - z)) = _
      rw [restrict_compl_singleton]

theorem newtonianPotential_integrable {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 2 ≤ n) {g : Domain n → E} (hg : Continuous g) (hcg : HasCompactSupport g)
    (x : Domain n) :
    Integrable (fun z : {z : Domain n // z ≠ 0} =>
      fundamentalSolution n hn z • g (x - z.val))
      ((volume : Measure (Domain n)).comap
        (Subtype.val : {z : Domain n // z ≠ 0} → Domain n)) := by
  let L : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  have hs : MeasurableSet {z : Domain n | z ≠ 0} :=
    (isClosed_singleton (x := (0 : Domain n))).isOpen_compl.measurableSet
  by_cases hn2 : n = 2
  · subst n
    have hi : Integrable (fun z => fundamentalLogExpression z • g (x - z)) volume :=
      hcg.convolutionExists_right L fundamentalLog_locallyIntegrable hg x
    simp_rw [fundamentalSolution_log]
    exact (integrableOn_iff_comap_subtypeVal hs).mp hi.integrableOn
  · have hn3 : 3 ≤ n := by omega
    have hi : Integrable (fun z => fundamentalPowerExpression z • g (x - z)) volume :=
      hcg.convolutionExists_right L (fundamentalPower_locallyIntegrable hn3) hg x
    simp_rw [fundamentalSolution_power hn3]
    exact (integrableOn_iff_comap_subtypeVal hs).mp hi.integrableOn

theorem newtonianPotential_continuous {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 2 ≤ n) {g : Domain n → E} (hg : Continuous g) (hcg : HasCompactSupport g) :
    Continuous (newtonianPotential hn g) := by
  let L : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  by_cases hn2 : n = 2
  · subst n
    have heq : newtonianPotential hn g = fundamentalLogExpression ⋆[L, volume] g :=
      funext (newtonianPotential_eq_log g)
    rw [heq]
    exact hcg.continuous_convolution_right L fundamentalLog_locallyIntegrable hg
  · have hn3 : 3 ≤ n := by omega
    have heq : newtonianPotential hn g = fundamentalPowerExpression ⋆[L, volume] g :=
      funext (newtonianPotential_eq_power hn3 g)
    rw [heq]
    exact hcg.continuous_convolution_right L (fundamentalPower_locallyIntegrable hn3) hg

theorem newtonianPotential_contDiff {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 2 ≤ n) {g : Domain n → E} {m : ℕ∞}
    (hg : ContDiff ℝ m g) (hcg : HasCompactSupport g) :
    ContDiff ℝ m (newtonianPotential hn g) := by
  let L : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  by_cases hn2 : n = 2
  · subst n
    have heq : newtonianPotential hn g = fundamentalLogExpression ⋆[L, volume] g :=
      funext (newtonianPotential_eq_log g)
    rw [heq]
    exact hcg.contDiff_convolution_right L fundamentalLog_locallyIntegrable hg
  · have hn3 : 3 ≤ n := by omega
    have heq : newtonianPotential hn g = fundamentalPowerExpression ⋆[L, volume] g :=
      funext (newtonianPotential_eq_power hn3 g)
    rw [heq]
    exact hcg.contDiff_convolution_right L (fundamentalPower_locallyIntegrable hn3) hg

theorem newtonianPotential_fderiv_data {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 2 ≤ n) {g : Domain n → E} (hg : ContDiff ℝ 1 g)
    (hcg : HasCompactSupport g) (x v : Domain n) :
    fderiv ℝ (newtonianPotential hn g) x v =
      newtonianPotential hn (fun z => fderiv ℝ g z v) x := by
  let L : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  by_cases hn2 : n = 2
  · subst n
    have heq : newtonianPotential hn g = fundamentalLogExpression ⋆[L, volume] g :=
      funext (newtonianPotential_eq_log g)
    have hd := hcg.hasFDerivAt_convolution_right L fundamentalLog_locallyIntegrable hg x
    rw [heq, hd.fderiv, convolution_precompR_apply L fundamentalLog_locallyIntegrable
      (hcg.fderiv ℝ) (hg.continuous_fderiv one_ne_zero), newtonianPotential_eq_log]
    rfl
  · have hn3 : 3 ≤ n := by omega
    have heq : newtonianPotential hn g = fundamentalPowerExpression ⋆[L, volume] g :=
      funext (newtonianPotential_eq_power hn3 g)
    have hi := fundamentalPower_locallyIntegrable hn3
    have hd := hcg.hasFDerivAt_convolution_right L hi hg x
    rw [heq, hd.fderiv, convolution_precompR_apply L hi
      (hcg.fderiv ℝ) (hg.continuous_fderiv one_ne_zero), newtonianPotential_eq_power hn3]
    rfl

theorem newtonianPotential_mixedColumns_data {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 2 ≤ n) {g : Domain n → E} (hg : ContDiff ℝ 2 g)
    (hcg : HasCompactSupport g) (x : Domain n) (i j : Fin n) :
    fderiv ℝ (fun y => fderiv ℝ (newtonianPotential hn g) y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) =
      newtonianPotential hn (fun z =>
        fderiv ℝ (fun w => fderiv ℝ g w (EuclideanSpace.single j 1)) z
          (EuclideanSpace.single i 1)) x := by
  have heq : (fun y => fderiv ℝ (newtonianPotential hn g) y (EuclideanSpace.single j 1)) =
      newtonianPotential hn (fun z => fderiv ℝ g z (EuclideanSpace.single j 1)) :=
    funext (fun y => newtonianPotential_fderiv_data hn (hg.of_le (by norm_num)) hcg y _)
  rw [heq]
  exact newtonianPotential_fderiv_data hn
    ((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
    (hcg.fderiv_apply ℝ _) x _

theorem newtonianPotential_applyCLM {n : ℕ}
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hn : 2 ≤ n) (L : E →L[ℝ] F) {g : Domain n → E}
    (hg : Continuous g) (hcg : HasCompactSupport g) (x : Domain n) :
    L (newtonianPotential hn g x) = newtonianPotential hn (fun z => L (g z)) x := by
  rw [newtonianPotential, newtonianPotential,
    ← L.integral_comp_comm (newtonianPotential_integrable hn hg hcg x)]
  apply integral_congr_ae
  filter_upwards with z
  exact L.map_smul _ _

end HolderToCK
end
