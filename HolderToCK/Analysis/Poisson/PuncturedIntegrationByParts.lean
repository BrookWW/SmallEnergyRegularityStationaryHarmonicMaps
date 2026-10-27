module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # Integration by parts with a single puncture in dimension at least two

Almost every line parallel to a fixed nonzero vector avoids the puncture.
One-dimensional integration by parts and Fubini therefore retain the ordinary
formula when the function and its classical derivative pairings are integrable.
-/

public section

open MeasureTheory Measure Module Set Filter
open scoped Topology

namespace HolderToCK

private theorem punctured_product_integrationByParts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [Nontrivial E]
    [(volume : Measure E).IsAddHaarMeasure]
    {f f' g g' : E × ℝ → ℝ}
    (hf'g : Integrable (fun x => f' x * g x) (volume.prod volume))
    (hfg' : Integrable (fun x => f x * g' x) (volume.prod volume))
    (hfg : Integrable (fun x => f x * g x) (volume.prod volume))
    (hf : ∀ x ≠ 0, HasLineDerivAt ℝ f (f' x) x (0, 1))
    (hg : ∀ x, HasLineDerivAt ℝ g (g' x) x (0, 1)) :
    (∫ x, f x * g' x ∂(volume.prod volume)) =
      -∫ x, f' x * g x ∂(volume.prod volume) := by
  rw [integral_prod _ hfg']
  calc
    _ = ∫ x : E, (-∫ t : ℝ, f' (x, t) * g (x, t)) := by
      apply integral_congr_ae
      filter_upwards [hf'g.prod_right_ae, hfg'.prod_right_ae, hfg.prod_right_ae,
        (volume : Measure E).ae_ne 0] with x hf'gx hfg'x hfgx hx
      apply integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
        (L := ContinuousLinearMap.mul ℝ ℝ) ?_ ?_ hfg'x hf'gx hfgx
      · intro t _
        have hxt : (x, t) ≠ (0 : E × ℝ) := by
          intro heq
          exact hx (congrArg Prod.fst heq)
        convert! (hf (x, t) hxt).scomp_of_eq t
          ((hasDerivAt_id t).add (hasDerivAt_const t (-t))) (by simp) <;> simp
      · intro t _
        convert! (hg (x, t)).scomp_of_eq t
          ((hasDerivAt_id t).add (hasDerivAt_const t (-t))) (by simp) <;> simp
    _ = _ := by rw [integral_neg, integral_prod _ hf'g]

private theorem punctured_product_haar_integrationByParts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [Nontrivial E]
    [(volume : Measure E).IsAddHaarMeasure]
    {μ : Measure (E × ℝ)} [μ.IsAddHaarMeasure]
    {f f' g g' : E × ℝ → ℝ}
    (hf'g : Integrable (fun x => f' x * g x) μ)
    (hfg' : Integrable (fun x => f x * g' x) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hf : ∀ x ≠ 0, HasLineDerivAt ℝ f (f' x) x (0, 1))
    (hg : ∀ x, HasLineDerivAt ℝ g (g' x) x (0, 1)) :
    (∫ x, f x * g' x ∂μ) = -∫ x, f' x * g x ∂μ := by
  have hμ : (volume : Measure E).prod volume =
      addHaarScalarFactor ((volume : Measure E).prod volume) μ • μ :=
    isAddLeftInvariant_eq_smul _ _
  have h1 : Integrable (fun x => f' x * g x) ((volume : Measure E).prod volume) := by
    rw [hμ]
    exact hf'g.smul_measure_nnreal
  have h2 : Integrable (fun x => f x * g' x) ((volume : Measure E).prod volume) := by
    rw [hμ]
    exact hfg'.smul_measure_nnreal
  have h3 : Integrable (fun x => f x * g x) ((volume : Measure E).prod volume) := by
    rw [hμ]
    exact hfg.smul_measure_nnreal
  rw [isAddLeftInvariant_eq_smul μ ((volume : Measure E).prod volume)]
  simp only [integral_smul_nnreal_measure, punctured_product_integrationByParts h1 h2 h3 hf hg,
    smul_neg]

theorem punctured_hasFDerivAt_integrationByParts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    (hdim : 2 ≤ finrank ℝ E) {v : E} (hv : v ≠ 0)
    {f g : E → ℝ} {f' g' : E → E →L[ℝ] ℝ}
    (hf'g : Integrable (fun x => f' x v * g x) μ)
    (hfg' : Integrable (fun x => f x * g' x v) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hf : ∀ x ≠ 0, HasFDerivAt f (f' x) x)
    (hg : ∀ x, HasFDerivAt g (g' x) x) :
    (∫ x, f x * g' x v ∂μ) = -∫ x, f' x v * g x ∂μ := by
  let n := finrank ℝ E
  let E' := Fin (n - 1) → ℝ
  have hn : 0 < n := by dsimp only [n]; omega
  letI : Nonempty (Fin (n - 1)) := Fin.pos_iff_nonempty.mp (by dsimp only [n]; omega)
  obtain ⟨L, hL⟩ : ∃ L : E ≃L[ℝ] (E' × ℝ), L v = (0, 1) := by
    have hdim' : finrank ℝ (E' × ℝ) = n := by
      simpa [E', n] using Nat.sub_add_cancel hn
    let L₀ : E ≃L[ℝ] (E' × ℝ) := (ContinuousLinearEquiv.ofFinrankEq hdim').symm
    obtain ⟨M, hM⟩ : ∃ M : (E' × ℝ) ≃L[ℝ] (E' × ℝ), M (L₀ v) = (0, 1) := by
      apply SeparatingDual.exists_continuousLinearEquiv_apply_eq
      · exact fun h => hv (L₀.injective (by simpa only [map_zero] using h))
      · exact fun h => one_ne_zero (congrArg Prod.snd h)
    exact ⟨L₀.trans M, by simp only [ContinuousLinearEquiv.trans_apply, hM]⟩
  let ν := Measure.map L μ
  suffices h : (∫ x : E' × ℝ, f (L.symm x) * g' (L.symm x) v ∂ν) =
      -∫ x : E' × ℝ, f' (L.symm x) v * g (L.symm x) ∂ν by
    have hemb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
    dsimp only [ν] at h
    rw [hemb.integral_map, hemb.integral_map] at h
    simpa only [L.symm_apply_apply] using h
  have Lemb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  apply punctured_product_haar_integrationByParts
  · simpa only [ν, Lemb.integrable_map_iff, Function.comp_def, L.symm_apply_apply] using hf'g
  · simpa only [ν, Lemb.integrable_map_iff, Function.comp_def, L.symm_apply_apply] using hfg'
  · simpa only [ν, Lemb.integrable_map_iff, Function.comp_def, L.symm_apply_apply] using hfg
  · intro x hx
    have hsymm : L.symm x ≠ 0 :=
      fun h => hx (L.symm.injective (by simpa only [map_zero] using h))
    have hvL : L.symm (0, 1) = v := by rw [← hL, L.symm_apply_apply]
    have hd := (hf (L.symm x) hsymm).comp x L.symm.hasFDerivAt
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, hvL] using
      hd.hasLineDerivAt (0, 1)
  · intro x
    have hvL : L.symm (0, 1) = v := by rw [← hL, L.symm_apply_apply]
    have hd := (hg (L.symm x)).comp x L.symm.hasFDerivAt
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, hvL] using
      hd.hasLineDerivAt (0, 1)

end HolderToCK
end
