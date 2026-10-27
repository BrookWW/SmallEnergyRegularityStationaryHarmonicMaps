module

public import HarmonicMaps.Analysis.DecayParameters
public import HarmonicMaps.Analysis.FiniteEnergySobolev
public import HarmonicMaps.EnergyLemmas
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Disjoint annuli and the source good shell

The actual finite floor count determines disjoint open annuli inside the
unit ball. Their total original HS energy yields one source index and both
energy bounds. Uniform geometric parameters precede every map and gradient.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology BigOperators

namespace HarmonicMaps

private theorem decay_floor_bound (delta tau : ℝ) (hd : 0 < delta)
    (hRatio : 2 ≤ tau / (3 * delta)) :
    2 ≤ ⌊tau / (3 * delta)⌋₊ ∧
    tau / (6 * delta) ≤ (⌊tau / (3 * delta)⌋₊ : ℝ) ∧
    (⌊tau / (3 * delta)⌋₊ : ℝ) * (3 * delta) ≤ tau := by
  let a := tau / (3 * delta)
  have ha : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 2).trans hRatio
  have hp : 2 ≤ ⌊a⌋₊ := Nat.le_floor hRatio
  have hFloor : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
  have hLt : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  have hPtwo : (2 : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast hp
  refine ⟨hp, ?_, (le_div_iff₀ (mul_pos (by norm_num) hd)).mp hFloor⟩
  have heq : tau / (6 * delta) = a / 2 := by dsimp only [a]; ring
  rw [heq]
  linarith only [hLt, hPtwo]

private theorem decay_disjoint_shell_choice {n : ℕ}
    (delta tau : ℝ) (hd : 0 < delta) (ht : 0 < tau)
    (hsmall : 2 * tau < 1 / 4) (hRatio : 2 ≤ tau / (3 * delta))
    (f : Domain n → ℝ)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) 1) volume)
    (hNonneg : ∀ x, 0 ≤ f x) :
    let p := ⌊tau / (3 * delta)⌋₊
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ p ∧
      let theta := tau + (3 * (j : ℝ) - 2) * delta
      tau < theta ∧ theta < 2 * tau ∧
      delta < theta ∧ theta + 2 * delta ≤ 2 * tau ∧
      IntegrableOn f
        (Metric.ball (0 : Domain n) (theta + 2 * delta) \
          Metric.closedBall 0 (theta - delta)) volume ∧
      (∫ x in Metric.ball (0 : Domain n) (theta + 2 * delta) \
          Metric.closedBall 0 (theta - delta), f x) ≤
        (∫ x in Metric.ball (0 : Domain n) 1, f x) / (p : ℝ) ∧
      (∫ x in Metric.ball (0 : Domain n) 1, f x) / (p : ℝ) ≤
        6 * delta / tau * (∫ x in Metric.ball (0 : Domain n) 1, f x) := by
  classical
  let p := ⌊tau / (3 * delta)⌋₊
  obtain ⟨hPtwo, hPlower, hPupper⟩ := decay_floor_bound delta tau hd hRatio
  have hp : 0 < p := lt_of_lt_of_le (by norm_num) hPtwo
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  let A : Fin p → Set (Domain n) := fun i =>
    Metric.ball 0 (tau + 3 * ((i.val : ℝ) + 1) * delta) \
      Metric.closedBall 0 (tau + 3 * (i.val : ℝ) * delta)
  have hSubset (i : Fin p) : A i ⊆ Metric.ball (0 : Domain n) 1 := by
    intro x hx
    have hi : (i.val : ℝ) + 1 ≤ p := by exact_mod_cast (Nat.succ_le_iff.mpr i.isLt)
    have ho : tau + 3 * ((i.val : ℝ) + 1) * delta ≤ 2 * tau := by
      nlinarith only [hi, hPupper, hd]
    apply Metric.ball_subset_ball (show tau + 3 * ((i.val : ℝ) + 1) * delta ≤ 1 by
      linarith only [ho, hsmall]) hx.1
  have hMeas (i : Fin p) : MeasurableSet (A i) :=
    Metric.isOpen_ball.measurableSet.diff Metric.isClosed_closedBall.measurableSet
  have hDisjoint : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hiout : ‖x‖ < tau + 3 * ((i.val : ℝ) + 1) * delta := by
      simpa only [Metric.mem_ball, dist_zero_right] using hxi.1
    have hiin : tau + 3 * (i.val : ℝ) * delta < ‖x‖ :=
      lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_zero_right] using hxi.2)
    have hjout : ‖x‖ < tau + 3 * ((j.val : ℝ) + 1) * delta := by
      simpa only [Metric.mem_ball, dist_zero_right] using hxj.1
    have hjin : tau + 3 * (j.val : ℝ) * delta < ‖x‖ :=
      lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_zero_right] using hxj.2)
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hij) with hlt | hgt
    · have hcast : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (Nat.succ_le_iff.mpr hlt)
      nlinarith only [hcast, hiout, hjin, hd]
    · have hcast : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast (Nat.succ_le_iff.mpr hgt)
      nlinarith only [hcast, hjout, hiin, hd]
  have hInt (i : Fin p) : IntegrableOn f (A i) volume := hf.mono_set (hSubset i)
  have hUnion : (⋃ i : Fin p, A i) ⊆ Metric.ball (0 : Domain n) 1 :=
    iUnion_subset hSubset
  have hSum : (∑ i : Fin p, ∫ x in A i, f x) ≤
      ∫ x in Metric.ball (0 : Domain n) 1, f x := by
    rw [← integral_iUnion_fintype hMeas hDisjoint hInt]
    exact setIntegral_mono_set hf (Eventually.of_forall hNonneg)
      (Eventually.of_forall hUnion)
  let E := ∫ x in Metric.ball (0 : Domain n) 1, f x
  have hE : 0 ≤ E := integral_nonneg hNonneg
  have hConstSum : (∑ _i : Fin p, E / (p : ℝ)) = E := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hpR.ne']
  have hChoice : ∃ i : Fin p, (∫ x in A i, f x) ≤ E / (p : ℝ) := by
    obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le
      (s := Finset.univ) (f := fun i : Fin p => ∫ x in A i, f x)
      (g := fun _ => E / (p : ℝ))
      ⟨⟨0, hp⟩, Finset.mem_univ _⟩ (hSum.trans_eq hConstSum.symm)
    exact ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hChoice
  let j := i.val + 1
  have hj1 : 1 ≤ j := by omega
  have hjp : j ≤ p := Nat.succ_le_iff.mpr i.isLt
  let theta := tau + (3 * (j : ℝ) - 2) * delta
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hjpR : (j : ℝ) ≤ p := by exact_mod_cast hjp
  have hTauDelta : 6 * delta ≤ tau := by
    have h := (le_div_iff₀ (mul_pos (by norm_num) hd)).mp hRatio
    linarith only [h]
  have hTheta : tau < theta := by dsimp only [theta]; nlinarith only [hjR, hd]
  have hOuter : theta + 2 * delta ≤ 2 * tau := by
    dsimp only [theta]
    nlinarith only [hjpR, hPupper, hd]
  have hAeq : A i = Metric.ball (0 : Domain n) (theta + 2 * delta) \
      Metric.closedBall 0 (theta - delta) := by
    have hjCast : (j : ℝ) = (i.val : ℝ) + 1 := by simp only [j, Nat.cast_add, Nat.cast_one]
    dsimp only [A, theta]
    rw [hjCast]
    congr 2 <;> ring
  have hFinal : E / (p : ℝ) ≤ 6 * delta / tau * E := by
    have hinv : (p : ℝ)⁻¹ ≤ 6 * delta / tau := by
      rw [← one_div]
      apply (div_le_div_iff₀ hpR ht).mpr
      have h : tau ≤ (p : ℝ) * (6 * delta) :=
        (div_le_iff₀ (mul_pos (by norm_num) hd)).mp hPlower
      simpa only [one_mul, mul_one, mul_comm] using h
    rw [div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left hinv hE).trans_eq (mul_comm _ _)
  refine ⟨j, hj1, hjp, hTheta, ?_, ?_, hOuter, ?_, ?_, hFinal⟩
  · linarith only [hOuter, hd]
  · exact (by linarith only [hTauDelta, hd] : delta < tau).trans hTheta
  · exact hAeq ▸ hInt i
  · exact hAeq ▸ hi

/-- Source parameters and genuine finite Sobolev data produce one of the
actual disjoint source shells, with both energy bounds and the same theta. -/
theorem decay_good_shell (n : ℕ) (hn : 2 ≤ n)
    (C₀ ρ : ℝ) (hC₀ : 0 < C₀) (hρ : 0 < ρ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
      let hbar := η ^ (1 / 4 : ℝ)
      let delta := η ^ (1 / 8 : ℝ)
      let gamma := 1 / (64 * ((n : ℝ) - 1))
      let tau := η ^ gamma
      let p := ⌊tau / (3 * delta)⌋₊
      (0 < η ∧ η < 1 ∧ 0 < hbar ∧ 0 < delta ∧ 0 < tau ∧
        0 < gamma ∧ gamma < 1 / 8 ∧
        hbar = delta ^ 2 ∧ hbar ≤ delta ∧
        Real.sqrt (C₀ * η) < ρ ∧ hbar ≤ 1 / 4 ∧
        delta ≤ 1 / 8 ∧ 2 * delta ≤ 1 / 4 ∧
        2 * tau < 1 / 4 ∧ 2 ≤ tau / (3 * delta)) ∧
      2 ≤ p ∧ tau / (6 * delta) ≤ (p : ℝ) ∧
      ∀ (q : ℕ) (N : CompactSmoothEmbeddedTarget q)
        (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
        MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
        TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
        dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal η →
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ p ∧
          let theta := tau + (3 * (j : ℝ) - 2) * delta
          tau < theta ∧ theta < 2 * tau ∧ delta < theta ∧
          theta + 2 * delta ≤ 2 * tau ∧
          (Metric.ball (0 : Domain n) (theta + 2 * delta) \
            Metric.closedBall 0 (theta - delta)) =
            {x : Domain n | tau + 3 * ((j : ℝ) - 1) * delta < ‖x‖ ∧
              ‖x‖ < tau + 3 * (j : ℝ) * delta} ∧
          IntegrableOn (fun x => hsNormSq (Du x))
            (Metric.ball (0 : Domain n) (theta + 2 * delta) \
              Metric.closedBall 0 (theta - delta)) volume ∧
          (∫ x in Metric.ball (0 : Domain n) (theta + 2 * delta) \
              Metric.closedBall 0 (theta - delta), hsNormSq (Du x)) ≤
            (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal / (p : ℝ) ∧
          (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal / (p : ℝ) ≤
            6 * delta / tau * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
  obtain ⟨η₀, hη₀, hη₀One, hParams⟩ := decay_geometric_parameters n hn C₀ ρ hC₀ hρ
  refine ⟨η₀, hη₀, hη₀One, ?_⟩
  intro η hη hηSmall
  dsimp only
  have hG := hParams η hη hηSmall
  have hGcopy := hG
  obtain ⟨_, _, _, hd, ht, _, _, _, _, _, _, _, _, hTau, hRatio⟩ := hGcopy
  obtain ⟨hp, hPlower, _⟩ := decay_floor_bound _ _ hd hRatio
  refine ⟨hG, hp, hPlower, ?_⟩
  intro q N u Du hu hN hE
  have hFinite : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE
  have hInt : IntegrableOn (fun x => hsNormSq (Du x))
      (Metric.ball (0 : Domain n) 1) volume :=
    (hu.memW12_unitBall_of_finiteEnergy N hN hFinite).integrable_hsNormSq
  obtain ⟨j, hj1, hjp, hTheta, hThetaUpper, hDeltaTheta, hOuter, hShellInt,
    hFirst, hSecond⟩ := decay_disjoint_shell_choice _ _ hd ht hTau hRatio
      (fun x => hsNormSq (Du x)) hInt (fun x => hsNormSq_nonneg (Du x))
  refine ⟨j, hj1, hjp, hTheta, hThetaUpper, hDeltaTheta, hOuter, ?_, hShellInt, ?_, ?_⟩
  · ext x
    simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right,
      not_le, mem_setOf_eq]
    have h1 : η ^ (1 / (64 * ((n : ℝ) - 1))) + (3 * (j : ℝ) - 2) * η ^ (1 / 8 : ℝ) +
        2 * η ^ (1 / 8 : ℝ) =
        η ^ (1 / (64 * ((n : ℝ) - 1))) + 3 * (j : ℝ) * η ^ (1 / 8 : ℝ) := by ring
    have h2 : η ^ (1 / (64 * ((n : ℝ) - 1))) + (3 * (j : ℝ) - 2) * η ^ (1 / 8 : ℝ) -
        η ^ (1 / 8 : ℝ) =
        η ^ (1 / (64 * ((n : ℝ) - 1))) + 3 * ((j : ℝ) - 1) * η ^ (1 / 8 : ℝ) := by ring
    rw [h1, h2, and_comm]
  · rw [dirichletEnergy_toReal hInt]
    exact hFirst
  · rw [dirichletEnergy_toReal hInt]
    exact hSecond

end HarmonicMaps

end
