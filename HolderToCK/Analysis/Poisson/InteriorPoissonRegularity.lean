module

public import HolderToCK.Analysis.Poisson.ForcingCutoff
public import HolderToCK.Analysis.Poisson.PotentialRegularity
public import HolderToCK.Analysis.Poisson.WeakHarmonicSmooth
public import HolderToCK.Analysis.ClassicalEquation
public import HarmonicMaps.Analysis.SobolevDifference

/-! # Classical regularity of the same weak Poisson solution

A compact Holder forcing defines its actual C2 Newtonian potential. Subtracting
that potential leaves the same continuous Sobolev map weakly harmonic on the
inner ball. Its smoothness gives the classical second derivatives of the
original solution and the original pointwise equation.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff

namespace HolderToCK

theorem weak_poisson_holder_newtonian_remainder {n q : ℕ}
    (hn : 2 ≤ n) {γ H L : ℝ} (hγ : 0 < γ) (hγOne : γ ≤ 1)
    {v f : Domain n → Ambient q} {Dv : Domain n → Gradient n q}
    (hv : MemW12Loc (ballDomain (0 : Domain n) 1) v Dv)
    (hcont : ContinuousOn v (Metric.ball (0 : Domain n) 1))
    (hEq : WeakPoissonOn (ballDomain (0 : Domain n) 1) Dv f)
    (hL : 0 ≤ L) (hbound : ∀ x ∈ Metric.ball (0 : Domain n) 1, ‖f x‖ ≤ L)
    (hH : 0 ≤ H) (hHolder : HolderBoundOn (Metric.ball (0 : Domain n) 1) f γ H) :
    ContDiffOn ℝ ∞ (v - newtonianPotential hn (schauderForcing f))
        (Metric.ball (0 : Domain n) (5 / 8)) ∧
      ∀ x ∈ Metric.ball (0 : Domain n) (5 / 8),
        Laplacian.laplacian (v - newtonianPotential hn (schauderForcing f)) x = 0 := by
  obtain ⟨B, hB⟩ := schauderCutoff_lipschitz n
  let G : ℝ := H + ((B : ℝ) + 8) * L
  have hG : 0 ≤ G := by positivity
  let g := schauderForcing f
  have hg : HolderBoundOn univ g γ G :=
    schauderForcing_holderBound hγ hγOne hH hL hbound hHolder hB
  have hcg : HasCompactSupport g := schauderForcing_hasCompactSupport f
  let P := newtonianPotential hn g
  have hP : ContDiff ℝ 2 P := newtonianPotential_holder_contDiff_two hn hγ hG hg hcg
  let Ω : OpenDomain n := ballDomain (0 : Domain n) (5 / 8)
  have hsub : Ω.val ⊆ (ballDomain (0 : Domain n) 1).val :=
    Metric.ball_subset_ball (by norm_num : (5 / 8 : ℝ) ≤ 1)
  have hvΩ := hv.mono hsub
  have hEqΩ := hEq.mono hsub
  have hpΩ : MemW12Loc Ω P
      (fun x i => fderiv ℝ P x (EuclideanSpace.single i 1)) :=
    memW12Loc_of_contDiffOn_one Ω (hP.of_le (by norm_num)).contDiffOn
  have hPEq : WeakPoissonOn Ω
      (fun x i => fderiv ℝ P x (EuclideanSpace.single i 1)) g :=
    weakPoissonOn_of_contDiffOn_two_of_laplacian_eq Ω hP.contDiffOn
      (fun x _ => newtonianPotential_holder_laplacian hn hγ hG hg hcg x)
  have hhΩ : MemW12Loc Ω (v - P)
      (fun x i => Dv x i - fderiv ℝ P x (EuclideanSpace.single i 1)) := by
    refine ⟨hvΩ.1.sub hpΩ.1, ?_, ?_⟩
    · intro K hK hKΩ
      exact (hvΩ.2.1 K hK hKΩ).sub (hpΩ.2.1 K hK hKΩ)
    · intro i K hK hKΩ
      exact (hvΩ.2.2 i K hK hKΩ).sub (hpΩ.2.2 i K hK hKΩ)
  have hhEq : WeakPoissonOn Ω
      (fun x i => Dv x i - fderiv ℝ P x (EuclideanSpace.single i 1)) (fun _ => 0) := by
    apply (hEqΩ.sub hPEq).congr (EventuallyEq.refl _ _)
    filter_upwards [ae_restrict_mem Ω.property.measurableSet] with x hx
    dsimp only [g]
    rw [schauderForcing_eq f (Metric.ball_subset_closedBall hx), sub_self]
  have hhcont : ContinuousOn (v - P) Ω.val := (hcont.mono hsub).sub hP.continuous.continuousOn
  exact hhEq.contDiffOn_of_continuous_weak_harmonic hn Ω hhΩ hhcont

theorem weak_poisson_holder_contDiffOn_two {n q : ℕ}
    (hn : 2 ≤ n) {γ H L : ℝ} (hγ : 0 < γ) (hγOne : γ ≤ 1)
    {v f : Domain n → Ambient q} {Dv : Domain n → Gradient n q}
    (hv : MemW12Loc (ballDomain (0 : Domain n) 1) v Dv)
    (hcont : ContinuousOn v (Metric.ball (0 : Domain n) 1))
    (hEq : WeakPoissonOn (ballDomain (0 : Domain n) 1) Dv f)
    (hL : 0 ≤ L) (hbound : ∀ x ∈ Metric.ball (0 : Domain n) 1, ‖f x‖ ≤ L)
    (hH : 0 ≤ H) (hHolder : HolderBoundOn (Metric.ball (0 : Domain n) 1) f γ H) :
    ContDiffOn ℝ 2 v (Metric.ball (0 : Domain n) (5 / 8)) ∧
      ∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), Laplacian.laplacian v x = f x := by
  obtain ⟨B, hB⟩ := schauderCutoff_lipschitz n
  let G : ℝ := H + ((B : ℝ) + 8) * L
  have hG : 0 ≤ G := by positivity
  let P := newtonianPotential hn (schauderForcing f)
  have hP : ContDiff ℝ 2 P := newtonianPotential_holder_contDiff_two hn hγ hG
    (schauderForcing_holderBound hγ hγOne hH hL hbound hHolder hB)
    (schauderForcing_hasCompactSupport f)
  obtain ⟨hh, _⟩ := weak_poisson_holder_newtonian_remainder hn hγ hγOne hv hcont hEq
    hL hbound hH hHolder
  let Ω := ballDomain (0 : Domain n) (5 / 8)
  have hsub : Ω.val ⊆ (ballDomain (0 : Domain n) 1).val :=
    Metric.ball_subset_ball (by norm_num : (5 / 8 : ℝ) ≤ 1)
  have hv2 : ContDiffOn ℝ 2 v Ω.val := by
    have hvSame := (hh.of_le (WithTop.coe_le_coe.mpr le_top)).add hP.contDiffOn
    apply hvSame.congr
    intro x _
    simp only [P, Pi.sub_apply, sub_add_cancel]
  refine ⟨hv2, ?_⟩
  exact (hEq.mono hsub).laplacian_eq_of_contDiffOn_two (hv.mono hsub).1 hv2
    ((hHolder.continuousOn hγ).mono hsub)

end HolderToCK
end
