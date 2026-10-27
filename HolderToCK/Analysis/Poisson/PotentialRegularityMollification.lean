module

public import HolderToCK.Analysis.Poisson.PotentialLimitsHessian
public import HolderToCK.Analysis.GradientLinearAlgebra
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-! # Uniform convergence of smooth potential derivatives -/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Convolution Topology

namespace HolderToCK

@[expose] noncomputable def compactDataApproximationScale (k : ℕ) : PositiveRadius :=
  ⟨1 / ((k : ℝ) + 1), by positivity⟩

theorem compactDataApproximationScale_tendsto :
    Tendsto (fun k => (compactDataApproximationScale k).val) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem compactDataApproximationScale_le_one (k : ℕ) :
    (compactDataApproximationScale k).val ≤ 1 := by
  change 1 / ((k : ℝ) + 1) ≤ 1
  apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
  linarith only [Nat.cast_nonneg (α := ℝ) k]

theorem compactDataMollification_fixedSupport {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Domain n → E} (hcg : HasCompactSupport g) :
    ∃ S : ℝ, tsupport g ⊆ Metric.closedBall (0 : Domain n) S ∧
      ∀ k, tsupport (compactDataMollification g (compactDataApproximationScale k)) ⊆
        Metric.closedBall (0 : Domain n) S := by
  obtain ⟨S, hS⟩ := hcg.isCompact.isBounded.subset_closedBall (0 : Domain n)
  refine ⟨S + 1, hS.trans (Metric.closedBall_subset_closedBall (by linarith only)), ?_⟩
  intro k
  apply (compactDataMollification_tsupport_subset hS (compactDataApproximationScale k)).trans
  apply Metric.closedBall_subset_closedBall
  linarith only [compactDataApproximationScale_le_one k]

theorem tendstoUniformlyOn_finiteSum
    {X E : Type*} [NormedAddCommGroup E] {a : Type*} (s : Finset a)
    {F : a → ℕ → X → E} {g : a → X → E} {K : Set X}
    (hF : ∀ i ∈ s, TendstoUniformlyOn (F i) (g i) atTop K) :
    TendstoUniformlyOn (fun k x => ∑ i ∈ s, F i k x)
      (fun x => ∑ i ∈ s, g i x) atTop K := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (tendsto_const_nhds (x := (0 : E))).tendstoUniformlyOn_const (s := K)
  | @insert i s hi ih =>
      have hiF := hF i (Finset.mem_insert_self i s)
      have hsF := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      have hsum := hiF.add hsF
      have heqF : F i + (fun k x => ∑ j ∈ s, F j k x) =
          (fun k x => F i k x + ∑ j ∈ s, F j k x) := by
        funext k x
        rfl
      have heqg : g i + (fun x => ∑ j ∈ s, g j x) =
          (fun x => g i x + ∑ j ∈ s, g j x) := by
        funext x
        rfl
      rw [heqF, heqg] at hsum
      simpa only [Finset.sum_insert hi] using hsum

theorem compactDataMollification_potential_tendstoUniformlyOn {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 2 ≤ n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (R : ℝ) :
    TendstoUniformlyOn (fun k => newtonianPotential hn
      (compactDataMollification g (compactDataApproximationScale k)))
      (newtonianPotential hn g) atTop (Metric.closedBall (0 : Domain n) R) := by
  obtain ⟨S, hgS, hFS⟩ := compactDataMollification_fixedSupport hcg
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  exact newtonianPotential_tendstoUniformlyOn hn
    (fun k => (compactDataMollification_contDiff hg (compactDataApproximationScale k)).continuous)
    hg hFS hgS (compactDataMollification_tendstoUniformly hη hH hHolder _
      compactDataApproximationScale_tendsto)

theorem compactDataMollification_gradient_tendstoUniformlyOn {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i : Fin n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (R : ℝ) :
    TendstoUniformlyOn (fun k => potentialGradientColumn i
      (compactDataMollification g (compactDataApproximationScale k)))
      (potentialGradientColumn i g) atTop (Metric.closedBall (0 : Domain n) R) := by
  obtain ⟨S, hgS, hFS⟩ := compactDataMollification_fixedSupport hcg
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  exact potentialGradientColumn_tendstoUniformlyOn hn i
    (fun k => (compactDataMollification_contDiff hg (compactDataApproximationScale k)).continuous)
    hg hFS hgS (compactDataMollification_tendstoUniformly hη hH hHolder _
      compactDataApproximationScale_tendsto)

theorem compactDataMollification_hessian_tendstoUniformlyOn {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (R : ℝ) :
    TendstoUniformlyOn (fun k => potentialHessianExpression i j
      (compactDataMollification g (compactDataApproximationScale k)))
      (potentialHessianExpression i j g) atTop (Metric.closedBall (0 : Domain n) R) := by
  obtain ⟨S, hgS, hFS⟩ := compactDataMollification_fixedSupport hcg
  exact potentialHessianExpression_tendstoUniformlyOn hn i j hη hH
    (fun k => compactDataMollification_holderBound hη hH hHolder (compactDataApproximationScale k))
    hHolder hFS hgS (compactDataMollification_tendstoUniformly hη hH hHolder _
      compactDataApproximationScale_tendsto)

@[expose] noncomputable def potentialGradientLinearMap {n q : ℕ}
    (g : Domain n → Ambient q) (x : Domain n) : Domain n →L[ℝ] Ambient q :=
  ∑ i : Fin n, (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).smulRight
    (potentialGradientColumn i g x)

@[expose] noncomputable def potentialHessianColumnLinearMap {n q : ℕ}
    (j : Fin n) (g : Domain n → Ambient q) (x : Domain n) : Domain n →L[ℝ] Ambient q :=
  ∑ i : Fin n, (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).smulRight
    (potentialHessianExpression i j g x)

theorem newtonianPotential_fderiv_eq_gradientLinearMap_smooth {n q : ℕ}
    (hn : 2 ≤ n) {g : Domain n → Ambient q} (hg : ContDiff ℝ 1 g)
    (hcg : HasCompactSupport g) (x : Domain n) :
    fderiv ℝ (newtonianPotential hn g) x = potentialGradientLinearMap g x := by
  rw [linearMap_eq_columnSum (fderiv ℝ (newtonianPotential hn g) x)]
  simp_rw [newtonianPotential_column_eq_gradient hn _ hg hcg]
  rfl

theorem potentialGradientColumn_fderiv_eq_hessianLinearMap_smooth {n q : ℕ}
    (hn : 2 ≤ n) (j : Fin n) {g : Domain n → Ambient q} {η H : ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H) (x : Domain n) :
    fderiv ℝ (potentialGradientColumn j g) x = potentialHessianColumnLinearMap j g x := by
  have heq : potentialGradientColumn j g =
      (fun x => fderiv ℝ (newtonianPotential hn g) x (EuclideanSpace.single j 1)) :=
    (funext fun x => newtonianPotential_column_eq_gradient hn j
      (hg.of_le (by norm_num)) hcg x).symm
  rw [heq, linearMap_eq_columnSum
    (fderiv ℝ (fun x => fderiv ℝ (newtonianPotential hn g) x (EuclideanSpace.single j 1)) x)]
  simp_rw [newtonianPotential_mixedColumns_eq_hessian hn _ j hg hcg hη hH hHolder]
  rfl

theorem compactDataMollification_fderivPotential_tendstoUniformlyOn {n q : ℕ}
    (hn : 2 ≤ n) {g : Domain n → Ambient q} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (R : ℝ) :
    TendstoUniformlyOn (fun k => fderiv ℝ (newtonianPotential hn
      (compactDataMollification g (compactDataApproximationScale k))))
      (potentialGradientLinearMap g) atTop (Metric.closedBall (0 : Domain n) R) := by
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  have heq : (fun k => fderiv ℝ (newtonianPotential hn
      (compactDataMollification g (compactDataApproximationScale k)))) =
      (fun k => potentialGradientLinearMap
        (compactDataMollification g (compactDataApproximationScale k))) := by
    funext k x
    exact newtonianPotential_fderiv_eq_gradientLinearMap_smooth hn
      ((compactDataMollification_contDiff hg _).of_le (WithTop.coe_le_coe.mpr le_top))
      (compactDataMollification_hasCompactSupport hcg _) x
  rw [heq]
  apply tendstoUniformlyOn_finiteSum Finset.univ
  intro i _
  exact (((ContinuousLinearMap.smulRightL ℝ (Domain n) (Ambient q))
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i)).uniformContinuous.comp_tendstoUniformlyOn
      (compactDataMollification_gradient_tendstoUniformlyOn (by omega) i hη hH hHolder hcg R))

theorem compactDataMollification_fderivGradient_tendstoUniformlyOn {n q : ℕ}
    (hn : 2 ≤ n) (j : Fin n) {g : Domain n → Ambient q} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (R : ℝ) :
    TendstoUniformlyOn (fun k => fderiv ℝ (potentialGradientColumn j
      (compactDataMollification g (compactDataApproximationScale k))))
      (potentialHessianColumnLinearMap j g) atTop (Metric.closedBall (0 : Domain n) R) := by
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  have heq : (fun k => fderiv ℝ (potentialGradientColumn j
      (compactDataMollification g (compactDataApproximationScale k)))) =
      (fun k => potentialHessianColumnLinearMap j
        (compactDataMollification g (compactDataApproximationScale k))) := by
    funext k x
    exact potentialGradientColumn_fderiv_eq_hessianLinearMap_smooth hn j
      ((compactDataMollification_contDiff hg _).of_le (WithTop.coe_le_coe.mpr le_top))
      (compactDataMollification_hasCompactSupport hcg _) hη hH
      (compactDataMollification_holderBound hη hH hHolder _) x
  rw [heq]
  apply tendstoUniformlyOn_finiteSum Finset.univ
  intro i _
  exact (((ContinuousLinearMap.smulRightL ℝ (Domain n) (Ambient q))
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i)).uniformContinuous.comp_tendstoUniformlyOn
      (compactDataMollification_hessian_tendstoUniformlyOn (by omega) i j hη hH hHolder hcg R))

end HolderToCK
end
