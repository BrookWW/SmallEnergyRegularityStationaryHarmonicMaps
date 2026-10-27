/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.BoundaryEvenPowerGrowth
public import StationaryHarmonicMaps.Analysis.LocalLpMorreyRepresentative
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.UniformSpace.UniformEmbedding
import StationaryHarmonicMaps.Analysis.CriticalMorreyMeanOscillation

/-!
# Stronger Morrey representatives up to the unit sphere

The literal even inversion graph retains the original stronger growth on
the double ball. Finite Sobolev restriction and local Campanato estimates
give the same-map Holder representative on the entire unit ball, with
no distance-to-boundary loss. Uniform continuity supplies its unique
continuous extension to the closed unit ball.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original stronger all-ball derivative growth gives the unique
continuous representative on the whole open unit ball and a uniform
Holder estimate for every pair, including pairs approaching the sphere. -/
theorem existsUnique_boundary_holder_representative_of_stronger_morrey
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (_hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀(q : ℕ) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
      (K : ℝ),MemW12 (ballDomain (0:Domain n) 1) u Du → 0≤K →
      (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Du x))≤K*r^((n:ℝ)-2+γ)) →
      ∃! w : ball (0:Domain n) 1 → Ambient q,
        IsContinuousRepresentative (ballDomain (0:Domain n) 1) u w ∧
        ∀x y : ball (0:Domain n) 1,
          ‖w x-w y‖≤C*Real.sqrt K*(dist (x:Domain n) (y:Domain n))^(γ/2) := by
  have hα : 0<γ/2 := half_pos hγ
  obtain ⟨C₀,hC₀,Hcamp⟩ := existsUnique_local_representative_of_meanOscillation n (γ/2) hα
  let ν := (n:ℝ)-2+γ
  let A := (2:ℝ)^ν*(1+(2:ℝ)^(2*n))
  let D := ((2:ℝ)^(n+1)*Real.sqrt (n:ℝ))*(volume.real (ball (0:Domain n) 1))^(-(1/(2:ℝ)))
  have hA : 0<A := by dsimp only [A];positivity
  have hD : 0≤D := by dsimp only [D];positivity
  let C := 1+C₀*D*Real.sqrt A
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro q u Du K hu hK hGrowth
  let I := EuclideanGeometry.inversion (0:Domain n) 1
  let U := fun x=>if ‖x‖≤1 then u x else u (I x)
  let DU := fun x i=>if ‖x‖≤1 then Du x i else
    ∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • Du (I x) j
  have hU : MemW12 (ballDomain (0:Domain n) 2) U DU :=
    memW12_even_inversion_extension_ball_two hn u Du hu
  letI : IsFiniteMeasure (volume.restrict (ballDomain (0:Domain n) 2).val) :=
    isFiniteMeasure_restrict.mpr (by exact measure_ball_ne_top)
  have hExt := even_inversion_power_growth_unitBall hn ν u Du hu K hK hGrowth
  let T := Real.sqrt (A*K)
  have hT : 0≤T := Real.sqrt_nonneg _
  have hOsc : ∀x∈ball (0:Domain n) (3*(2:ℝ)/4),∀r : ℝ,0<r → r≤(2:ℝ)/4 →
      (⨍y in ball x r,‖U y-(⨍z in ball x r,U z)‖)≤(D*T)*r^(γ/2) := by
    intro x hx r hr hrCap
    have hSub : ball x r⊆ball (0:Domain n) 2 := by
      intro y hy
      have H := dist_triangle y x (0:Domain n)
      have hx0 : dist x (0:Domain n)<3*(2:ℝ)/4 := hx
      have hyx : dist y x<r := hy
      change dist y (0:Domain n)<2
      linarith only [H,hx0,hyx,hrCap]
    have hW : MemW12 (ballDomain x r) U DU := memW12_of_openDomain_subset hU hSub
    have hPower : (∫y in ball x r,(Real.sqrt (hsNormSq (DU y)))^(2:ℝ))≤
        T^(2:ℝ)*r^((n:ℝ)-2+2*(γ/2)) := by
      simp only [Real.rpow_two,Real.sq_sqrt (hsNormSq_nonneg _)]
      have hTSq : T^2=A*K := Real.sq_sqrt (mul_nonneg hA.le hK)
      rw [hTSq]
      have H := hExt x r hr
      change (∫y in ball x r∩ball (0:Domain n) 2,hsNormSq (DU y))≤A*K*r^ν at H
      rw [inter_eq_left.mpr hSub] at H
      rw [show (n:ℝ)-2+2*(γ/2)=ν by dsimp only [ν];ring]
      exact H
    exact sobolev_meanOscillation_of_lp_growth x hr (by norm_num) (by norm_num) hT hW hPower
  have hUI : IntegrableOn U (ball (0:Domain n) 2) volume :=
    hU.2.1.integrable (by norm_num)
  obtain ⟨w₀,hw,_hUnique⟩ := Hcamp q U 0 2 (D*T) (by norm_num) (mul_nonneg hD hT) hUI hOsc
  let j : ball (0:Domain n) 1 → ball (0:Domain n) ((2:ℝ)/2) :=
    fun x=>⟨x,by simpa only [div_self (by norm_num : (2:ℝ)≠0)] using x.2⟩
  let w : ball (0:Domain n) 1 → Ambient q := fun x=>w₀ (j x)
  have hRepU : IsContinuousRepresentative (ballDomain (0:Domain n) 1) U w := by
    refine ⟨hw.1.1.comp (continuous_subtype_val.subtype_mk _),?_⟩
    have hMeasure : volume.restrict (ballDomain (0:Domain n) 1).val≤
        volume.restrict (ballDomain (0:Domain n) ((2:ℝ)/2)).val :=
      Measure.restrict_mono_set volume (ball_subset_ball (by norm_num))
    filter_upwards [hw.1.2.filter_mono (ae_mono hMeasure)] with x hx
    intro hxBall
    exact hx (by simpa only [div_self (by norm_num : (2:ℝ)≠0)] using hxBall)
  have hRep : IsContinuousRepresentative (ballDomain (0:Domain n) 1) u w := by
    refine ⟨hRepU.1,?_⟩
    filter_upwards [hRepU.2] with x hx
    intro hxBall
    have hxNorm : ‖x‖≤1 := (mem_ball_zero_iff.mp hxBall).le
    exact (hx hxBall).trans (if_pos hxNorm)
  have hBound : ∀x y : ball (0:Domain n) 1,
      ‖w x-w y‖≤C*Real.sqrt K*(dist (x:Domain n) (y:Domain n))^(γ/2) := by
    intro x y
    have H := hw.2.2.2 (j x) (j y)
    have hFactor : C₀*(D*T)=(C₀*D*Real.sqrt A)*Real.sqrt K := by
      rw [show T=Real.sqrt A*Real.sqrt K from Real.sqrt_mul hA.le K]
      ring
    rw [hFactor] at H
    exact H.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show C₀*D*Real.sqrt A≤C by dsimp only [C];linarith)
        (Real.sqrt_nonneg K)) (Real.rpow_nonneg dist_nonneg _))
  refine ⟨w,⟨hRep,hBound⟩,?_⟩
  intro z hz
  exact hz.1.unique hRep

/-- A genuine Holder function on the open unit ball has a unique continuous
extension to the closed ball, with the same Holder constant. -/
theorem existsUnique_closedBall_extension_of_holder_unitBall {n q : ℕ}
    (w : ball (0:Domain n) 1 → Ambient q) (α A : ℝ) (hα : 0<α) (hA : 0≤A)
    (hBound : ∀x y : ball (0:Domain n) 1,
      ‖w x-w y‖≤A*(dist (x:Domain n) (y:Domain n))^α) :
    ∃! W : closedBall (0:Domain n) 1 → Ambient q,
      Continuous W ∧
      (∀x : ball (0:Domain n) 1,W ⟨x,ball_subset_closedBall x.2⟩=w x) ∧
      ∀x y : closedBall (0:Domain n) 1,
        ‖W x-W y‖≤A*(dist (x:Domain n) (y:Domain n))^α := by
  let i : ball (0:Domain n) 1 → closedBall (0:Domain n) 1 := inclusion ball_subset_closedBall
  have hi : Isometry i := fun _ _=>rfl
  have hDense : DenseRange i := by
    apply (denseRange_inclusion_iff ball_subset_closedBall).2
    rw [closure_ball (0:Domain n) (by norm_num : (1:ℝ)≠0)]
  have hHolder : HolderWith ⟨A,hA⟩ ⟨α,hα.le⟩ w := by
    intro x y
    rw [edist_dist,edist_dist]
    rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal (dist (w x) (w y))≤
      ENNReal.ofReal A*(ENNReal.ofReal (dist (x:Domain n) (y:Domain n)))^α
    rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα.le,← ENNReal.ofReal_mul hA]
    exact ENNReal.ofReal_le_ofReal (by simpa only [dist_eq_norm] using hBound x y)
  have hUniform := hHolder.uniformContinuous hα
  let di := hi.isUniformInducing.isDenseInducing hDense
  let W := di.extend w
  have hCont : Continuous W :=
    (uniformContinuous_uniformly_extend hi.isUniformInducing hDense hUniform).continuous
  have hEq (x : ball (0:Domain n) 1) : W (i x)=w x :=
    di.extend_eq_at hUniform.continuous.continuousAt
  have hClosed : IsClosed {p : closedBall (0:Domain n) 1×closedBall (0:Domain n) 1 |
      ‖W p.1-W p.2‖≤A*(dist (p.1:Domain n) (p.2:Domain n))^α} := by
    apply isClosed_le ((hCont.comp continuous_fst).sub (hCont.comp continuous_snd)).norm
    exact continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
      ((continuous_subtype_val.comp continuous_fst).dist (continuous_subtype_val.comp continuous_snd)))
  have hBoundClosed : ∀x y : closedBall (0:Domain n) 1,
      ‖W x-W y‖≤A*(dist (x:Domain n) (y:Domain n))^α := by
    apply isClosed_property2 hDense (p:=fun x y : closedBall (0:Domain n) 1=>
      ‖W x-W y‖≤A*(dist (x:Domain n) (y:Domain n))^α) hClosed
    intro x y
    rw [hEq,hEq]
    exact hBound x y
  refine ⟨W,⟨hCont,hEq,hBoundClosed⟩,?_⟩
  intro z hz
  apply hDense.equalizer hz.1 hCont
  funext x
  exact (hz.2.1 x).trans (hEq x).symm

/-- Original stronger native derivative growth constructs the unique
continuous representative on the closed unit ball. Its values inside the
ball agree with the original map almost everywhere, and the same uniform
Holder estimate holds for every pair of boundary or interior points. -/
theorem existsUnique_closedBall_holder_representative_of_stronger_morrey
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀(q : ℕ) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
      (K : ℝ),MemW12 (ballDomain (0:Domain n) 1) u Du → 0≤K →
      (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Du x))≤K*r^((n:ℝ)-2+γ)) →
      ∃! W : closedBall (0:Domain n) 1 → Ambient q,
        Continuous W ∧
        (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀hx : x∈ball (0:Domain n) 1,
          W ⟨x,ball_subset_closedBall hx⟩=u x) ∧
        ∀x y : closedBall (0:Domain n) 1,
          ‖W x-W y‖≤C*Real.sqrt K*(dist (x:Domain n) (y:Domain n))^(γ/2) := by
  obtain ⟨C,hC,Hopen⟩ := existsUnique_boundary_holder_representative_of_stronger_morrey n hn γ hγ hγTwo
  refine ⟨C,hC,?_⟩
  intro q u Du K hu hK hGrowth
  obtain ⟨w,hw,_hwUnique⟩ := Hopen q u Du K hu hK hGrowth
  obtain ⟨W,hW,hWUnique⟩ := existsUnique_closedBall_extension_of_holder_unitBall w (γ/2)
    (C*Real.sqrt K) (half_pos hγ) (mul_nonneg hC.le (Real.sqrt_nonneg K)) hw.2
  have hAE : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀hx : x∈ball (0:Domain n) 1,
      W ⟨x,ball_subset_closedBall hx⟩=u x := by
    filter_upwards [hw.1.2] with x hx
    intro hxBall
    exact (hW.2.1 ⟨x,hxBall⟩).trans (hx hxBall)
  refine ⟨W,⟨hW.1,hAE,hW.2.2⟩,?_⟩
  intro z hz
  have hzRep : IsContinuousRepresentative (ballDomain (0:Domain n) 1) u
      (fun x=>z ⟨x,ball_subset_closedBall x.2⟩) :=
    ⟨hz.1.comp (continuous_subtype_val.subtype_mk _),hz.2.1⟩
  have hEq := hzRep.unique hw.1
  exact hWUnique z ⟨hz.1,fun x=>congrFun hEq x,hz.2.2⟩

end StationaryHarmonicMaps.Analysis

end
