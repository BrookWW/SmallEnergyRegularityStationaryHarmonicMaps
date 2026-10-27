module

public import HarmonicMaps.Energy
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Measurable indicators on actual L2 classes

The literal measurable indicator gives a contractive continuous linear operator
on the original L2 AE classes. The Euclidean squared norm is the actual
integral of the representative squared norm.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace StationaryHarmonicMaps.Analysis

@[expose] def l2IndicatorValue {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Measure X)
    (S : Set X) (hS : MeasurableSet S) (f : Lp V 2 μ) : Lp V 2 μ :=
  ((Lp.memLp f).indicator hS).toLp (S.indicator f)

theorem l2IndicatorValue_ae {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Measure X)
    (S : Set X) (hS : MeasurableSet S) (f : Lp V 2 μ) :
    (l2IndicatorValue μ S hS f : X → V)=ᵐ[μ] S.indicator f := by
  change ((((Lp.memLp f).indicator hS).toLp (S.indicator f)) : X → V)=ᵐ[μ] S.indicator f
  exact MemLp.coeFn_toLp _

@[expose] def l2Indicator {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Measure X)
    (S : Set X) (hS : MeasurableSet S) : Lp V 2 μ →L[ℝ] Lp V 2 μ := by
  let L : Lp V 2 μ →ₗ[ℝ] Lp V 2 μ :=
    { toFun := l2IndicatorValue μ S hS
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [l2IndicatorValue_ae μ S hS (f+g),l2IndicatorValue_ae μ S hS f,
          l2IndicatorValue_ae μ S hS g,Lp.coeFn_add f g,
          Lp.coeFn_add (l2IndicatorValue μ S hS f) (l2IndicatorValue μ S hS g)] with x hx hf hg hadd hsum
        rw [hx,hsum]
        simp only [Pi.add_apply]
        rw [hf,hg]
        by_cases hs : x∈S
        · simp only [indicator_of_mem hs,Pi.add_apply] at hadd ⊢
          exact hadd
        · simp only [indicator_of_notMem hs,add_zero]
      map_smul' := by
        intro c f
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [l2IndicatorValue_ae μ S hS (c • f),l2IndicatorValue_ae μ S hS f,
          Lp.coeFn_smul c f,Lp.coeFn_smul c (l2IndicatorValue μ S hS f)] with x hx hf hc hmul
        rw [hx,hmul]
        simp only [Pi.smul_apply]
        rw [hf]
        by_cases hs : x∈S
        · simp only [indicator_of_mem hs,Pi.smul_apply] at hc ⊢
          exact hc
        · simp only [indicator_of_notMem hs,smul_zero] }
  exact L.mkContinuous 1 fun f=>by
    change ‖((Lp.memLp f).indicator hS).toLp (S.indicator f)‖≤1*‖f‖
    rw [Lp.norm_toLp,one_mul,Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.memLp f).2.ne (eLpNorm_indicator_le _)

theorem l2_euclidean_norm_sq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {d : ℕ} (F : Lp (Ambient d) 2 μ) : ‖F‖^2=∫x,‖F x‖^2 ∂μ := by
  calc
    _=inner ℝ F F := (real_inner_self_eq_norm_sq F).symm
    _=∫x,inner ℝ (F x) (F x) ∂μ := L2.inner_def F F
    _=_ := integral_congr_ae (Eventually.of_forall fun x=>real_inner_self_eq_norm_sq (F x))

end StationaryHarmonicMaps.Analysis

end
