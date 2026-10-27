module

public import StationaryHarmonicMaps.Analysis.LpPoincareBall
public import StationaryHarmonicMaps.Analysis.EffectiveEuclideanSobolev
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Explicit Euclidean Sobolev gain for actual zero-boundary weak graphs

The compact graph approximants in the literal W0 definition satisfy the
proved Gagliardo--Nirenberg--Sobolev inequality. Actual lower-exponent
strong convergence controls the derivative norm. An actual almost-everywhere
subsequence and Fatou recover the original map's higher integrability;
that integrability is a conclusion, not an additional premise.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal NNReal

namespace StationaryHarmonicMaps.Analysis

/-- A constant chosen before the target and ball gives actual Sobolev gain for every native W0 graph. -/
theorem exists_zeroBoundary_sobolev_lp_bound_explicit (n : ℕ) (hn : 0 < n)
    (p s : ℝ≥0) (hp : 1 ≤ p) (hp₂ : p ≤ 2) (_hs : 0 < s)
    (hsp : (s : ℝ)⁻¹=(p : ℝ)⁻¹-(n : ℝ)⁻¹) :
    ∃ C : ℝ≥0, C=1+euclideanSobolevCoefficient n (p:ℝ) ∧ 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (r : ℝ)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      HasZeroBoundaryValues (ballDomain a r) u Du →
      MemLp u (s : ℝ≥0∞) (volume.restrict (Metric.ball a r)) ∧
      eLpNorm u (s : ℝ≥0∞) (volume.restrict (Metric.ball a r)) ≤ (C : ℝ≥0∞) *
        eLpNorm (fun x => Real.sqrt (hsNormSq (Du x))) (p : ℝ≥0∞)
          (volume.restrict (Metric.ball a r)) := by
  let C₀ : ℝ≥0 := euclideanSobolevCoefficient n (p:ℝ)
  let C : ℝ≥0 := 1+C₀
  refine ⟨C,rfl,by dsimp only [C]; positivity,?_⟩
  intro q a r u Du hu
  let μ : Measure (Domain n) := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  obtain ⟨huW,m,hm,hmc,hconv,hDconv⟩ := hu
  have hmL (k : ℕ) : MemLp (m k) 2 μ := (hm k).continuous.memLp_of_hasCompactSupport (hmc k).1
  have hmD (k : ℕ) (i : Fin n) :
      MemLp (fun x => fderiv ℝ (m k) x (EuclideanSpace.single i 1)) 2 μ :=
    ((hm k).continuous_fderiv (by simp) |>.clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hmc k).1.fderiv_apply ℝ (EuclideanSpace.single i 1))
  let H := fun k x => Real.sqrt (hsNormSq (fun i => fderiv ℝ (m k) x (EuclideanSpace.single i 1)))
  let G := fun x => Real.sqrt (hsNormSq (Du x))
  have hH (k : ℕ) : MemLp (H k) 2 μ := memLp_sqrt_sum_norm_sq _ (hmD k)
  have hG : MemLp G 2 μ := memLp_sqrt_sum_norm_sq Du huW.2.2
  have hHSlim := tendsto_hsNorm_eLpNorm_of_columns_L2
    (fun k x i => fderiv ℝ (m k) x (EuclideanSpace.single i 1)) Du hmD huW.2.2 hDconv
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₂R : (p : ℝ) ≤ 2 := by exact_mod_cast hp₂
  have hp0R : 0 < (p : ℝ) := lt_of_lt_of_le zero_lt_one hpR
  have hHp (k : ℕ) : MemLp (H k) (p : ℝ≥0∞) μ := (hH k).mono_exponent (by exact_mod_cast hp₂)
  have hGp : MemLp G (p : ℝ≥0∞) μ := hG.mono_exponent (by exact_mod_cast hp₂)
  have hLower : Tendsto (fun k => eLpNorm (H k-G) (p : ℝ≥0∞) μ) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using
      tendsto_eLpNorm_real_of_L2 hH hG hHSlim hp0R hp₂R
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' H hHp G hGp).mpr hLower
  have hNormLim : Tendsto (fun k => eLpNorm (H k) (p : ℝ≥0∞) μ) atTop
      (𝓝 (eLpNorm G (p : ℝ≥0∞) μ)) := by
    simpa only [Lp.enorm_toLp] using hLp.enorm
  have hbound (k : ℕ) : eLpNorm (m k) (s : ℝ≥0∞) μ ≤
      (C₀ : ℝ≥0∞)*eLpNorm (H k) (p : ℝ≥0∞) μ := by
    have HG := eLpNorm_le_explicit_euclidean_fderiv_of_eq_inner n
      ((hm k).of_le (by simp)) (hmc k).1 hp hn hsp
    have hIndm : (Metric.ball a r).indicator (m k)=m k := by
      funext x
      by_cases hx : x ∈ Metric.ball a r
      · exact indicator_of_mem hx _
      · rw [indicator_of_notMem hx]
        exact (image_eq_zero_of_notMem_tsupport (fun h => hx ((hmc k).2 h))).symm
    have hIndH : (Metric.ball a r).indicator (H k)=H k := by
      funext x
      by_cases hx : x ∈ Metric.ball a r
      · exact indicator_of_mem hx _
      · rw [indicator_of_notMem hx]
        have hz : fderiv ℝ (m k) x = 0 :=
          fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hx ((hmc k).2 h))
        simp only [H,hz,zero_apply,hsNormSq,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),
          Finset.sum_const_zero,Real.sqrt_zero]
    have hfull (A : ℝ≥0∞) : eLpNorm (m k) A volume=eLpNorm (m k) A μ := by
      rw [← hIndm,eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
      rw [hIndm]
    rw [hfull] at HG
    apply HG.trans
    apply mul_le_mul_right
    calc
      eLpNorm (fderiv ℝ (m k)) (p : ℝ≥0∞) volume ≤ eLpNorm (H k) (p : ℝ≥0∞) volume := by
        apply eLpNorm_mono_ae
        exact Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (show 0 ≤ H k x from Real.sqrt_nonneg _)]
          exact HolderToCK.norm_linearMap_le_sqrt_hsNormSq _
      _ = eLpNorm (H k) (p : ℝ≥0∞) μ := by
        rw [← hIndH,eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball,hIndH]
  have hmeasure : TendstoInMeasure μ m atTop u :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (fun k => (hmL k).aestronglyMeasurable)
      huW.2.1.aestronglyMeasurable hconv
  obtain ⟨σ,hσ,hAE⟩ := hmeasure.exists_seq_tendsto_ae
  have hFatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := (s : ℝ≥0∞))
    (fun k => (hmL (σ k)).aestronglyMeasurable) u hAE
  have hRhs := ENNReal.Tendsto.const_mul (a := (C₀ : ℝ≥0∞))
    (hNormLim.comp hσ.tendsto_atTop) (Or.inr ENNReal.coe_ne_top)
  have hFinal : eLpNorm u (s : ℝ≥0∞) μ ≤ (C₀ : ℝ≥0∞)*eLpNorm G (p : ℝ≥0∞) μ := by
    calc
      _ ≤ atTop.liminf (fun k => eLpNorm (m (σ k)) (s : ℝ≥0∞) μ) := hFatou
      _ ≤ atTop.liminf (fun k => (C₀ : ℝ≥0∞)*eLpNorm (H (σ k)) (p : ℝ≥0∞) μ) :=
        liminf_le_liminf (Eventually.of_forall fun k => hbound (σ k))
      _ = _ := hRhs.liminf_eq
  have hFinite : (C₀ : ℝ≥0∞)*eLpNorm G (p : ℝ≥0∞) μ < ⊤ :=
    ENNReal.mul_lt_top ENNReal.coe_lt_top hGp.eLpNorm_lt_top
  refine ⟨⟨huW.2.1.aestronglyMeasurable,hFinal.trans_lt hFinite⟩,?_⟩
  have hC : (C₀ : ℝ≥0∞) ≤ C := by
    exact_mod_cast (show C₀ ≤ C from le_add_of_nonneg_left zero_le_one)
  exact hFinal.trans (mul_le_mul_left hC _)

end StationaryHarmonicMaps.Analysis

end
