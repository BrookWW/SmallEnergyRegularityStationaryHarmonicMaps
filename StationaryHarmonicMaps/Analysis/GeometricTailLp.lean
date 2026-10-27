module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Integer moments from an actual geometric tail bound

Linear amplitude shells dominate every finite integer moment. Their
polynomially weighted geometric masses are summable. The resulting
integrability and moment bound require only a.e. strong measurability and
the actual tail measures on a finite measure space.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace StationaryHarmonicMaps.Analysis

/-- The shifted polynomial weights are summable against a genuine geometric decay. -/
theorem summable_shifted_pow_mul_geometric (k : ℕ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρOne : ρ < 1) :
    Summable (fun m : ℕ => ((m : ℝ) + 2) ^ k * ρ ^ m) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one (r := ρ) k
    (by simpa only [Real.norm_eq_abs, abs_of_pos hρ] using hρOne)
  have hshift := (summable_nat_add_iff 2).2 hs
  refine (hshift.mul_left (ρ ^ 2)⁻¹).congr fun m => ?_
  push_cast
  rw [pow_add]
  field_simp [hρ.ne']

/-- Every value above one amplitude lies in an actual consecutive amplitude shell. -/
theorem exists_geometric_tail_shell {a y : ℝ} (ha : 0 < a) (hay : a < y) :
    ∃ m : ℕ, a * ((m : ℝ) + 1) < y ∧ y ≤ a * ((m : ℝ) + 2) := by
  classical
  have hex : ∃ n : ℕ, y ≤ a * ((n : ℝ) + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_ge (y / a)
    refine ⟨n, ?_⟩
    have H := (div_le_iff₀ ha).mp hn
    nlinarith
  let N := Nat.find hex
  have hN : y ≤ a * ((N : ℝ) + 1) := Nat.find_spec hex
  have hNpos : 0 < N := by
    by_contra hn
    have hzero : N = 0 := Nat.eq_zero_of_not_pos hn
    simp only [hzero, Nat.cast_zero, zero_add, mul_one] at hN
    exact (not_le_of_gt hay) hN
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
  refine ⟨m, ?_, ?_⟩
  · have hlt : m < Nat.find hex := by change m < N; rw [hm]; exact Nat.lt_succ_self m
    exact lt_of_not_ge (Nat.find_min hex hlt)
  · simpa only [hm, Nat.cast_succ, add_assoc, one_add_one_eq_two] using hN

/-- Geometric tail masses give a finite extended integer-moment bound for a measurable representative. -/
theorem lintegral_norm_pow_le_of_geometric_tail {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (μ : Measure X) [IsFiniteMeasure μ]
    (k : ℕ) {ρ a M : ℝ} (hρ : 0 < ρ) (hρOne : ρ < 1)
    (f : X → E) (hf : StronglyMeasurable f) (ha : 0 < a) (hM : 0 ≤ M)
    (htail : ∀ m : ℕ, μ {x | a * ((m : ℝ) + 1) < ‖f x‖} ≤
      ENNReal.ofReal (M * ρ ^ m)) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ k) ∂μ) ≤
      ENNReal.ofReal (((1 : ℝ) + ∑' m : ℕ, ((m : ℝ) + 2) ^ k * ρ ^ m) *
        a ^ k * (μ.real univ + M)) := by
  classical
  let S (m : ℕ) := {x : X | a * ((m : ℝ) + 1) < ‖f x‖}
  let T (m : ℕ) : X → ℝ≥0∞ :=
    (S m).indicator (fun _ => ENNReal.ofReal ((a * ((m : ℝ) + 2)) ^ k))
  let w (m : ℕ) : ℝ := ((m : ℝ) + 2) ^ k * ρ ^ m
  let W : ℝ := ∑' m, w m
  let C : ℝ := 1 + W
  have hw : Summable w := summable_shifted_pow_mul_geometric k hρ hρOne
  have hwpos (m : ℕ) : 0 ≤ w m := by dsimp only [w]; positivity
  have hW : 0 ≤ W := tsum_nonneg hwpos
  have hCOne : 1 ≤ C := by dsimp only [C]; linarith
  have hWC : W ≤ C := by dsimp only [C]; linarith
  have hS (m : ℕ) : MeasurableSet (S m) := measurableSet_lt measurable_const hf.norm.measurable
  have hT (m : ℕ) : Measurable (T m) := measurable_const.indicator (hS m)
  have hpoint (x : X) : ENNReal.ofReal (‖f x‖ ^ k) ≤ ENNReal.ofReal (a ^ k) + ∑' m, T m x := by
    by_cases hx : ‖f x‖ ≤ a
    · exact (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hx k)).trans
        (le_add_right le_rfl)
    · obtain ⟨m, hm, hupper⟩ := exists_geometric_tail_shell ha (lt_of_not_ge hx)
      calc
        _ ≤ ENNReal.ofReal ((a * ((m : ℝ) + 2)) ^ k) :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hupper k)
        _ = T m x := by simp only [T, indicator_of_mem (show x ∈ S m from hm)]
        _ ≤ ∑' m, T m x := ENNReal.le_tsum m
        _ ≤ _ := le_add_left le_rfl
  have hterm (m : ℕ) : (∫⁻ x, T m x ∂μ) ≤
      ENNReal.ofReal (a ^ k * M) * ENNReal.ofReal (w m) := by
    dsimp only [T]
    rw [lintegral_indicator_const (hS m)]
    calc
      _ ≤ ENNReal.ofReal ((a * ((m : ℝ) + 2)) ^ k) * ENNReal.ofReal (M * ρ ^ m) :=
        mul_le_mul_right (htail m) _
      _ = ENNReal.ofReal (((a * ((m : ℝ) + 2)) ^ k) * (M * ρ ^ m)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ a ^ k * M)]
        congr 1
        dsimp only [w]
        rw [mul_pow]
        ring
  have hμ : ENNReal.ofReal (μ.real univ) = μ univ :=
    ENNReal.ofReal_toReal (measure_ne_top μ univ)
  have hreal : a ^ k * μ.real univ + a ^ k * M * W ≤ C * a ^ k * (μ.real univ + M) := by
    calc
      _ ≤ C * (a ^ k * μ.real univ) + (a ^ k * M) * C :=
        add_le_add (le_mul_of_one_le_left (by positivity) hCOne)
          (mul_le_mul_of_nonneg_left hWC (by positivity))
      _ = _ := by ring
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (a ^ k) + ∑' m, T m x ∂μ := lintegral_mono hpoint
    _ = ENNReal.ofReal (a ^ k) * μ univ + ∑' m, ∫⁻ x, T m x ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_const,
        lintegral_tsum (fun m => (hT m).aemeasurable)]
    _ ≤ ENNReal.ofReal (a ^ k) * μ univ +
        ∑' m, ENNReal.ofReal (a ^ k * M) * ENNReal.ofReal (w m) :=
      add_le_add le_rfl (ENNReal.tsum_le_tsum hterm)
    _ = ENNReal.ofReal (a ^ k * μ.real univ + a ^ k * M * W) := by
      rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg hwpos hw, ← hμ,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ a ^ k),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ a ^ k * M),
        ← ENNReal.ofReal_add (by positivity : 0 ≤ a ^ k * μ.real univ)
          (by positivity : 0 ≤ a ^ k * M * W)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- One constant depending only on the integer exponent and decay ratio controls every actual tail datum. -/

@[expose] noncomputable def shiftedGeometricMomentConstant (k : ℕ) (ρ : ℝ) : ℝ :=
  1 + ∑' m : ℕ, ((m : ℝ) + 2)^k * ρ^m

theorem geometric_tail_integer_moment_explicit (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ)
    (hρ : 0 < ρ) (hρOne : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ C = shiftedGeometricMomentConstant k ρ ∧ ∀ {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
      (μ : Measure X) [IsFiniteMeasure μ] (f : X → E),
      AEStronglyMeasurable f μ → ∀ {a M : ℝ}, 0 < a → 0 ≤ M →
      (∀ m : ℕ, μ {x | a * ((m : ℝ) + 1) < ‖f x‖} ≤ ENNReal.ofReal (M * ρ ^ m)) →
      MemLp f (k : ℝ≥0∞) μ ∧ Integrable (fun x => ‖f x‖ ^ k) μ ∧
        (∫ x, ‖f x‖ ^ k ∂μ) ≤ C * a ^ k * (μ.real univ + M) := by
  let W : ℝ := ∑' m : ℕ, ((m : ℝ) + 2) ^ k * ρ ^ m
  have hW : 0 ≤ W := tsum_nonneg (fun m => by positivity)
  refine ⟨1 + W, by positivity, rfl, ?_⟩
  intro X E _ _ μ _ f hf a M ha hM htail
  let g := hf.mk f
  have hfg : f =ᵐ[μ] g := hf.ae_eq_mk
  have hg : StronglyMeasurable g := hf.stronglyMeasurable_mk
  have htailg (m : ℕ) : μ {x | a * ((m : ℝ) + 1) < ‖g x‖} ≤
      ENNReal.ofReal (M * ρ ^ m) := by
    have hset : {x | a * ((m : ℝ) + 1) < ‖g x‖} =ᵐ[μ]
        {x | a * ((m : ℝ) + 1) < ‖f x‖} := by
      filter_upwards [hfg] with x hx
      exact congrArg (fun v : E => a * ((m : ℝ) + 1) < ‖v‖) hx.symm
    exact (measure_congr hset).le.trans (htail m)
  have hlin := lintegral_norm_pow_le_of_geometric_tail μ k hρ hρOne g hg ha hM htailg
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ ‖g x‖ ^ k :=
    Eventually.of_forall (fun x => pow_nonneg (norm_nonneg _) k)
  have hIntg : Integrable (fun x => ‖g x‖ ^ k) μ :=
    ⟨(hg.norm.pow k).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnonneg).2 (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hkg : MemLp g (k : ℝ≥0∞) μ := by
    apply (integrable_norm_rpow_iff hg.aestronglyMeasurable
      (by exact_mod_cast hkpos.ne') (by simp)).mp
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast] using hIntg
  have hnorm : (fun x => ‖f x‖ ^ k) =ᵐ[μ] (fun x => ‖g x‖ ^ k) :=
    hfg.mono (fun x hx => congrArg (fun v : E => ‖v‖ ^ k) hx)
  refine ⟨hkg.ae_eq hfg.symm, hIntg.congr hnorm.symm, ?_⟩
  calc
    _ = ∫ x, ‖g x‖ ^ k ∂μ := integral_congr_ae hnorm
    _ = (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ k) ∂μ).toReal :=
      integral_eq_lintegral_of_nonneg_ae hnonneg hIntg.aestronglyMeasurable
    _ ≤ (ENNReal.ofReal ((1 + W) * a ^ k * (μ.real univ + M))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    _ = _ := ENNReal.toReal_ofReal (by positivity)

theorem geometric_tail_integer_moment (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ)
    (hρ : 0 < ρ) (hρOne : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
      (μ : Measure X) [IsFiniteMeasure μ] (f : X → E),
      AEStronglyMeasurable f μ → ∀ {a M : ℝ}, 0 < a → 0 ≤ M →
      (∀ m : ℕ, μ {x | a * ((m : ℝ) + 1) < ‖f x‖} ≤ ENNReal.ofReal (M * ρ ^ m)) →
      MemLp f (k : ℝ≥0∞) μ ∧ Integrable (fun x => ‖f x‖ ^ k) μ ∧
        (∫ x, ‖f x‖ ^ k ∂μ) ≤ C * a ^ k * (μ.real univ + M) := by
  obtain ⟨C, hC, _hFormula, H⟩ :=
    geometric_tail_integer_moment_explicit k hk ρ hρ hρOne
  exact ⟨C, hC, H⟩

end StationaryHarmonicMaps.Analysis

end
