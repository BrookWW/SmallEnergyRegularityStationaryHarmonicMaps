module

public import HarmonicMaps.Analysis.VariableMollificationPullback
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Local analytic consequences of restricted pushforward domination

The estimates use only the target restricted measure. They transport local
Lp membership, integrability, almost-everywhere properties and nonnegative
integrals through the forward map.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace HarmonicMaps

variable {n : ℕ} {F : Domain n → Domain n} {μ ν : Measure (Domain n)}
  {C : ℝ≥0∞}

/-- A finite pushforward majorant preserves local Lp membership. -/
theorem memLp_comp_of_map_le {E : Type*} [NormedAddCommGroup E]
    {f : Domain n → E} {p : ℝ≥0∞} (hF : Measurable F)
    (hbound : Measure.map F μ ≤ C • ν) (hC : C ≠ ⊤) (hf : MemLp f p ν) :
    MemLp (f ∘ F) p μ :=
  ((hf.smul_measure hC).mono_measure hbound).comp_of_map hF.aemeasurable

/-- The sharp measure constant gives its usual `1/p` power in Lp. -/
theorem eLpNorm_comp_le_of_map_le {E : Type*} [NormedAddCommGroup E]
    {f : Domain n → E} {p : ℝ≥0∞} (hF : Measurable F)
    (hbound : Measure.map F μ ≤ C • ν) (hp : p ≠ ⊤)
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm (f ∘ F) p μ ≤ C ^ (1 / p).toReal * eLpNorm f p ν := by
  have hm : AEStronglyMeasurable f (Measure.map F μ) :=
    (hf.smul_measure C).mono_measure hbound
  rw [← eLpNorm_map_measure hm hF.aemeasurable]
  exact (eLpNorm_mono_measure f hbound).trans_eq
    (eLpNorm_smul_measure_of_ne_top hp f C)

/-- Integrability is required only for the measure on the target region. -/
theorem integrable_comp_of_map_le {E : Type*} [NormedAddCommGroup E]
    {f : Domain n → E} (hF : Measurable F)
    (hbound : Measure.map F μ ≤ C • ν) (hC : C ≠ ⊤) (hf : Integrable f ν) :
    Integrable (f ∘ F) μ := by
  have hm := (hf.smul_measure hC).mono_measure hbound
  exact (integrable_map_measure hm.aestronglyMeasurable hF.aemeasurable).mp hm

/-- Pushforward domination transports every almost-everywhere target property. -/
theorem ae_comp_of_map_le {P : Domain n → Prop} (hF : Measurable F)
    (hbound : Measure.map F μ ≤ C • ν) (hP : ∀ᵐ z ∂ν, P z) :
    ∀ᵐ x ∂μ, P (F x) :=
  ae_of_ae_map hF.aemeasurable
    (ae_mono hbound (Measure.ae_smul_measure hP C))

/-- A nonnegative local real integral acquires exactly the measure majorant. -/
theorem integral_comp_le_of_map_le {f : Domain n → ℝ} {K : ℝ}
    (hF : Measurable F) (hbound : Measure.map F μ ≤ ENNReal.ofReal K • ν)
    (hK : 0 ≤ K) (hf : Integrable f ν) (hpos : 0 ≤ᵐ[ν] f) :
    (∫ x, f (F x) ∂μ) ≤ K * ∫ z, f z ∂ν := by
  have hi := hf.smul_measure (c := ENNReal.ofReal K) ENNReal.ofReal_ne_top
  have hm := hi.mono_measure hbound
  rw [← integral_map hF.aemeasurable hm.aestronglyMeasurable]
  calc
    (∫ z, f z ∂Measure.map F μ) ≤ ∫ z, f z ∂ENNReal.ofReal K • ν :=
      integral_mono_measure hbound (Measure.ae_smul_measure hpos _) hi
    _ = K * ∫ z, f z ∂ν := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal hK, smul_eq_mul]

end HarmonicMaps
