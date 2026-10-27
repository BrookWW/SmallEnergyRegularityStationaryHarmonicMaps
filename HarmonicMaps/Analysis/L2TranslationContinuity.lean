module

public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# L2 continuity of translations and scalar amplitudes

The continuity statements concern global L2 functions. Restriction data can be
passed to them through the zero extension supplied by the indicator lemma.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace HarmonicMaps

/-- A measurable set's zero extension carries restricted L2 data to global L2. -/
theorem memLp_zeroExtension {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {s : Set (Domain n)} (hs : MeasurableSet s) {f : Domain n → E}
    (hf : MemLp f 2 (volume.restrict s)) :
    MemLp (s.indicator f) 2 volume :=
  (memLp_indicator_iff_restrict hs).mpr hf

/-- Translation by a vector tending to zero converges in the actual L2 seminorm. -/
theorem tendsto_eLpNorm_translation_sub {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : Domain n → E} (hf : MemLp f 2 volume) :
    Tendsto (fun v : Domain n => eLpNorm (fun x => f (x - v) - f x) 2 volume)
      (𝓝 0) (𝓝 0) := by
  let T : C(Domain n, C(Domain n, Domain n)) :=
    (⟨fun p : Domain n × Domain n => p.2 - p.1,
      continuous_snd.sub continuous_fst⟩ : C(Domain n × Domain n, Domain n)).curry
  have hT (v : Domain n) : MeasurePreserving (T v) volume volume :=
    measurePreserving_sub_right volume v
  have hcont : Continuous (fun v : Domain n =>
      Lp.compMeasurePreserving (T v) (hT v) (hf.toLp f)) :=
    continuous_const.compMeasurePreservingLp T.continuous hT (by norm_num)
  have hid : Lp.compMeasurePreserving (T 0) (hT 0) (hf.toLp f) = hf.toLp f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (hf.toLp f) (hT 0)] with x hx
    simpa [T] using hx
  have hlim := (hcont.tendsto (0 : Domain n)).edist
    (tendsto_const_nhds (x := hf.toLp f))
  simp only [hid, edist_self] at hlim
  convert hlim using 1
  funext v
  rw [Lp.toLp_compMeasurePreserving, Lp.edist_toLp_toLp]
  rfl

/-- Multiplication by a real amplitude tending to one converges in L2. -/
theorem tendsto_eLpNorm_amplitude_sub {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Domain n → E} (hf : MemLp f 2 volume) :
    Tendsto (fun t : ℝ => eLpNorm (fun x => t • f x - f x) 2 volume)
      (𝓝 1) (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => ‖t - 1‖ₑ * eLpNorm f 2 volume) (𝓝 1) (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ => ‖t - 1‖ₑ) (𝓝 1) (𝓝 0) := by
      simpa only [Function.comp_def, enorm_zero] using (continuous_enorm.tendsto (0 : ℝ)).comp
        (by simpa using ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 1) (𝓝 1)).sub
          (tendsto_const_nhds (x := (1 : ℝ)))))
    simpa using ENNReal.Tendsto.mul_const ht (Or.inr hf.eLpNorm_ne_top)
  convert h using 1
  funext t
  have heq : (fun x => t • f x - f x) = (t - 1) • f := by
    funext x
    simp [sub_smul]
  rw [heq, eLpNorm_const_smul]

end HarmonicMaps
