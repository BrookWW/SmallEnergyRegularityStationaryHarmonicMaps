module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Rational energy thresholds from certified amplitude bounds

The arithmetic uses rational majorants throughout. Positive lower bounds for
the two amplitude thresholds and upper bounds for the analytic coefficients
produce a positive rational energy threshold and a rational Hölder coefficient.
-/

@[expose] public section

open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The joint stationary Morrey factor evaluated at a rational geometric bound. -/
def rationalMorreyFactor (n q : ℕ) (L : ℚ) : ℚ :=
  (1+(q:ℚ)*(2*L)^2)*(4:ℚ)^(n-2)

/-- A rational majorant for `(1+G)*sqrt M`. -/
def rationalAmplitudeMajorant (n q : ℕ) (L G : ℚ) : ℚ :=
  (1+G)*(1+rationalMorreyFactor n q L)

/-- The squared amplitude threshold divided by a rational amplitude majorant. -/
def rationalEnergyThreshold (n q : ℕ) (L G κ θ : ℚ) : ℚ :=
  (min κ θ/rationalAmplitudeMajorant n q L G)^2

/-- A rational coefficient dominating the fixed three-quarter-ball rescaling. -/
def rationalHolderCoefficient (n q : ℕ) (L G H : ℚ) : ℚ :=
  2*H*rationalAmplitudeMajorant n q L G

theorem rationalMorreyFactor_pos (n q : ℕ) (L : ℚ) :
    0<rationalMorreyFactor n q L := by
  unfold rationalMorreyFactor
  positivity

theorem rationalAmplitudeMajorant_pos (n q : ℕ) (L : ℚ) {G : ℚ} (hG : 0≤G) :
    0<rationalAmplitudeMajorant n q L G := by
  have hM := rationalMorreyFactor_pos n q L
  unfold rationalAmplitudeMajorant
  positivity

theorem rationalEnergyThreshold_pos (n q : ℕ) (L : ℚ) {G κ θ : ℚ}
    (hG : 0≤G) (hκ : 0<κ) (hθ : 0<θ) :
    0<rationalEnergyThreshold n q L G κ θ := by
  have hK := rationalAmplitudeMajorant_pos n q L hG
  unfold rationalEnergyThreshold
  exact pow_pos (div_pos (lt_min hκ hθ) hK) 2

theorem rationalHolderCoefficient_pos (n q : ℕ) (L : ℚ) {G H : ℚ}
    (hG : 0≤G) (hH : 0<H) : 0<rationalHolderCoefficient n q L G H := by
  have hK := rationalAmplitudeMajorant_pos n q L hG
  unfold rationalHolderCoefficient
  positivity

theorem sqrt_le_one_add {M : ℝ} (hM : 0≤M) : Real.sqrt M≤1+M := by
  apply (Real.sqrt_le_left (by positivity : 0≤1+M)).mpr
  nlinarith only [hM,sq_nonneg M]

theorem real_amplitude_le_rational_majorant
    (n q : ℕ) (L G : ℚ) {M g : ℝ}
    (hM : 0≤M) (hMbound : M≤(rationalMorreyFactor n q L:ℝ))
    (hg : 0≤g) (hgG : g≤(G:ℝ)) :
    (1+g)*Real.sqrt M≤(rationalAmplitudeMajorant n q L G:ℝ) := by
  have hRoot : Real.sqrt M≤1+(rationalMorreyFactor n q L:ℝ) :=
    (sqrt_le_one_add hM).trans (by linarith only [hMbound])
  calc
    _≤(1+(G:ℝ))*(1+(rationalMorreyFactor n q L:ℝ)) :=
      mul_le_mul (by linarith only [hgG]) hRoot (Real.sqrt_nonneg M) (by linarith only [hg,hgG])
    _=(rationalAmplitudeMajorant n q L G:ℝ) := by
      unfold rationalAmplitudeMajorant
      push_cast
      rfl

theorem sqrt_energy_amplitude_le_min
    (n q : ℕ) (L G κ θ : ℚ) (hG : 0≤G) (hκ : 0<κ) (hθ : 0<θ)
    {E : ℝ} (_hE : 0≤E) (hSmall : E≤(rationalEnergyThreshold n q L G κ θ:ℝ)) :
    (rationalAmplitudeMajorant n q L G:ℝ)*Real.sqrt E≤(min κ θ:ℝ) := by
  have hKq := rationalAmplitudeMajorant_pos n q L hG
  have hK : 0<(rationalAmplitudeMajorant n q L G:ℝ) := by exact_mod_cast hKq
  have hτ : 0<(min κ θ:ℝ) := by exact_mod_cast (lt_min hκ hθ)
  have hSmall' : E≤((min κ θ:ℝ)/(rationalAmplitudeMajorant n q L G:ℝ))^2 := by
    norm_cast at hSmall ⊢
  have hRoot : Real.sqrt E≤(min κ θ:ℝ)/(rationalAmplitudeMajorant n q L G:ℝ) :=
    (Real.sqrt_le_left (div_pos hτ hK).le).mpr hSmall'
  exact (mul_le_mul_of_nonneg_left hRoot hK.le).trans_eq (by field_simp)

/-- The certified rational threshold controls both amplitudes in the
original stationary system, including zero normalized energy. -/
theorem rational_energy_amplitudes (n q : ℕ) (L G κ θ : ℚ)
    (hG : 0≤G) (hκ : 0<κ) (hθ : 0<θ)
    (E : ℝ≥0∞) (hE : E≤ENNReal.ofReal (rationalEnergyThreshold n q L G κ θ:ℝ)) :
    let M : ℝ := (rationalMorreyFactor n q L:ℝ)
    let η := Real.sqrt M*Real.sqrt E.toReal
    let β := (1+(G:ℝ))*η
    0≤η ∧ η≤(κ:ℝ) ∧ 0≤β ∧ β≤(θ:ℝ) ∧
      ENNReal.ofReal M*E=ENNReal.ofReal (η^2) ∧
      (G:ℝ)*η^2≤β^2 ∧ η^2≤β^2 ∧
      β≤(rationalAmplitudeMajorant n q L G:ℝ)*Real.sqrt E.toReal := by
  intro M η β
  have hM : 0<M := by dsimp only [M];exact_mod_cast rationalMorreyFactor_pos n q L
  have hGR : 0≤(G:ℝ) := by exact_mod_cast hG
  have hFin : E≠⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE
  have hThreshold : 0≤(rationalEnergyThreshold n q L G κ θ:ℝ) := by
    exact_mod_cast (rationalEnergyThreshold_pos n q L hG hκ hθ).le
  have hReal : E.toReal≤(rationalEnergyThreshold n q L G κ θ:ℝ) :=
    ((ENNReal.toReal_le_toReal hFin ENNReal.ofReal_ne_top).mpr hE).trans_eq
      (ENNReal.toReal_ofReal hThreshold)
  have hη : 0≤η := mul_nonneg (Real.sqrt_nonneg M) (Real.sqrt_nonneg E.toReal)
  have hβ : 0≤β := mul_nonneg (by linarith only [hGR]) hη
  have hηβ : η≤β := by dsimp only [β];nlinarith only [hGR,hη]
  have hβBound : β≤(rationalAmplitudeMajorant n q L G:ℝ)*Real.sqrt E.toReal := by
    have H := real_amplitude_le_rational_majorant n q L G hM.le le_rfl hGR le_rfl
    simpa only [β,η,mul_assoc] using mul_le_mul_of_nonneg_right H (Real.sqrt_nonneg E.toReal)
  have hSmall := sqrt_energy_amplitude_le_min n q L G κ θ hG hκ hθ
    ENNReal.toReal_nonneg hReal
  have hβMin : β≤min (κ:ℝ) (θ:ℝ) := hβBound.trans hSmall
  have hEtaSmall : η≤(κ:ℝ) := hηβ.trans (hβMin.trans (min_le_left _ _))
  have hBetaSmall : β≤(θ:ℝ) := hβMin.trans (min_le_right _ _)
  have hSquare : η^2=M*E.toReal := by
    dsimp only [η]
    rw [mul_pow,Real.sq_sqrt hM.le,Real.sq_sqrt ENNReal.toReal_nonneg]
  refine ⟨hη,hEtaSmall,hβ,hBetaSmall,?_,?_,?_,hβBound⟩
  · rw [hSquare,ENNReal.ofReal_mul hM.le,ENNReal.ofReal_toReal hFin]
  · have hCoeff : (G:ℝ)≤(1+(G:ℝ))^2 := by nlinarith only [hGR,sq_nonneg (G:ℝ)]
    calc
      _≤(1+(G:ℝ))^2*η^2 := mul_le_mul_of_nonneg_right hCoeff (sq_nonneg η)
      _=β^2 := by dsimp only [β];ring
  · exact pow_le_pow_left₀ hη hηβ 2

end StationaryHarmonicMaps.Analysis
