module

public import HolderToCK.Analysis.WeakPoissonZeroBoundaryGreen
public import HarmonicMaps.Analysis.HarmonicEnergyAlgebra
public import HarmonicMaps.EnergyLemmas

/-! # Exact energy orthogonality for a native weak harmonic replacement

The genuine zero-boundary difference tests the harmonic weak equation.
The original displayed gradients give the Hilbert--Schmidt expansion with
coefficient one, without any boundary smoothness assumption on the maps.
-/

public section

open HarmonicMaps MeasureTheory

namespace HolderToCK

theorem weak_harmonic_replacement_energy_orthogonality {n q : ℕ} (Ω : OpenDomain n)
    {u w : Domain n → Ambient q} {Du Dw : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (hw : MemW12 Ω w Dw)
    (hHarmonic : WeakPoissonOn Ω Dw (fun _ => 0))
    (hzero : HasZeroBoundaryValues Ω (u - w) (fun x i => Du x i - Dw x i)) :
    (∫ x in Ω.val, hsNormSq (Du x)) =
      (∫ x in Ω.val, hsNormSq (Dw x)) +
        (∫ x in Ω.val, hsNormSq (fun i => Du x i - Dw x i)) ∧
    dirichletEnergy Dw Ω.val ≤ dirichletEnergy Du Ω.val := by
  have hDuInt := hu.integrable_hsNormSq
  have hDwInt := hw.integrable_hsNormSq
  have hDiffInt := hzero.1.integrable_hsNormSq
  have hGreen := hHarmonic.zeroBoundary_green hw.2.2 MemLp.zero' hzero
  have hcrosszero : (∫ x in Ω.val, ∑ i : Fin n,
      inner ℝ (Dw x i) (Du x i - Dw x i)) = 0 := by
    simpa only [inner_zero_left, integral_zero, neg_zero] using hGreen.2.2
  have hpoint (x : Domain n) : hsNormSq (Du x) =
      hsNormSq (Dw x) + hsNormSq (fun i => Du x i - Dw x i) +
        2 * ∑ i : Fin n, inner ℝ (Dw x i) (Du x i - Dw x i) :=
    hsNormSq_sub_orthogonality (Du x) (Dw x)
  have hidentity : (∫ x in Ω.val, hsNormSq (Du x)) =
      (∫ x in Ω.val, hsNormSq (Dw x)) +
        (∫ x in Ω.val, hsNormSq (fun i => Du x i - Dw x i)) := by
    calc
      _ = ∫ x in Ω.val, hsNormSq (Dw x) +
          (hsNormSq (fun i => Du x i - Dw x i) +
            2 * ∑ i : Fin n, inner ℝ (Dw x i) (Du x i - Dw x i)) := by
        apply setIntegral_congr_fun Ω.property.measurableSet
        intro x _
        dsimp only
        rw [hpoint x]
        ring
      _ = (∫ x in Ω.val, hsNormSq (Dw x)) +
          ((∫ x in Ω.val, hsNormSq (fun i => Du x i - Dw x i)) +
            2 * (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (Dw x i) (Du x i - Dw x i))) := by
        calc
          _ = (∫ x in Ω.val, hsNormSq (Dw x)) +
              (∫ x in Ω.val, hsNormSq (fun i => Du x i - Dw x i) +
                2 * ∑ i : Fin n, inner ℝ (Dw x i) (Du x i - Dw x i)) :=
            integral_add hDwInt (hDiffInt.add (hGreen.1.const_mul 2))
          _ = (∫ x in Ω.val, hsNormSq (Dw x)) +
              ((∫ x in Ω.val, hsNormSq (fun i => Du x i - Dw x i)) +
                (∫ x in Ω.val, 2 * ∑ i : Fin n, inner ℝ (Dw x i) (Du x i - Dw x i))) := by
            rw [integral_add hDiffInt (hGreen.1.const_mul 2)]
          _ = _ := by rw [integral_const_mul]
      _ = _ := by rw [hcrosszero, mul_zero, add_zero]
  have hle : (∫ x in Ω.val, hsNormSq (Dw x)) ≤ ∫ x in Ω.val, hsNormSq (Du x) := by
    have hnonneg : 0 ≤ ∫ x in Ω.val, hsNormSq (fun i => Du x i - Dw x i) :=
      integral_nonneg (fun _ => hsNormSq_nonneg _)
    linarith only [hidentity, hnonneg]
  refine ⟨hidentity, ?_⟩
  rw [dirichletEnergy_eq_ofReal_integral hDwInt, dirichletEnergy_eq_ofReal_integral hDuInt]
  exact ENNReal.ofReal_le_ofReal hle

end HolderToCK
end
