module

public import StationaryHarmonicMaps.Analysis.CompensationRowIntegration

/-! # The actual corrected cancellation piece is integrable and has zero integral -/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original low zero-mean piece and the actual mass-normalized high row produce the genuine corrected integrable zero-mean piece. -/
theorem integrable_corrected_compensation_piece_integral_zero {X I : Type*}
    [MeasurableSpace X] [Countable I] (μ : Measure X) (F ψ : I → X → ℝ)
    (hF : ∀ j,Integrable (F j) μ) (hFinite : ∀ x,Function.HasFiniteSupport (fun j=>F j x))
    (hAbsI : Integrable (fun x=>∑' j,|F j x|) μ)
    (hψ : ∀ j,Integrable (ψ j) μ) (hNonneg : ∀ j x,0≤ψ j x)
    (hMass : ∀ j,0<(∫ x,ψ j x ∂μ))
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ μ) (hBound : ∀ x,|φ x|≤1)
    (b : X → ℝ) (hb : Integrable b μ) (hbMean : (∫ x,b x ∂μ)=0) :
    let d := fun j=>(∫ x,φ x*F j x ∂μ)/(∫ x,ψ j x ∂μ)
    let A := fun x=>b x-(∑' j,φ x*F j x)+(∑' j,d j*ψ j x)
    Integrable A μ ∧ (∫ x,A x ∂μ)=0 := by
  intro d A
  obtain ⟨_hRows,_hPAbsI,hPI,_hQAbsI,hQI,hRowsEq⟩ :=
    integrable_compensation_row_and_integral_eq μ F ψ hF hFinite hAbsI hψ hNonneg hMass φ hφ hBound
  refine ⟨(hb.sub hPI).add hQI,?_⟩
  have hIntegral : (∫ x,A x ∂μ)=(∫ x,b x ∂μ)-(∫ x,(∑' j,φ x*F j x) ∂μ)+(∫ x,(∑' j,d j*ψ j x) ∂μ) := by
    have H := (integral_add (hb.sub hPI) hQI).trans
      (congrArg (fun t : ℝ=>t+(∫ x,(∑' j,d j*ψ j x) ∂μ)) (integral_sub hb hPI))
    simpa only [A,Pi.sub_apply] using H
  rw [hIntegral,hbMean,hRowsEq]
  ring

end StationaryHarmonicMaps.Analysis

end
