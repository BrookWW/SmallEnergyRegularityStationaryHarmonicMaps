module

public import StationaryHarmonicMaps.Analysis.FiniteWeightedSum

/-!
# Actual pointwise algebra of the corrected partition pieces

On the high bad set the original function cancels between the low piece
and the original product row. The remaining genuine finite weighted
sums involve only the original low/high averages and actual correction
coefficients. Outside that set every high weight is zero.
-/

public section

open HarmonicMaps Set

namespace StationaryHarmonicMaps.Analysis

/-- A genuine finite high partition makes the original unbounded scalar cancel in the actual corrected piece, leaving only the three actual coefficient bounds. -/
theorem abs_corrected_piece_le_on_partition {I : Type*} (w c d : I → ℝ)
    (hFinite : Function.HasFiniteSupport w) (hNonneg : ∀ j,0≤w j) (hSum : ∑' j,w j=1)
    (f φ ci Mlo Mhi Mcor : ℝ) (hφ0 : 0≤φ) (hφ1 : φ≤1)
    (hci : |ci|≤Mlo) (hc : ∀ j,|c j|≤Mhi) (hd : ∀ j,|d j|≤Mcor) :
    |φ*(f-ci)-(∑' j,φ*(w j*(f-c j)))+(∑' j,d j*w j)|≤Mlo+Mhi+Mcor := by
  have hSf : Summable (fun j=>w j*f) := (summable_of_hasFiniteSupport hFinite).mul_right _
  have hCFinite : Function.HasFiniteSupport (fun j=>w j*c j) := hFinite.subset (by
    intro j hj;by_contra hn
    have H : w j=0 := not_not.mp hn
    exact hj (by change w j*c j=0;rw [H,zero_mul]))
  have hSc : Summable (fun j=>w j*c j) := summable_of_hasFiniteSupport hCFinite
  have hProduct : (∑' j,φ*(w j*(f-c j)))=φ*(f-∑' j,w j*c j) := by
    rw [tsum_mul_left]
    simp_rw [mul_sub]
    rw [hSf.tsum_sub hSc,tsum_mul_right,hSum,one_mul]
    ring
  have hHigh : |∑' j,w j*c j|≤Mhi := abs_tsum_mul_le_of_finite_weights w c hFinite hNonneg hSum Mhi hc
  have hCorr : |∑' j,d j*w j|≤Mcor := by
    rw [show (∑' j,d j*w j)=(∑' j,w j*d j) from tsum_congr fun _=>mul_comm _ _]
    exact abs_tsum_mul_le_of_finite_weights w d hFinite hNonneg hSum Mcor hd
  have hLow : |φ*((∑' j,w j*c j)-ci)|≤Mhi+Mlo := by
    rw [abs_mul,abs_of_nonneg hφ0]
    calc
      _ ≤ 1*|(∑' j,w j*c j)-ci| := mul_le_mul_of_nonneg_right hφ1 (abs_nonneg _)
      _ ≤ Mhi+Mlo := by rw [one_mul];exact (abs_sub _ _).trans (add_le_add hHigh hci)
  rw [hProduct]
  have hAlg : φ*(f-ci)-φ*(f-∑' j,w j*c j)=φ*((∑' j,w j*c j)-ci) := by ring
  rw [hAlg]
  exact (abs_add_le _ _).trans ((add_le_add hLow hCorr).trans_eq (by ring))

/-- When the original high partition vanishes, the actual corrected expression is the original low piece with its genuine value bound. -/
theorem abs_corrected_piece_le_off_partition {I : Type*} (w c d : I → ℝ) (hZero : ∀ j,w j=0)
    (f φ ci Mlo Mf : ℝ) (hφ0 : 0≤φ) (hφ1 : φ≤1) (hci : |ci|≤Mlo) (hf : |f|≤Mf) :
    |φ*(f-ci)-(∑' j,φ*(w j*(f-c j)))+(∑' j,d j*w j)|≤Mf+Mlo := by
  simp only [hZero,zero_mul,mul_zero,tsum_zero,sub_zero,add_zero]
  rw [abs_mul,abs_of_nonneg hφ0]
  exact (mul_le_mul_of_nonneg_right hφ1 (abs_nonneg _)).trans
    (by rw [one_mul];exact (abs_sub _ _).trans (add_le_add hf hci))

end StationaryHarmonicMaps.Analysis

end
