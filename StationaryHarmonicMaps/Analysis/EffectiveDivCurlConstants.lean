module

public import StationaryHarmonicMaps.Analysis.DivCurlScaleNormalization
public import StationaryHarmonicMaps.Analysis.EffectiveEuclideanVolume
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer majorants for the lower-exponent div--curl estimates

The Sobolev exponent is the literal rational number `2*n/(n+1)`.
Its Sobolev coefficient simplifies to `2*n`. The remaining square roots,
ball volumes and powers have dimension-dependent integer majorants.
-/

@[expose] public section

open HarmonicMaps MeasureTheory Metric
open scoped NNReal ENNReal ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

def divcurlLocalSobolevMajorant (n : ℕ) : ℕ :=
  (1+2*n)*(n+2+4*n*2^22*(n+1)*2^n)

def divcurlLowerKernelMajorant (n : ℕ) : ℕ :=
  1+divcurlLocalSobolevMajorant n*(n+1)

def divcurlScaledKernelMajorant (n : ℕ) : ℕ :=
  divcurlLowerKernelMajorant n*2^n*(1+4^n)

def divcurlDyadicKernelMajorant (n : ℕ) : ℕ :=
  divcurlScaledKernelMajorant n*2^n*2^n

def divcurlGrandKernelMajorant (n : ℕ) : ℕ :=
  divcurlDyadicKernelMajorant n*(4*(n+1)*5^n)

theorem euclideanSobolevCoefficient_clms {n : ℕ} (hn : 2≤n) (p : ℝ≥0)
    (hp : (p:ℝ)=2*(n:ℝ)/((n:ℝ)+1)) :
    euclideanSobolevCoefficient n (p:ℝ)=(2*n:ℝ≥0) := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hn0 : 0<(n:ℝ) := by linarith only [hnR]
  have hn1 : 0<(n:ℝ)-1 := by linarith only [hnR]
  have hnp : 0<(n:ℝ)-(p:ℝ) := by
    rw [hp,sub_pos,div_lt_iff₀ (by positivity : 0<(n:ℝ)+1)]
    nlinarith only [mul_pos hn0 hn1]
  have hRatio : (p:ℝ)*((n:ℝ)-1)/((n:ℝ)-p)=2 := by
    apply (div_eq_iff hnp.ne').mpr
    rw [hp]
    field_simp
    ring
  unfold euclideanSobolevCoefficient
  rw [hRatio]
  norm_num
  ring

theorem localSobolevPoincareConstant_clms_le {n : ℕ} (hn : 2≤n) (p : ℝ≥0)
    (hp : 1<p) (hpFormula : (p:ℝ)=2*(n:ℝ)/((n:ℝ)+1)) :
    localSobolevPoincareConstant n p≤(divcurlLocalSobolevMajorant n:ℝ) := by
  have hRoot : Real.sqrt (n:ℝ)≤(n:ℝ)+1 := by
    apply (Real.sqrt_le_left (by positivity : 0≤(n:ℝ)+1)).mpr
    nlinarith only [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]
  have hpR : 1<(p:ℝ) := by exact_mod_cast hp
  have hInv : 1/(p:ℝ)≤1 := (div_le_one (by linarith only [hpR] : 0<(p:ℝ))).mpr hpR.le
  have hPow : ((2:ℝ)^n)^(1/(p:ℝ))≤(2:ℝ)^n :=
    Real.rpow_le_self_of_one_le (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hInv
  rw [localSobolevPoincareConstant,euclideanSobolevCoefficient_clms hn p hpFormula]
  have hFactors :
      1+Real.sqrt (n:ℝ)+4*(n:ℝ)*(2:ℝ)^22*Real.sqrt (n:ℝ)*((2:ℝ)^n)^(1/(p:ℝ))≤
        (n:ℝ)+2+4*(n:ℝ)*(2:ℝ)^22*((n:ℝ)+1)*(2:ℝ)^n := by
    apply add_le_add
    · linarith only [hRoot]
    · gcongr
  calc
    _≤(1+(2*n:ℝ≥0):ℝ)*((n:ℝ)+2+4*(n:ℝ)*(2:ℝ)^22*((n:ℝ)+1)*(2:ℝ)^n) :=
      mul_le_mul_of_nonneg_left hFactors (by positivity)
    _=(divcurlLocalSobolevMajorant n:ℝ) := by
      unfold divcurlLocalSobolevMajorant
      push_cast
      ring

theorem divcurlLowerExponentConstant_clms_le {n : ℕ} (hn : 2≤n) (p : ℝ≥0)
    (hp : 1<p) (hpFormula : (p:ℝ)=2*(n:ℝ)/((n:ℝ)+1)) :
    divcurlLowerExponentConstant n p≤(divcurlLowerKernelMajorant n:ℝ) := by
  have hRoot : Real.sqrt (n:ℝ)≤(n:ℝ)+1 := by
    apply (Real.sqrt_le_left (by positivity : 0≤(n:ℝ)+1)).mpr
    nlinarith only [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]
  have hLocal := localSobolevPoincareConstant_clms_le hn p hp hpFormula
  unfold divcurlLowerExponentConstant divcurlLowerKernelMajorant
  push_cast
  have hProduct := mul_le_mul hLocal hRoot (Real.sqrt_nonneg _) (by positivity)
  linarith only [hProduct]

theorem euclidean_unit_ball_positive_rpow_le (n : ℕ) (s : ℝ)
    (hs : 0≤s) (hsTwo : s≤2) :
    (volume.real (ball (0:Domain n) 1))^s≤1+(4:ℝ)^n := by
  let V : ℝ := volume.real (ball (0:Domain n) 1)
  have hV : 0≤V := ENNReal.toReal_nonneg
  have hUpper : V≤(2:ℝ)^n := euclidean_unit_ball_volume_upper_bound n
  by_cases hOne : V≤1
  · exact (Real.rpow_le_one hV hOne hs).trans
      (by linarith only [pow_nonneg (by norm_num : (0:ℝ)≤4) n])
  · calc
      _≤V^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (not_le.mp hOne).le hsTwo
      _=V^2 := by norm_num
      _≤((2:ℝ)^n)^2 := pow_le_pow_left₀ hV hUpper 2
      _=(4:ℝ)^n := by rw [pow_two,←mul_pow];norm_num
      _≤1+(4:ℝ)^n := by linarith only [pow_nonneg (by norm_num : (0:ℝ)≤4) n]

theorem divcurlScaledAverageConstant_clms_le {n : ℕ} (hn : 2≤n) (p : ℝ≥0)
    (hp : 1<p) (hpFormula : (p:ℝ)=2*(n:ℝ)/((n:ℝ)+1)) :
    divcurlScaledAverageConstant n p≤(divcurlScaledKernelMajorant n:ℝ) := by
  have hpR : 1<(p:ℝ) := by exact_mod_cast hp
  have hp0 : 0<(p:ℝ) := by linarith only [hpR]
  have hInv : 1/(p:ℝ)≤1 := (div_le_one hp0).mpr hpR.le
  have hPow : ((2:ℝ)^n)^(1/(p:ℝ))≤(2:ℝ)^n :=
    Real.rpow_le_self_of_one_le (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hInv
  have hTwo : 2/(p:ℝ)≤2 := (div_le_iff₀ hp0).mpr (by linarith only [hpR])
  have hVolume := euclidean_unit_ball_positive_rpow_le n (2/(p:ℝ)) (by positivity) hTwo
  have hLower := divcurlLowerExponentConstant_clms_le hn p hp hpFormula
  unfold divcurlScaledAverageConstant
  calc
    _≤(divcurlLowerKernelMajorant n:ℝ)*(2:ℝ)^n*(1+(4:ℝ)^n) :=
      mul_le_mul (mul_le_mul hLower hPow (by positivity) (Nat.cast_nonneg _))
        hVolume (Real.rpow_nonneg ENNReal.toReal_nonneg _) (by positivity)
    _=(divcurlScaledKernelMajorant n:ℝ) := by
      unfold divcurlScaledKernelMajorant
      push_cast
      rfl

theorem clms_maximal_moment_coefficient_le {n : ℕ} (hn : 2≤n) (p : ℝ≥0)
    (hpFormula : (p:ℝ)=2*(n:ℝ)/((n:ℝ)+1)) :
    ((2:ℝ)^(2/(p:ℝ))*(2/(p:ℝ))/(2/(p:ℝ)-1))*(5:ℝ)^n ≤
      (4*(n+1)*5^n:ℕ) := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (n:ℝ)≠0 := by linarith only [hnR]
  have hRatio : 2/(p:ℝ)=((n:ℝ)+1)/(n:ℝ) := by
    rw [hpFormula]
    field_simp
  have hGap : (n:ℝ)+1-(n:ℝ)≠0 := by ring_nf;norm_num
  have hCancel : (2/(p:ℝ))/(2/(p:ℝ)-1)=(n:ℝ)+1 := by
    rw [hRatio]
    field_simp
    ring
  have hTwo : 2/(p:ℝ)≤2 := by
    rw [hRatio]
    exact (div_le_iff₀ (by linarith only [hnR] : 0<(n:ℝ))).mpr (by linarith only [hnR])
  have hPow : (2:ℝ)^(2/(p:ℝ))≤4 := by
    calc
      _≤(2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hTwo
      _=4 := by norm_num
  calc
    _=(2:ℝ)^(2/(p:ℝ))*((2/(p:ℝ))/(2/(p:ℝ)-1))*(5:ℝ)^n := by ring
    _=(2:ℝ)^(2/(p:ℝ))*((n:ℝ)+1)*(5:ℝ)^n := by rw [hCancel]
    _≤4*((n:ℝ)+1)*(5:ℝ)^n := by gcongr
    _=(4*(n+1)*5^n:ℕ) := by push_cast;rfl

theorem exists_divcurl_scaled_average_kernel_bound_effective (n : ℕ) (hn : 2 ≤ n) :
    ∃ p : ℝ≥0, (p : ℝ)=2*(n : ℝ)/((n : ℝ)+1) ∧ 1 < p ∧ p < 2 ∧
      ∃ C : ℝ, 0 < C ∧ C=(divcurlScaledKernelMajorant n:ℝ) ∧ ∀ (q : ℕ) (a : Domain n) (r : ℝ), 0 < r →
        ∀ (Z : Domain n → Gradient n q),
          (∀ i,MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball a (2*r)))) →
          HolderToCK.WeakPoissonOn (ballDomain a (2*r)) Z (fun _ => (0 : Ambient q)) →
          ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
            MemW12 (ballDomain a (2*r)) w Dw →
            ∀ (κ : Domain n → ℝ), ContDiff ℝ ∞ κ → HasCompactSupport κ →
            tsupport κ ⊆ Metric.ball a r → ∀ B : ℝ, 0 ≤ B →
            (∀ x ∈ Metric.ball a r,∀ i : Fin n,
              |fderiv ℝ κ x (EuclideanSpace.single i 1)| ≤ B*r^(-(n : ℝ)-1)) →
            IntegrableOn (fun x => κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i))
              (Metric.ball a r) volume ∧
            |∫ x in Metric.ball a r,κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i)| ≤
              C*B*(⨍ x in Metric.ball a r,(Real.sqrt (hsNormSq (Z x)))^(p : ℝ))^(1/(p : ℝ))*
                (⨍ x in Metric.ball a (2*r),(Real.sqrt (hsNormSq (Dw x)))^(p : ℝ))^(1/(p : ℝ)) := by
  obtain ⟨p,hpFormula,hp1,hp2,C,hCEq,hC,H⟩ := exists_divcurl_scaled_average_kernel_bound_explicit n hn
  have hBound : C≤(divcurlScaledKernelMajorant n:ℝ) :=
    hCEq.trans_le (divcurlScaledAverageConstant_clms_le hn p hp1 hpFormula)
  have hPos : 0<(divcurlScaledKernelMajorant n:ℝ) := hC.trans_le hBound
  refine ⟨p,hpFormula,hp1,hp2,(divcurlScaledKernelMajorant n:ℝ),hPos,rfl,?_⟩
  intro q a r hr Z hZ hDiv w Dw hw κ hκ hcκ hsκ B hB hDκ
  obtain ⟨hI,hEstimate⟩ := H q a r hr Z hZ hDiv w Dw hw κ hκ hcκ hsκ B hB hDκ
  have hAverage (S : Set (Domain n)) (V : Domain n → Gradient n q) :
      0 ≤ ⨍ x in S, (Real.sqrt (hsNormSq (V x))) ^ (p : ℝ) := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hAZ := Real.rpow_nonneg (hAverage (ball a r) Z) (1/(p:ℝ))
  have hAW := Real.rpow_nonneg (hAverage (ball a (2*r)) Dw) (1/(p:ℝ))
  refine ⟨hI,hEstimate.trans ?_⟩
  gcongr

end StationaryHarmonicMaps.Analysis
