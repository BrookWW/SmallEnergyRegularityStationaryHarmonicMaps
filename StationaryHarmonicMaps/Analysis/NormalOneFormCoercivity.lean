module

public import StationaryHarmonicMaps.Analysis.NormalOneFormMean
public import HarmonicMaps.Analysis.SobolevPoincare

/-!
# Actual coefficient coercivity for normal one-forms

The original coefficient means are controlled by their actual divergence.
The native ball Poincare inequality then controls their full L2 norm
without imposing any additional mean normalization or coefficient trace.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Normal contraction, actual coefficient means and native ball Poincare control the same original one-form map energy. -/
theorem smooth_normal_oneForm_coefficient_bound {n q : ℕ}
    (A : Fin n → Domain n → Ambient q) (hA : ∀ i, ContDiff ℝ ∞ (A i))
    (hNormal : ∀ y : Domain n, ‖y‖=1 → (∑ i : Fin n,y i • A i y)=0) :
    let e := fun x : Domain n=>∑ i : Fin n,‖A i x‖^2
    let g := fun x : Domain n=>∑ k : Fin n,∑ i : Fin n,
      ‖fderiv ℝ (A i) x (EuclideanSpace.single k 1)‖^2
    let d := fun x : Domain n=>‖∑ i : Fin n,fderiv ℝ (A i) x (EuclideanSpace.single i 1)‖^2
    IntegrableOn e (ball (0 : Domain n) 1) volume ∧
      IntegrableOn g (ball (0 : Domain n) 1) volume ∧
      IntegrableOn d (ball (0 : Domain n) 1) volume ∧
      (∫ x in ball (0 : Domain n) 1,e x) ≤
        (2*(2:ℝ)^(n+1))*(∫ x in ball (0 : Domain n) 1,g x) +
          (2*(n:ℝ))*(∫ x in ball (0 : Domain n) 1,d x) := by
  intro e g d
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let Cp : ℝ := (2:ℝ)^(n+1)
  let m := volume.real (ball (0 : Domain n) 1)
  let a := fun i : Fin n=>⨍ x in ball (0 : Domain n) 1,A i x
  let G := fun (i : Fin n) (x : Domain n)=>hsNormSq
    (fun k : Fin n=>fderiv ℝ (A i) x (EuclideanSpace.single k 1))
  have hW (i : Fin n) := memW12_ball_of_ambient_c1 (0 : Domain n) 1 (A i) ((hA i).of_le (by simp))
  have hAI (i : Fin n) : MemLp (A i) 2 μ := (hW i).2.1
  have heI (i : Fin n) : Integrable (fun x=>‖A i x‖^2) μ :=
    (hW i).2.1.integrable_norm_pow (by decide : (2:ℕ)≠0)
  have hGI (i : Fin n) : Integrable (G i) μ :=
    integrable_finsetSum _ (fun k _=>(hW i).2.2 k |>.integrable_norm_pow (by decide : (2:ℕ)≠0))
  have hGsum (x : Domain n) : (∑ i : Fin n,G i x)=g x := by
    dsimp only [G,hsNormSq,g]
    exact Finset.sum_comm
  have heInt : Integrable e μ := integrable_finsetSum _ (fun i _=>heI i)
  have hgInt : Integrable g μ :=
    (integrable_finsetSum _ (fun i _=>hGI i)).congr (Eventually.of_forall hGsum)
  have hDiv : ContDiff ℝ ∞ (fun x : Domain n=>∑ i : Fin n,
      fderiv ℝ (A i) x (EuclideanSpace.single i 1)) := ContDiff.sum (fun i _=>
    ((hA i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hdInt : Integrable d μ :=
    (memW12_ball_of_ambient_c1 (0 : Domain n) 1 _ (hDiv.of_le (by simp))).2.1.integrable_norm_pow
      (by decide : (2:ℕ)≠0)
  have hcoeff (i : Fin n) : (∫ x,‖A i x‖^2 ∂μ) ≤
      (2*Cp)*(∫ x,G i x ∂μ)+2*(∫ x,d x ∂μ) := by
    have hsubLp : MemLp (fun x=>A i x-a i) 2 μ := (hAI i).sub (memLp_const _)
    have hsubI : Integrable (fun x=>‖A i x-a i‖^2) μ := hsubLp.integrable_norm_pow (by decide : (2:ℕ)≠0)
    have hConstI : Integrable (fun _x : Domain n=>2*‖a i‖^2) μ := integrable_const _
    have hpoint (x : Domain n) : ‖A i x‖^2 ≤ 2*‖A i x-a i‖^2+2*‖a i‖^2 := by
      have ht : ‖A i x‖≤‖A i x-a i‖+‖a i‖ := by
        simpa only [sub_add_cancel] using norm_add_le (A i x-a i) (a i)
      nlinarith only [ht,norm_nonneg (A i x),norm_nonneg (A i x-a i),norm_nonneg (a i),
        sq_nonneg (‖A i x-a i‖-‖a i‖)]
    have hp : (∫ x,‖A i x-a i‖^2 ∂μ) ≤ Cp*(∫ x,G i x ∂μ) := by
      simpa only [one_pow,mul_one] using (hW i).poincare_ball (by norm_num : (0:ℝ)<1)
    have hm : m*‖a i‖^2 ≤ ∫ x,d x ∂μ :=
      (smooth_normal_oneForm_mean_square_bound A hA hNormal i).2
    calc
      _ ≤ ∫ x,(2*‖A i x-a i‖^2+2*‖a i‖^2) ∂μ :=
        integral_mono (heI i) ((hsubI.const_mul 2).add hConstI) hpoint
      _ = 2*(∫ x,‖A i x-a i‖^2 ∂μ)+2*(m*‖a i‖^2) := by
        rw [integral_add (hsubI.const_mul 2) hConstI,integral_const_mul,integral_const]
        simp only [Measure.restrict_apply_univ,measureReal_def,μ,m,smul_eq_mul]
        ring
      _ ≤ 2*(Cp*(∫ x,G i x ∂μ))+2*(∫ x,d x ∂μ) :=
        add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num))
          (mul_le_mul_of_nonneg_left hm (by norm_num))
      _ = _ := by ring
  have hsum : (∑ i : Fin n,∫ x,‖A i x‖^2 ∂μ) ≤
      (2*Cp)*(∑ i : Fin n,∫ x,G i x ∂μ)+(2*(n:ℝ))*(∫ x,d x ∂μ) := by
    have H := Finset.sum_le_sum (s := Finset.univ) (fun i _=>hcoeff i)
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at H
    nlinarith only [H]
  have heEq : (∑ i : Fin n,∫ x,‖A i x‖^2 ∂μ)=∫ x,e x ∂μ :=
    (integral_finsetSum _ (fun i _=>heI i)).symm
  have hgEq : (∑ i : Fin n,∫ x,G i x ∂μ)=∫ x,g x ∂μ := by
    rw [← integral_finsetSum _ (fun i _=>hGI i)]
    exact integral_congr_ae (Eventually.of_forall hGsum)
  rw [heEq,hgEq] at hsum
  exact ⟨heInt,hgInt,hdInt,hsum⟩

end StationaryHarmonicMaps.Analysis

end
