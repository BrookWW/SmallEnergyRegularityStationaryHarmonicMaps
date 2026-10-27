module

public import StationaryHarmonicMaps.Analysis.SobolevStrongCompleteness
public import HarmonicMaps.Energy
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Actual strong native limits from quadratic energy control

A genuine pairwise map-and-gradient energy estimate transfers the actual
L2 Cauchy property of a finite control family to the original native
Sobolev maps and every displayed weak column.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

private theorem integral_norm_sq_toLp_norm_sq {n q : ℕ} {μ : Measure (Domain n)}
    {f : Domain n → Ambient q} (hf : MemLp f 2 μ) :
    (∫ x,‖f x‖^2 ∂μ)=‖hf.toLp f‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simpa only [real_inner_self_eq_norm_sq] using HolderToCK.integral_inner_eq_L2_inner hf hf

private theorem integral_diff_norm_sq_eq {n q : ℕ} {μ : Measure (Domain n)}
    (f g : Domain n → Ambient q) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x,‖f x-g x‖^2 ∂μ)=‖hf.toLp f-hg.toLp g‖^2 := by
  have H := integral_norm_sq_toLp_norm_sq (hf.sub hg)
  rw [MemLp.toLp_sub] at H
  simpa only [Pi.sub_apply] using H

private theorem cauchySeq_of_sq_norm_control {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (t : ℕ × ℕ → ℝ)
    (ht : Tendsto t atTop (𝓝 0))
    (hb : ∀ p : ℕ × ℕ,‖f p.1-f p.2‖^2 ≤ t p) : CauchySeq f := by
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  have hs : Tendsto (fun p : ℕ × ℕ=>‖f p.1-f p.2‖^2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _=>sq_nonneg _) hb
  have H := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero,dist_eq_norm] using H

/-- Actual pairwise quadratic energy control by a genuine finite L2 Cauchy family produces the native strong Sobolev limit. -/
theorem exists_native_strong_limit_of_quadratic_control {n q m k : ℕ} (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (hNative : ∀ s,MemW12 Ω (u s) (Du s))
    (W : ℕ → Domain n → Fin m → Ambient k)
    (hW : ∀ s a,MemLp (fun x=>W s x a) 2 (volume.restrict Ω.val))
    (hWCauchy : ∀ a : Fin m,CauchySeq (fun s=>(hW s a).toLp (fun x=>W s x a)))
    (C : ℝ)
    (hControl : ∀ s t : ℕ,
      (∫ x,‖u s x-u t x‖^2 ∂volume.restrict Ω.val) +
        (∫ x,hsNormSq (fun i=>Du s x i-Du t x i) ∂volume.restrict Ω.val) ≤
          C*(∑ a : Fin m,∫ x,‖W s x a-W t x a‖^2 ∂volume.restrict Ω.val)) :
    ∃ (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
      MemW12 Ω v Dv ∧
      Tendsto (fun s=>eLpNorm (fun x=>u s x-v x) 2 (volume.restrict Ω.val)) atTop (𝓝 0) ∧
      ∀ i : Fin n,Tendsto (fun s=>eLpNorm (fun x=>Du s x i-Dv x i) 2
        (volume.restrict Ω.val)) atTop (𝓝 0) := by
  let μ := volume.restrict Ω.val
  let Z := fun (s : ℕ) (a : Fin m)=>(hW s a).toLp (fun x=>W s x a)
  let T := fun p : ℕ × ℕ=>C*(∑ a : Fin m,‖Z p.1 a-Z p.2 a‖^2)
  have hZ (a : Fin m) : Tendsto (fun p : ℕ × ℕ=>‖Z p.1 a-Z p.2 a‖^2) atTop (𝓝 0) := by
    have H := (cauchySeq_iff_tendsto_dist_atTop_0.mp (hWCauchy a)).pow 2
    simpa only [dist_eq_norm,zero_pow (by decide : (2:ℕ)≠0)] using H
  have hT : Tendsto T atTop (𝓝 0) := by
    have H := (tendsto_finsetSum Finset.univ (fun a _=>hZ a)).const_mul C
    simpa only [Finset.sum_const_zero,mul_zero] using H
  have hWEq (s t : ℕ) : (∑ a : Fin m,∫ x,‖W s x a-W t x a‖^2 ∂μ)=
      ∑ a : Fin m,‖Z s a-Z t a‖^2 := by
    apply Finset.sum_congr rfl
    intro a _
    exact integral_diff_norm_sq_eq _ _ (hW s a) (hW t a)
  have hMap (p : ℕ × ℕ) :
      ‖(hNative p.1).2.1.toLp (u p.1)-(hNative p.2).2.1.toLp (u p.2)‖^2 ≤ T p := by
    have hEq : ‖(hNative p.1).2.1.toLp (u p.1)-(hNative p.2).2.1.toLp (u p.2)‖^2 =
        ∫ x,‖u p.1 x-u p.2 x‖^2 ∂μ := by
      symm
      exact integral_diff_norm_sq_eq _ _ (hNative p.1).2.1 (hNative p.2).2.1
    calc
      _ = _ := hEq
      _ ≤ (∫ x,‖u p.1 x-u p.2 x‖^2 ∂μ)+
          ∫ x,hsNormSq (fun i=>Du p.1 x i-Du p.2 x i) ∂μ :=
        le_add_of_nonneg_right (integral_nonneg fun x=>Finset.sum_nonneg (fun i _=>sq_nonneg ‖Du p.1 x i-Du p.2 x i‖))
      _ ≤ C*(∑ a : Fin m,∫ x,‖W p.1 x a-W p.2 x a‖^2 ∂μ) := hControl p.1 p.2
      _ = _ := by rw [hWEq]
  have hCol (i : Fin n) (p : ℕ × ℕ) :
      ‖((hNative p.1).2.2 i).toLp (fun x=>Du p.1 x i)-
        ((hNative p.2).2.2 i).toLp (fun x=>Du p.2 x i)‖^2 ≤ T p := by
    have hI : Integrable (fun x=>hsNormSq (fun j=>Du p.1 x j-Du p.2 x j)) μ :=
      integrable_finsetSum _ (fun j _=>((hNative p.1).2.2 j |>.sub ((hNative p.2).2.2 j)).integrable_norm_pow
        (by decide : (2:ℕ)≠0))
    have hJ : Integrable (fun x=>‖Du p.1 x i-Du p.2 x i‖^2) μ :=
      ((hNative p.1).2.2 i |>.sub ((hNative p.2).2.2 i)).integrable_norm_pow (by decide : (2:ℕ)≠0)
    have hEq : ‖((hNative p.1).2.2 i).toLp (fun x=>Du p.1 x i)-
        ((hNative p.2).2.2 i).toLp (fun x=>Du p.2 x i)‖^2 =
          ∫ x,‖Du p.1 x i-Du p.2 x i‖^2 ∂μ := by
      symm
      exact integral_diff_norm_sq_eq _ _ ((hNative p.1).2.2 i) ((hNative p.2).2.2 i)
    calc
      _ = _ := hEq
      _ ≤ ∫ x,hsNormSq (fun j=>Du p.1 x j-Du p.2 x j) ∂μ := integral_mono hJ hI (fun x=>
        Finset.single_le_sum (fun j _=>sq_nonneg ‖Du p.1 x j-Du p.2 x j‖) (Finset.mem_univ i))
      _ ≤ (∫ x,‖u p.1 x-u p.2 x‖^2 ∂μ)+
          ∫ x,hsNormSq (fun j=>Du p.1 x j-Du p.2 x j) ∂μ :=
        le_add_of_nonneg_left (integral_nonneg fun x=>sq_nonneg _)
      _ ≤ C*(∑ a : Fin m,∫ x,‖W p.1 x a-W p.2 x a‖^2 ∂μ) := hControl p.1 p.2
      _ = _ := by rw [hWEq]
  exact exists_native_strong_limit_of_L2_cauchy Ω u Du hNative
    (cauchySeq_of_sq_norm_control _ T hT hMap)
    (fun i=>cauchySeq_of_sq_norm_control _ T hT (hCol i))

end StationaryHarmonicMaps.Analysis

end
