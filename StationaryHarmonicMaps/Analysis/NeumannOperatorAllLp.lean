/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.NeumannClassHighMoments
public import StationaryHarmonicMaps.Analysis.SelfAdjointMomentDuality

/-!
# One actual Neumann operator with all Lp estimates

A single genuine Neumann L2 projection precedes every original input and
every exponent greater than one. Its same native potential, all natural
Sobolev tests, signed weak equation and coefficient-one L2 energy remain
part of the result. Higher moments and self-adjoint duality supply all Lp
moments of that same original operator output.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- One actual Neumann projection and its original native response have every
Lp moment estimate, with dimension/exponent constants uniform in the target. -/
theorem exists_same_neumann_operator_all_lp_unitBall (n : ℕ) (hn : 2≤n) :
    ∃ Cp : {p : ℝ //1<p} → ℝ,(∀p,0<Cp p) ∧ ∀q : ℕ,
      let μ := volume.restrict (ball (0:Domain n) 1)
      let D := fun (P : Domain n → Ambient (n*q)) x i=>WithLp.toLp 2
        (fun j : Fin q=>P x (finProdFinEquiv (i,j)))
      ∃T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
        ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀V,T (T V)=T V) ∧
        ∀W : Lp (Ambient (n*q)) 2 μ,∃u : Domain n → Ambient q,
          MemW12 (ballDomain (0:Domain n) 1) u (D (T W)) ∧
          (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (D (T W) x i) (Dψ x i)) μ ∧
            Integrable (fun x=>∑i : Fin n,inner ℝ (D W x i) (Dψ x i)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (D (T W) x i) (Dψ x i) ∂μ)=
              ∫x,∑i : Fin n,inner ℝ (D W x i) (Dψ x i) ∂μ) ∧
          HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1)
            (fun x i=>D (T W) x i-D W x i) (fun _=>0) ∧
          (∫x,hsNormSq (D (T W) x) ∂μ)≤∫x,hsNormSq (D W x) ∂μ ∧
          ∀p : {p : ℝ //1<p},MemLp (fun x=>W x) (ENNReal.ofReal p.val) μ →
            MemLp (fun x=>(T W) x) (ENNReal.ofReal p.val) μ ∧
            (∫x,‖(T W) x‖^p.val ∂μ)≤Cp p*(∫x,‖W x‖^p.val ∂μ) := by
  classical
  obtain ⟨Ch,hCh,HT⟩ := exists_neumann_class_all_high_moments_unitBall n hn
  have hConj (p : {p : ℝ //1<p}) (hp : p.val<2) : 2<p.val/(p.val-1) := by
    apply (lt_div_iff₀ (by linarith [p.property] : 0<p.val-1)).mpr
    linarith only [hp]
  let Cp : {p : ℝ //1<p} → ℝ := fun p=>
    if hp : p.val<2 then (Ch ⟨p.val/(p.val-1),hConj p hp⟩)^(p.val-1)
    else if hpEq : p.val=2 then 1 else Ch ⟨p.val,lt_of_le_of_ne (not_lt.mp hp) (Ne.symm hpEq)⟩
  have hCp (p : {p : ℝ //1<p}) : 0<Cp p := by
    dsimp only [Cp]
    split_ifs with hp hpEq
    · exact Real.rpow_pos_of_pos (hCh _) _
    · norm_num
    · exact hCh _
  refine ⟨Cp,hCp,?_⟩
  intro q μ D
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  obtain ⟨T,hT,hSelf,hIdem,Hresponse⟩ := HT q
  have hHigh (r : {r : ℝ //2<r}) (W : Lp (Ambient (n*q)) 2 μ)
      (hW : MemLp (fun x=>W x) (ENNReal.ofReal r.val) μ) :
      MemLp (fun x=>(T W) x) (ENNReal.ofReal r.val) μ ∧
        (∫x,‖(T W) x‖^r.val ∂μ)≤Ch r*(∫x,‖W x‖^r.val ∂μ) := by
    obtain ⟨_u,_hu,_hNat,_hEq,H⟩ := Hresponse W
    exact H r hW
  have hNorm (W : Lp (Ambient (n*q)) 2 μ) : ‖W‖^2=∫x,‖W x‖^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    exact integral_congr_ae (Eventually.of_forall fun x=>real_inner_self_eq_norm_sq (W x))
  have hTwo (W : Lp (Ambient (n*q)) 2 μ) :
      (∫x,‖(T W) x‖^2 ∂μ)≤∫x,‖W x‖^2 ∂μ := by
    rw [← hNorm (T W),← hNorm W]
    have hNW : ‖T W‖≤‖W‖ := (T.le_opNorm W).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hT (norm_nonneg W))
    exact pow_le_pow_left₀ (norm_nonneg _) hNW 2
  refine ⟨T,hT,hSelf,hIdem,?_⟩
  intro W
  obtain ⟨u,hu,hNat,hEq,_hHighW⟩ := Hresponse W
  have hEnergy : (∫x,hsNormSq (D (T W) x) ∂μ)≤∫x,hsNormSq (D W x) ∂μ := by
    simpa only [D,hs_unflatten_hsNormSq] using hTwo W
  refine ⟨u,hu,hNat,hEq,hEnergy,?_⟩
  intro p hW
  by_cases hpLow : p.val<2
  · have hLow := selfAdjoint_low_moment_bound_of_high_moment μ p.val p.property hpLow
      (Ch ⟨p.val/(p.val-1),hConj p hpLow⟩) (hCh _).le T hSelf
      (hHigh ⟨p.val/(p.val-1),hConj p hpLow⟩) W
    simpa only [Cp,dif_pos hpLow] using hLow
  · by_cases hpEq : p.val=2
    · refine ⟨?_,?_⟩
      · simpa only [hpEq,ENNReal.ofReal_ofNat] using Lp.memLp (T W)
      · simpa [Cp,hpLow,hpEq,Real.rpow_two] using hTwo W
    · have hpHigh : 2<p.val := lt_of_le_of_ne (not_lt.mp hpLow) (Ne.symm hpEq)
      simpa only [Cp,dif_neg hpLow,dif_neg hpEq] using hHigh ⟨p.val,hpHigh⟩ W hW

end StationaryHarmonicMaps.Analysis

end
