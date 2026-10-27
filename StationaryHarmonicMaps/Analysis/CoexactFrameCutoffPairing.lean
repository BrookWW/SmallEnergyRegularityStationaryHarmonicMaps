module

public import StationaryHarmonicMaps.Analysis.CoexactNativeVariationalPairing
public import StationaryHarmonicMaps.Analysis.CoexactFrameProductTest

/-!
# Coexact pairings with the native frame and cutoff

The bounded parent-ball frame and cutoff give their literal Leibniz graph
on each query ball. Natural solenoidal tests annihilate that graph, leaving
the derivative of the frame times the mean-subtracted cutoff.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Bounded native frame coordinates multiply the original L2 columns. -/
theorem memLp_bounded_native_frame_columns {n m q : ℕ} (Ω : OpenDomain n)
    (p : Domain n → Ambient m) (Dp : Domain n → Gradient n m)
    (hp : MemW12 Ω p Dp) (M : ℝ)
    (hpBound : ∀ᵐx∂volume.restrict Ω.val,‖p x‖≤M)
    (L : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (Z : Domain n → Gradient n q)
    (hZ : ∀i,MemLp (fun x=>Z x i) 2 (volume.restrict Ω.val)) :
    ∀i,MemLp (fun x=>L (p x) (Z x i)) 2 (volume.restrict Ω.val) := by
  intro i
  have hA := L.continuous.comp_aestronglyMeasurable hp.2.1.aestronglyMeasurable
  have hMeas := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (hA.prodMk (hZ i).aestronglyMeasurable)
  apply (hZ i).of_le_mul (c:=‖L‖*|M|) hMeas
  filter_upwards [hpBound] with x hx
  calc
    _≤‖L (p x)‖*‖Z x i‖ := (L (p x)).le_opNorm _
    _≤(‖L‖*|M|)*‖Z x i‖ := mul_le_mul_of_nonneg_right
      ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (hx.trans (le_abs_self M)) (norm_nonneg _))) (norm_nonneg _)

/-- The original bounded native parent-ball cutoff and frame have the exact
compensated pairing with every natural solenoidal L2 query-ball field. -/
theorem native_frame_cutoff_solenoidal_pairing_ball {n m q : ℕ}
    (a : Domain n) (R : ℝ) (hR : 0<R)
    (p : Domain n → Ambient m) (Dp : Domain n → Gradient n m)
    (hp : MemW12 (ballDomain a R) p Dp) (M : ℝ)
    (hpBound : ∀ᵐx∂volume.restrict (ball a R),‖p x‖≤M)
    (L : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q)
    (hv : HasZeroBoundaryValues (ballDomain a R) v Dv) (N : ℝ)
    (hvBound : ∀ᵐx∂volume.restrict (ball a R),‖v x‖≤N)
    (b : Domain n) (t : ℝ) (hSub : ball b t⊆ball a R) (c : Ambient q)
    (Q : Domain n → Gradient n q)
    (hQ : ∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball b t)))
    (hNatural : ∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain b t) ψ Dψ →
      (∫x in ball b t,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) :
    (∀i,MemLp (fun x=>L (p x) (Dv x i)) 2 (volume.restrict (ball b t))) ∧
    (∀i,MemLp (fun x=>L (Dp x i) (v x-c)) 2 (volume.restrict (ball b t))) ∧
    IntegrableOn (fun x=>∑i : Fin n,inner ℝ (L (p x) (Dv x i)) (Q x i)) (ball b t) volume ∧
    IntegrableOn (fun x=>∑i : Fin n,inner ℝ (L (Dp x i) (v x-c)) (Q x i)) (ball b t) volume ∧
    (∫x in ball b t,∑i : Fin n,inner ℝ (L (p x) (Dv x i)) (Q x i))=
      -(∫x in ball b t,∑i : Fin n,inner ℝ (L (Dp x i) (v x-c)) (Q x i)) := by
  let μ := volume.restrict (ball b t)
  have hW := native_frame_cutoff_sub_constant_test_ball a R hR p Dp hp M hpBound
    L v Dv hv N hvBound b t hSub c
  have hF (i : Fin n) : MemLp (fun x=>L (p x) (Dv x i)) 2 μ :=
    (memLp_bounded_native_frame_columns (ballDomain a R) p Dp hp M hpBound
      L Dv hv.1.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)
  have hA (i : Fin n) : MemLp (fun x=>L (Dp x i) (v x-c)) 2 μ := by
    have H := (hW.2.2 i).sub (hF i)
    change MemLp (fun x=>(L (Dp x i) (v x-c)+L (p x) (Dv x i))-
      L (p x) (Dv x i)) 2 μ at H
    simpa only [add_sub_cancel_right] using H
  have hFI := integrable_finsetSum Finset.univ (fun i _=>
    HolderToCK.integrable_inner_of_memLp_two (hF i) (hQ i))
  have hAI := integrable_finsetSum Finset.univ (fun i _=>
    HolderToCK.integrable_inner_of_memLp_two (hA i) (hQ i))
  have hZero : (∫x,∑i : Fin n,inner ℝ
      (L (Dp x i) (v x-c)+L (p x) (Dv x i)) (Q x i) ∂μ)=0 := by
    calc
      _=∫x,∑i : Fin n,inner ℝ (Q x i)
          (L (Dp x i) (v x-c)+L (p x) (Dv x i)) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun x=>
          Finset.sum_congr rfl fun i _=>real_inner_comm _ _)
      _=0 := hNatural _ _ hW
  have hSum : (∫x,∑i : Fin n,inner ℝ (L (Dp x i) (v x-c)) (Q x i) ∂μ)+
      (∫x,∑i : Fin n,inner ℝ (L (p x) (Dv x i)) (Q x i) ∂μ)=0 := by
    simpa only [inner_add_left,Finset.sum_add_distrib,integral_add hAI hFI] using hZero
  exact ⟨hF,hA,hFI,hAI,eq_neg_of_add_eq_zero_right hSum⟩

end StationaryHarmonicMaps.Analysis

end
