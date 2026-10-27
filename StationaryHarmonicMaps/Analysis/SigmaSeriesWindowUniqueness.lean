module

public import StationaryHarmonicMaps.Analysis.AbsolutelyIntegrableSeries
public import Mathlib.Order.Filter.AtTopBot.Interval

/-!
# Actual full-series identification from original two-sided L1 windows

The original finite absolute integral series produces genuine AE
absolute convergence of the full sigma-indexed series. Its actual
symmetric integer windows converge to that same series in L1 by a real
integrable norm dominator. Their original L1 convergence to the supplied
function then gives actual AE equality by uniqueness.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original absolutely integrable sigma series and genuine two-sided window convergence identify the supplied original function with the same actual full series almost everywhere. -/
theorem ae_eq_sigma_series_of_strong_L1_windows {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (I : ℤ → Type*) [∀ j,Countable (I j)]
    (F : (j : ℤ) → I j → X → ℝ) (hF : ∀ j i,Integrable (F j i) μ)
    (hNorm : (∑' p : Σ j,I j,∫⁻ x,ENNReal.ofReal |F p.1 p.2 x| ∂μ)<∞)
    (f : X → ℝ) (hf : Integrable f μ)
    (hWindow : ∀ N : ℕ,Integrable (fun x=>∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),∑' i,F j i x) μ)
    (hApprox : Tendsto (fun N : ℕ=>∫ x,|f x-∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),∑' i,F j i x| ∂μ)
      atTop (𝓝 (0 : ℝ))) :
    f=ᵐ[μ](fun x=>∑' p : Σ j,I j,F p.1 p.2 x) := by
  classical
  let V := fun (p : Σ j,I j) (x : X)=>F p.1 p.2 x
  let T := fun x=>∑' p : Σ j,I j,V p x
  let R := fun x=>∑' p : Σ j,I j,|V p x|
  let W := fun (N : ℕ) (x : X)=>∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),∑' i,F j i x
  obtain ⟨hAE,hRI,hTI,_hIntegral⟩ := integrable_tsum_of_finite_lintegral_abs_sum μ V
    (fun p=>hF p.1 p.2) hNorm
  have hPoint : ∀ᵐ x ∂μ,Tendsto (fun N : ℕ=>W N x) atTop (𝓝 (T x)) := by
    filter_upwards [hAE] with x hx
    have H := hx.2.sigma.hasSum
    change Tendsto (fun s : Finset ℤ=>∑ j∈s,∑' i,F j i x) atTop (𝓝 (∑' j,∑' i,F j i x)) at H
    have HN := H.comp (Finset.tendsto_Icc_neg (R := ℤ))
    rw [← hx.2.tsum_sigma] at HN
    exact HN
  have hBounds : ∀ᵐ x ∂μ,(∀ N : ℕ,|W N x|≤R x) ∧ |T x|≤R x := by
    filter_upwards [hAE] with x hx
    have hAbs : Summable (fun p : Σ j,I j=>|V p x|) := hx.1
    have hFibre (j : ℤ) : Summable (fun i : I j=>|F j i x|) := hAbs.comp_injective (i := fun i : I j=>Sigma.mk j i)
      (by intro a b hab;exact eq_of_heq (Sigma.mk.inj hab).2)
    have hGroupNonneg (j : ℤ) : 0≤∑' i : I j,|F j i x| := tsum_nonneg (fun _=>abs_nonneg _)
    have hGroupBound (j : ℤ) : |∑' i : I j,F j i x|≤∑' i : I j,|F j i x| := by
      have H := norm_tsum_le_tsum_norm (show Summable (fun i : I j=>‖F j i x‖) from by simpa only [Real.norm_eq_abs] using hFibre j)
      simpa only [Real.norm_eq_abs] using H
    constructor
    · intro N
      have H1 : |W N x|≤∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),|∑' i : I j,F j i x| := by
        simpa only [Real.norm_eq_abs] using norm_sum_le (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun j=>∑' i : I j,F j i x)
      have H2 := Finset.sum_le_sum (fun j (_hj : j∈Finset.Icc (-(N : ℤ)) (N : ℤ))=>hGroupBound j)
      have H3 := hAbs.sigma.sum_le_tsum (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun j _=>hGroupNonneg j)
      exact H1.trans (H2.trans (H3.trans_eq hAbs.tsum_sigma.symm))
    · have H := norm_tsum_le_tsum_norm (show Summable (fun p : Σ j,I j=>‖V p x‖) from by simpa only [Real.norm_eq_abs] using hx.1)
      simpa only [Real.norm_eq_abs] using H
  have hErrorBound (N : ℕ) : ∀ᵐ x ∂μ,‖|W N x-T x|‖≤2*R x := by
    filter_upwards [hBounds] with x hx
    rw [Real.norm_eq_abs,abs_abs]
    exact (abs_sub _ _).trans ((add_le_add (hx.1 N) hx.2).trans_eq (by ring))
  have hErrorPoint : ∀ᵐ x ∂μ,Tendsto (fun N : ℕ=>|W N x-T x|) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hPoint] with x hx
    simpa only [sub_self,abs_zero] using (hx.sub_const (T x)).abs
  have hToSeries : Tendsto (fun N : ℕ=>∫ x,|W N x-T x| ∂μ) atTop (𝓝 (0 : ℝ)) := by
    have H := tendsto_integral_of_dominated_convergence (fun x=>2*R x)
      (fun N=>((hWindow N).sub hTI).abs.aestronglyMeasurable) (hRI.const_mul 2) hErrorBound hErrorPoint
    simpa only [integral_zero,Pi.sub_apply,W,T] using H
  have hNormBound (N : ℕ) : (∫ x,|f x-T x| ∂μ)≤(∫ x,|f x-W N x| ∂μ)+(∫ x,|W N x-T x| ∂μ) := by
    calc
      _ ≤ ∫ x,|f x-W N x|+|W N x-T x| ∂μ := integral_mono (hf.sub hTI).abs
        (((hf.sub (hWindow N)).abs).add ((hWindow N).sub hTI).abs) (fun x=>by
          change |f x-T x|≤_
          have H := abs_add_le (f x-W N x) (W N x-T x)
          have hAlg : f x-T x=(f x-W N x)+(W N x-T x) := by ring
          rw [hAlg]
          exact H)
      _ = _ := integral_add (hf.sub (hWindow N)).abs ((hWindow N).sub hTI).abs
  have hZero : (∫ x,|f x-T x| ∂μ)=0 := le_antisymm
    (ge_of_tendsto (by simpa only [zero_add] using hApprox.add hToSeries) (Eventually.of_forall hNormBound))
    (integral_nonneg fun _=>abs_nonneg _)
  have hAEZero := (integral_eq_zero_iff_of_nonneg (fun x=>abs_nonneg (f x-T x)) (hf.sub hTI).abs).mp hZero
  filter_upwards [hAEZero] with x hx
  exact sub_eq_zero.mp (abs_eq_zero.mp hx)

end StationaryHarmonicMaps.Analysis

end
