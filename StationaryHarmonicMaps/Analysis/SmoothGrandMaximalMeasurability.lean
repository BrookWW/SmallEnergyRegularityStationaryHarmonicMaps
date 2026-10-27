module

public import StationaryHarmonicMaps.Analysis.DivCurlHardyMajorant
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Lower semicontinuity of the literal smooth grand kernel supremum

Compact support inside an open ball supplies a strict uniform margin.
The derivative bound is global because the kernel vanishes off its
support. An admissible kernel therefore remains admissible at every
sufficiently close center. Every strict superlevel of the actual grand
supremum is open, including its infinite values.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The actual supremum over all smooth compact normalized kernels is lower semicontinuous and measurable, without any integrability hypothesis on the supplied scalar field. -/
theorem lowerSemicontinuous_measurable_smooth_grand_kernel {n : ℕ} (f : Domain n → ℝ) :
    let J := fun a => ⨆ r : PositiveRadius, ⨆ κ : Domain n → ℝ,
      ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
      ⨆ (_ : tsupport κ⊆Metric.ball a r.val),
      ⨆ (_ : ∀ x∈Metric.ball a r.val,∀ i : Fin n,
        |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤r.val^(-(n : ℝ)-1)),
        ENNReal.ofReal |∫ x,κ x*f x|
    LowerSemicontinuous J ∧ Measurable J := by
  intro J
  have hLS : LowerSemicontinuous J := by
    intro a t ht
    obtain ⟨r,ht⟩ := lt_iSup_iff.mp ht
    obtain ⟨κ,ht⟩ := lt_iSup_iff.mp ht
    obtain ⟨hκ,ht⟩ := lt_iSup_iff.mp ht
    obtain ⟨hcκ,ht⟩ := lt_iSup_iff.mp ht
    obtain ⟨hsκ,ht⟩ := lt_iSup_iff.mp ht
    obtain ⟨hDκ,ht⟩ := lt_iSup_iff.mp ht
    have hGlobal (x : Domain n) (i : Fin n) :
        |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤r.val^(-(n : ℝ)-1) := by
      by_cases hx : x∈Metric.ball a r.val
      · exact hDκ x hx i
      · rw [fderiv_of_notMem_tsupport ℝ (fun H=>hx (hsκ H)),zero_apply,abs_zero]
        exact Real.rpow_nonneg r.property.le _
    obtain ⟨s,hs,hsSupp⟩ := exists_pos_lt_subset_ball r.property (isClosed_tsupport κ) hsκ
    filter_upwards [Metric.ball_mem_nhds a (sub_pos.mpr hs.2)] with b hb
    have hNew : tsupport κ⊆Metric.ball b r.val := by
      intro x hx
      have hxa : dist x a<s := hsSupp hx
      have hab : dist a b<r.val-s := by simpa only [Metric.mem_ball,dist_comm] using hb
      change dist x b<r.val
      calc
        _ ≤ dist x a+dist a b := dist_triangle _ _ _
        _ < s+(r.val-s) := add_lt_add hxa hab
        _ = r.val := by ring
    exact ht.trans_le (le_iSup_of_le r (le_iSup_of_le κ (le_iSup_of_le hκ
      (le_iSup_of_le hcκ (le_iSup_of_le hNew (le_iSup_of_le (fun x _hx i=>hGlobal x i) le_rfl))))))
  exact ⟨hLS,hLS.measurable⟩

/-- The original rough div--curl data produce the same literal measurable grand maximal field with a genuine finite bilinear L1 estimate. -/
theorem exists_divcurl_measurable_grand_kernel_bound_explicit (n : ℕ) (hn : 2≤n) :
    ∃ K : ℝ,0<K ∧ K=(divcurlGrandKernelMajorant n:ℝ) ∧ ∀ (q : ℕ) (Z : Domain n → Gradient n q),
      (∀ i,MemLp (fun x=>Z x i) 2 volume) →
      HolderToCK.WeakPoissonOn (⟨univ,isOpen_univ⟩ : OpenDomain n) Z (fun _=>(0 : Ambient q)) →
      ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
        MemW12Loc (⟨univ,isOpen_univ⟩ : OpenDomain n) w Dw →
        (∀ i,MemLp (fun x=>Dw x i) 2 volume) →
        let J := fun a => ⨆ r : PositiveRadius, ⨆ κ : Domain n → ℝ,
          ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
          ⨆ (_ : tsupport κ⊆Metric.ball a r.val),
          ⨆ (_ : ∀ x∈Metric.ball a r.val,∀ i : Fin n,
            |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤r.val^(-(n : ℝ)-1)),
            ENNReal.ofReal |∫ x,κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i)|
        LowerSemicontinuous J ∧ Measurable J ∧
          (∫⁻ a,J a)≤ENNReal.ofReal K *
            (ENNReal.ofReal (∫ x,hsNormSq (Z x)))^((1 : ℝ)/2) *
            (ENNReal.ofReal (∫ x,hsNormSq (Dw x)))^((1 : ℝ)/2) ∧
          (∫⁻ a,J a)<(∞ : ℝ≥0∞) ∧ (∀ᵐ a ∂volume,J a≠(∞ : ℝ≥0∞)) := by
  obtain ⟨K,hK,hKEq,H⟩ := exists_divcurl_grand_kernel_lintegral_bound_explicit n hn
  refine ⟨K,hK,hKEq,?_⟩
  intro q Z hZ hdiv w Dw hw hDw J
  obtain ⟨hBound,hI⟩ := H q Z hZ hdiv w Dw hw hDw
  obtain ⟨hLS,hMeas⟩ := lowerSemicontinuous_measurable_smooth_grand_kernel
    (fun x=>∑ i : Fin n,inner ℝ (Z x i) (Dw x i))
  exact ⟨hLS,hMeas,hBound,hI,(ae_lt_top' hMeas.aemeasurable hI.ne).mono (fun _ hx=>hx.ne)⟩

theorem exists_divcurl_measurable_grand_kernel_bound (n : ℕ) (hn : 2≤n) :
    ∃ K : ℝ,0<K ∧ ∀ (q : ℕ) (Z : Domain n → Gradient n q),
      (∀ i,MemLp (fun x=>Z x i) 2 volume) →
      HolderToCK.WeakPoissonOn (⟨univ,isOpen_univ⟩ : OpenDomain n) Z (fun _=>(0 : Ambient q)) →
      ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
        MemW12Loc (⟨univ,isOpen_univ⟩ : OpenDomain n) w Dw →
        (∀ i,MemLp (fun x=>Dw x i) 2 volume) →
        let J := fun a => ⨆ r : PositiveRadius, ⨆ κ : Domain n → ℝ,
          ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
          ⨆ (_ : tsupport κ⊆Metric.ball a r.val),
          ⨆ (_ : ∀ x∈Metric.ball a r.val,∀ i : Fin n,
            |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤r.val^(-(n : ℝ)-1)),
            ENNReal.ofReal |∫ x,κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i)|
        LowerSemicontinuous J ∧ Measurable J ∧
          (∫⁻ a,J a)≤ENNReal.ofReal K *
            (ENNReal.ofReal (∫ x,hsNormSq (Z x)))^((1 : ℝ)/2) *
            (ENNReal.ofReal (∫ x,hsNormSq (Dw x)))^((1 : ℝ)/2) ∧
          (∫⁻ a,J a)<(∞ : ℝ≥0∞) ∧ (∀ᵐ a ∂volume,J a≠(∞ : ℝ≥0∞)) := by
  obtain ⟨K,hK,_hKEq,H⟩ := exists_divcurl_measurable_grand_kernel_bound_explicit n hn
  exact ⟨K,hK,H⟩

end StationaryHarmonicMaps.Analysis

end
