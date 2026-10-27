module

public import StationaryHarmonicMaps.Analysis.LocalDivCurlHardy
public import StationaryHarmonicMaps.Analysis.HardyMeanOscillationPairing

/-!
# Actual local continuous div--curl pairing

The original ball-solenoidal field and original native zero-boundary
graph produce the true grand-integrable contraction through the proved
Kelvin and zero extensions. Its actual Hardy pairing gives a unique
limit of the original ball integrals, with the original bilinear energy
bound. No extension, atomic family or Hardy duality is a premise.
-/

@[expose] public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

def effectiveLocalDivcurlPairingConstant (n : ℕ) : ℚ :=
  2*rationalHardyPairingConstant n*(divcurlGrandKernelMajorant n:ℚ)

/-- Original solenoidal L2/W0 data and original global mean oscillation produce the unique continuous local div--curl pairing and its actual energy bound. -/
theorem existsUnique_local_divcurl_continuous_pairing_explicit (n : ℕ) (hn : 2≤n) :
    ∃ C : ℝ,0<C ∧ C=(effectiveLocalDivcurlPairingConstant n:ℝ) ∧ ∀ (q : ℕ) (a : Domain n) (r : ℝ),0<r →
      ∀ (Z : Domain n → Gradient n q),
        (∀ i,MemLp (fun x=>Z x i) 2 (volume.restrict (Metric.ball a r))) →
        HolderToCK.WeakPoissonOn (ballDomain a r) Z (fun _=>(0 : Ambient q)) →
        ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
          HasZeroBoundaryValues (ballDomain a r) w Dw →
          ∀ (b : Domain n → ℝ) (B : ℝ),AEStronglyMeasurable b volume → 0≤B →
            (∀ (x : Domain n) (s : ℝ),0<s → IntegrableOn b (Metric.ball x s) volume ∧
              (⨍ y in Metric.ball x s,|b y-(⨍ z in Metric.ball x s,b z)|)≤B) →
            let F := fun x=>∑ i : Fin n,inner ℝ (Z x i) (Dw x i)
            ∃! l : ℝ,
              (∀ k : ℕ,IntegrableOn (fun x=>F x*min (k : ℝ) (max (-(k : ℝ)) (b x)))
                (Metric.ball a r) volume) ∧
              Tendsto (fun k : ℕ=>∫ x in Metric.ball a r,F x*min (k : ℝ) (max (-(k : ℝ)) (b x)))
                atTop (𝓝 l) ∧
              |l|≤C*B*Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Z x))*
                Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Dw x)) ∧
              (IntegrableOn (fun x=>F x*b x) (Metric.ball a r) volume →
                l=(∫ x in Metric.ball a r,F x*b x)) := by
  classical
  obtain ⟨K,hK,hKEq,Hhardy⟩ := exists_local_divcurl_measurable_grand_kernel_bound_explicit n hn
  obtain ⟨D,hD,hDEq,Hpair⟩ := existsUnique_continuous_pairing_of_finite_smooth_grand_kernel_explicit n (by omega)
  let C : ℝ := (effectiveLocalDivcurlPairingConstant n:ℝ)
  have hNumeric : D*K*Real.sqrt 2≤C := by
    have hRoot : Real.sqrt 2≤2 := by norm_num
    calc
      _≤D*K*2 := mul_le_mul_of_nonneg_left hRoot (mul_nonneg hD.le hK.le)
      _=C := by
        rw [hDEq,←rationalHardyPairingConstant_cast,hKEq]
        dsimp only [C,effectiveLocalDivcurlPairingConstant]
        push_cast
        ring
  have hC : 0<C := (mul_pos (mul_pos hD hK) (Real.sqrt_pos.mpr (by norm_num))).trans_le hNumeric
  refine ⟨C,hC,rfl,?_⟩
  intro q a r hr Z hZ hDiv w Dw hw b B hb hB hBMO F
  let f := (Metric.ball a r).indicator F
  obtain ⟨hf,_hMean,_hLS,_hMeas,hGrand,hFinite,_hAE,_hI,_hOrdBound⟩ :=
    Hhardy q a r hr Z hZ hDiv w Dw hw
  obtain ⟨l,⟨hAllI,hLimit,hEstimate,hAgree⟩,_hUnique⟩ :=
    Hpair f hf hFinite b B hb hB hBMO
  have hIndicator (v : Domain n → ℝ) :
      (fun x=>f x*v x)=(Metric.ball a r).indicator (fun x=>F x*v x) := by
    funext x
    dsimp only [f]
    by_cases hx : x∈Metric.ball a r
    · rw [indicator_of_mem hx,indicator_of_mem hx]
    · rw [indicator_of_notMem hx,indicator_of_notMem hx,zero_mul]
  have hIntegral (v : Domain n → ℝ) :
      (∫ x,f x*v x)=(∫ x in Metric.ball a r,F x*v x) := by
    rw [hIndicator,integral_indicator measurableSet_ball]
  have hLocalI (k : ℕ) : IntegrableOn
      (fun x=>F x*min (k : ℝ) (max (-(k : ℝ)) (b x))) (Metric.ball a r) volume := by
    apply (integrable_indicator_iff measurableSet_ball).mp
    rw [← hIndicator]
    exact hAllI k
  have hLocalLimit : Tendsto
      (fun k : ℕ=>∫ x in Metric.ball a r,F x*min (k : ℝ) (max (-(k : ℝ)) (b x))) atTop (𝓝 l) := by
    simpa only [hIntegral] using hLimit
  have hEnergyBound := ENNReal.toReal_mono ENNReal.ofReal_ne_top hGrand
  rw [ENNReal.toReal_ofReal] at hEnergyBound
  swap
  · positivity
  have hBound : |l|≤C*B*Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Z x))*
      Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Dw x)) := by
    calc
      _≤D*B*(K*Real.sqrt 2*Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Z x))*
          Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Dw x))) :=
        hEstimate.trans (mul_le_mul_of_nonneg_left hEnergyBound (mul_nonneg hD.le hB))
      _=(D*K*Real.sqrt 2)*B*Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Z x))*
          Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Dw x)) := by ring
      _≤_ := by gcongr
  refine ⟨l,⟨hLocalI,hLocalLimit,hBound,?_⟩,?_⟩
  · intro hProduct
    have hGlobalProduct : Integrable (fun x=>f x*b x) volume := by
      rw [hIndicator]
      exact (integrable_indicator_iff measurableSet_ball).mpr hProduct
    exact (hAgree hGlobalProduct).trans (hIntegral b)
  · intro t ht
    exact tendsto_nhds_unique ht.2.1 hLocalLimit

theorem existsUnique_local_divcurl_continuous_pairing (n : ℕ) (hn : 2≤n) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (a : Domain n) (r : ℝ),0<r →
      ∀ (Z : Domain n → Gradient n q),
        (∀ i,MemLp (fun x=>Z x i) 2 (volume.restrict (Metric.ball a r))) →
        HolderToCK.WeakPoissonOn (ballDomain a r) Z (fun _=>(0 : Ambient q)) →
        ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
          HasZeroBoundaryValues (ballDomain a r) w Dw →
          ∀ (b : Domain n → ℝ) (B : ℝ),AEStronglyMeasurable b volume → 0≤B →
            (∀ (x : Domain n) (s : ℝ),0<s → IntegrableOn b (Metric.ball x s) volume ∧
              (⨍ y in Metric.ball x s,|b y-(⨍ z in Metric.ball x s,b z)|)≤B) →
            let F := fun x=>∑ i : Fin n,inner ℝ (Z x i) (Dw x i)
            ∃! l : ℝ,
              (∀ k : ℕ,IntegrableOn (fun x=>F x*min (k : ℝ) (max (-(k : ℝ)) (b x)))
                (Metric.ball a r) volume) ∧
              Tendsto (fun k : ℕ=>∫ x in Metric.ball a r,F x*min (k : ℝ) (max (-(k : ℝ)) (b x)))
                atTop (𝓝 l) ∧
              |l|≤C*B*Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Z x))*
                Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Dw x)) ∧
              (IntegrableOn (fun x=>F x*b x) (Metric.ball a r) volume →
                l=(∫ x in Metric.ball a r,F x*b x)) := by
  obtain ⟨C,hC,_hCEq,H⟩ := existsUnique_local_divcurl_continuous_pairing_explicit n hn
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end
