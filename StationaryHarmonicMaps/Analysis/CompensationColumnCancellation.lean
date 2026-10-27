module

public import StationaryHarmonicMaps.Analysis.WhitneyCompactIntersection
public import StationaryHarmonicMaps.Analysis.PartitionCancellationSum

/-!
# Actual finite low-index compensation columns

A compact original high support inside the original low bad set meets
only finitely many low Whitney supports. Every omitted original
numerator is identically zero. The actual low partition identity and
the original high zero integral therefore give a genuinely finite
column sum of the actual compensation coefficients equal to zero.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original low Whitney data and an actual compactly supported high zero-mean piece produce a genuinely finite compensation column with zero original sum. -/
theorem finite_compensation_column_sum_zero {n : ℕ}
    (S U : Set (Domain n)) (hOpen : IsOpen S) (hComp : Sᶜ.Nonempty)
    (hDisj : U.PairwiseDisjoint (fun a=>Metric.ball a (Metric.infDist a Sᶜ/20)))
    (θ : U → Domain n → ℝ) (hθ : ∀ a,ContDiff ℝ ∞ (θ a))
    (hSuppθ : ∀ a,tsupport (θ a)⊆Metric.ball a.val (10*(Metric.infDist a.val Sᶜ/20)))
    (hBounds : ∀ a x,0≤θ a x ∧ θ a x≤1) (hPart : ∀ x∈S,∑' a,θ a x=1)
    (K : Set (Domain n)) (hK : IsCompact K) (hKS : K⊆S)
    (b : Domain n → ℝ) (hb : Integrable b volume) (hSuppb : Function.support b⊆K)
    (hMean : (∫ x,b x)=0) (m : ℝ) :
    let d := fun a=>(∫ x,θ a x*b x)/m
    (∀ a,Integrable (fun x=>θ a x*b x) volume) ∧
      Function.HasFiniteSupport d ∧ (∑' a,d a)=0 := by
  classical
  intro d
  have hCenterFin := finite_whitney_balls_intersecting_compact S U hOpen hComp hDisj K hK hKS
  have hFin : {a : U | a.val∈{a∈U | (Metric.ball a (10*(Metric.infDist a Sᶜ/20))∩K).Nonempty}}.Finite :=
    hCenterFin.preimage Subtype.val_injective.injOn
  let F := hFin.toFinset
  have hProdI (a : U) : Integrable (fun x=>θ a x*b x) volume := hb.bdd_mul (hθ a).continuous.aestronglyMeasurable
    (Eventually.of_forall fun x=>by rw [Real.norm_of_nonneg (hBounds a x).1];exact (hBounds a x).2)
  have hZeroProd (a : U) (ha : a∉F) (x : Domain n) : θ a x*b x=0 := by
    by_cases hxb : b x=0
    · rw [hxb,mul_zero]
    · by_cases hxθ : θ a x=0
      · rw [hxθ,zero_mul]
      · exact False.elim (ha (hFin.mem_toFinset.mpr
          ⟨a.property,x,hSuppθ a (subset_tsupport (θ a) hxθ),hSuppb hxb⟩))
  have hZeroD (a : U) (ha : a∉F) : d a=0 := by
    have hEq : (fun x=>θ a x*b x)=fun _=>0 := funext (hZeroProd a ha)
    dsimp only [d]
    rw [hEq,integral_zero,zero_div]
  have hFiniteD : Function.HasFiniteSupport d := F.finite_toSet.subset (by
    intro a ha
    by_contra hnot
    exact ha (hZeroD a hnot))
  have hProductSum (x : Domain n) : (∑ a∈F,θ a x*b x)=b x := by
    have hSum : (∑' a,θ a x*b x)=b x := by
      by_cases hx : b x=0
      · simp only [hx,mul_zero,tsum_zero]
      · rw [tsum_mul_right,hPart x (hKS (hSuppb hx)),one_mul]
    exact (tsum_eq_sum (fun a ha=>hZeroProd a ha x)).symm.trans hSum
  refine ⟨hProdI,hFiniteD,?_⟩
  rw [tsum_eq_sum hZeroD]
  calc
    _ = (∑ a∈F,∫ x,θ a x*b x)/m := (Finset.sum_div _ _ _).symm
    _ = (∫ x,(∑ a∈F,θ a x*b x))/m := congrArg (fun t : ℝ=>t/m)
      (integral_finsetSum _ (fun a _=>hProdI a)).symm
    _ = (∫ x,b x)/m := congrArg (fun t : ℝ=>t/m) (integral_congr_ae (Eventually.of_forall hProductSum))
    _ = 0 := by rw [hMean,zero_div]

end StationaryHarmonicMaps.Analysis

end
