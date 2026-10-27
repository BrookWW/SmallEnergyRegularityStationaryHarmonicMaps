module

public import HarmonicMaps.Sobolev
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability of compactly supported outer-variation tests

The derivative of a compactly supported C1 test has a global operator bound.
Its action on each displayed Sobolev gradient column is L2 on the compact
projection of the test support. The first-variation density is therefore L1
there and vanishes outside that compact set.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff

namespace StationaryHarmonicMaps

private theorem integrable_inner_of_memLp_two {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

/-- The literal outer-variation density is integrable on the whole source space. -/
theorem integrable_outerVariation_density {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {V : Domain n × Ambient q → Ambient q}
    (hV : ContDiff ℝ 1 V) (hc : HasCompactSupport V)
    (hs : tsupport V ⊆ Ω.val ×ˢ (Set.univ : Set (Ambient q))) :
    Integrable (fun x => ∑ i : Fin n,
      inner ℝ (Du x i)
        (fderiv ℝ V (x, u x) (EuclideanSpace.single i (1 : ℝ), Du x i))) volume := by
  let K : Set (Domain n) := Prod.fst '' tsupport V
  have hK : IsCompact K := hc.image continuous_fst
  have hKΩ : K ⊆ Ω.val := by
    rintro x ⟨z, hz, rfl⟩
    exact (hs hz).1
  let μ : Measure (Domain n) := volume.restrict K
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have huK : MemLp u 2 μ := hu.2.1 K hK hKΩ
  have hDu (i : Fin n) : MemLp (fun x => Du x i) 2 μ := hu.2.2 i K hK hKΩ
  have hgraph : AEStronglyMeasurable (fun x => (x, u x)) μ :=
    continuous_id.aestronglyMeasurable.prodMk huK.aestronglyMeasurable
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hV.continuous_fderiv (by norm_num))
  have hcolumn (i : Fin n) :
      MemLp (fun x => (EuclideanSpace.single i (1 : ℝ), Du x i)) 2 μ :=
    memLp_prod_iff.mpr ⟨memLp_const _, hDu i⟩
  have hderivative (i : Fin n) : MemLp
      (fun x => fderiv ℝ V (x, u x) (EuclideanSpace.single i (1 : ℝ), Du x i)) 2 μ := by
    have hmeas : AEStronglyMeasurable
        (fun x => fderiv ℝ V (x, u x) (EuclideanSpace.single i (1 : ℝ), Du x i)) μ :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (((hV.continuous_fderiv (by norm_num)).comp_aestronglyMeasurable hgraph).prodMk
          (hcolumn i).aestronglyMeasurable)
    apply (hcolumn i).of_le_mul hmeas
    filter_upwards [] with x
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hC (x, u x)) (norm_nonneg _))
  have hlocal : IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (Du x i)
        (fderiv ℝ V (x, u x) (EuclideanSpace.single i (1 : ℝ), Du x i))) K volume :=
    integrable_finsetSum Finset.univ
      (fun i _ => integrable_inner_of_memLp_two (hDu i) (hderivative i))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hlocal
  intro x hx
  by_contra hxK
  have hxV : (x, u x) ∉ tsupport V := fun h => hxK ⟨(x, u x), h, rfl⟩
  apply hx
  simp only [fderiv_of_notMem_tsupport (𝕜 := ℝ) hxV, zero_apply,
    inner_zero_right, Finset.sum_const_zero]

/-- The same density has a genuine integral on its open Sobolev domain. -/
theorem integrableOn_outerVariation_density {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {V : Domain n × Ambient q → Ambient q}
    (hV : ContDiff ℝ 1 V) (hc : HasCompactSupport V)
    (hs : tsupport V ⊆ Ω.val ×ˢ (Set.univ : Set (Ambient q))) :
    IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (Du x i)
        (fderiv ℝ V (x, u x) (EuclideanSpace.single i (1 : ℝ), Du x i))) Ω.val volume :=
  (integrable_outerVariation_density hu hV hc hs).integrableOn

end StationaryHarmonicMaps

end
