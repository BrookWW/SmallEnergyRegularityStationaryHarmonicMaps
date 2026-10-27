module

public import StationaryHarmonicMaps.Analysis.FiniteColumnReconstruction

/-!
# Actual reconstruction by the fully corrected pieces

Original pointwise finite low and high support families make the
original bad sums genuine finite sums. The original finite zero-sum
compensation columns give a finite total correction sum equal to zero.
The complete corrected expression then reconstructs the difference of
the original two good functions, including the mean corrections.
-/

public section

open HarmonicMaps Set

namespace StationaryHarmonicMaps.Analysis

/-- Genuine finite partition families and actual finite zero-sum correction columns give pointwise finite corrected pieces reconstructing the same original good-function difference. -/
theorem corrected_partition_pieces_reconstruct_good_difference {X I J : Type*}
    (Slo Shi : Set X) (hNested : Shi⊆Slo) (θ : I → X → ℝ) (ψ : J → X → ℝ)
    (hθFinite : ∀ x,Function.HasFiniteSupport (fun i=>θ i x))
    (hψFinite : ∀ x,Function.HasFiniteSupport (fun j=>ψ j x))
    (hψSupp : ∀ j,Function.support (ψ j)⊆Shi)
    (hθPart : ∀ x∈Slo,∑' i,θ i x=1)
    (f : X → ℝ) (c : I → ℝ) (d : J → ℝ) (e : I → J → ℝ)
    (hColumns : ∀ j,Function.HasFiniteSupport (fun i=>e i j)) (hZero : ∀ j,(∑' i,e i j)=0) :
    let blo := fun i x=>θ i x*(f x-c i)
    let bhi := fun j x=>ψ j x*(f x-d j)
    let A := fun i x=>blo i x-(∑' j,θ i x*bhi j x)+(∑' j,e i j*ψ j x)
    let glo := fun x=>f x-∑' i,blo i x
    let ghi := fun x=>f x-∑' j,bhi j x
    (∀ x,Function.HasFiniteSupport (fun i=>A i x)) ∧ (∀ x,(∑' i,A i x)=ghi x-glo x) := by
  intro blo bhi A glo ghi
  have hBloFinite (x : X) : Function.HasFiniteSupport (fun i=>blo i x) := (hθFinite x).subset (by
    intro i hi;by_contra hn
    have H : θ i x=0 := not_not.mp hn
    exact hi (by change θ i x*(f x-c i)=0;rw [H,zero_mul]))
  have hProductEq (i : I) (x : X) : (∑' j,θ i x*bhi j x)=θ i x*(∑' j,bhi j x) := tsum_mul_left
  have hProductFinite (x : X) : Function.HasFiniteSupport (fun i=>∑' j,θ i x*bhi j x) := (hθFinite x).subset (by
    intro i hi;by_contra hn
    have H : θ i x=0 := not_not.mp hn
    exact hi (by change (∑' j,θ i x*bhi j x)=0;rw [hProductEq,H,zero_mul]))
  have hProductSum (x : X) : (∑' i,∑' j,θ i x*bhi j x)=∑' j,bhi j x := by
    simp_rw [hProductEq]
    rw [tsum_mul_right]
    by_cases hx : x∈Slo
    · rw [hθPart x hx,one_mul]
    · have hZeroHigh (j : J) : bhi j x=0 := by
        have hψZero : ψ j x=0 := by
          by_contra hn
          exact hx (hNested (hψSupp j hn))
        change ψ j x*(f x-d j)=0
        rw [hψZero,zero_mul]
      simp only [hZeroHigh,tsum_zero,mul_zero]
  have hCorrection (x : X) : Function.HasFiniteSupport (fun i=>∑' j,e i j*ψ j x) ∧
      (∑' i,∑' j,e i j*ψ j x)=0 :=
    finite_column_correction_tsum_zero (fun j=>ψ j x) (hψFinite x) e hColumns hZero
  have hAFinite (x : X) : Function.HasFiniteSupport (fun i=>A i x) :=
    ((hθFinite x).union (hCorrection x).1).subset (by
      intro i hi
      by_contra hn
      have hNot := not_or.mp hn
      have hθZero : θ i x=0 := not_not.mp hNot.1
      have hCorrZero : (∑' j,e i j*ψ j x)=0 := not_not.mp hNot.2
      exact hi (by change θ i x*(f x-c i)-(∑' j,θ i x*bhi j x)+(∑' j,e i j*ψ j x)=0
                   simp only [hθZero,zero_mul,tsum_zero,hCorrZero,sub_self,add_zero]))
  refine ⟨hAFinite,?_⟩
  intro x
  have hSBlo : Summable (fun i=>blo i x) := summable_of_hasFiniteSupport (hBloFinite x)
  have hSProduct : Summable (fun i=>∑' j,θ i x*bhi j x) := summable_of_hasFiniteSupport (hProductFinite x)
  have hSCorrection : Summable (fun i=>∑' j,e i j*ψ j x) := summable_of_hasFiniteSupport (hCorrection x).1
  change (∑' i,((blo i x-(∑' j,θ i x*bhi j x))+(∑' j,e i j*ψ j x)))=_
  rw [(hSBlo.sub hSProduct).tsum_add hSCorrection,hSBlo.tsum_sub hSProduct,hProductSum,(hCorrection x).2,add_zero]
  dsimp only [glo,ghi]
  ring

end StationaryHarmonicMaps.Analysis

end
