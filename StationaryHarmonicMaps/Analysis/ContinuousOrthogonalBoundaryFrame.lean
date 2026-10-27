/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.BoundaryStrongerMorreyRepresentative
public import StationaryHarmonicMaps.Geometry.OrientationDeterminant

/-!
# Continuous orthogonal and special-orthogonal frames on the closed ball

The stronger original derivative growth produces the actual closed-ball
representative. Original almost-everywhere values in a closed carrier
persist at every interior and sphere point. Orthogonality and determinant
one are closed constraints of the literal continuous operator decoder.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original AE closed-carrier values persist everywhere on the
closed unit ball for any actual continuous closed-ball representative. -/
theorem closedBall_representative_mem_closed_of_ae {n m : ℕ}
    (u : Domain n → Ambient m) (W : closedBall (0:Domain n) 1 → Ambient m)
    (hW : Continuous W)
    (hAE : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀hx : x∈ball (0:Domain n) 1,
      W ⟨x,ball_subset_closedBall hx⟩=u x)
    (K : Set (Ambient m)) (hK : IsClosed K)
    (huK : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),u x∈K) :
    ∀x : closedBall (0:Domain n) 1,W x∈K := by
  let i : ball (0:Domain n) 1 → closedBall (0:Domain n) 1 := inclusion ball_subset_closedBall
  have hi : Isometry i := fun _ _=>rfl
  have hDense : DenseRange i := by
    apply (denseRange_inclusion_iff ball_subset_closedBall).2
    rw [closure_ball (0:Domain n) (by norm_num : (1:ℝ)≠0)]
  have hRep : IsContinuousRepresentative (ballDomain (0:Domain n) 1) u (fun x=>W (i x)) :=
    ⟨hW.comp hi.continuous,hAE⟩
  exact isClosed_property hDense (hK.preimage hW) (hRep.mem_closed_of_ae K hK huK)

/-- Original native orthogonal frame data with strictly stronger Morrey
growth have a unique uniform Holder representative taking orthogonal
values at every point of the closed unit ball. -/
theorem existsUnique_continuous_orthogonal_closedBall_frame_of_stronger_morrey
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀(m q : ℕ)
      (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
      (p : Domain n → Ambient m) (Dp : Domain n → Gradient n m) (K : ℝ),
      MemW12 (ballDomain (0:Domain n) 1) p Dp → 0≤K →
      (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Dp x))≤K*r^((n:ℝ)-2+γ)) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (R (p x))*R (p x)=1) →
      ∃! P : closedBall (0:Domain n) 1 → Ambient m,
        Continuous P ∧
        (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀hx : x∈ball (0:Domain n) 1,
          P ⟨x,ball_subset_closedBall hx⟩=p x) ∧
        (∀x y : closedBall (0:Domain n) 1,
          ‖P x-P y‖≤C*Real.sqrt K*(dist (x:Domain n) (y:Domain n))^(γ/2)) ∧
        ∀x : closedBall (0:Domain n) 1,star (R (P x))*R (P x)=1 := by
  obtain ⟨C,hC,Hrep⟩ := existsUnique_closedBall_holder_representative_of_stronger_morrey n hn γ hγ hγTwo
  refine ⟨C,hC,?_⟩
  intro m q R p Dp K hp hK hGrowth hOrth
  obtain ⟨P,hP,hUnique⟩ := Hrep m p Dp K hp hK hGrowth
  have hStar : Continuous (fun z : Ambient m=>star (R z)) :=
    (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).continuous.comp R.continuous
  have hClosed : IsClosed {z : Ambient m | star (R z)*R z=1} :=
    isClosed_eq (hStar.mul R.continuous) continuous_const
  have hOrthClosed := closedBall_representative_mem_closed_of_ae p P hP.1 hP.2.1 _ hClosed hOrth
  refine ⟨P,⟨hP.1,hP.2.1,hP.2.2,hOrthClosed⟩,?_⟩
  intro z hz
  exact hUnique z ⟨hz.1,hz.2.1,hz.2.2.1⟩

/-- Original native special-orthogonal AE frame data with strictly
stronger growth produce a unique closed-ball Holder representative with
orthogonality and determinant one at every sphere and interior point. -/
theorem existsUnique_continuous_special_orthogonal_closedBall_frame_of_stronger_morrey
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀(m q : ℕ)
      (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
      (p : Domain n → Ambient m) (Dp : Domain n → Gradient n m) (K : ℝ),
      MemW12 (ballDomain (0:Domain n) 1) p Dp → 0≤K →
      (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Dp x))≤K*r^((n:ℝ)-2+γ)) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (R (p x))*R (p x)=1) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),(R (p x)).det=1) →
      ∃! P : closedBall (0:Domain n) 1 → Ambient m,
        Continuous P ∧
        (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀hx : x∈ball (0:Domain n) 1,
          P ⟨x,ball_subset_closedBall hx⟩=p x) ∧
        (∀x y : closedBall (0:Domain n) 1,
          ‖P x-P y‖≤C*Real.sqrt K*(dist (x:Domain n) (y:Domain n))^(γ/2)) ∧
        ∀x : closedBall (0:Domain n) 1,star (R (P x))*R (P x)=1 ∧ (R (P x)).det=1 := by
  obtain ⟨C,hC,Horth⟩ := existsUnique_continuous_orthogonal_closedBall_frame_of_stronger_morrey n hn γ hγ hγTwo
  refine ⟨C,hC,?_⟩
  intro m q R p Dp K hp hK hGrowth hOrth hDet
  obtain ⟨P,hP,hUnique⟩ := Horth m q R p Dp K hp hK hGrowth hOrth
  have hClosed : IsClosed {z : Ambient m | (R z).det=1} :=
    isClosed_eq ((contDiff_operator_det q).continuous.comp R.continuous) continuous_const
  have hDetClosed := closedBall_representative_mem_closed_of_ae p P hP.1 hP.2.1 _ hClosed hDet
  refine ⟨P,⟨hP.1,hP.2.1,hP.2.2.1,fun x=>⟨hP.2.2.2 x,hDetClosed x⟩⟩,?_⟩
  intro z hz
  exact hUnique z ⟨hz.1,hz.2.1,hz.2.2.1,fun x=>(hz.2.2.2 x).1⟩

end StationaryHarmonicMaps.Analysis

end
