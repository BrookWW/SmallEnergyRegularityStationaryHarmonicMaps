module

public import StationaryHarmonicMaps.Analysis.WeakPoissonCutoff
public import StationaryHarmonicMaps.Analysis.OrthogonalConnectionIntegrability
public import StationaryHarmonicMaps.Geometry.OrthogonalCutoffAlgebra

/-!
# The genuine weak cutoff equation in a Sobolev orthogonal frame

The original map and actual weak columns give a full-space Sobolev cutoff.
Its weak equation, the bounded frame product test and differentiated
orthogonality give all four expanded error terms with actual local L¹
integrability. Gauge existence, a coexact connection and quantitative error
bounds remain separate mathematical obligations.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The expanded cutoff error and transformed weak equation are actual integrable fields. -/
theorem weak_orthogonal_frame_cutoff {n m q : ℕ} {Ω : OpenDomain n}
    {p : Domain n → Ambient m} {Dp : Domain n → Gradient n m}
    (hp : MemW12Loc Ω p Dp) {M : ℝ}
    (hb : ∀ᵐ x ∂volume.restrict Ω.val, ‖p x‖ ≤ M)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (horth : ∀ᵐ x ∂volume.restrict Ω.val, star (R (p x)) * R (p x) = 1)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (A : Domain n → Fin n → Ambient q →L[ℝ] Ambient q)
    (hA : ∀ i, LocallyMemL2 Ω (fun x => A x i))
    (hEq : HolderToCK.WeakPoissonOn Ω Du (fun x => -(∑ i : Fin n, A x i (Du x i))))
    (c : Ambient q) (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω.val) :
    let Dv (x : Domain n) (i : Fin n) :=
      χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c)
    let Z (x : Domain n) (i : Fin n) :=
      star (R (p x)) * R (Dp x i) + star (R (p x)) * A x i * R (p x)
    let W (x : Domain n) := ∑ i : Fin n, Z x i (star (R (p x)) (Dv x i))
    let e (x : Domain n) :=
      (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) •
        star (R (Dp x i)) (u x - c)) +
      (2 : ℝ) • (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) •
        star (R (p x)) (Du x i)) +
      Laplacian.laplacian χ x • star (R (p x)) (u x - c) +
      ∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) •
        Z x i (star (R (p x)) (u x - c))
    MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) (fun x => χ x • (u x - c)) Dv ∧
    LocallyIntegrableOn e Ω.val volume ∧
    ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Ω.val →
      IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (star (R (p x)) (Dv x i))
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) Ω.val volume ∧
      IntegrableOn (fun x => inner ℝ (W x) (ψ x)) Ω.val volume ∧
      IntegrableOn (fun x => inner ℝ (e x) (ψ x)) Ω.val volume ∧
      (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (star (R (p x)) (Dv x i))
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        (∫ x in Ω.val, inner ℝ (W x) (ψ x)) -
          ∫ x in Ω.val, inner ℝ (e x) (ψ x) := by
  let Dv (x : Domain n) (i : Fin n) :=
    χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c)
  let Fv (x : Domain n) := χ x • (-(∑ i : Fin n, A x i (Du x i))) +
    (2 : ℝ) • (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • Du x i) +
    Laplacian.laplacian χ x • (u x - c)
  let Z (x : Domain n) (i : Fin n) :=
    star (R (p x)) * R (Dp x i) + star (R (p x)) * A x i * R (p x)
  let W (x : Domain n) := ∑ i : Fin n, Z x i (star (R (p x)) (Dv x i))
  let e (x : Domain n) :=
    (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) •
      star (R (Dp x i)) (u x - c)) +
    (2 : ℝ) • (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) •
      star (R (p x)) (Du x i)) +
    Laplacian.laplacian χ x • star (R (p x)) (u x - c) +
    ∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) •
      Z x i (star (R (p x)) (u x - c))
  let J (x : Domain n) := star (R (p x)) (Fv x) +
    ∑ i : Fin n, star (R (Dp x i)) (Dv x i)
  have hcut := (memW12_cutoff_sub_const hu c χ hχ hcχ hsχ).to_memW12Loc
  have hPcut := weakPoissonOn_cutoff_sub_const hu hEq c χ hχ hcχ hsχ
  have hflux := weak_operator_flux_transform hp hb R hcut hPcut
  have hZ := locallyMemL2_frame_connection hp hb R A hA
  have hE := locallyMemL2_operator_flux hp hb R hcut
  have hW : LocallyIntegrableOn W Ω.val volume :=
    locallyIntegrableOn_operator_contraction Z hZ _ hE
  have hdorth := ae_orthogonal_frame_derivative hp R M hb horth
  have hJ : J =ᵐ[volume.restrict Ω.val] (fun x => e x - W x) := by
    filter_upwards [horth, hdorth] with x hx hdx
    exact orthogonal_cutoff_forcing_identity (R (p x)) (fun i => R (Dp x i)) (A x)
      (Du x) (u x - c) (χ x) (Laplacian.laplacian χ x)
      (fun i => fderiv ℝ χ x (EuclideanSpace.single i 1))
      (mul_star_eq_one_of_star_mul_eq_one _ hx) hdx
  have heq : (fun x => J x + W x) =ᵐ[volume.restrict Ω.val] e := by
    filter_upwards [hJ] with x hx
    rw [hx, sub_add_cancel]
  have he : LocallyIntegrableOn e Ω.val volume :=
    LocallyIntegrableOn.congr heq (hflux.1.add hW)
  refine ⟨memW12_cutoff_sub_const_univ hu c χ hχ hcχ hsχ, he, ?_⟩
  intro ψ hψ hcψ hsψ
  obtain ⟨hleft, _hJtest, hweak⟩ := hflux.2 ψ hψ hcψ hsψ
  have hWtest := integrable_locallyL1_vector_test hW ψ hψ.continuous hcψ hsψ
  have hetest := integrable_locallyL1_vector_test he ψ hψ.continuous hcψ hsψ
  have hinner : (fun x => inner ℝ (J x) (ψ x)) =ᵐ[volume.restrict Ω.val]
      (fun x => inner ℝ (e x) (ψ x) - inner ℝ (W x) (ψ x)) := by
    filter_upwards [hJ] with x hx
    rw [hx, inner_sub_left]
  refine ⟨hleft, hWtest.integrableOn, hetest.integrableOn, ?_⟩
  calc
    _ = -(∫ x in Ω.val, inner ℝ (J x) (ψ x)) := hweak
    _ = -((∫ x in Ω.val, inner ℝ (e x) (ψ x)) -
        ∫ x in Ω.val, inner ℝ (W x) (ψ x)) := by
      rw [integral_congr_ae hinner, integral_sub hetest.integrableOn hWtest.integrableOn]
    _ = _ := neg_sub _ _

end StationaryHarmonicMaps.Analysis

end
