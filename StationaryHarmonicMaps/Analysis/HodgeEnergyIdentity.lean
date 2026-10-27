module

public import StationaryHarmonicMaps.Analysis.HilbertSchmidtEncoding
public import HolderToCK.Analysis.L2PairingContinuity

/-!
# Actual residual energy of orthogonal one-form responses

Original column L2 data and genuine projection self-pairings determine the
energy of the same original residual. The Hilbert--Schmidt square uses
every column, and all real integrals are proved integrable before expansion.
-/

public section

open HarmonicMaps MeasureTheory Filter

namespace StationaryHarmonicMaps.Analysis

/-- Actual orthogonal projection pairings give the full energy identity and contraction for the same residual, with its L2 membership derived from the original decomposition. -/
theorem hs_residual_energy_identity_of_projection_pairings {X : Type*} [MeasurableSpace X]
    {n q : ℕ} (μ : Measure X) (F D P h : X → Gradient n q)
    (hF : ∀j,MemLp (fun x=>F x j) 2 μ)
    (hD : ∀j,MemLp (fun x=>D x j) 2 μ)
    (hP : ∀j,MemLp (fun x=>P x j) 2 μ)
    (hEq : ∀ᵐ x ∂μ,∀j,F x j=D x j+P x j+h x j)
    (hDself : (∫x,hsNormSq (D x) ∂μ)=∫x,∑j : Fin n,inner ℝ (F x j) (D x j) ∂μ)
    (hPself : (∫x,hsNormSq (P x) ∂μ)=∫x,∑j : Fin n,inner ℝ (F x j) (P x j) ∂μ)
    (hOrth : (∫x,∑j : Fin n,inner ℝ (D x j) (P x j) ∂μ)=0) :
    (∀j,MemLp (fun x=>h x j) 2 μ) ∧ Integrable (fun x=>hsNormSq (h x)) μ ∧
      (∫x,hsNormSq (D x) ∂μ)+(∫x,hsNormSq (P x) ∂μ)+(∫x,hsNormSq (h x) ∂μ)=
        ∫x,hsNormSq (F x) ∂μ ∧
      (∫x,hsNormSq (h x) ∂μ)≤∫x,hsNormSq (F x) ∂μ := by
  have hResidual : h =ᵐ[μ] (fun x j=>F x j-D x j-P x j) := by
    filter_upwards [hEq] with x hx
    funext j
    rw [hx j]
    abel
  have hH (j : Fin n) : MemLp (fun x=>h x j) 2 μ :=
    MemLp.ae_eq (hResidual.mono fun _ hx=>(congrFun hx j).symm) (((hF j).sub (hD j)).sub (hP j))
  have hI (A : X → Gradient n q) (hA : ∀j,MemLp (fun x=>A x j) 2 μ) :
      Integrable (fun x=>hsNormSq (A x)) μ :=
    integrable_finsetSum _ (fun j _=>(hA j).integrable_norm_pow (by decide : (2:ℕ)≠0))
  have hPair (A B : X → Gradient n q) (hA : ∀j,MemLp (fun x=>A x j) 2 μ)
      (hB : ∀j,MemLp (fun x=>B x j) 2 μ) :
      Integrable (fun x=>∑j : Fin n,inner ℝ (A x j) (B x j)) μ :=
    integrable_finsetSum _ (fun j _=>by
      apply (L2.integrable_inner (𝕜:=ℝ) ((hA j).toLp (fun x=>A x j))
        ((hB j).toLp (fun x=>B x j))).congr
      filter_upwards [(hA j).coeFn_toLp,(hB j).coeFn_toLp] with x hx hy
      rw [hx,hy])
  have hSquare (a b c : Ambient q) : ‖a-b-c‖^2=
      ‖a‖^2+‖b‖^2+‖c‖^2-2*inner ℝ a b-2*inner ℝ a c+2*inner ℝ b c := by
    rw [norm_sub_sq_real,norm_sub_sq_real,inner_sub_left]
    ring
  have hPoint : ∀ᵐ x ∂μ,hsNormSq (h x)=
      hsNormSq (F x)+hsNormSq (D x)+hsNormSq (P x)-
        2*(∑j : Fin n,inner ℝ (F x j) (D x j))-
        2*(∑j : Fin n,inner ℝ (F x j) (P x j))+
        2*(∑j : Fin n,inner ℝ (D x j) (P x j)) := by
    filter_upwards [hResidual] with x hx
    rw [hx]
    simp only [hsNormSq,hSquare,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
  have hE : (∫x,hsNormSq (h x) ∂μ)=
      (∫x,hsNormSq (F x) ∂μ)+(∫x,hsNormSq (D x) ∂μ)+(∫x,hsNormSq (P x) ∂μ)-
        2*(∫x,∑j : Fin n,inner ℝ (F x j) (D x j) ∂μ)-
        2*(∫x,∑j : Fin n,inner ℝ (F x j) (P x j) ∂μ)+
        2*(∫x,∑j : Fin n,inner ℝ (D x j) (P x j) ∂μ) := by
    have H1 := integral_add (((((hI F hF).add (hI D hD)).add (hI P hP)).sub
      ((hPair F D hF hD).const_mul 2)).sub ((hPair F P hF hP).const_mul 2))
      ((hPair D P hD hP).const_mul 2)
    have H2 := integral_sub ((((hI F hF).add (hI D hD)).add (hI P hP)).sub
      ((hPair F D hF hD).const_mul 2)) ((hPair F P hF hP).const_mul 2)
    have H3 := integral_sub (((hI F hF).add (hI D hD)).add (hI P hP))
      ((hPair F D hF hD).const_mul 2)
    have H4 := integral_add ((hI F hF).add (hI D hD)) (hI P hP)
    have H5 := integral_add (hI F hF) (hI D hD)
    simp only [Pi.add_apply,Pi.sub_apply] at H1 H2 H3 H4 H5
    rw [integral_congr_ae hPoint,H1,H2,H3,H4,H5]
    simp only [integral_const_mul]
  rw [← hDself,← hPself,hOrth] at hE
  have hIdentity : (∫x,hsNormSq (D x) ∂μ)+(∫x,hsNormSq (P x) ∂μ)+
      (∫x,hsNormSq (h x) ∂μ)=∫x,hsNormSq (F x) ∂μ := by linarith only [hE]
  refine ⟨hH,hI h hH,hIdentity,?_⟩
  have hD0 : 0≤∫x,hsNormSq (D x) ∂μ := integral_nonneg (fun x=>Finset.sum_nonneg (fun j _=>sq_nonneg ‖D x j‖))
  have hP0 : 0≤∫x,hsNormSq (P x) ∂μ := integral_nonneg (fun x=>Finset.sum_nonneg (fun j _=>sq_nonneg ‖P x j‖))
  linarith only [hIdentity,hD0,hP0]

end StationaryHarmonicMaps.Analysis

end
