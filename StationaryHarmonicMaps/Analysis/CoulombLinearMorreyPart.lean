module

public import StationaryHarmonicMaps.Analysis.CoexactOperatorLpMorrey
public import StationaryHarmonicMaps.Geometry.OrthogonalRightHS
public import StationaryHarmonicMaps.Geometry.GaugedEnergyAlgebra

/-!
# The actual linear Morrey component of a Coulomb connection

Conjugation by the original orthogonal frame preserves every encoded
Hilbert--Schmidt energy. The genuine coexact projection of P* A P therefore
has the full power growth of the original connection. Its native gradient
complement and closed normal tensor identify the actual relative response.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The linear relative component of the original transformed connection
inherits every subdimensional power-growth bound of the original A. -/
theorem exists_coulomb_linear_relative_power_growth (n : ℕ) (hn : 2≤n)
    (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n:ℝ)) :
    ∃ L : ℝ,0<L ∧ ∀(q : ℕ)
      (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
      (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q)),
      (∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) →
      ∀(p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
        (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q)) (K : ℝ),
        MemW12 (ballDomain (0 : Domain n) 1) p Dp →
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (p x))*R (p x)=1) →
        (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
        0≤K →
        (∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
          (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (A x i)))≤K*r^ν) →
        let G := fun x i=>E (star (R (p x))*A x i*R (p x))
        let μ := volume.restrict (ball (0 : Domain n) 1)
        ∃(u : Domain n → Ambient (q*q))
          (c : Fin n → Fin n → Domain n → Ambient (q*q))
          (Dc : Fin n → Fin n → Domain n → Gradient n (q*q))
          (Q : Domain n → Gradient n (q*q)),
          MemW12 (ballDomain (0 : Domain n) 1) u (fun x i=>G x i-Q x i) ∧
          (∀i j,MemW12 (ballDomain (0 : Domain n) 1) (c i j) (Dc i j)) ∧
          (∀i,MemLp (fun x=>Q x i) 2 μ) ∧
          (∀ᵐx∂μ,∀i j,c i j x= -c j i x) ∧
          (∀ᵐx∂μ,∀i j k,Dc i j x k+Dc j k x i+Dc k i x j=0) ∧
          (∀ᵐx∂μ,∀j,(∑i : Fin n,Dc i j x i)=Q x j) ∧
          (∀(j : Fin n) (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (c i j x) (Dψ x i)) μ ∧
            Integrable (fun x=>inner ℝ (Q x j) (ψ x)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (c i j x) (Dψ x i) ∂μ)=-(∫x,inner ℝ (Q x j) (ψ x) ∂μ)) ∧
          (∀(ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ)=0) ∧
          ((∫x,∑j : Fin n,∑i : Fin n,‖c i j x‖^2 ∂μ)+
            (∫x,∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Dc i j x k‖^2 ∂μ)≤
              (4*(2 : ℝ)^(n+1)+2*(n : ℝ)+2)*(∫x,hsNormSq (Q x) ∂μ)) ∧
          ∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
            (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Q x))≤L*K*r^ν := by
  obtain ⟨_Cp,Cm,_hCp,hCm,HT⟩ := exists_same_coexact_operator_all_lp_and_power_growth_unitBall n hn
  refine ⟨Cm ⟨ν,hν,hνn⟩,hCm _,?_⟩
  intro q E R hE p Dp A K hp hOrth hA hK hGrowth G μ
  have hP := R.continuous.comp_aestronglyMeasurable hp.2.1.aestronglyMeasurable
  have hGNorm (i : Fin n) : ∀ᵐx∂μ,‖G x i‖=‖E (A x i)‖ := by
    filter_upwards [hOrth] with x hx
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have hStar : star (star (R (p x)))*star (R (p x))=1 := by
      rw [star_star]
      exact mul_star_eq_one_of_star_mul_eq_one _ hx
    change ‖E (star (R (p x))*A x i*R (p x))‖^2=‖E (A x i)‖^2
    rw [encoded_norm_sq_mul_right_orthogonal E hE _ _ hx,
      encoded_norm_sq_mul_left_orthogonal E hE _ _ hStar]
  have hGLp (i : Fin n) : MemLp (fun x=>G x i) 2 μ := by
    have hEA := E.lipschitz.comp_memLp (map_zero E) (hA i)
    have hGM : AEStronglyMeasurable (fun x=>G x i) μ :=
      E.continuous.comp_aestronglyMeasurable ((((ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).continuous.comp_aestronglyMeasurable hP).mul (hA i).aestronglyMeasurable).mul hP)
    exact hEA.of_le hGM ((hGNorm i).mono fun x hx=>hx.le)
  have hGHS : (fun x=>hsNormSq (G x))=ᵐ[μ](fun x=>hsNormSq (fun i=>E (A x i))) := by
    filter_upwards [ae_all_iff.mpr hGNorm] with x hx
    simp only [hsNormSq,hx]
  let enc : Gradient n (q*q) → Ambient (n*(q*q)) := fun H=>WithLp.toLp 2
    (fun k=>H (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  let dec := fun (W : Domain n → Ambient (n*(q*q))) x i=>WithLp.toLp 2
    (fun j : Fin (q*q)=>W x (finProdFinEquiv (i,j)))
  let W := (memLp_hs_flatten G hGLp).toLp (fun x=>enc (G x))
  have hDecode : dec W=ᵐ[μ]G := by
    filter_upwards [(memLp_hs_flatten G hGLp).coeFn_toLp] with x hx
    change (fun i=>WithLp.toLp 2 (fun j : Fin (q*q)=>W x (finProdFinEquiv (i,j))))=G x
    rw [hx]
    exact hs_unflatten_flatten (G x)
  obtain ⟨T,_hT,_hSelf,_hIdem,Hresponse⟩ := HT (q*q)
  obtain ⟨u,c,Dc,hu,hc,hSkew,hClosed,hDiv,hNormal,hNatural,hH1,_hEnergy,_hCore,_hLp,hM⟩ := Hresponse W
  have huG : MemW12 (ballDomain (0 : Domain n) 1) u (fun x i=>G x i-dec (T W) x i) :=
    hu.congr_ae (Eventually.of_forall fun _=>rfl) (hDecode.mono fun x hx=>by
      change (fun i=>dec W x i-dec (T W) x i)=(fun i=>G x i-dec (T W) x i)
      rw [hx])
  refine ⟨u,c,Dc,dec (T W),huG,hc,(fun i=>memLp_hs_unflatten (T W) (Lp.memLp (T W)) i),
    hSkew,hClosed,hDiv,hNormal,hNatural,hH1,?_⟩
  apply hM ⟨ν,hν,hνn⟩ K hK
  intro a ha r hr
  have hDecodedHS : (fun x=>hsNormSq (dec W x))=ᵐ[μ](fun x=>hsNormSq (G x)) :=
    hDecode.mono fun x hx=>congrArg hsNormSq hx
  have hAE : (fun x=>hsNormSq (dec W x))=ᵐ[μ](fun x=>hsNormSq (fun i=>E (A x i))) :=
    hDecodedHS.trans hGHS
  rw [integral_congr_ae (hAE.filter_mono (ae_mono (Measure.restrict_mono_set volume inter_subset_right)))]
  exact hGrowth a ha r hr

end StationaryHarmonicMaps.Analysis

end
