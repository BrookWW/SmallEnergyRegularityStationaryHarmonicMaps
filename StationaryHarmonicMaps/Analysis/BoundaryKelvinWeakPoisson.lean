module

public import StationaryHarmonicMaps.Analysis.KelvinConformalPairing
public import StationaryHarmonicMaps.Analysis.SobolevOddKelvinExtension
public import StationaryHarmonicMaps.Analysis.BoundaryInversionGeometry
public import StationaryHarmonicMaps.Analysis.HodgeDirichletUniqueness
public import StationaryHarmonicMaps.Analysis.DirichletOperatorOffSupport

/-!
# Actual boundary harmonicity of the same odd Kelvin graph

The original zero-boundary graph and original raw weak equation produce
weak harmonicity of the literal reflected graph on every sphere-centered
query ball where the original forcing field vanishes. The weighted test
is genuinely W0. Its derivative vanishes outside that query, by the true
inversion geometry. No reflected harmonicity or trace certificate is an
input, and the original map may have arbitrary null-set sphere values.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The original native Dirichlet graph and raw divergence equation produce the actual literal reflected native graph and its weak harmonicity on every off-support boundary query. -/
theorem odd_kelvin_native_weak_harmonic_boundary_ball {n q : ℕ} (hn : 2≤n)
    (a : Domain n) (ha : ‖a‖=1) (r : ℝ) (hr : 0<r)
    (u : Domain n → Ambient q) (Du F : Domain n → Gradient n q)
    (hu : HasZeroBoundaryValues (ballDomain (0:Domain n) 1) u Du)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0:Domain n) 1)))
    (hEq : HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1)
      (fun x i=>Du x i-F x i) (fun _=>(0:Ambient q)))
    (hZero : F =ᵐ[volume.restrict (ball (0:Domain n) 1∩ball a r)] (fun _=>(0:Gradient n q))) :
    let I := inversion (0:Domain n) 1
    let w := fun x : Domain n=>‖x‖^(2-(n:ℝ))
    let C := fun x i=>∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • Du (I x) j
    let U := fun x : Domain n=>if ‖x‖≤1 then u x else -w x • u (I x)
    let Dext := fun (x : Domain n) (i : Fin n)=>if ‖x‖≤1 then Du x i else
      -w x • C x i-((2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x (EuclideanSpace.single i 1)) • u (I x)
    MemW12 (ballDomain a r) U Dext ∧
      HolderToCK.WeakPoissonOn (ballDomain a r) Dext (fun _=>(0:Ambient q)) := by
  classical
  intro I w C U Dext
  let Ω := ballDomain (0:Domain n) 1
  let μ := volume.restrict (ball (0:Domain n) 1)
  have hLarge : MemW12 (ballDomain (0:Domain n) (2+r)) U Dext :=
    memW12_odd_kelvin_extension_ball hn (2+r) (by linarith) u Du hu
  have hSub : ball a r⊆ball (0:Domain n) (2+r) := by
    intro x hx
    have HT := dist_triangle x a 0
    have Hx : dist x a<r := hx
    have Ha : dist a 0=1 := by simpa only [dist_zero_right] using ha
    change dist x 0<2+r
    linarith
  have hNative : MemW12 (ballDomain a r) U Dext :=
    ⟨hLarge.1.mono hSub,hLarge.2.1.mono_measure (Measure.restrict_mono_set volume hSub),
      fun i=>(hLarge.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)⟩
  refine ⟨hNative,locallyIntegrableOn_zero,?_⟩
  intro ψ hψ hcψ hsψ
  obtain ⟨φ,_hφ,hφW,_hVal,hφD,_hExterior,hGlobal,hGlobalEq⟩ :=
    exists_weighted_kelvin_conformal_pairing hn u Du hu ψ hψ hcψ
  have hG (i : Fin n) : MemLp (fun x=>Du x i-F x i) 2 μ := (hu.1.2.2 i).sub (hF i)
  have hSmooth (v : Domain n → Ambient q) (hv : ContDiff ℝ ∞ v) (hcv : HasCompactSupport v)
      (hsv : tsupport v⊆Ω.val) :
      (∫x in Ω.val,∑i : Fin n,inner ℝ (Du x i-F x i) (fderiv ℝ v x (EuclideanSpace.single i 1)))=
        ∫x in Ω.val,∑i : Fin n,inner ℝ (0:Ambient q) (fderiv ℝ v x (EuclideanSpace.single i 1)) := by
    have H := (hEq.2 v hv hcv hsv).2.2
    simpa only [inner_zero_left,Finset.sum_const_zero,integral_zero,neg_zero] using H
  have hNativePair := gradient_pairing_eq_on_zeroBoundary_of_smooth Ω
    (fun x i=>Du x i-F x i) (fun _=>(0:Gradient n q)) hG (fun _=>MemLp.zero) hSmooth hφW
  have hGZero : (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Du x i-F x i)
      (fderiv ℝ φ x (EuclideanSpace.single i 1)))=0 := by
    simpa only [Ω,ballDomain,Pi.zero_apply,inner_zero_left,Finset.sum_const_zero,integral_zero] using hNativePair.2.2
  have hFCondition : ∀ᵐx : Domain n∂volume,x∈ball (0:Domain n) 1∩ball a r → F x=0 :=
    (ae_restrict_iff' (measurableSet_ball.inter measurableSet_ball)).mp hZero
  letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  have hAE0 : ∀ᵐx : Domain n∂volume,x≠0 := by simp [ae_iff]
  have hOutsideInversion (y : Domain n) (hy : y∈ball (0:Domain n) 1) (hy0 : y≠0)
      (hNot : y∉ball a r) : I y∉ball a r := by
    intro hIy
    have hNorm : ‖y‖<1 := by simpa only [mem_ball_zero_iff] using hy
    have hExterior : 1<‖I y‖ := by
      rw [show ‖I y‖=‖y‖⁻¹ from norm_unit_inversion y]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hy0)).mpr hNorm
    have H := unit_inversion_image_exterior_boundary_ball_subset a ha r
      ⟨I y,⟨hIy,hExterior⟩,rfl⟩
    change I (I y)∈ball a r∩ball (0:Domain n) 1 at H
    rw [show I (I y)=y from inversion_inversion _ (by norm_num : (1:ℝ)≠0) _] at H
    exact hNot H.1
  have hφZero (y : Domain n) (hy : y∈ball (0:Domain n) 1) (hy0 : y≠0)
      (hNot : y∉ball a r) (i : Fin n) : fderiv ℝ φ y (EuclideanSpace.single i 1)=0 := by
    have hNotY : y∉tsupport ψ := fun h=>hNot (hsψ h)
    have hNotIy : I y∉tsupport ψ := fun h=>hOutsideInversion y hy hy0 hNot (hsψ h)
    have hDψ : fderiv ℝ ψ y=0 := fderiv_of_notMem_tsupport (𝕜:=ℝ) hNotY
    have hDψI : fderiv ℝ ψ (I y)=0 := fderiv_of_notMem_tsupport (𝕜:=ℝ) hNotIy
    have hψI : ψ (I y)=0 := image_eq_zero_of_notMem_tsupport hNotIy
    rw [hφD y (EuclideanSpace.single i 1) hy0]
    change fderiv ℝ ψ y (EuclideanSpace.single i 1)-
      ‖y‖^(2-(n:ℝ)) • fderiv ℝ ψ (I y) (fderiv ℝ I y (EuclideanSpace.single i 1))-
      ((2-(n:ℝ))*‖y‖^(-(n:ℝ))*inner ℝ y (EuclideanSpace.single i 1)) • ψ (I y)=0
    simp only [hDψ,hDψI,hψI,zero_apply,smul_zero,sub_zero]
  have hDensity : (fun x=>∑i : Fin n,inner ℝ (Du x i-F x i)
      (fderiv ℝ φ x (EuclideanSpace.single i 1))) =ᵐ[μ]
        (fun x=>∑i : Fin n,inner ℝ (Du x i) (fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
    filter_upwards [hFCondition.filter_mono (ae_mono Measure.restrict_le_self),
      hAE0.filter_mono (ae_mono Measure.restrict_le_self),ae_restrict_mem measurableSet_ball] with y hFy hy0 hy
    by_cases hIn : y∈ball a r
    · have hF0 : F y=0 := hFy ⟨hy,hIn⟩
      simp only [hF0,Pi.zero_apply,sub_zero]
    · simp only [hφZero y hy hy0 hIn,inner_zero_right,Finset.sum_const_zero]
  have hPhiIntegral : (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Du x i)
      (fderiv ℝ φ x (EuclideanSpace.single i 1)))=0 := by
    calc
      _=(∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Du x i-F x i)
        (fderiv ℝ φ x (EuclideanSpace.single i 1))) := (integral_congr_ae hDensity).symm
      _=0 := hGZero
  refine ⟨hGlobal.integrableOn,?_,?_⟩
  · simp only [inner_zero_left]
    exact integrable_zero _ _ _
  · calc
      (∫x in (ballDomain a r).val,∑i : Fin n,inner ℝ (Dext x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=
          ∫x,∑i : Fin n,inner ℝ (Dext x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        have hNot : x∉tsupport ψ := fun h=>hx (hsψ h)
        have hDψ : fderiv ℝ ψ x=0 := fderiv_of_notMem_tsupport (𝕜:=ℝ) hNot
        simp only [hDψ,zero_apply,inner_zero_right,Finset.sum_const_zero]
      _=(∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Du x i)
          (fderiv ℝ φ x (EuclideanSpace.single i 1))) := hGlobalEq
      _=0 := hPhiIntegral
      _= -(∫x in (ballDomain a r).val,inner ℝ (0:Ambient q) (ψ x)) := by
        simp only [inner_zero_left,integral_zero,neg_zero]

/-- One fixed actual Dirichlet L2 operator supplies the same original response before all boundary queries, with its literal odd reflection genuinely native and harmonic on every off-support boundary ball. -/
theorem exists_dirichlet_L2_operator_boundary_harmonic_unitBall {n q : ℕ} (hn : 2≤n) :
    let μ := volume.restrict (ball (0:Domain n) 1)
    let E : Gradient n q → Ambient (n*q) := fun A=>WithLp.toLp 2
      (fun k=>A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    ∃T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
      ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀Z,T (T Z)=T Z) ∧
      ∀(F : Domain n → Gradient n q) (hF : ∀i,MemLp (fun x=>F x i) 2 μ),
        let A := (memLp_hs_flatten F hF).toLp (fun x=>E (F x))
        let Q := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2
          (fun j : Fin q=>(T A) x (finProdFinEquiv (i,j)))
        ∃f : Domain n → Ambient q,HasZeroBoundaryValues (ballDomain (0:Domain n) 1) f Q ∧
          (∫x,hsNormSq (Q x) ∂μ)≤∫x,hsNormSq (F x) ∂μ ∧
          HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1) (fun x i=>Q x i-F x i) (fun _=>(0:Ambient q)) ∧
          ∀(a : Domain n),‖a‖=1 → ∀(r : ℝ),0<r →
            F =ᵐ[volume.restrict (ball (0:Domain n) 1∩ball a r)] (fun _=>(0:Gradient n q)) →
            let I := inversion (0:Domain n) 1
            let w := fun x : Domain n=>‖x‖^(2-(n:ℝ))
            let C := fun x i=>∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • Q (I x) j
            let U := fun x : Domain n=>if ‖x‖≤1 then f x else -w x • f (I x)
            let Dext := fun (x : Domain n) (i : Fin n)=>if ‖x‖≤1 then Q x i else
              -w x • C x i-((2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x (EuclideanSpace.single i 1)) • f (I x)
            MemW12 (ballDomain a r) U Dext ∧
              HolderToCK.WeakPoissonOn (ballDomain a r) Dext (fun _=>(0:Ambient q)) := by
  intro μ E
  obtain ⟨T,hNorm,hSelf,hIdem,H⟩ := exists_dirichlet_L2_operator_interior_offSupport_bounds_unitBall (q:=q) hn
  refine ⟨T,hNorm,hSelf,hIdem,?_⟩
  intro F hF A Q
  obtain ⟨f,hf,hEnergy,hEq,_hInterior⟩ := H F hF
  refine ⟨f,hf,hEnergy,hEq,?_⟩
  intro a ha r hr hZero
  exact odd_kelvin_native_weak_harmonic_boundary_ball hn a ha r hr f Q F hf hF hEq hZero

end StationaryHarmonicMaps.Analysis

end
