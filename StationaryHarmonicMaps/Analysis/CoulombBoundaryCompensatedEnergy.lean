module

public import StationaryHarmonicMaps.Analysis.BoundaryCoexactCompensatedEnergy
public import StationaryHarmonicMaps.Analysis.NativeCoexactUniqueness
public import StationaryHarmonicMaps.Analysis.OrthogonalCoefficientBounds
public import StationaryHarmonicMaps.Analysis.EffectiveMatrixCoefficientBounds
public import StationaryHarmonicMaps.Analysis.SkewCoulombNearEnergy

/-!
# Full-ball compensation for the same nonlinear Coulomb response

Natural-response uniqueness transfers the constructed compensated bound
to the originally displayed relative response. Applied to the true
logarithmic derivative, it controls the same nonlinear coexact field on
the entire ball. The original critical frame norm remains an a priori input.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The compensated energy bound applies to every actual natural response
of the same bilinear gradient, identified through its native complement. -/
theorem exists_same_boundary_coexact_compensated_energy (n : ℕ) (hn : 2≤n)
    (m k : ℕ) (B : Ambient m →L[ℝ] (Ambient m →L[ℝ] Ambient k)) :
    ∃C : ℝ,0<C ∧ ∀ (u : Domain n → Ambient m) (Du : Domain n → Gradient n m)
      (η M : ℝ),MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M) →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀ (Q : Domain n → Gradient n k) (v : Domain n → Ambient k),
        (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
        MemW12 (ballDomain (0 : Domain n) 1) v (fun x i=>B (u x) (Du x i)-Q x i) →
        (∀ (ψ : Domain n → Ambient k) (Dψ : Domain n → Gradient n k),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) →
        (∫x in ball (0 : Domain n) 1,hsNormSq (Q x))≤
          C*η^2*(∫x in ball (0 : Domain n) 1,hsNormSq (Du x)) := by
  obtain ⟨C,hC,HC⟩ := exists_boundary_coexact_compensated_energy n hn m k B
  refine ⟨C,hC,?_⟩
  intro u Du η M hu hη hBound hCritical Q v hQ hv hNatural
  obtain ⟨b,Db,P,f,Df,hf,_hb,hP,_hSkew,_hClosed,_hDiv,_hNormal,hPN,hDecomp,hBoundP⟩ :=
    HC u Du η M hu hη hBound hCritical
  let F := fun x i=>B (u x) (Du x i)
  have hF (i : Fin n) : MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1)) :=
    ((hv.2.2 i).add (hQ i)).ae_eq (Eventually.of_forall fun x=>sub_add_cancel _ _)
  have hf' : MemW12 (ballDomain (0 : Domain n) 1) f (fun x i=>F x i-P x i) := by
    apply hf.congr_ae (Eventually.of_forall fun _=>rfl)
    filter_upwards [hDecomp] with x hx
    funext i
    exact (eq_sub_iff_add_eq.mpr (hx i).symm)
  have hEqual := native_coexact_response_unique_ae (ballDomain (0 : Domain n) 1)
    F Q P hF hQ hP v f hv hf' hNatural (fun ψ Dψ hψ=>(hPN ψ Dψ hψ).2)
  exact (integral_congr_ae (hEqual.mono fun _ hx=>congrArg hsNormSq hx)).le.trans hBoundP

/-- The original critical orthogonal frame controls its same natural
nonlinear logarithmic-derivative response over the whole ball. -/
theorem exists_coulomb_boundary_compensated_energy (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) :
    ∃C : ℝ,0<C ∧ ∀ (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
      (η : ℝ),MemW12 (ballDomain (0 : Domain n) 1) p Dp →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (p x))*R (p x)=1) → 0≤η →
      criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀ (Q : Domain n → Gradient n (q*q)) (v : Domain n → Ambient (q*q)),
        (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
        MemW12 (ballDomain (0 : Domain n) 1) v
          (fun x i=>E (star (R (p x))*R (Dp x i))-Q x i) →
        (∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) →
        (∫x in ball (0 : Domain n) 1,hsNormSq (Q x))≤
          C*η^2*(∫x in ball (0 : Domain n) 1,hsNormSq (Dp x)) := by
  let O := Ambient q →L[ℝ] Ambient q
  let M := Ambient (q*q)
  let S : M →L[ℝ] O := (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).toContinuousLinearMap.comp R
  let mulOp := ContinuousLinearMap.compL ℝ (Ambient q) (Ambient q) (Ambient q)
  let post := ContinuousLinearMap.compL ℝ M O M
  let B : M →L[ℝ] (M →L[ℝ] M) := (post E).comp (mulOp.bilinearComp S R)
  have hB (z w : M) : B z w=E (star (R z)*R w) := rfl
  obtain ⟨C,hC,HC⟩ := exists_same_boundary_coexact_compensated_energy n hn (q*q) (q*q) B
  refine ⟨C,hC,?_⟩
  intro p Dp η hp hOrth hη hCritical Q v hQ hv hNatural
  apply HC p Dp η (Real.sqrt (q : ℝ)) hp hη
    (ae_orthogonal_coordinates_bound (Ω:=ballDomain (0 : Domain n) 1) E R hER hE p hOrth) hCritical Q v hQ
  · simpa only [hB] using hv
  · exact hNatural

/-- The compensated energy bound applies to every actual natural response
of the same bilinear gradient, identified through its native complement. -/
theorem effective_same_boundary_coexact_compensated_energy (n : ℕ) (hn : 2≤n)
    (m k : ℕ) (coefficientBound : ℚ) (hBound : 0 ≤ coefficientBound)
    (B : Ambient m →L[ℝ] (Ambient m →L[ℝ] Ambient k))
    (hB : ‖B‖ ≤ (coefficientBound : ℝ)) :
    ∀ (u : Domain n → Ambient m) (Du : Domain n → Gradient n m)
      (η M : ℝ),MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M) →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀ (Q : Domain n → Gradient n k) (v : Domain n → Ambient k),
        (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
        MemW12 (ballDomain (0 : Domain n) 1) v (fun x i=>B (u x) (Du x i)-Q x i) →
        (∀ (ψ : Domain n → Ambient k) (Dψ : Domain n → Gradient n k),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) →
        (∫x in ball (0 : Domain n) 1,hsNormSq (Q x))≤
          (effectiveCenteredCoexactConstant n m coefficientBound : ℝ)*η^2*(∫x in ball (0 : Domain n) 1,hsNormSq (Du x)) := by
  have HC := effective_boundary_coexact_compensated_energy n hn m k coefficientBound hBound B hB
  intro u Du η M hu hη hBound hCritical Q v hQ hv hNatural
  obtain ⟨b,Db,P,f,Df,hf,_hb,hP,_hSkew,_hClosed,_hDiv,_hNormal,hPN,hDecomp,hBoundP⟩ :=
    HC u Du η M hu hη hBound hCritical
  let F := fun x i=>B (u x) (Du x i)
  have hF (i : Fin n) : MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1)) :=
    ((hv.2.2 i).add (hQ i)).ae_eq (Eventually.of_forall fun x=>sub_add_cancel _ _)
  have hf' : MemW12 (ballDomain (0 : Domain n) 1) f (fun x i=>F x i-P x i) := by
    apply hf.congr_ae (Eventually.of_forall fun _=>rfl)
    filter_upwards [hDecomp] with x hx
    funext i
    exact (eq_sub_iff_add_eq.mpr (hx i).symm)
  have hEqual := native_coexact_response_unique_ae (ballDomain (0 : Domain n) 1)
    F Q P hF hQ hP v f hv hf' hNatural (fun ψ Dψ hψ=>(hPN ψ Dψ hψ).2)
  exact (integral_congr_ae (hEqual.mono fun _ hx=>congrArg hsNormSq hx)).le.trans hBoundP

@[expose] def effectiveCoulombCompensatedEnergyConstant (n q : ℕ) : ℚ :=
  effectiveCenteredCoexactConstant n (q*q) ((q + 1 : ℕ) : ℚ)

theorem effectiveCoulombCompensatedEnergyConstant_pos (n : ℕ) (hn : 2 ≤ n) (q : ℕ) :
    0 < effectiveCoulombCompensatedEnergyConstant n q :=
  effectiveCenteredCoexactConstant_pos n hn (q*q) (by positivity)

/-- The original critical orthogonal frame controls its same natural
nonlinear logarithmic-derivative response over the whole ball. -/
theorem effective_coulomb_boundary_compensated_energy (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) :
    ∀ (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
      (η : ℝ),MemW12 (ballDomain (0 : Domain n) 1) p Dp →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (p x))*R (p x)=1) → 0≤η →
      criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀ (Q : Domain n → Gradient n (q*q)) (v : Domain n → Ambient (q*q)),
        (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
        MemW12 (ballDomain (0 : Domain n) 1) v
          (fun x i=>E (star (R (p x))*R (Dp x i))-Q x i) →
        (∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) →
        (∫x in ball (0 : Domain n) 1,hsNormSq (Q x))≤
          (effectiveCoulombCompensatedEnergyConstant n q : ℝ)*η^2*(∫x in ball (0 : Domain n) 1,hsNormSq (Dp x)) := by
  let Bs := skewLogarithmicAlternation E R
  have hBs : ‖Bs‖ ≤ (((q + 1 : ℕ) : ℚ) : ℝ) := by
    simpa only [Bs, Rat.cast_natCast, Nat.cast_add, Nat.cast_one, Rat.cast_add, Rat.cast_one] using
      skewLogarithmicAlternation_norm_le q E R hER hE
  have HC := effective_same_boundary_coexact_compensated_energy n hn (q*q) (q*q)
    ((q + 1 : ℕ) : ℚ) (by positivity) Bs hBs
  intro p Dp η hp hOrth hη hCritical Q v hQ hv hNatural
  have hBound := ae_orthogonal_coordinates_bound (Ω:=ballDomain (0 : Domain n) 1) E R hER hE p hOrth
  have hLog := ae_native_orthogonal_logarithmic_alternation E R p Dp hp.to_memW12Loc
    (Real.sqrt (q : ℝ)) hBound hOrth
  have hvAlt : MemW12 (ballDomain (0 : Domain n) 1) v
      (fun x i => Bs (p x) (Dp x i) - Q x i) := by
    apply hv.congr_ae (Eventually.of_forall fun _ => rfl)
    filter_upwards [hLog] with x hx
    funext i
    rw [hx i]
  exact HC p Dp η (Real.sqrt (q : ℝ)) hp hη hBound hCritical Q v hQ hvAlt hNatural

end StationaryHarmonicMaps.Analysis

end
