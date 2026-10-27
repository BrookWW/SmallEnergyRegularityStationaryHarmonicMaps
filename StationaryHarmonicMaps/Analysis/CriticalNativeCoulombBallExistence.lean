module

public import StationaryHarmonicMaps.Analysis.CriticalNativeCoulombExistence
public import StationaryHarmonicMaps.Analysis.NativeNaturalWeakPoisson
public import StationaryHarmonicMaps.Analysis.CoexactNativeDualTestBall
public import StationaryHarmonicMaps.Analysis.AffineMorreyScaling

/-!
# Critical native natural Coulomb frames on arbitrary balls

Positive affine transport preserves the native frame graph, special
orthogonality and the literal transformed connection. The full truncated
critical supremum is invariant, and every original native natural test
transports with its actual integrability. The constants precede the ball
and the original connection.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff
noncomputable section
namespace StationaryHarmonicMaps.Analysis

/-- An original small critical skew connection on any positive-radius ball
has a native special orthogonal Coulomb frame. Its literal connection has
the complete critical bound, every integrable native natural zero test,
and the original zero-forcing weak Poisson equation. -/
theorem exists_small_critical_native_coulomb_frame_ball
    (n : ℕ) (hn : 2≤n) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,
      ‖e.symm T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) :
    ∃ε C : ℝ,0<ε ∧ 0<C ∧
      ∀(a : Domain n) (r : ℝ),0<r →
      ∀(A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q)) (η : ℝ),
        (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball a r))) →
        (∀i,∀ᵐx∂volume.restrict (ball a r),star (A x i)= -(A x i)) →
        0≤η → η≤ε →
        criticalGradientMorreySquare (fun x i=>e.symm (A x i)) (ball a r)≤ENNReal.ofReal (η^2) →
        ∃(p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain a r) p Dp ∧
          (∀ᵐx∂volume.restrict (ball a r),star (e (p x))*e (p x)=1) ∧
          (∀ᵐx∂volume.restrict (ball a r),(e (p x)).det=1) ∧
          let Zop := fun x i=>star (e (p x))*e (Dp x i)+star (e (p x))*A x i*e (p x)
          let Z := fun x i=>e.symm (Zop x i)
          (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball a r))) ∧
          (∀ᵐx∂volume.restrict (ball a r),∀i,star (Zop x i)= -(Zop x i)) ∧
          (criticalGradientMorreySquare Dp (ball a r)+
            criticalGradientMorreySquare Z (ball a r)≤ENNReal.ofReal (C*η^2)) ∧
          (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
            MemW12 (ballDomain a r) ψ Dψ →
            IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Z x i) (Dψ x i)) (ball a r) volume ∧
            (∫x in ball a r,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) ∧
          HolderToCK.WeakPoissonOn (ballDomain a r) Z (fun _=>0) := by
  obtain ⟨ε,C,hε,hC,H⟩ := exists_small_critical_native_coulomb_frame n hn q e hE
  refine ⟨ε,C,hε,hC,?_⟩
  intro a r hr A η hA hSkew hη hSmall hCritical
  let A₀ := fun (x : Domain n) (i : Fin n)=>r • A (a+r • x) i
  have hA₀ (i : Fin n) : MemLp (fun x=>A₀ x i) 2 (volume.restrict (ball (0:Domain n) 1)) := by
    have hPull : MemLp (fun x=>r • A (a+r • (x-(0:Domain n))) i) 2
        (volume.restrict (ball (0:Domain n) (r/r))) :=
      (memLp_affineBall a (0:Domain n) hr r (hA i)).const_smul r
    simpa only [A₀,div_self hr.ne',sub_zero] using hPull
  have hSkew₀ (i : Fin n) : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
      star (A₀ x i)= -(A₀ x i) := by
    have hPull := ae_affineBall a (0:Domain n) hr r (hSkew i)
    simp only [div_self hr.ne',sub_zero] at hPull
    filter_upwards [hPull] with x hx
    simp only [A₀,star_smul,star_trivial,hx,smul_neg]
  have hCritical₀ : criticalGradientMorreySquare (fun x i=>e.symm (A₀ x i))
      (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) := by
    have hEq := criticalGradientMorreySquare_affineBall_encoded_operator
      e.symm.toContinuousLinearMap A a (0:Domain n) hr r
    simp only [div_self hr.ne',sub_zero] at hEq
    exact hEq.trans_le hCritical
  obtain ⟨p₀,Dp₀,hp₀,hOrth₀,hDet₀,hZLp₀,hZSkew₀,hSum₀,hNatural₀⟩ :=
    H A₀ η hA₀ hSkew₀ hη hSmall hCritical₀
  let p := fun x=>p₀ (r⁻¹ • (x-a))
  let Dp := fun x i=>r⁻¹ • Dp₀ (r⁻¹ • (x-a)) i
  let Zop₀ := fun x i=>star (e (p₀ x))*e (Dp₀ x i)+star (e (p₀ x))*A₀ x i*e (p₀ x)
  let Z₀ := fun x i=>e.symm (Zop₀ x i)
  let Zop := fun x i=>star (e (p x))*e (Dp x i)+star (e (p x))*A x i*e (p x)
  let Z := fun x i=>e.symm (Zop x i)
  have hRadius : (1:ℝ)/r⁻¹=r := by field_simp
  have hp : MemW12 (ballDomain a r) p Dp := by
    simpa only [hRadius,zero_add] using hp₀.affineBall_pullback a (inv_pos.mpr hr)
  have hOrth : ∀ᵐx∂volume.restrict (ball a r),star (e (p x))*e (p x)=1 := by
    simpa only [hRadius,zero_add] using ae_affineBall (0:Domain n) a (inv_pos.mpr hr) 1 hOrth₀
  have hDet : ∀ᵐx∂volume.restrict (ball a r),(e (p x)).det=1 := by
    simpa only [hRadius,zero_add] using ae_affineBall (0:Domain n) a (inv_pos.mpr hr) 1 hDet₀
  have hZopEq (x : Domain n) (i : Fin n) : Zop x i=r⁻¹ • Zop₀ (r⁻¹ • (x-a)) i := by
    have hInverse : a+r • (r⁻¹ • (x-a))=x := by
      rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,add_sub_cancel]
    dsimp only [Zop,Zop₀,p,Dp,A₀]
    rw [hInverse]
    ext v
    simp only [add_apply,mul_apply_eq_comp,smul_apply,map_smul,smul_add,smul_smul,
      inv_mul_cancel₀ hr.ne',one_smul]
  have hZEq : Z=(fun x i=>r⁻¹ • Z₀ (r⁻¹ • (x-a)) i) := by
    funext x i
    change e.symm (Zop x i)=r⁻¹ • e.symm (Zop₀ (r⁻¹ • (x-a)) i)
    rw [hZopEq,map_smul]
  have hZLp (i : Fin n) : MemLp (fun x=>Z x i) 2 (volume.restrict (ball a r)) := by
    have hPull : MemLp (fun x=>r⁻¹ • Z₀ ((0:Domain n)+r⁻¹ • (x-a)) i) 2
        (volume.restrict (ball a ((1:ℝ)/r⁻¹))) :=
      (memLp_affineBall (0:Domain n) a (inv_pos.mpr hr) 1 (hZLp₀ i)).const_smul r⁻¹
    rw [hZEq]
    simpa only [hRadius,zero_add] using hPull
  have hZSkew : ∀ᵐx∂volume.restrict (ball a r),∀i,star (Zop x i)= -(Zop x i) := by
    have hPull := ae_affineBall (0:Domain n) a (inv_pos.mpr hr) 1 hZSkew₀
    simp only [hRadius,zero_add] at hPull
    filter_upwards [hPull] with x hx
    intro i
    rw [hZopEq,star_smul,star_trivial,hx i,smul_neg]
  have hDpCritical : criticalGradientMorreySquare Dp (ball a r)=
      criticalGradientMorreySquare Dp₀ (ball (0:Domain n) 1) := by
    simpa only [hRadius,zero_add] using criticalGradientMorreySquare_affineBall
      (0:Domain n) a (inv_pos.mpr hr) 1 Dp₀
  have hZCritical : criticalGradientMorreySquare Z (ball a r)=
      criticalGradientMorreySquare Z₀ (ball (0:Domain n) 1) := by
    rw [hZEq]
    simpa only [hRadius,zero_add] using criticalGradientMorreySquare_affineBall
      (0:Domain n) a (inv_pos.mpr hr) 1 Z₀
  have hSum : criticalGradientMorreySquare Dp (ball a r)+
      criticalGradientMorreySquare Z (ball a r)≤ENNReal.ofReal (C*η^2) := by
    rw [hDpCritical,hZCritical]
    exact hSum₀
  have hNatural (ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q))
      (hψ : MemW12 (ballDomain a r) ψ Dψ) :
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Z x i) (Dψ x i)) (ball a r) volume ∧
      (∫x in ball a r,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0 := by
    refine ⟨integrable_column_pairing (volume.restrict (ball a r)) Z Dψ hZLp hψ.2.2,?_⟩
    have hTests := natural_solenoidal_affineBall (0:Domain n) a (inv_pos.mpr hr) 1 Z₀
      (fun ψ Dψ hψ=>(hNatural₀ ψ Dψ hψ).2)
    have hZero : (∫x in ball a r,∑i : Fin n,
        inner ℝ (Z₀ (r⁻¹ • (x-a)) i) (Dψ x i))=0 := by
      simpa only [hRadius,zero_add] using hTests ψ Dψ (by simpa only [hRadius] using hψ)
    rw [hZEq]
    simp only [real_inner_smul_left,←Finset.mul_sum,integral_const_mul,hZero,mul_zero]
  exact ⟨p,Dp,hp,hOrth,hDet,hZLp,hZSkew,hSum,hNatural,
    weakPoisson_zero_of_native_natural (ballDomain a r) Z hZLp (fun ψ Dψ hψ=>(hNatural ψ Dψ hψ).2)⟩

/-- An original small critical skew connection on any positive-radius ball
has a native special orthogonal Coulomb frame. Its literal connection has
the complete critical bound, every integrable native natural zero test,
and the original zero-forcing weak Poisson equation. -/
theorem effective_small_critical_native_coulomb_frame_ball
    (n : ℕ) (hn : 2≤n) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,
      ‖e.symm T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) :
    ∀(a : Domain n) (r : ℝ),0<r →
      ∀(A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q)) (η : ℝ),
        (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball a r))) →
        (∀i,∀ᵐx∂volume.restrict (ball a r),star (A x i)= -(A x i)) →
        0≤η → η≤(effectiveCoulombFrameSmallness n q : ℝ) →
        criticalGradientMorreySquare (fun x i=>e.symm (A x i)) (ball a r)≤ENNReal.ofReal (η^2) →
        ∃(p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain a r) p Dp ∧
          (∀ᵐx∂volume.restrict (ball a r),star (e (p x))*e (p x)=1) ∧
          (∀ᵐx∂volume.restrict (ball a r),(e (p x)).det=1) ∧
          let Zop := fun x i=>star (e (p x))*e (Dp x i)+star (e (p x))*A x i*e (p x)
          let Z := fun x i=>e.symm (Zop x i)
          (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball a r))) ∧
          (∀ᵐx∂volume.restrict (ball a r),∀i,star (Zop x i)= -(Zop x i)) ∧
          (criticalGradientMorreySquare Dp (ball a r)+
            criticalGradientMorreySquare Z (ball a r)≤ENNReal.ofReal ((effectiveCoulombFrameGradientConstant n q : ℝ)*η^2)) ∧
          (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
            MemW12 (ballDomain a r) ψ Dψ →
            IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Z x i) (Dψ x i)) (ball a r) volume ∧
            (∫x in ball a r,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) ∧
          HolderToCK.WeakPoissonOn (ballDomain a r) Z (fun _=>0) := by
  let C : ℝ := effectiveCoulombFrameGradientConstant n q
  have H := effective_small_critical_native_coulomb_frame n hn q e hE
  intro a r hr A η hA hSkew hη hSmall hCritical
  let A₀ := fun (x : Domain n) (i : Fin n)=>r • A (a+r • x) i
  have hA₀ (i : Fin n) : MemLp (fun x=>A₀ x i) 2 (volume.restrict (ball (0:Domain n) 1)) := by
    have hPull : MemLp (fun x=>r • A (a+r • (x-(0:Domain n))) i) 2
        (volume.restrict (ball (0:Domain n) (r/r))) :=
      (memLp_affineBall a (0:Domain n) hr r (hA i)).const_smul r
    simpa only [A₀,div_self hr.ne',sub_zero] using hPull
  have hSkew₀ (i : Fin n) : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
      star (A₀ x i)= -(A₀ x i) := by
    have hPull := ae_affineBall a (0:Domain n) hr r (hSkew i)
    simp only [div_self hr.ne',sub_zero] at hPull
    filter_upwards [hPull] with x hx
    simp only [A₀,star_smul,star_trivial,hx,smul_neg]
  have hCritical₀ : criticalGradientMorreySquare (fun x i=>e.symm (A₀ x i))
      (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) := by
    have hEq := criticalGradientMorreySquare_affineBall_encoded_operator
      e.symm.toContinuousLinearMap A a (0:Domain n) hr r
    simp only [div_self hr.ne',sub_zero] at hEq
    exact hEq.trans_le hCritical
  obtain ⟨p₀,Dp₀,hp₀,hOrth₀,hDet₀,hZLp₀,hZSkew₀,hSum₀,hNatural₀⟩ :=
    H A₀ η hA₀ hSkew₀ hη hSmall hCritical₀
  let p := fun x=>p₀ (r⁻¹ • (x-a))
  let Dp := fun x i=>r⁻¹ • Dp₀ (r⁻¹ • (x-a)) i
  let Zop₀ := fun x i=>star (e (p₀ x))*e (Dp₀ x i)+star (e (p₀ x))*A₀ x i*e (p₀ x)
  let Z₀ := fun x i=>e.symm (Zop₀ x i)
  let Zop := fun x i=>star (e (p x))*e (Dp x i)+star (e (p x))*A x i*e (p x)
  let Z := fun x i=>e.symm (Zop x i)
  have hRadius : (1:ℝ)/r⁻¹=r := by field_simp
  have hp : MemW12 (ballDomain a r) p Dp := by
    simpa only [hRadius,zero_add] using hp₀.affineBall_pullback a (inv_pos.mpr hr)
  have hOrth : ∀ᵐx∂volume.restrict (ball a r),star (e (p x))*e (p x)=1 := by
    simpa only [hRadius,zero_add] using ae_affineBall (0:Domain n) a (inv_pos.mpr hr) 1 hOrth₀
  have hDet : ∀ᵐx∂volume.restrict (ball a r),(e (p x)).det=1 := by
    simpa only [hRadius,zero_add] using ae_affineBall (0:Domain n) a (inv_pos.mpr hr) 1 hDet₀
  have hZopEq (x : Domain n) (i : Fin n) : Zop x i=r⁻¹ • Zop₀ (r⁻¹ • (x-a)) i := by
    have hInverse : a+r • (r⁻¹ • (x-a))=x := by
      rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,add_sub_cancel]
    dsimp only [Zop,Zop₀,p,Dp,A₀]
    rw [hInverse]
    ext v
    simp only [add_apply,mul_apply_eq_comp,smul_apply,map_smul,smul_add,smul_smul,
      inv_mul_cancel₀ hr.ne',one_smul]
  have hZEq : Z=(fun x i=>r⁻¹ • Z₀ (r⁻¹ • (x-a)) i) := by
    funext x i
    change e.symm (Zop x i)=r⁻¹ • e.symm (Zop₀ (r⁻¹ • (x-a)) i)
    rw [hZopEq,map_smul]
  have hZLp (i : Fin n) : MemLp (fun x=>Z x i) 2 (volume.restrict (ball a r)) := by
    have hPull : MemLp (fun x=>r⁻¹ • Z₀ ((0:Domain n)+r⁻¹ • (x-a)) i) 2
        (volume.restrict (ball a ((1:ℝ)/r⁻¹))) :=
      (memLp_affineBall (0:Domain n) a (inv_pos.mpr hr) 1 (hZLp₀ i)).const_smul r⁻¹
    rw [hZEq]
    simpa only [hRadius,zero_add] using hPull
  have hZSkew : ∀ᵐx∂volume.restrict (ball a r),∀i,star (Zop x i)= -(Zop x i) := by
    have hPull := ae_affineBall (0:Domain n) a (inv_pos.mpr hr) 1 hZSkew₀
    simp only [hRadius,zero_add] at hPull
    filter_upwards [hPull] with x hx
    intro i
    rw [hZopEq,star_smul,star_trivial,hx i,smul_neg]
  have hDpCritical : criticalGradientMorreySquare Dp (ball a r)=
      criticalGradientMorreySquare Dp₀ (ball (0:Domain n) 1) := by
    simpa only [hRadius,zero_add] using criticalGradientMorreySquare_affineBall
      (0:Domain n) a (inv_pos.mpr hr) 1 Dp₀
  have hZCritical : criticalGradientMorreySquare Z (ball a r)=
      criticalGradientMorreySquare Z₀ (ball (0:Domain n) 1) := by
    rw [hZEq]
    simpa only [hRadius,zero_add] using criticalGradientMorreySquare_affineBall
      (0:Domain n) a (inv_pos.mpr hr) 1 Z₀
  have hSum : criticalGradientMorreySquare Dp (ball a r)+
      criticalGradientMorreySquare Z (ball a r)≤ENNReal.ofReal (C*η^2) := by
    rw [hDpCritical,hZCritical]
    exact hSum₀
  have hNatural (ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q))
      (hψ : MemW12 (ballDomain a r) ψ Dψ) :
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Z x i) (Dψ x i)) (ball a r) volume ∧
      (∫x in ball a r,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0 := by
    refine ⟨integrable_column_pairing (volume.restrict (ball a r)) Z Dψ hZLp hψ.2.2,?_⟩
    have hTests := natural_solenoidal_affineBall (0:Domain n) a (inv_pos.mpr hr) 1 Z₀
      (fun ψ Dψ hψ=>(hNatural₀ ψ Dψ hψ).2)
    have hZero : (∫x in ball a r,∑i : Fin n,
        inner ℝ (Z₀ (r⁻¹ • (x-a)) i) (Dψ x i))=0 := by
      simpa only [hRadius,zero_add] using hTests ψ Dψ (by simpa only [hRadius] using hψ)
    rw [hZEq]
    simp only [real_inner_smul_left,←Finset.mul_sum,integral_const_mul,hZero,mul_zero]
  exact ⟨p,Dp,hp,hOrth,hDet,hZLp,hZSkew,hSum,hNatural,
    weakPoisson_zero_of_native_natural (ballDomain a r) Z hZLp (fun ψ Dψ hψ=>(hNatural ψ Dψ hψ).2)⟩

/-- An original small critical skew connection on any positive-radius ball
has a native special orthogonal Coulomb frame. Its literal connection has
the complete critical bound, every integrable native natural zero test,
and the original zero-forcing weak Poisson equation. -/
theorem exists_small_critical_native_coulomb_frame_ball_effective
    (n : ℕ) (hn : 2≤n) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,
      ‖e.symm T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) :
    ∃ε C : ℝ,0<ε ∧ 0<C ∧
      ε = (effectiveCoulombFrameSmallness n q : ℝ) ∧
      C = (effectiveCoulombFrameGradientConstant n q : ℝ) ∧
      ∀(a : Domain n) (r : ℝ),0<r →
      ∀(A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q)) (η : ℝ),
        (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball a r))) →
        (∀i,∀ᵐx∂volume.restrict (ball a r),star (A x i)= -(A x i)) →
        0≤η → η≤ε →
        criticalGradientMorreySquare (fun x i=>e.symm (A x i)) (ball a r)≤ENNReal.ofReal (η^2) →
        ∃(p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain a r) p Dp ∧
          (∀ᵐx∂volume.restrict (ball a r),star (e (p x))*e (p x)=1) ∧
          (∀ᵐx∂volume.restrict (ball a r),(e (p x)).det=1) ∧
          let Zop := fun x i=>star (e (p x))*e (Dp x i)+star (e (p x))*A x i*e (p x)
          let Z := fun x i=>e.symm (Zop x i)
          (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball a r))) ∧
          (∀ᵐx∂volume.restrict (ball a r),∀i,star (Zop x i)= -(Zop x i)) ∧
          (criticalGradientMorreySquare Dp (ball a r)+
            criticalGradientMorreySquare Z (ball a r)≤ENNReal.ofReal (C*η^2)) ∧
          (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
            MemW12 (ballDomain a r) ψ Dψ →
            IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Z x i) (Dψ x i)) (ball a r) volume ∧
            (∫x in ball a r,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) ∧
          HolderToCK.WeakPoissonOn (ballDomain a r) Z (fun _=>0) := by
  refine ⟨(effectiveCoulombFrameSmallness n q : ℝ), (effectiveCoulombFrameGradientConstant n q : ℝ),
    ?_, ?_, rfl, rfl, effective_small_critical_native_coulomb_frame_ball n hn q e hE⟩
  · exact_mod_cast effectiveCoulombFrameSmallness_pos n hn q
  · exact_mod_cast effectiveCoulombFrameGradientConstant_pos n hn q

end StationaryHarmonicMaps.Analysis
end
