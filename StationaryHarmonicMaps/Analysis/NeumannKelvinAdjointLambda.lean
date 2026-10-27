module

public import StationaryHarmonicMaps.Analysis.NeumannKelvinAdjointDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The reciprocal radial parameter of the actual Neumann adjoint

The genuine substitution t = r / λ preserves both positive endpoints and
their orientation. It gives the original test and its actual derivative at
the same dilation sample λ⁻¹y, with the exact reciprocal Jacobian weight.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- A continuous original field has the exact oriented reciprocal-parameter radial integral, for every real power and positive endpoints. -/
theorem neumann_adjoint_radial_integral_eq_reciprocal {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (p : ℝ) (f : Domain n → G) (hf : Continuous f) (x : Domain n)
    (r upper : ℝ) (hr : 0<r) (hUpper : 0<upper) :
    (∫t in r⁻¹..upper,t^p • f (t • (r⁻¹ • x)))=
      r^(p+1) • (∫s in (r/upper)..r^2,s^(-p-2) • f (s⁻¹ • x)) := by
  let a := r/upper
  let b := r^2
  let T := fun s : ℝ=>r*s⁻¹
  let DT := fun s : ℝ=> -r*(s^2)⁻¹
  let g := fun t : ℝ=>t^p • f (t • (r⁻¹ • x))
  have ha : 0<a := div_pos hr hUpper
  have hb : 0<b := sq_pos_of_pos hr
  have hsPos (s : ℝ) (hs : s∈uIcc a b) : 0<s := (lt_min ha hb).trans_le hs.1
  have hT (s : ℝ) (hs : s∈uIcc a b) : HasDerivAt T (DT s) s := by
    have H := (hasDerivAt_inv (hsPos s hs).ne').const_mul r
    exact H.congr_deriv (by change r*(-(s^2)⁻¹)= -r*(s^2)⁻¹;ring)
  have hDT : ContinuousOn DT (uIcc a b) := by
    intro s hs
    exact (continuousAt_const.mul ((continuousAt_id.pow 2).inv₀
      (pow_ne_zero 2 (hsPos s hs).ne'))).continuousWithinAt
  have hg : ContinuousOn g (T '' uIcc a b) := by
    rintro t ⟨s,hs,rfl⟩
    have hTp : 0<T s := mul_pos hr (inv_pos.mpr (hsPos s hs))
    exact ((Real.continuousAt_rpow_const (T s) p (Or.inl hTp.ne')).smul
      (hf.continuousAt.comp (continuousAt_id.smul continuousAt_const))).continuousWithinAt
  have H := intervalIntegral.integral_deriv_smul_comp' hT hDT hg
  have hTa : T a=upper := by dsimp only [T,a];field_simp
  have hTb : T b=r⁻¹ := by dsimp only [T,b];field_simp
  rw [hTa,hTb] at H
  have hPoint (s : ℝ) (hs : s∈uIcc a b) : DT s • (g ∘ T) s=
      -(r^(p+1)) • (s^(-p-2) • f (s⁻¹ • x)) := by
    have hsP : 0<s := hsPos s hs
    have hSample : T s • (r⁻¹ • x)=s⁻¹ • x := by
      dsimp only [T]
      rw [smul_smul]
      congr 1
      field_simp
    have hInv2 : (s^2)⁻¹=s^(-2 : ℝ) := by rw [Real.rpow_neg hsP.le,Real.rpow_two]
    have hSP : (s^2)⁻¹*s^(-p)=s^(-p-2) := by
      rw [hInv2,← Real.rpow_add hsP]
      congr 1
      ring
    have hRP : r*r^p=r^(p+1) := (mul_comm _ _).trans (Real.rpow_add_one hr.ne' p).symm
    have hWeight : DT s*(T s)^p= -(r^(p+1))*s^(-p-2) := by
      dsimp only [DT,T]
      rw [Real.mul_rpow hr.le (inv_nonneg.mpr hsP.le),Real.inv_rpow hsP.le,
        ← Real.rpow_neg hsP.le]
      calc
        _ = -(r*r^p)*((s^2)⁻¹*s^(-p)) := by ring
        _ = _ := by rw [hSP,hRP]
    change DT s • ((T s)^p • f (T s • (r⁻¹ • x)))=_
    rw [hSample,smul_smul,hWeight,← smul_smul]
  rw [intervalIntegral.integral_congr hPoint,intervalIntegral.integral_smul] at H
  have hReverse : (∫t in upper..r⁻¹,g t)= -(∫t in r⁻¹..upper,g t) :=
    intervalIntegral.integral_symm _ _
  rw [hReverse] at H
  have H' : r^(p+1) • (∫s in a..b,s^(-p-2) • f (s⁻¹ • x))=
      ∫t in r⁻¹..upper,g t := by
    simpa only [neg_smul,neg_inj] using H
  exact H'.symm

/-- The same native adjoint has the true reciprocal-window derivative with weight λ to the power minus n. -/
theorem exists_neumann_kelvin_adjoint_with_reciprocal_gradient {n q : ℕ}
    (upper : ℝ) (hUpper : 0<upper) (ψ : Domain n → Ambient q)
    (hψ : ContDiff ℝ ∞ ψ) (hZero : ∀z : Domain n,upper≤‖z‖ → ψ z=0) :
    ∃ φ : Domain n → Ambient q,ContDiff ℝ ∞ φ ∧
      MemW12 (ballDomain (0 : Domain n) 1) φ
        (fun x i=>fderiv ℝ φ x (EuclideanSpace.single i 1)) ∧
      (∀y : Domain n,y≠0 → φ y=neumannKelvinRay upper ψ (‖y‖⁻¹ • y) ‖y‖) ∧
      (∀y : Domain n,‖y‖≤upper⁻¹ → φ y=0) ∧
      (∀ (y v : Domain n),y≠0 →
        let r := ‖y‖
        let T := fun w : Domain n=>w-(inner ℝ y w/r^2) • y
        fderiv ℝ φ y v=r^(2-(n : ℝ)) • fderiv ℝ ψ (inversion (0 : Domain n) 1 y)
          (fderiv ℝ (inversion (0 : Domain n) 1) y v)+((n : ℝ)-2) •
          (r^((n : ℝ)-2) • (∫s in (r/upper)..r^2,s^(-(n : ℝ)) •
            fderiv ℝ ψ (s⁻¹ • y) (T v)))) ∧
      (∀ (a : Domain n) (s : ℝ),‖a‖=1 → tsupport ψ⊆ball a s →
        ∀y : Domain n,‖y‖≤1 → y∉ball a s → φ y=0) ∧
      ∀ (a : Domain n) (s : ℝ),‖a‖=1 → tsupport ψ⊆ball a s →
        ∀y : Domain n,‖y‖<1 → s<dist y a → fderiv ℝ φ y=0 := by
  obtain ⟨φ,hφ,hNative,hEq,hNear,hDerivative,hSupport,hGradSupport⟩ :=
    exists_neumann_kelvin_adjoint_with_gradient upper hUpper ψ hψ hZero
  refine ⟨φ,hφ,hNative,hEq,hNear,?_,hSupport,hGradSupport⟩
  intro y v hy r T
  let θ := r⁻¹ • y
  have hr : 0<r := norm_pos_iff.mpr hy
  have hT : T v=v-(inner ℝ θ v) • θ := by
    simp only [T,θ,real_inner_smul_left,smul_smul,div_eq_mul_inv,← inv_pow]
    congr 2
    ring
  have H := hDerivative y v hy
  change fderiv ℝ φ y v=r^(2-(n : ℝ)) • fderiv ℝ ψ (inversion (0 : Domain n) 1 y)
    (fderiv ℝ (inversion (0 : Domain n) 1) y v)+(((n : ℝ)-2)/r) •
      (∫t in r⁻¹..upper,t^((n : ℝ)-2) • fderiv ℝ ψ (t • θ) (v-(inner ℝ θ v) • θ)) at H
  rw [← hT] at H
  have hChange := neumann_adjoint_radial_integral_eq_reciprocal ((n : ℝ)-2)
    (fun z=>fderiv ℝ ψ z (T v)) ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
    y r upper hr hUpper
  have hExponent : -((n : ℝ)-2)-2= -(n : ℝ) := by ring
  rw [hExponent] at hChange
  rw [hChange] at H
  have hWeight : (((n : ℝ)-2)/r)*r^(((n : ℝ)-2)+1)=((n : ℝ)-2)*r^((n : ℝ)-2) := by
    rw [Real.rpow_add_one hr.ne',div_eq_mul_inv]
    field_simp
  rw [smul_smul,hWeight,← smul_smul] at H
  exact H

end StationaryHarmonicMaps.Analysis

end
