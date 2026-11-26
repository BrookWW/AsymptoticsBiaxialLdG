module

public import Thesis.Upstream.AmbientGradientHilbert
public import Thesis.Variational.DifferenceQuotientEnergyAlgebra
import StratificationTheory.Foundation.CompactSobolevCutoff

/-! The tangential difference quotient estimate for the actual elliptic graph. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff ENNReal RealInnerProductSpace

namespace Thesis

/-- Cutoff times the normalized difference of an original weak field. -/
@[expose] def differenceQuotientTestValue {n q : ℕ} (χ : Domain n → ℝ)
    (i : Fin n) (h : ℝ) (u : Domain n → Ambient q) (x : Domain n) : Ambient q :=
  (χ x)^2 • ambientDifferenceQuotient i h u x

/-- The product rule columns of the squared-cutoff difference test. -/
@[expose] def differenceQuotientTestColumns {n q : ℕ} (χ : Domain n → ℝ)
    (i : Fin n) (h : ℝ) (u : Domain n → Ambient q)
    (D : Domain n → HarmonicMaps.Gradient n q) (x : Domain n) (j : Fin n) : Ambient q :=
  (2*χ x*(fderiv ℝ χ x (EuclideanSpace.single j 1))) • ambientDifferenceQuotient i h u x +
    (χ x)^2 • ambientDifferenceQuotient i h (fun y => D y j) x

/-- The displayed cutoff test belongs to the actual whole-space weak graph. -/
theorem memW12_differenceQuotientTest {n q : ℕ} {χ : Domain n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hu : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) u D) (i : Fin n) (h : ℝ) :
    MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) (differenceQuotientTestValue χ i h u)
      (differenceQuotientTestColumns χ i h u D) := by
  let c (x : Domain n) := χ x * χ x
  have hc : ContDiff ℝ ∞ c := hχ.mul hχ
  have hComp : HasCompactSupport c := hcχ.mul_right
  have hh := (memW12_differenceQuotient_univ hu i h).to_memW12Loc.smoothCutoff_univ
    hc hComp (subset_univ _)
  have hVal : (fun x => c x • ambientDifferenceQuotient i h u x) = differenceQuotientTestValue χ i h u := by
    funext x
    rw [differenceQuotientTestValue,pow_two]
  have hCols :
      (fun x j => coordinateDerivative c hc j x • ambientDifferenceQuotient i h u x +
        c x • ambientDifferenceQuotient i h (fun y => D y j) x) =
      differenceQuotientTestColumns χ i h u D := by
    funext x j
    have hCj : coordinateDerivative c hc j x =
        2*χ x*(fderiv ℝ χ x (EuclideanSpace.single j 1)) := by
      unfold coordinateDerivative
      change fderiv ℝ (fun x => χ x * χ x) x (EuclideanSpace.single j 1) = _
      rw [fderiv_fun_mul (hχ.differentiable (by simp) x) (hχ.differentiable (by simp) x),
        add_apply,smul_apply,smul_eq_mul]
      ring
    rw [hCj,differenceQuotientTestColumns,pow_two]
  rwa [hVal,hCols] at hh

private theorem integral_sq_norm_of_memLp_two {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) :
    Integrable (fun x => ‖v x‖^2) μ := (memLp_two_iff_integrable_sq_norm hv.1).mp hv

private theorem integral_inner_le_young_sq {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure X}
    {f g : X → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {ell : ℝ} (hell : 0 < ell) :
    (∫ x, inner ℝ (f x) (g x) ∂μ) ≤
      (ell/8)*(∫ x, ‖g x‖^2 ∂μ) + (2/ell)*(∫ x, ‖f x‖^2 ∂μ) := by
    have hwδI := integral_sq_norm_of_memLp_two hg
    have hfI := integral_sq_norm_of_memLp_two hf
    rw [← integral_const_mul,← integral_const_mul,← integral_add (hwδI.const_mul (ell/8)) (hfI.const_mul (2/ell))]
    apply integral_mono (integrable_inner_of_memLp_two hf hg)
      ((hwδI.const_mul (ell/8)).add (hfI.const_mul (2/ell)))
    intro x
    refine ((le_abs_self _).trans (abs_real_inner_le_norm (f x) (g x))).trans ?_
    have he : (4*(ell/8))⁻¹ = 2/ell := by
      rw [show 4*(ell/8) = ell/2 by ring,inv_div]
    simpa only [Pi.add_apply,he,mul_comm ‖g x‖ ‖f x‖] using
      mul_le_young_sq ‖g x‖ ‖f x‖ (show 0 < ell/8 by positivity)

private theorem integral_sq_norm_cutoff_add_le {B E : Type*} [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure B}
    {χ : B → ℝ} {W X T : B → E} (hχB : ∀ x, |χ x| ≤ 1)
    (hW : ∀ x, W x = χ x • (X x+T x)) (hWLp : MemLp W 2 μ)
    (hX : MemLp X 2 μ) (hT : MemLp T 2 μ) :
    (∫ x, ‖W x‖^2 ∂μ) ≤ 2*(∫ x, ‖X x‖^2 ∂μ) + 2*(∫ x, ‖T x‖^2 ∂μ) := by
    have hXI := integral_sq_norm_of_memLp_two hX
    have hTI := integral_sq_norm_of_memLp_two hT
    have hWL2 := integral_sq_norm_of_memLp_two hWLp
    rw [← integral_const_mul,← integral_const_mul,← integral_add (hXI.const_mul 2) (hTI.const_mul 2)]
    apply integral_mono hWL2 ((hXI.const_mul 2).add (hTI.const_mul 2))
    intro x
    have hN : ‖W x‖ ≤ ‖X x‖+‖T x‖ := by
      rw [hW,norm_smul,Real.norm_eq_abs]
      exact ((mul_le_mul_of_nonneg_right (hχB x) (norm_nonneg _)).trans_eq (one_mul _)).trans (norm_add_le _ _)
    have hS := pow_le_pow_left₀ (norm_nonneg _) hN 2
    have hYoung := sq_nonneg (‖X x‖-‖T x‖)
    change ‖W x‖^2 ≤ 2*‖X x‖^2+2*‖T x‖^2
    nlinarith only [hS,hYoung]

/-- The finite elliptic difference identity controls the squared gradient
differences on the set where the cutoff equals one. The constants involve
only the ellipticity, coefficient bounds, and cutoff derivative bound. -/
theorem cutoff_differenceQuotient_gradient_bound {n q : ℕ}
    (ell M L H : ℝ) (hell : 0 < ell) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : Domain n → Ambient q}
      {D : Domain n → HarmonicMaps.Gradient n q}
      (_hu : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) u D) (_hf : MemLp f 2 volume)
      (A : Domain n → AmbientGradientHilbert n q →L[ℝ] AmbientGradientHilbert n q)
      (_hFlux : MemLp (fun x => A x (packAmbientGradient (D x))) 2 volume)
      (χ : Domain n → ℝ) (_hχ : ContDiff ℝ ∞ χ) (_hcχ : HasCompactSupport χ)
      (_hχB : ∀ x, |χ x| ≤ 1)
      (_hχD : ∀ x, ∑ j : Fin n, (2*(fderiv ℝ χ x (EuclideanSpace.single j 1)))^2 ≤ H^2)
      (i : Fin n) (h : ℝ) (_hh : h ≠ 0)
      (_hAB : ∀ x, χ x ≠ 0 → ‖A (x+h • EuclideanSpace.single i 1)‖ ≤ M ∧
        ‖ambientDifferenceQuotient i h A x‖ ≤ L)
      (_hEll : ∀ x, χ x ≠ 0 → ∀ y : AmbientGradientHilbert n q,
        ell*‖y‖^2 ≤ inner ℝ (A (x+h • EuclideanSpace.single i 1) y) y)
      (_hEq :
        (∫ x, inner ℝ (A x (packAmbientGradient (D x)))
          (ambientDifferenceQuotient i (-h)
            (fun y => packAmbientGradient (differenceQuotientTestColumns χ i h u D y)) x)) =
        -(∫ x, inner ℝ (f x)
          (ambientDifferenceQuotient i (-h) (differenceQuotientTestValue χ i h u) x))),
        (∫ x, ‖χ x • ambientDifferenceQuotient i h (fun y => packAmbientGradient (D y)) x‖^2) ≤
          C*((∫ x, hsNormSq (D x)) + ∫ x, ‖f x‖^2) := by
  let K₀ := L^2/ell+1/2
  let K₁ := M^2/ell+L^2/2
  let γ := K₀+(K₁+ell/4)*H^2
  let C := (4/ell)*(γ+2/ell)
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hK₁ : 0 ≤ K₁ := by dsimp only [K₁]; positivity
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro u f D hu hf A hFlux χ hχ hcχ hχB hχD i h hh hAB hEll hEq
  let Y (x : Domain n) := packAmbientGradient (D x)
  let d (x : Domain n) := ambientDifferenceQuotient i h u x
  let Dδ := ambientDifferenceQuotient i h Y
  let X (x : Domain n) := χ x • Dδ x
  let T (x : Domain n) := packAmbientGradient (fun j : Fin n =>
    (2*(fderiv ℝ χ x (EuclideanSpace.single j 1))) • d x)
  let w := differenceQuotientTestValue χ i h u
  let G := differenceQuotientTestColumns χ i h u D
  let W (x : Domain n) := packAmbientGradient (G x)
  let aδ := ambientDifferenceQuotient i h (fun x => A x (Y x))
  let wδ := ambientDifferenceQuotient i (-h) w
  have hW (x : Domain n) : W x = χ x • (X x+T x) := by
    apply PiLp.ext
    intro j
    have he := congrArg (fun g : AmbientGradientHilbert n q => g j)
      (packAmbientGradient_differenceQuotient D i h x).symm
    simp only [packAmbientGradient_apply] at he
    change (2*χ x*(fderiv ℝ χ x (EuclideanSpace.single j 1))) • d x +
      (χ x)^2 • ambientDifferenceQuotient i h (fun y => D y j) x =
      (χ x) • ((χ x • Dδ x) j + (2*(fderiv ℝ χ x (EuclideanSpace.single j 1))) • d x)
    simp only [PiLp.smul_apply,smul_add,smul_smul,← he,pow_two]
    rw [show χ x * (2 * (fderiv ℝ χ x) (EuclideanSpace.single j 1)) =
      2*χ x*(fderiv ℝ χ x (EuclideanSpace.single j 1)) by ring,add_comm]
  have hU : MemLp u 2 (volume : Measure (Domain n)) := by
    simpa only [Measure.restrict_univ] using hu.2.1
  have hY : MemLp Y 2 volume := memLp_packAmbientGradient (fun j => by
    simpa only [Measure.restrict_univ] using hu.2.2 j)
  have hd : MemLp d 2 volume := memLp_ambientDifferenceQuotient hU i h
  have hDδ : MemLp Dδ 2 volume := memLp_ambientDifferenceQuotient hY i h
  have hχTop : MemLp χ ∞ volume := memLp_top_of_bound hχ.continuous.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hχB x)
  have hX : MemLp X 2 volume := hDδ.smul (r := (2 : ℝ≥0∞)) hχTop
  have hT : MemLp T 2 volume := by
    apply memLp_packAmbientGradient
    intro j
    have hCj : Continuous (fun x : Domain n => 2*(fderiv ℝ χ x (EuclideanSpace.single j 1))) :=
      continuous_const.mul ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hCLp : MemLp (fun x : Domain n => 2*(fderiv ℝ χ x (EuclideanSpace.single j 1))) ∞ volume := by
      apply memLp_top_of_bound hCj.aestronglyMeasurable |H|
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs]
      apply le_of_sq_le_sq _ (abs_nonneg _)
      rw [sq_abs,sq_abs]
      exact (Finset.single_le_sum (f := fun k : Fin n =>
        (2*(fderiv ℝ χ x (EuclideanSpace.single k 1)))^2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans (hχD x)
    exact hd.smul (r := (2 : ℝ≥0∞)) hCLp
  have hwSob := memW12_differenceQuotientTest hχ hcχ hu i h
  have hwLp : MemLp w 2 volume := by simpa only [Measure.restrict_univ] using hwSob.2.1
  have hWLp : MemLp W 2 volume := memLp_packAmbientGradient (fun j => by
    simpa only [Measure.restrict_univ] using hwSob.2.2 j)
  have haδ : MemLp aδ 2 volume := memLp_ambientDifferenceQuotient hFlux i h
  have hwδ : MemLp wδ 2 volume := memLp_ambientDifferenceQuotient hwLp i (-h)
  have hShiftEq : (∫ x, inner ℝ (aδ x) (W x)) = ∫ x, inner ℝ (f x) (wδ x) := by
    have hIBP : (∫ x, inner ℝ (A x (Y x)) (ambientDifferenceQuotient i (-h) W x)) =
      -(∫ x, inner ℝ (aδ x) (W x)) :=
      integral_inner_ambientDifferenceQuotient_right (v := fun x => A x (Y x)) (w := W) hFlux hWLp i h
    exact neg_injective (hIBP.symm.trans hEq)
  have hPointLower (x : Domain n) : (ell/2)*‖X x‖^2 ≤
      inner ℝ (aδ x) (W x) + K₀*‖Y x‖^2 + K₁*‖T x‖^2 := by
    rw [hW]
    by_cases he : χ x = 0
    · simp only [X,he,zero_smul,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,
        inner_zero_right,zero_add]
      positivity
    · rw [show aδ x = ambientDifferenceQuotient i h (fun y => A y (Y y)) x from rfl,
        ambientDifferenceQuotient_operator_apply,real_inner_smul_right,← real_inner_smul_left,
        smul_add,← map_smul]
      exact half_coercivity_le_cutoff_pairing _ _ (X x) (T x) (Y x) (χ x) ell M L
        hell (hχB x) (hAB x he).1 (hAB x he).2 (hEll x he (X x))
  have hXI := integral_sq_norm_of_memLp_two hX
  have hYI := integral_sq_norm_of_memLp_two hY
  have hTI := integral_sq_norm_of_memLp_two hT
  have hDI := integral_sq_norm_of_memLp_two hd
  have hLower := integral_mono (hXI.const_mul (ell/2))
    (((integrable_inner_of_memLp_two haδ hWLp).add (hYI.const_mul K₀)).add (hTI.const_mul K₁))
    hPointLower
  rw [integral_const_mul,integral_add' ((integrable_inner_of_memLp_two haδ hWLp).add (hYI.const_mul K₀))
      (hTI.const_mul K₁),
    integral_add' (integrable_inner_of_memLp_two haδ hWLp) (hYI.const_mul K₀),
    integral_const_mul,integral_const_mul,hShiftEq]
    at hLower
  have hUp := integral_inner_le_young_sq hf hwδ hell
  have hGW := integral_sq_norm_cutoff_add_le hχB hW hWLp hX hT
  have hDis : (∫ x, ‖wδ x‖^2) ≤ 2*(∫ x, ‖X x‖^2) + 2*(∫ x, ‖T x‖^2) := by
    apply (integral_globalSobolev_differenceQuotient_sq_le hwSob i (neg_ne_zero.mpr hh)).trans
    simpa only [W,norm_packAmbientGradient_sq] using hGW
  have hTBound : (∫ x, ‖T x‖^2) ≤ H^2*(∫ x, ‖Y x‖^2) := by
    have hTQ : (∫ x, ‖T x‖^2) ≤ H^2*(∫ x, ‖d x‖^2) := by
      rw [← integral_const_mul]
      apply integral_mono hTI (hDI.const_mul _)
      intro x
      simp only [T,norm_packAmbientGradient_sq,hsNormSq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
        ← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (by simpa only [mul_pow] using hχD x) (sq_nonneg _)
    apply hTQ.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    simpa only [Y,norm_packAmbientGradient_sq] using integral_globalSobolev_differenceQuotient_sq_le hu i hh
  let IX := ∫ x, ‖X x‖^2
  let IY := ∫ x, ‖Y x‖^2
  let IT := ∫ x, ‖T x‖^2
  let IF := ∫ x, ‖f x‖^2
  have hY₀ : 0 ≤ IY := integral_nonneg fun _ => sq_nonneg _
  have hF₀ : 0 ≤ IF := integral_nonneg fun _ => sq_nonneg _
  have hComb := hUp.trans (add_le_add
    (mul_le_mul_of_nonneg_left hDis (div_nonneg hell.le (by norm_num : (0 : ℝ) ≤ 8))) le_rfl)
  have hLead : (ell/4)*IX ≤ K₀*IY + (K₁+ell/4)*IT + (2/ell)*IF := by
    dsimp only [IX,IY,IT,IF]
    linarith only [hLower,hComb]
  have hEnd : (ell/4)*IX ≤ γ*IY + (2/ell)*IF := by
    have := mul_le_mul_of_nonneg_left hTBound (show 0 ≤ K₁+ell/4 by positivity)
    dsimp only [γ,IX,IY,IT,IF] at hLead ⊢
    linarith only [hLead,this]
  have hOut : IX ≤ C*(IY+IF) := by
    apply (mul_le_mul_iff_of_pos_left (show 0 < ell/4 by positivity)).mp
    have he : (ell/4)*C = γ+2/ell := by
      dsimp only [C]
      field_simp [hell.ne']
    rw [← mul_assoc,he]
    have hYle : γ*IY ≤ (γ+2/ell)*IY :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hY₀
    have hFle : (2/ell)*IF ≤ (γ+2/ell)*IF :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hγ) hF₀
    exact hEnd.trans (by rw [mul_add]; exact add_le_add hYle hFle)
  simpa only [IX,IY,IF,X,Dδ,Y,norm_packAmbientGradient_sq] using hOut

end Thesis
