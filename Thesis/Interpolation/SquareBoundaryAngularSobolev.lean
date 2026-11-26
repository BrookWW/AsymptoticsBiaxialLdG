module

public import Thesis.Interpolation.SquareBoundaryAngularMeasure
public import Thesis.Interpolation.IntervalAbsoluteContinuity
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The original four square-side Sobolev traces in native angular coordinates. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped NNReal Topology

namespace Thesis

private theorem squareUnclamped_ac_on_sector
    {E : Type*} [NormedAddCommGroup E] (b : C(UnitSquareBoundary,E)) (i : Fin 2) (upper : Bool)
    (hSide : AbsolutelyContinuousOnInterval (b ∘ unitSquareSideParameter i upper) (-1) 1) :
    AbsolutelyContinuousOnInterval (squareBoundaryUnclamped b)
      (unitSquareSideAngleCenter i upper-Real.pi/4) (unitSquareSideAngleCenter i upper+Real.pi/4) := by
  let c := unitSquareSideAngleCenter i upper
  let s := unitSquareSideAngleSign i upper
  let lo := c-Real.pi/4
  let hi := c+Real.pi/4
  let F := squareBoundaryUnclamped b
  let U := Icc lo hi
  let t (θ : ℝ) := Real.tan (θ-c)
  let g (θ : ℝ) := s*t θ
  have hπ : 0 < Real.pi := Real.pi_pos
  have hLH : lo ≤ hi := by dsimp only [lo,hi]; linarith only [hπ]
  have hGood (θ : ℝ) (hθ : θ ∈ U) : θ-c ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by
    have hl : c-Real.pi/4 ≤ θ := hθ.1
    have hu : θ ≤ c+Real.pi/4 := hθ.2
    exact ⟨by linarith only [hl,hπ],by linarith only [hu,hπ]⟩
  have hTMono : MonotoneOn t U := by
    intro θ hθ ψ hψ h
    exact Real.strictMonoOn_tan.monotoneOn (hGood θ hθ) (hGood ψ hψ) (by linarith only [h])
  have hTLower : t lo = -1 := by
    dsimp only [t,lo]
    rw [show c-Real.pi/4-c = -(Real.pi/4) by ring,Real.tan_neg,Real.tan_pi_div_four]
  have hTUpper : t hi = 1 := by
    dsimp only [t,hi]
    rw [show c+Real.pi/4-c = Real.pi/4 by ring,Real.tan_pi_div_four]
  have hTBounds (θ : ℝ) (hθ : θ ∈ U) : t θ ∈ Icc (-1 : ℝ) 1 := by
    have hL := hTMono (left_mem_Icc.mpr hLH) hθ hθ.1
    have hR := hTMono hθ (right_mem_Icc.mpr hLH) hθ.2
    exact ⟨hTLower ▸ hL,hTUpper ▸ hR⟩
  have hSign : s = 1 ∨ s = -1 := unitSquareSideAngleSign_eq i upper
  have hGBounds (θ : ℝ) (hθ : θ ∈ U) : g θ ∈ Icc (-1 : ℝ) 1 := by
    have ht := hTBounds θ hθ
    rcases hSign with h | h
    · simpa only [g,h,one_mul] using ht
    · dsimp only [g]
      rw [h,neg_one_mul]
      exact ⟨by linarith only [ht.2],by linarith only [ht.1]⟩
  have hGM : MonotoneOn g U ∨ AntitoneOn g U := by
    rcases hSign with h | h
    · exact Or.inl (by simpa only [g,h,one_mul] using hTMono)
    · exact Or.inr (by simpa only [g,h,neg_one_mul] using hTMono.neg)
  have hGdiff : ContDiffOn ℝ 1 g U := by
    have hTan : ContDiffOn ℝ 1 Real.tan (Ioo (-(Real.pi/2)) (Real.pi/2)) := by
      intro x hx
      exact ((Real.contDiffAt_tan).mpr (Real.cos_pos_of_mem_Ioo hx).ne').contDiffWithinAt
    have hT : ContDiffOn ℝ 1 t U :=
      hTan.comp ((contDiff_id.sub contDiff_const).contDiffOn) hGood
    exact contDiffOn_const.mul hT
  obtain ⟨K,hK⟩ := hGdiff.exists_lipschitzOnWith one_ne_zero (convex_Icc lo hi) isCompact_Icc
  have hMap : MapsTo g (uIcc lo hi) (uIcc (-1 : ℝ) 1) := by
    rw [uIcc_of_le hLH,uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact hGBounds
  have hK' : LipschitzOnWith K g (uIcc lo hi) := by simpa only [uIcc_of_le hLH,U] using hK
  have hGM' : MonotoneOn g (uIcc lo hi) ∨ AntitoneOn g (uIcc lo hi) := by
    simpa only [uIcc_of_le hLH,U] using hGM
  have hC := absolutelyContinuousOnInterval_comp_monotoneOn hSide hMap hK' hGM'
  apply absolutelyContinuousOnInterval_congr hC
  rw [uIcc_of_le hLH]
  intro θ hθ
  have hInv : unitSquareSideAngle i upper (g θ) = θ := by
    change c+s*Real.arctan (s*t θ) = θ
    have hTan : Real.arctan (t θ) = θ-c := Real.arctan_tan (hGood θ hθ).1 (hGood θ hθ).2
    rcases hSign with hs | hs
    · simp only [hs,one_mul,hTan]
      ring
    · simp only [hs,neg_one_mul,Real.arctan_neg,hTan]
      ring
  change b (unitSquareSideParameter i upper (g θ)) =
    b (unitSquareCircleHomeomorph.symm (StratificationTheory.circleNativeParam θ))
  rw [← unitSquareCircle_symm_sideAngle i upper (hGBounds θ hθ), hInv]

private theorem squareSideAngle_abs_derivative_ge_half (i : Fin 2) (upper : Bool)
    {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    1/2 ≤ |unitSquareSideAngleSign i upper * (1+s^2)⁻¹| := by
  have hS : |unitSquareSideAngleSign i upper| = 1 := by
    rcases unitSquareSideAngleSign_eq i upper with h | h <;> simp [h]
  have hPos : 0 < 1+s^2 := by positivity
  have hSq : s^2 ≤ 1 := by
    have hAbs := (abs_lt.mpr hs).le
    nlinarith only [mul_nonneg (sub_nonneg.mpr hAbs) (add_nonneg zero_le_one (abs_nonneg s)),sq_abs s]
  rw [abs_mul,hS,one_mul,abs_of_nonneg (inv_nonneg.mpr hPos.le), inv_eq_one_div]
  apply (le_div_iff₀ hPos).mpr
  linarith only [hSq]

private theorem squareSideAngle_energy_density_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : C(UnitSquareBoundary,E)) (i : Fin 2) (upper : Bool) {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    |unitSquareSideAngleSign i upper * (1+s^2)⁻¹| *
      ‖deriv (squareBoundaryUnclamped b) (unitSquareSideAngle i upper s)‖^2 ≤
        2*‖deriv (b ∘ unitSquareSideParameter i upper) s‖^2 := by
  let F := squareBoundaryUnclamped b
  let φ := unitSquareSideAngle i upper
  let e := b ∘ unitSquareSideParameter i upper
  let J := unitSquareSideAngleSign i upper * (1+s^2)⁻¹
  have hJ : 1/2 ≤ |J| := squareSideAngle_abs_derivative_ge_half i upper hs
  change |J| * ‖deriv F (φ s)‖^2 ≤ 2*‖deriv e s‖^2
  by_cases hF : DifferentiableAt ℝ F (φ s)
  · have hEq : e =ᶠ[𝓝 s] F ∘ φ := by
      filter_upwards [(isOpen_Ioo.mem_nhds hs)] with x hx
      exact (congrArg b (unitSquareCircle_symm_sideAngle i upper (Ioo_subset_Icc_self hx))).symm
    have hDeriv : HasDerivAt e (J • deriv F (φ s)) s :=
      (hF.hasDerivAt.scomp s (unitSquareSideAngle_hasDerivAt i upper s)).congr_of_eventuallyEq hEq
    rw [hDeriv.deriv,norm_smul,Real.norm_eq_abs,mul_pow]
    have h := mul_nonneg (sub_nonneg.mpr hJ)
      (mul_nonneg (abs_nonneg J) (sq_nonneg ‖deriv F (φ s)‖))
    nlinarith only [h]
  · rw [deriv_zero_of_not_differentiableAt hF,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero]
    exact mul_nonneg (by norm_num) (sq_nonneg _)

private theorem squareUnclamped_energy_on_sector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : C(UnitSquareBoundary,E)) (i : Fin 2) (upper : Bool)
    (hSide : MemLp (deriv (b ∘ unitSquareSideParameter i upper)) 2 (volume.restrict (Ioo (-1 : ℝ) 1))) :
    let F := squareBoundaryUnclamped b
    let c := unitSquareSideAngleCenter i upper
    let H (t : ℝ) := ‖deriv F t‖^2
    IntervalIntegrable H volume (c-Real.pi/4) (c+Real.pi/4) ∧
      (∫ t in (c-Real.pi/4)..(c+Real.pi/4), H t) ≤
        2*∫ s in Ioo (-1 : ℝ) 1, ‖deriv (b ∘ unitSquareSideParameter i upper) s‖^2 := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let F := squareBoundaryUnclamped b
  let c := unitSquareSideAngleCenter i upper
  let H (t : ℝ) := ‖deriv F t‖^2
  let φ := unitSquareSideAngle i upper
  let J (s : ℝ) := unitSquareSideAngleSign i upper * (1+s^2)⁻¹
  let side (s : ℝ) := ‖deriv (b ∘ unitSquareSideParameter i upper) s‖^2
  change IntervalIntegrable H volume (c-Real.pi/4) (c+Real.pi/4) ∧
    (∫ t in (c-Real.pi/4)..(c+Real.pi/4), H t) ≤ 2*∫ s in Ioo (-1 : ℝ) 1, side s
  have hA : c-Real.pi/4 ≤ c+Real.pi/4 := by linarith only [Real.pi_pos]
  have hJ (s : ℝ) (_ : s ∈ Ioo (-1 : ℝ) 1) : HasDerivWithinAt φ (J s) (Ioo (-1 : ℝ) 1) s :=
    (unitSquareSideAngle_hasDerivAt i upper s).hasDerivWithinAt
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Real.arctan_injective
    change c+unitSquareSideAngleSign i upper*Real.arctan x =
      c+unitSquareSideAngleSign i upper*Real.arctan y at hxy
    have hne : unitSquareSideAngleSign i upper ≠ 0 := by
      rcases unitSquareSideAngleSign_eq i upper with h | h <;> simp [h]
    exact mul_left_cancel₀ hne (add_left_cancel hxy)
  have hS : IntegrableOn side (Ioo (-1 : ℝ) 1) :=
    (memLp_two_iff_integrable_sq_norm hSide.aestronglyMeasurable).mp hSide
  have hS' : IntegrableOn (fun s => 2*side s) (Ioo (-1 : ℝ) 1) := hS.const_mul 2
  let G (s : ℝ) := |J s| • H (φ s)
  have hG₀ (s : ℝ) : 0 ≤ G s := by
    exact mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hMeas : Measurable G := by
    have hH : Measurable H := (stronglyMeasurable_deriv F).norm.measurable.pow_const 2
    have hφc : Continuous φ := continuous_const.add (continuous_const.mul Real.continuous_arctan)
    have hDen : Continuous (fun x : ℝ => 1+x^2) := continuous_const.add (continuous_id.pow 2)
    have hJc : Continuous J := continuous_const.mul
      (hDen.inv₀ fun x => ne_of_gt (by positivity : 0 < (1 : ℝ)+x^2))
    exact hJc.abs.measurable.smul (hH.comp hφc.measurable)
  have hG : IntegrableOn G (Ioo (-1 : ℝ) 1) := hS'.mono' hMeas.aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioo (a := (-1 : ℝ)) (b := 1))] with s hs
    rw [Real.norm_of_nonneg (hG₀ s)]
    exact squareSideAngle_energy_density_le b i upper hs)
  have hH := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hJ hφ.injOn H).mpr hG
  rw [image_unitSquareSideAngle] at hH
  have hInt : IntervalIntegrable H volume (c-Real.pi/4) (c+Real.pi/4) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA,IntegrableOn,
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact hH
  refine ⟨hInt,?_⟩
  rw [intervalIntegral_eq_setIntegral_Ioo hA,← image_unitSquareSideAngle,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hJ hφ.injOn,← integral_const_mul]
  apply setIntegral_mono_on hG hS' measurableSet_Ioo
  exact fun s hs => squareSideAngle_energy_density_le b i upper hs

private theorem squareUnclamped_periodic_energy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : C(UnitSquareBoundary,E)) :
    Function.Periodic (fun t => ‖deriv (squareBoundaryUnclamped b) t‖^2) (2*Real.pi) := by
  intro t
  let F := squareBoundaryUnclamped b
  have hF : (fun x => F (x+2*Real.pi)) = F := funext (squareBoundaryUnclamped_periodic b)
  change ‖deriv F (t+2*Real.pi)‖^2 = ‖deriv F t‖^2
  rw [← deriv_comp_add_const (f := F),hF]

private theorem squareUnclamped_ac_integrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : C(UnitSquareBoundary,E))
    (hAC : ∀ i : Fin 2, ∀ upper : Bool, AbsolutelyContinuousOnInterval
      (b ∘ unitSquareSideParameter i upper) (-1) 1)
    (hMem : ∀ i : Fin 2, ∀ upper : Bool, MemLp (deriv (b ∘ unitSquareSideParameter i upper)) 2
      (volume.restrict (Ioo (-1 : ℝ) 1))) :
    AbsolutelyContinuousOnInterval (squareBoundaryUnclamped b) (-Real.pi) Real.pi ∧
      ∀ a c, IntervalIntegrable (fun t => ‖deriv (squareBoundaryUnclamped b) t‖^2) volume a c := by
  let F := squareBoundaryUnclamped b
  let H (t : ℝ) := ‖deriv F t‖^2
  let P (a c : ℝ) := AbsolutelyContinuousOnInterval F a c ∧ IntervalIntegrable H volume a c
  have hSector (i : Fin 2) (upper : Bool) : P
      (unitSquareSideAngleCenter i upper-Real.pi/4) (unitSquareSideAngleCenter i upper+Real.pi/4) :=
    ⟨squareUnclamped_ac_on_sector b i upper (hAC i upper),
      (squareUnclamped_energy_on_sector b i upper (hMem i upper)).1⟩
  let t₀ := -(3*Real.pi/4)
  let t₁ := -(Real.pi/4)
  let t₂ := Real.pi/4
  let t₃ := 3*Real.pi/4
  let t₄ := 5*Real.pi/4
  have h₀ : P t₀ t₁ := by
    have h := hSector 1 false
    change P (-(Real.pi/2)-Real.pi/4) (-(Real.pi/2)+Real.pi/4) at h
    convert h using 1 <;> dsimp only [t₀,t₁] <;> ring
  have h₁ : P t₁ t₂ := by
    have h := hSector 0 true
    change P (0-Real.pi/4) (0+Real.pi/4) at h
    simpa only [t₁,t₂,zero_sub,zero_add] using h
  have h₂ : P t₂ t₃ := by
    have h := hSector 1 true
    change P (Real.pi/2-Real.pi/4) (Real.pi/2+Real.pi/4) at h
    convert h using 1 <;> dsimp only [t₂,t₃] <;> ring
  have h₃ : P t₃ t₄ := by
    have h := hSector 0 false
    change P (Real.pi-Real.pi/4) (Real.pi+Real.pi/4) at h
    convert h using 1 <;> dsimp only [t₃,t₄] <;> ring
  have hJoin {a c d : ℝ} (ha : a ≤ c) (hb : c ≤ d) (hL : P a c) (hR : P c d) : P a d :=
    ⟨absolutelyContinuousOnInterval_of_adjacent ha hb hL.1 hR.1,hL.2.trans hR.2⟩
  have ht₀₁ : t₀ ≤ t₁ := by dsimp only [t₀,t₁]; linarith only [Real.pi_pos]
  have ht₁₂ : t₁ ≤ t₂ := by dsimp only [t₁,t₂]; linarith only [Real.pi_pos]
  have ht₂₃ : t₂ ≤ t₃ := by dsimp only [t₂,t₃]; linarith only [Real.pi_pos]
  have ht₃₄ : t₃ ≤ t₄ := by dsimp only [t₃,t₄]; linarith only [Real.pi_pos]
  have hFull : P t₀ t₄ :=
    hJoin (ht₀₁.trans (ht₁₂.trans ht₂₃)) ht₃₄
      (hJoin (ht₀₁.trans ht₁₂) ht₂₃ (hJoin ht₀₁ ht₁₂ h₀ h₁) h₂) h₃
  have hπ₂ : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have htFull : t₀+2*Real.pi = t₄ := by dsimp only [t₀,t₄]; ring
  have hI : IntervalIntegrable H volume t₀ (t₀+2*Real.pi) := htFull.symm ▸ hFull.2
  refine ⟨?_,(squareUnclamped_periodic_energy b).intervalIntegrable hπ₂.ne' hI⟩
  have hRight : AbsolutelyContinuousOnInterval F t₀ Real.pi := by
    apply hFull.1.mono
    rw [uIcc_of_le (by dsimp only [t₀]; linarith only [Real.pi_pos]),
      uIcc_of_le (ht₀₁.trans (ht₁₂.trans (ht₂₃.trans ht₃₄)))]
    exact Icc_subset_Icc le_rfl (by dsimp only [t₄]; linarith only [Real.pi_pos])
  let tPrev := -(5*Real.pi/4)
  have htPrev : tPrev ≤ t₀ := by dsimp only [tPrev,t₀]; linarith only [Real.pi_pos]
  have hPrev : AbsolutelyContinuousOnInterval (fun t => F (t+2*Real.pi)) tPrev t₀ := by
    apply absolutelyContinuousOnInterval_comp_add_right htPrev
    rw [htFull,show tPrev+2*Real.pi = t₃ by dsimp only [tPrev,t₃]; ring]
    exact h₃.1
  have hPrev' : AbsolutelyContinuousOnInterval F tPrev t₀ :=
    absolutelyContinuousOnInterval_congr hPrev (fun t _ => squareBoundaryUnclamped_periodic b t)
  have hπ₀ : -Real.pi ≤ t₀ := by dsimp only [t₀]; linarith only [Real.pi_pos]
  have hLeft : AbsolutelyContinuousOnInterval F (-Real.pi) t₀ := by
    apply hPrev'.mono
    rw [uIcc_of_le hπ₀,uIcc_of_le htPrev]
    exact Icc_subset_Icc (by dsimp only [tPrev]; linarith only [Real.pi_pos]) le_rfl
  exact absolutelyContinuousOnInterval_of_adjacent hπ₀
    (by dsimp only [t₀]; linarith only [Real.pi_pos]) hLeft hRight

private theorem deriv_squareBoundaryAngular_eq_unclamped
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : C(UnitSquareBoundary,E))
    {x : ℝ} (hx : x ∈ Ioo 0 (2*Real.pi)) :
    deriv (squareBoundaryAngular b) x = deriv (squareBoundaryUnclamped b) (x-Real.pi) := by
  have h : squareBoundaryAngular b =ᶠ[𝓝 x] fun t => squareBoundaryUnclamped b (t-Real.pi) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact squareBoundaryAngular_eq_unclamped b (Ioo_subset_Icc_self ht)
  rw [h.deriv_eq,deriv_comp_sub_const]

/-- The four original absolute-continuity and derivative hypotheses give
the actual angular Sobolev trace, with energy bound twice their sum. -/
theorem squareBoundaryAngularSobolev : External.SquareBoundaryAngularSobolev := by
  refine ⟨2,by norm_num,?_⟩
  intro E instAdd instSpace instDim b hSide
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let F := squareBoundaryUnclamped b
  let H (t : ℝ) := ‖deriv F t‖^2
  let G (t : ℝ) := ‖deriv (squareBoundaryAngular b) t‖^2
  have hπ : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  obtain ⟨hAC,hI⟩ := squareUnclamped_ac_integrable b (fun i u => (hSide i u).1)
    (fun i u => (hSide i u).2)
  have hS : AbsolutelyContinuousOnInterval (fun t => F (t-Real.pi)) 0 (2*Real.pi) := by
    simp_rw [sub_eq_add_neg]
    apply absolutelyContinuousOnInterval_comp_add_right hπ.le
    rw [zero_add,show 2*Real.pi + -Real.pi = Real.pi by ring]
    exact hAC
  have hC : AbsolutelyContinuousOnInterval (squareBoundaryAngular b) 0 (2*Real.pi) := by
    apply absolutelyContinuousOnInterval_congr hS
    rw [uIcc_of_le hπ.le]
    exact fun _ ht => (squareBoundaryAngular_eq_unclamped b ht).symm
  have hEq : G =ᵐ[volume.restrict (Ioo 0 (2*Real.pi))] fun x => H (x-Real.pi) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioo (a := (0 : ℝ)) (b := 2*Real.pi))]
      with x hx
    dsimp only [G,H,F]
    rw [deriv_squareBoundaryAngular_eq_unclamped b hx]
  have hShift : IntervalIntegrable (fun t => H (t-Real.pi)) volume 0 (2*Real.pi) := by
    convert (hI (-Real.pi) Real.pi).comp_sub_right Real.pi using 1 <;> ring
  have hInt : IntegrableOn G (Ioo 0 (2*Real.pi)) := by
    have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le hπ.le).mp hShift
    rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h
    exact h.congr hEq.symm
  refine ⟨hC,(memLp_two_iff_integrable_sq_norm
    (stronglyMeasurable_deriv (squareBoundaryAngular b)).aestronglyMeasurable).mpr hInt,?_⟩
  change (∫ t in Ioo 0 (2*Real.pi), G t) ≤ _
  calc
    _ = ∫ t in Ioo 0 (2*Real.pi), H (t-Real.pi) := integral_congr_ae hEq
    _ = ∫ t in (-Real.pi)..Real.pi, H t := by
      rw [← intervalIntegral_eq_setIntegral_Ioo hπ.le,intervalIntegral.integral_comp_sub_right,
        zero_sub,show 2*Real.pi-Real.pi = Real.pi by ring]
    _ = ∑ i : Fin 2, ∑ upper : Bool,
        ∫ t in (unitSquareSideAngleCenter i upper-Real.pi/4)..(unitSquareSideAngleCenter i upper+Real.pi/4),
          H t := integral_twoPi_eq_squareSideAngle_sectors (squareUnclamped_periodic_energy b) hI
    _ ≤ ∑ i : Fin 2, ∑ upper : Bool, 2*∫ t in Ioo (-1 : ℝ) 1,
          ‖deriv (b ∘ unitSquareSideParameter i upper) t‖^2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun upper _ =>
        (squareUnclamped_energy_on_sector b i upper (hSide i upper).2).2
    _ = _ := by simp only [Finset.mul_sum]

end Thesis
