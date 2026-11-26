module

public import Thesis.Variational.DirichletPoissonInverse
public import Thesis.Foundation.FrobeniusInnerProduct
import Thesis.Variational.H10StrongApproximation
import Thesis.Variational.H10WeakGreen
import Thesis.Variational.WeakCorrectionGreen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! A weak comparison principle using compact smooth tests of the literal
Dirichlet graph. -/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius RealInnerProductSpace

namespace Thesis

local instance weakComparisonInnerProduct : InnerProductSpace ℝ S0 := frobeniusInnerProductSpace

local instance weakComparisonContinuousENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

private theorem exists_smoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ deriv Real.smoothTransition t ∧
      deriv Real.smoothTransition t ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨K,hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max K 0,le_max_right _ _,fun t => ⟨Real.smoothTransition.monotone.deriv_nonneg,?_⟩⟩
  by_cases h : t ∈ Icc (0 : ℝ) 1
  · exact (le_abs_self _).trans ((hK t h).trans (le_max_left _ _))
  · have ht : t < 0 ∨ 1 < t := by
      simp only [mem_Icc,not_and_or,not_le] at h
      exact h
    obtain ht | ht := ht
    · have hEq : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        exact Real.smoothTransition.zero_of_nonpos hs.le
      rw [hEq.deriv_eq,deriv_const]
      exact le_max_right _ _
    · have hEq : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact Real.smoothTransition.one_of_one_le hs.le
      rw [hEq.deriv_eq,deriv_const]
      exact le_max_right _ _

private theorem exists_compact_smooth_comparison_test
    {U : Set Point} (hU : IsOpen U) (L : S0 →L[ℝ] ℝ) (e : S0)
    {u : Point → S0} (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (hus : tsupport u ⊆ U)
    {B : Point → ℝ} (hB : ContDiffOn ℝ ∞ B U) (hPos : ∀ x ∈ U, 0 ≤ B x) :
    ∃ φ : Point → S0, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
      ∀ x ∈ U, φ x = Real.smoothTransition (L (u x)-B x) • e ∧
        ∀ j, coordDeriv j φ x =
          (deriv Real.smoothTransition (L (u x)-B x) *
            (L (coordDeriv j u x)-coordDeriv j B x)) • e := by
  let f (x : Point) := L (u x)-B x
  let g (x : Point) := Real.smoothTransition (f x) • e
  let φ := U.indicator g
  have hφEq (x : Point) (hx : x ∈ U) : φ =ᶠ[𝓝 x] g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact indicator_of_mem hy g
  have hg₀ (x : Point) (hx : x ∈ U) (hz : u x = 0) : g x = 0 := by
    have hf₀ : f x ≤ 0 := by simp [f,hz,hPos x hx]
    change Real.smoothTransition (f x) • e = 0
    rw [Real.smoothTransition.zero_of_nonpos hf₀,zero_smul]
  have hφs : tsupport φ ⊆ tsupport u := by
    apply closure_mono
    intro x hx
    by_contra hn
    apply (Function.mem_support.mp hx)
    change U.indicator g x = 0
    by_cases h : x ∈ U
    · rw [indicator_of_mem h]
      exact hg₀ x h (Function.notMem_support.mp hn)
    · exact indicator_of_notMem h g
  have hF : ContDiffOn ℝ ∞ f U := (L.contDiff.comp hu).contDiffOn.sub hB
  have hG : ContDiffOn ℝ ∞ g U :=
    (Real.smoothTransition.contDiff.comp_contDiffOn hF).smul contDiffOn_const
  have hφ : ContDiff ℝ ∞ φ := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact ((hG x hx).contDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq (hφEq x hx)
    · have hZ : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hus (hφs h)))
      exact contDiffAt_const.congr_of_eventuallyEq hZ
  refine ⟨φ,hφ,huc.of_isClosed_subset (isClosed_tsupport φ) hφs,hφs.trans hus,?_⟩
  intro x hx
  refine ⟨indicator_of_mem hx g,?_⟩
  intro j
  have hD := ((hF x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hθ := (Real.smoothTransition.contDiff.differentiable (n := 1) one_ne_zero
    (f x)).hasDerivAt
  have hChain := ((hθ.comp_hasFDerivAt x hD.hasFDerivAt).smul_const e).congr_of_eventuallyEq
    (hφEq x hx)
  rw [coordDeriv, hChain.fderiv, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  have hb := ((hB x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  change (deriv Real.smoothTransition (f x) * coordDeriv j f x) • e = _
  have hCol := DFunLike.congr_fun
    (((L.hasFDerivAt.comp x (hu.differentiable (by simp) x).hasFDerivAt).sub hb.hasFDerivAt).fderiv)
    (axis j)
  rw [show coordDeriv j f x = L (coordDeriv j u x)-coordDeriv j B x from hCol]

private theorem exists_H10_smooth_approximation_subtype {U : Set Point} (w : H10 U) :
    ∃ (wₙ : ℕ → H10 U) (uₙ : ℕ → Point → S0), Tendsto wₙ atTop (𝓝 w) ∧
      ∀ n, ContDiff ℝ ∞ (uₙ n) ∧ HasCompactSupport (uₙ n) ∧ tsupport (uₙ n) ⊆ U ∧
        h10Value (wₙ n) =ᵐ[volume.restrict U] uₙ n ∧
        h10Gradient (wₙ n) =ᵐ[volume.restrict U] ClassicalGradient (uₙ n) := by
  obtain ⟨p,f,hp,hf⟩ := w.exists_smooth_graph_approximation
  have hM (n : ℕ) : p n ∈ h10Submodule U :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f n,hf n⟩)
  let v (n : ℕ) : H10 U := ⟨p n,hM n⟩
  refine ⟨v,f,tendsto_subtype_rng.mpr hp,?_⟩
  intro n
  refine ⟨(hf n).1,(hf n).2.1,(hf n).2.2.1,(hf n).2.2.2.1,?_⟩
  filter_upwards [ae_all_iff.mpr (hf n).2.2.2.2] with x hx
  exact funext hx

private theorem frobenius_unit_smul_right (e : S0) (he : ‖e‖ = 1) (a b : ℝ) :
    frobeniusS0 (a • e) (b • e) = a * b := by
  rw [← frobeniusCoordinateEquiv_inner,map_smul,map_smul,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,frobeniusCoordinateEquiv.norm_map,he]
  ring

private theorem frobenius_direction_smul_right (e v : S0) (t : ℝ) :
    frobeniusS0 v (t • e) = t * (innerSL ℝ e) v := by
  have hL : (innerSL ℝ e) v = frobeniusS0 e v :=
    (innerSL_apply_apply ℝ e v).trans (frobenius_inner_eq e v)
  rw [hL,← frobeniusCoordinateEquiv_inner v,← frobeniusCoordinateEquiv_inner e,map_smul,
    real_inner_smul_right,real_inner_comm]

private theorem comparison_test_column_bound (e : S0) (he : ‖e‖ = 1)
    (z : S0) (b C t : ℝ) (ht : 0 ≤ t) (hCt : t ≤ C) :
    let a := (t*((innerSL ℝ e) z-b)) • e
    frobeniusS0 a a ≤ C * (frobeniusS0 z a - frobeniusS0 (b • e) a) := by
  let L : S0 →L[ℝ] ℝ := innerSL ℝ e
  let d := L z-b
  change frobeniusS0 ((t*d) • e) ((t*d) • e) ≤
    C * (frobeniusS0 z ((t*d) • e)-frobeniusS0 (b • e) ((t*d) • e))
  rw [frobenius_unit_smul_right e he,frobenius_direction_smul_right,frobenius_unit_smul_right e he]
  have heq : (t*d) * L z - b*(t*d) = t*d^2 := by
    unfold d
    ring
  change (t*d)*(t*d) ≤ C*((t*d)*L z-b*(t*d))
  rw [heq]
  calc
    (t*d)*(t*d) = t*t*d^2 := by ring
    _ ≤ C*t*d^2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCt ht) (sq_nonneg _)
    _ = C*(t*d^2) := by ring

private theorem comparison_gradient_absorb {U : Set Point} (w v q : H10 U)
    {C : ℝ} (hC : 0 ≤ C)
    (hSq : ‖h10GradientCoordinates U q‖^2 ≤ C * (h10PrincipalPart U w q - h10PrincipalPart U v q)) :
    ‖h10GradientCoordinates U q‖ ≤ C * ‖h10GradientCoordinates U (v-w)‖ := by
  have hCross : h10PrincipalPart U w q - h10PrincipalPart U v q =
      inner ℝ (h10GradientCoordinates U (v-w)) (h10GradientCoordinates U q) := by
    let G := h10GradientCoordinates U
    have hInner : inner ℝ (G (v-w)) (G q) = inner ℝ (G v) (G q) - inner ℝ (G w) (G q) :=
      (congrArg (fun t : DirichletGradientCoordinates U => inner ℝ t (G q)) (G.map_sub v w)).trans
        (inner_sub_left (G v) (G w) (G q))
    rw [h10PrincipalPart_eq_neg_gradientCoordinate_inner w q,
      h10PrincipalPart_eq_neg_gradientCoordinate_inner v q, hInner]
    ring
  rw [hCross] at hSq
  have hCS := real_inner_le_norm (h10GradientCoordinates U (v-w)) (h10GradientCoordinates U q)
  have hFin := hSq.trans (mul_le_mul_of_nonneg_left hCS hC)
  by_cases h0 : ‖h10GradientCoordinates U q‖ = 0
  · rw [h0]
    positivity
  · have hPos : 0 < ‖h10GradientCoordinates U q‖ := (norm_nonneg _).lt_of_ne' h0
    apply le_of_mul_le_mul_left _ hPos
    nlinarith only [hFin]

private theorem comparison_test_gradient_bound
    {U : Set Point} (hU : IsOpen U) (e : S0) (he : ‖e‖ = 1)
    {w v q : H10 U} {u φ : Point → S0} {B : Point → ℝ}
    {f : Point → S0} (hf : MemLp f 2 (volume.restrict U))
    (hW : ∀ z : H10 U, h10PrincipalPart U w z = ∫ x in U, frobeniusS0 (f x) (h10Value z x))
    (hB : ContDiffOn ℝ ∞ B U)
    (hSup : ∀ᵐ x ∂volume.restrict U, laplacian B x ≤ (innerSL ℝ e) (f x))
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ U)
    (hφVal : ∀ x ∈ U, φ x = Real.smoothTransition ((innerSL ℝ e) (u x)-B x) • e)
    (hφGrad : ∀ x ∈ U, ∀ j, coordDeriv j φ x =
      (deriv Real.smoothTransition ((innerSL ℝ e) (u x)-B x) *
        ((innerSL ℝ e) (coordDeriv j u x)-coordDeriv j B x)) • e)
    (hVG : h10Gradient v =ᵐ[volume.restrict U] ClassicalGradient u)
    (hQVal : h10Value q =ᵐ[volume.restrict U] φ)
    (hQGrad : h10Gradient q =ᵐ[volume.restrict U] ClassicalGradient φ)
    {C : ℝ} (hC : 0 ≤ C)
    (hDeriv : ∀ t : ℝ, 0 ≤ deriv Real.smoothTransition t ∧ deriv Real.smoothTransition t ≤ C) :
    ‖h10GradientCoordinates U q‖ ≤ C * ‖h10GradientCoordinates U (v-w)‖ := by
  let S : ℝ →L[ℝ] S0 := (ContinuousLinearMap.id ℝ ℝ).smulRight e
  let b : Point → S0 := S ∘ B
  have hB₂ : ContDiffOn ℝ 2 B U := hB.of_le (WithTop.coe_le_coe.mpr le_top)
  have hb : ContDiffOn ℝ 2 b U := S.contDiff.comp_contDiffOn hB₂
  have hbCol (x : Point) (hx : x ∈ U) (j : Fin 3) :
      coordDeriv j b x = coordDeriv j B x • e :=
    coordDeriv_compCLM S (((hB x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) j
  have hbLap (x : Point) (hx : x ∈ U) : laplacian b x = laplacian B x • e :=
    laplacian_compCLM hU hB₂ hx S
  let E (x : Point) := ∑ j : Fin 3, frobeniusS0 (h10Gradient q x j) (h10Gradient q x j)
  let V (x : Point) := -(∑ j : Fin 3, frobeniusS0 (h10Gradient v x j) (h10Gradient q x j))
  let D (x : Point) := -(∑ j : Fin 3, frobeniusS0 (coordDeriv j b x) (coordDeriv j φ x))
  let A (x : Point) := frobeniusS0 (laplacian b x) (φ x)
  obtain ⟨hD,hA,hDG⟩ := green_h10_smoothTest hU hb hφ hφc hφs
  change IntegrableOn D U at hD
  change IntegrableOn A U at hA
  change (∫ x in U, D x) = ∫ x in U, A x at hDG
  have hE : IntegrableOn E U :=
    integrable_finsetSum _ fun j _ => integrable_frobenius_of_memLp (Lp.memLp (q.val.2 j)) (Lp.memLp (q.val.2 j))
  have hV : IntegrableOn V U :=
    (integrable_finsetSum _ fun j _ =>
      integrable_frobenius_of_memLp (Lp.memLp (v.val.2 j)) (Lp.memLp (q.val.2 j))).neg
  have hLocal : E ≤ᵐ[volume.restrict U] (fun x => C * (D x - V x)) := by
    filter_upwards [ae_restrict_mem hU.measurableSet,hVG,hQGrad] with x hx hVx hQx
    simp only [E,D,V,hVx,hQx,ClassicalGradient,neg_sub_neg,← Finset.sum_sub_distrib,Finset.mul_sum,hbCol x hx]
    apply Finset.sum_le_sum
    intro j _
    rw [hφGrad x hx j]
    exact comparison_test_column_bound e he _ _ C _ (hDeriv _).1 (hDeriv _).2
  have hInt : (∫ x in U, E x) ≤ C * ((∫ x in U, D x) - h10PrincipalPart U v q) := by
    have h := integral_mono_ae hE ((hD.sub hV).const_mul C) hLocal
    rw [integral_const_mul] at h
    change (∫ x in U, E x) ≤ C * (∫ x in U, D x - V x) at h
    rw [integral_sub hD hV] at h
    exact h.trans_eq (by rw [h10PrincipalPart_apply])
  have hF := integrable_frobenius_of_memLp hf (Lp.memLp q.val.1)
  have hDA : (∫ x in U, D x) ≤ h10PrincipalPart U w q := by
    rw [hDG,hW]
    apply integral_mono_ae hA hF
    filter_upwards [hSup,hQVal,ae_restrict_mem hU.measurableSet] with x hx hqx hIn
    change A x ≤ frobeniusS0 (f x) (h10Value q x)
    dsimp only [A]
    rw [hqx,hφVal x hIn,hbLap x hIn,frobenius_unit_smul_right e he,frobenius_direction_smul_right]
    rw [mul_comm (laplacian B x)]
    exact mul_le_mul_of_nonneg_left hx (Real.smoothTransition.nonneg _)
  have hGradEnergy : ‖h10GradientCoordinates U q‖^2 = ∫ x in U, E x := by
    have h := h10PrincipalPart_eq_neg_gradientCoordinate_inner q q
    rw [real_inner_self_eq_norm_sq,h10PrincipalPart_apply,integral_neg] at h
    exact (neg_inj.mp h).symm
  apply comparison_gradient_absorb w v q hC
  exact hGradEnergy.trans_le (hInt.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hDA _) hC))

private theorem norm_h10_le_gradient_coordinate_bound {U : Set Point} (hU : IsBoundedDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : H10 U, ‖q‖ ≤ C * ‖h10GradientCoordinates U q‖ := by
  obtain ⟨C,hC⟩ := exists_antilipschitz_h10GradientCoordinates hU.1.measurableSet hU.2.2
  refine ⟨C, C.coe_nonneg, fun q => ?_⟩
  simpa only [dist_zero_right,map_zero] using hC.le_mul_dist q 0

private theorem comparison_cutoff_limit {U : Set Point} (hU : IsOpen U)
    (e : S0) (he : ‖e‖ = 1) (B : Point → ℝ)
    (v q : ℕ → H10 U) (w : H10 U) (u φ : ℕ → Point → S0)
    (hV : Tendsto v atTop (𝓝 w)) (hQ : Tendsto q atTop (𝓝 0))
    (hu : ∀ n, h10Value (v n) =ᵐ[volume.restrict U] u n)
    (hφ : ∀ n, h10Value (q n) =ᵐ[volume.restrict U] φ n)
    (hTest : ∀ n x, x ∈ U → φ n x = Real.smoothTransition ((innerSL ℝ e) (u n x)-B x) • e) :
    ∀ᵐ x ∂volume.restrict U, (innerSL ℝ e) (h10Value w x) ≤ B x := by
  let μ := volume.restrict U
  let P : H10 U → Lp S0 2 μ := fun z => z.val.1
  have hP : Continuous P := continuous_fst.comp continuous_subtype_val
  have hZero : P 0 = 0 := rfl
  have hPV : Tendsto (P ∘ v) atTop (𝓝 (P w)) := hP.continuousAt.tendsto.comp hV
  have hPQ : Tendsto (P ∘ q) atTop (𝓝 0) := by
    rw [← hZero]
    exact hP.continuousAt.tendsto.comp hQ
  obtain ⟨κ,hκ,hκAE⟩ := (tendstoInMeasure_of_tendsto_Lp hPV).exists_seq_tendsto_ae
  obtain ⟨ι,hι,hιAE⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hPQ.comp hκ.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hκAE,hιAE,ae_all_iff.mpr hu,ae_all_iff.mpr hφ,
    Lp.coeFn_zero (α := Point) (E := S0) (p := 2) (μ := μ),
    ae_restrict_mem hU.measurableSet] with x hxv hxq hxu hxφ hZ hxU
  change Tendsto (fun n => h10Value (v (κ n)) x) atTop (𝓝 (h10Value w x)) at hxv
  change Tendsto (fun n => h10Value (q (κ (ι n))) x) atTop
    (𝓝 ((0 : Lp S0 2 μ) x)) at hxq
  rw [hZ] at hxq
  have hvLim : Tendsto (fun n => u (κ (ι n)) x) atTop (𝓝 (h10Value w x)) :=
    (hxv.comp hι.tendsto_atTop).congr fun n => hxu (κ (ι n))
  have hQlim : Tendsto (fun n => φ (κ (ι n)) x) atTop (𝓝 (0 : S0)) :=
    hxq.congr fun n => hxφ (κ (ι n))
  let L : S0 →L[ℝ] ℝ := innerSL ℝ e
  have hxlim : Tendsto (fun n => Real.smoothTransition (L (u (κ (ι n)) x)-B x) • e)
      atTop (𝓝 (Real.smoothTransition (L (h10Value w x)-B x) • e)) :=
    (Real.smoothTransition.continuousAt.tendsto.comp
      ((L.continuous.continuousAt.tendsto.comp hvLim).sub_const (B x))).smul_const e
  have hOther := hxlim.congr fun n => (hTest (κ (ι n)) x hxU).symm
  have hEq := tendsto_nhds_unique hOther hQlim
  have he₀ : e ≠ 0 := by intro heq; simp [heq] at he
  have hTc := (smul_eq_zero.mp hEq).resolve_right he₀
  exact sub_nonpos.mp (Real.smoothTransition.zero_iff_nonpos.mp hTc)

/-- A nonnegative smooth scalar supersolution bounds the corresponding
component of the zero-trace weak Dirichlet field almost everywhere.
The forcing and the tests pair on the original domain. -/
theorem h10_weakDirichlet_component_le_smooth_supersolution
    {U : Set Point} (hU : IsBoundedDomain U)
    (e : S0) (he : ‖e‖ = 1) (w : H10 U)
    {f : Point → S0} (hf : MemLp f 2 (volume.restrict U))
    (hW : ∀ z : H10 U, h10PrincipalPart U w z = ∫ x in U, frobeniusS0 (f x) (h10Value z x))
    {B : Point → ℝ} (hB : ContDiffOn ℝ ∞ B U) (hBPos : ∀ x ∈ U, 0 ≤ B x)
    (hSup : ∀ᵐ x ∂volume.restrict U, laplacian B x ≤ frobeniusS0 e (f x)) :
    ∀ᵐ x ∂volume.restrict U, frobeniusS0 e (h10Value w x) ≤ B x := by
  have hInner (z : S0) : (innerSL ℝ e) z = frobeniusS0 e z :=
    (innerSL_apply_apply ℝ e z).trans (frobenius_inner_eq e z)
  have hSup' : ∀ᵐ x ∂volume.restrict U, laplacian B x ≤ (innerSL ℝ e) (f x) :=
    hSup.mono fun x hx => (hInner (f x)).symm ▸ hx
  obtain ⟨C,hC,hDeriv⟩ := exists_smoothTransition_deriv_bound
  obtain ⟨v,u,hV,hData⟩ := exists_H10_smooth_approximation_subtype w
  choose φ hφS hφC hφU hφData using fun n =>
    exists_compact_smooth_comparison_test hU.1 (innerSL ℝ e) e
      (hData n).1 (hData n).2.1 (hData n).2.2.1 hB hBPos
  choose q hQVal hQGrad using fun n =>
    (hasZeroTrace_of_contDiff_hasCompactSupport hU.1 (hφS n) (hφC n) (hφU n)).exists_H10_with_ae_data hU.1
  have hEst (n : ℕ) : ‖h10GradientCoordinates U (q n)‖ ≤ C * ‖h10GradientCoordinates U (v n-w)‖ :=
    comparison_test_gradient_bound hU.1 e he hf hW hB hSup' (hφS n) (hφC n) (hφU n)
      (fun x hx => (hφData n x hx).1) (fun x hx => (hφData n x hx).2)
      (hData n).2.2.2.2 (hQVal n) (hQGrad n) hC hDeriv
  obtain ⟨K,hK₀,hK⟩ := norm_h10_le_gradient_coordinate_bound hU
  have hL : Tendsto (fun n => ‖h10GradientCoordinates U (v n-w)‖) atTop (𝓝 0) := by
    have hZero : Tendsto (fun n => v n - w) atTop (𝓝 0) := by
      simpa only [sub_self] using hV.sub_const w
    have h := (h10GradientCoordinates U).continuous.continuousAt.tendsto.comp hZero
    simpa only [Function.comp_apply,map_zero,norm_zero] using h.norm
  have hQ : Tendsto q atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using (hL.const_mul C).const_mul K)
      (fun _ => norm_nonneg _) (fun n => ?_)
    exact (hK (q n)).trans (mul_le_mul_of_nonneg_left (hEst n) hK₀)
  have hLimit := comparison_cutoff_limit hU.1 e he B v q w u φ hV hQ
    (fun n => (hData n).2.2.2.1) hQVal (fun n x hx => (hφData n x hx).1)
  exact hLimit.mono fun x hx => hInner (h10Value w x) ▸ hx

end Thesis
