module

public import Thesis.External.DirichletPoissonHolder
public import Thesis.Variational.SmoothWallGeometry
import Thesis.Variational.FirstCorrectionEquations
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Hölder convergence on the closed domain from dense interior convergence. -/

public section

open Filter Set Topology
open scoped ContDiff ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem exists_positive_rpow_modulus {β H τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) :
    ∃ r > 0, ∀ d : ℝ, 0 ≤ d → d < r → H * d ^ β < τ := by
  have hC := (Real.continuousAt_rpow_const (0 : ℝ) β (Or.inr hβ.le)).const_mul H
  have hT : Tendsto (fun d : ℝ => H * d^β) (𝓝 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hβ.ne', mul_zero] using hC.tendsto
  obtain ⟨r, hr, hR⟩ := Metric.mem_nhds_iff.mp (hT.eventually_lt_const hτ)
  exact ⟨r, hr, fun d hd h => hR (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hd] using h)⟩

/-- Eventual equicontinuity and convergence on a dense part of a compact set
give uniform convergence on the compact set. -/
theorem tendstoUniformlyOn_of_holder_and_dense
    {E : Type*} [NormedAddCommGroup E] {K A : Set Point}
    (hK : IsCompact K) (hAK : A ⊆ K) (hKA : K ⊆ closure A)
    {f : ℕ → Point → E} {g : Point → E} (hg : ContinuousOn g K)
    {β H : ℝ} (hβ : 0 < β)
    (hF : ∀ᶠ n in atTop, ∀ x ∈ K, ∀ y ∈ K, ‖f n x - f n y‖ ≤ H * dist x y ^ β)
    (hP : ∀ x ∈ A, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    TendstoUniformlyOn f g atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hε₃ : 0 < ε / 3 := by positivity
  obtain ⟨r₀, hr₀, hg₀⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hg) (ε / 3) hε₃
  obtain ⟨r₁, hr₁, hF₁⟩ := exists_positive_rpow_modulus (H := H) hβ hε₃
  let r := min r₀ r₁
  have hr : 0 < r := lt_min hr₀ hr₁
  let V (a : A) := Metric.ball (a : Point) r
  have hCover : K ⊆ ⋃ a : A, V a := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hKA hx) r hr
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V (fun _ => Metric.isOpen_ball) hCover
  have hClose : ∀ᶠ n in atTop, ∀ y ∈ I, dist (g y) (f n y) < ε / 3 := by
    apply (Filter.eventually_all_finset I).2
    intro y _
    filter_upwards [(Metric.tendsto_nhds.mp (hP y y.property)) (ε / 3) hε₃] with n hn
    exact dist_comm (g y) (f n y) ▸ hn
  filter_upwards [hF, hClose] with n hn hnI x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hI hx)
  have hyK := hAK y.property
  have h₀ := hg₀ x hx y hyK (hxy.trans_le (min_le_left _ _))
  have h₁ := hnI y hy
  have hyx : dist (y : Point) x < r₁ :=
    (dist_comm x (y : Point)) ▸ (hxy.trans_le (min_le_right _ _))
  have h₂ : dist (f n y) (f n x) < ε / 3 :=
    (dist_eq_norm (f n y) (f n x)).symm ▸ (hn y hyK x hx).trans_lt (hF₁ _ dist_nonneg hyx)
  have hT := dist_triangle (g x) (g y) (f n x)
  have hT' := dist_triangle (g y) (f n y) (f n x)
  linarith only [hT, hT', h₀, h₁, h₂]

private theorem holderSeminorm_le_of_norm_sub_le
    {E : Type*} [NormedAddCommGroup E] {K : Set Point} {f : Point → E} {α C : ℝ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (h : ∀ x ∈ K, ∀ y ∈ K, ‖f x - f y‖ ≤ C * dist x y ^ α) :
    holderSeminorm α K f ≤ ENNReal.ofReal C := by
  apply iSup_le
  intro x
  apply iSup_le
  intro y
  apply ENNReal.ofReal_le_ofReal
  by_cases hd : dist (x : Point) (y : Point) = 0
  · rw [hd, Real.zero_rpow hα.ne', div_zero]
    exact hC
  · exact (div_le_iff₀ (Real.rpow_pos_of_pos (lt_of_le_of_ne dist_nonneg (Ne.symm hd)) α)).2
      (h x x.property y y.property)

theorem holderSeminorm_lt_top_of_higherHolder
    {E : Type*} [NormedAddCommGroup E] {K : Set Point} (hK : IsCompact K) {f : Point → E}
    {α β C : ℝ} (hα : 0 < α) (hαβ : α < β) (hC : 0 ≤ C)
    (h : ∀ x ∈ K, ∀ y ∈ K, ‖f x - f y‖ ≤ C * dist x y ^ β) :
    holderSeminorm α K f < ⊤ := by
  let R := max 1 (Metric.diam K)
  have hR : 0 ≤ R := (zero_le_one (α := ℝ)).trans (le_max_left _ _)
  refine (holderSeminorm_le_of_norm_sub_le (C := C * R^(β-α)) hα (mul_nonneg hC (Real.rpow_nonneg hR _))
    ?_).trans_lt ENNReal.ofReal_lt_top
  intro x hx y hy
  let d := dist x y
  have hd : d ≤ R := (Metric.dist_le_diam_of_mem hK.isBounded hx hy).trans (le_max_right _ _)
  have hScale : d^β ≤ R^(β-α) * d^α := by
    by_cases hd₀ : d = 0
    · rw [hd₀, Real.zero_rpow (hα.trans hαβ).ne', Real.zero_rpow hα.ne', mul_zero]
    · have he : d^β = d^(β-α) * d^α := by
        rw [← Real.rpow_add (lt_of_le_of_ne dist_nonneg (Ne.symm hd₀)), sub_add_cancel]
      rw [he]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow dist_nonneg hd (sub_nonneg.mpr hαβ.le))
        (Real.rpow_nonneg dist_nonneg _)
  exact (h x hx y hy).trans ((mul_le_mul_of_nonneg_left hScale hC).trans_eq (mul_assoc _ _ _).symm)

private theorem norm_sub_le_of_uniform_limit_of_holder
    {E : Type*} [NormedAddCommGroup E] {K : Set Point}
    {f : ℕ → Point → E} {g : Point → E} (hU : TendstoUniformlyOn f g atTop K)
    {β H : ℝ} (hF : ∀ᶠ n in atTop, ∀ x ∈ K, ∀ y ∈ K, ‖f n x - f n y‖ ≤ H * dist x y ^ β) :
    ∀ x ∈ K, ∀ y ∈ K, ‖g x - g y‖ ≤ H * dist x y ^ β := by
  intro x hx y hy
  exact le_of_tendsto (((hU.tendsto_at hx).sub (hU.tendsto_at hy)).norm)
    (hF.mono fun n hn => hn x hx y hy)

/-- Uniform convergence and an eventual bound at a larger Hölder exponent
give convergence of the difference at the smaller exponent. -/
theorem tendsto_holderSeminorm_sub_of_uniformlyOn_and_holder
    {E : Type*} [NormedAddCommGroup E] {K : Set Point}
    {f : ℕ → Point → E} {g : Point → E} (hU : TendstoUniformlyOn f g atTop K)
    {α β H : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hF : ∀ᶠ n in atTop, ∀ x ∈ K, ∀ y ∈ K, ‖f n x - f n y‖ ≤ H * dist x y ^ β) :
    Tendsto (fun n => holderSeminorm α K (f n - g)) atTop (𝓝 0) := by
  have hg := norm_sub_le_of_uniform_limit_of_holder hU hF
  apply ENNReal.tendsto_nhds_zero.mpr
  intro η hη
  by_cases hTop : η = ⊤
  · simp [hTop]
  let τ := η.toReal
  have hτ : 0 < τ := ENNReal.toReal_pos hη.ne' hTop
  obtain ⟨r, hr, hSmall⟩ := exists_positive_rpow_modulus (H := 2 * H) (sub_pos.mpr hαβ) hτ
  have hrα : 0 < r^α := Real.rpow_pos_of_pos hr α
  have hE : 0 < τ * r^α / 2 := by positivity
  filter_upwards [hF, Metric.tendstoUniformlyOn_iff.mp hU (τ*r^α/2) hE] with n hn hClose
  refine (holderSeminorm_le_of_norm_sub_le hα hτ.le ?_).trans ENNReal.ofReal_toReal_le
  intro x hx y hy
  let d := dist x y
  have hd : 0 ≤ d := dist_nonneg
  by_cases hd₀ : d = 0
  · have hxy : x = y := dist_eq_zero.mp hd₀
    subst y
    simp [Real.zero_rpow hα.ne']
  have hdpos := lt_of_le_of_ne hd (Ne.symm hd₀)
  by_cases hNear : d < r
  · have hsplit : (f n - g) x - (f n - g) y =
        (f n x - f n y) - (g x - g y) := by simp only [Pi.sub_apply]; abel
    calc
      _ ≤ (H * d^β) + (H * d^β) := by
        rw [hsplit]
        exact (norm_sub_le _ _).trans (add_le_add (hn x hx y hy) (hg x hx y hy))
      _ = (2 * H * d^(β-α)) * d^α := by
        rw [mul_assoc, ← Real.rpow_add hdpos, sub_add_cancel]
        ring
      _ ≤ τ * d^α := mul_le_mul_of_nonneg_right (hSmall d hd hNear).le (Real.rpow_nonneg hd _)
  · have hx' : ‖(f n - g) x‖ < τ*r^α/2 := by
      simpa only [Pi.sub_apply, ← dist_eq_norm, dist_comm (f n x) (g x)] using hClose x hx
    have hy' : ‖(f n - g) y‖ < τ*r^α/2 := by
      simpa only [Pi.sub_apply, ← dist_eq_norm, dist_comm (f n y) (g y)] using hClose y hy
    calc
      _ ≤ ‖(f n - g) x‖ + ‖(f n - g) y‖ := norm_sub_le _ _
      _ ≤ τ*r^α := by linarith only [hx', hy']
      _ ≤ τ*d^α := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le (le_of_not_gt hNear) hα.le) hτ.le

theorem exists_value_laplacian_bound_of_contDiffOn_closure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Point} (hU : IsSmoothDomain U) {v : Point → E} (hv : ContDiffOn ℝ 2 v (closure U)) :
    ∃ M F : ℝ, 0 ≤ M ∧ 0 ≤ F ∧
      (∀ x ∈ U, ‖v x‖ ≤ M) ∧ ∀ x ∈ U, ‖laplacian v x‖ ≤ F := by
  let W := closure U
  let G (x : Point) := ∑ j : Fin 3, iteratedFDerivWithin ℝ 2 v W x (fun _ => axis j)
  have hW : IsCompact W := hU.1.2.2.isCompact_closure
  have hC (j : Fin 3) : ContinuousOn (fun x => iteratedFDerivWithin ℝ 2 v W x (fun _ => axis j)) W :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Point) E (fun _ => axis j)).continuous.comp_continuousOn
      (hv.continuousOn_iteratedFDerivWithin (by norm_num) hU.uniqueDiffOn_closure)
  have hG : ContinuousOn G W := continuousOn_finsetSum _ fun j _ => hC j
  obtain ⟨M, hM⟩ := hW.exists_bound_of_continuousOn hv.continuousOn
  obtain ⟨F, hF⟩ := hW.exists_bound_of_continuousOn hG
  refine ⟨max M 0, max F 0, le_max_right _ _, le_max_right _ _,
    fun x hx => (hM x (subset_closure hx)).trans (le_max_left _ _), ?_⟩
  intro x hx
  have hxC := (hv x (subset_closure hx)).contDiffAt
    (mem_of_superset (hU.1.1.mem_nhds hx) subset_closure)
  have hxEq : G x = laplacian v x := by
    unfold G laplacian
    apply Finset.sum_congr rfl
    intro j _
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn_closure hxC (subset_closure hx)]
    exact (coordDeriv_twice_eq_iteratedFDeriv_two hxC j).symm
  rw [← hxEq]
  exact (hF x (subset_closure hx)).trans (le_max_left _ _)

/-- Bounded Poisson data and zero boundary trace turn convergence of the
values and classical columns in the open domain into the prescribed
closed-domain Hölder convergence. -/
theorem convergesC1HolderClosure_of_zero_trace_Poisson
    (hPoisson : External.GlobalDirichletPoissonGradientHolder)
    {U : Set Point} (hU : IsSmoothDomain U)
    (v : ℕ → Point → S0) (q : Point → S0)
    (hv : ∀ n, ContDiffOn ℝ 2 (v n) (closure U)) (hq : ContDiffOn ℝ 1 q (closure U))
    (hTrace : ∀ n, EqOn (v n) (fun _ => 0) (frontier U))
    (hPoint : ∀ x ∈ U, Tendsto (fun n => v n x) atTop (𝓝 (q x)) ∧
      Tendsto (fun n => ClassicalGradient (v n) x) atTop (𝓝 (ClassicalGradient q x)))
    {M F : ℝ} (hM : 0 ≤ M) (hF : 0 ≤ F)
    (hB : ∀ᶠ n in atTop, (∀ x ∈ U, ‖v n x‖ ≤ M) ∧ ∀ x ∈ U, ‖laplacian (v n) x‖ ≤ F)
    {α : ℝ} (hα : 0 < α) (hα₁ : α < 1) :
    ConvergesC1HolderLoc α U ∅ v q := by
  let W := closure U
  let D (w : Point → S0) (x : Point) (j : Fin 3) := fderivWithin ℝ w W x (axis j)
  let β := (α + 1) / 2
  have hαβ : α < β := by dsimp only [β]; linarith only [hα₁]
  have hβ : 0 < β := hα.trans hαβ
  have hβ₁ : β < 1 := by dsimp only [β]; linarith only [hα₁]
  obtain ⟨C, hC, hReg⟩ := hPoisson U hU β hβ hβ₁
  have hW : IsCompact W := hU.1.2.2.isCompact_closure
  have hv₁ (n : ℕ) : ContDiffOn ℝ 1 (v n) W := (hv n).of_le (by norm_num)
  have hDcl {w : Point → S0} (hw : ContDiffOn ℝ 1 w W) : ContinuousOn (D w) W := by
    apply continuousOn_pi.mpr
    intro j
    exact (ContinuousLinearMap.apply ℝ S0 (axis j)).continuous.comp_continuousOn
      (hw.continuousOn_fderivWithin hU.uniqueDiffOn_closure le_rfl)
  have hDint {w : Point → S0} (hw : ContDiffOn ℝ 1 w W) (x : Point) (hx : x ∈ U) :
      D w x = ClassicalGradient w x := by
    have hNear := mem_of_superset (hU.1.1.mem_nhds hx) subset_closure
    have hDiff := ((hw x (subset_closure hx)).contDiffAt hNear).differentiableAt one_ne_zero
    funext j
    exact DFunLike.congr_fun (fderivWithin_eq_fderiv (uniqueDiffWithinAt_of_mem_nhds hNear) hDiff) (axis j)
  let H := C * (M + F)
  have hH : 0 ≤ H := mul_nonneg hC.le (add_nonneg hM hF)
  have hHold : ∀ᶠ n in atTop, ∀ x ∈ W, ∀ y ∈ W,
      ‖v n x - v n y‖ + ‖D (v n) x - D (v n) y‖ ≤ H * dist x y^β := by
    filter_upwards [hB] with n hn
    exact (hReg (v n) (hv n) (hTrace n) M F hM hF hn.1 hn.2).2
  have hHold₀ := hHold.mono fun n hn x hx y hy =>
    (le_add_of_nonneg_right (norm_nonneg (D (v n) x - D (v n) y))).trans (hn x hx y hy)
  have hHold₁ := hHold.mono fun n hn x hx y hy =>
    (le_add_of_nonneg_left (norm_nonneg (v n x - v n y))).trans (hn x hx y hy)
  have hV : TendstoUniformlyOn v q atTop W :=
    tendstoUniformlyOn_of_holder_and_dense hW subset_closure subset_rfl hq.continuousOn hβ hHold₀
      (fun x hx => (hPoint x hx).1)
  have hDu : TendstoUniformlyOn (fun n => D (v n)) (D q) atTop W := by
    apply tendstoUniformlyOn_of_holder_and_dense hW subset_closure subset_rfl (hDcl hq) hβ hHold₁
    intro x hx
    rw [hDint hq x hx]
    have h := (hPoint x hx).2
    exact h.congr' (Eventually.of_forall fun n => (hDint (hv₁ n) x hx).symm)
  simp only [ConvergesC1HolderLoc, Set.sdiff_empty]
  refine ⟨hv₁, hq, ?_⟩
  intro K hK hKw
  have hHk (n : ℕ) : holderSeminorm α K (D (v n)) < ⊤ := by
    obtain ⟨Mₙ, Fₙ, hMₙ, hFₙ, hm, hf⟩ := exists_value_laplacian_bound_of_contDiffOn_closure hU (hv n)
    have hT := (hReg (v n) (hv n) (hTrace n) Mₙ Fₙ hMₙ hFₙ hm hf).2
    apply holderSeminorm_lt_top_of_higherHolder hK hα hαβ (mul_nonneg hC.le (add_nonneg hMₙ hFₙ))
    exact fun x hx y hy => (le_add_of_nonneg_left (norm_nonneg (v n x - v n y))).trans (hT x (hKw hx) y (hKw hy))
  have hGk : holderSeminorm α K (D q) < ⊤ := by
    apply holderSeminorm_lt_top_of_higherHolder hK hα hαβ hH
    exact fun x hx y hy => norm_sub_le_of_uniform_limit_of_holder hDu hHold₁ x (hKw hx) y (hKw hy)
  exact ⟨hHk, hGk, hV.mono hKw, hDu.mono hKw,
    tendsto_holderSeminorm_sub_of_uniformlyOn_and_holder (hDu.mono hKw) hα hαβ
      (hHold₁.mono fun n hn x hx y hy => hn x (hKw hx) y (hKw hy))⟩

end Thesis

end
