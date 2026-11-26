module

public import Thesis.Variational.GlobalComparison
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! The actual zero-trace field and its weak columns in the frozen graph. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal NNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem norm_twoLp_sub_lt_of_lintegral_lt {μ : Measure Point}
    {f g : Point → S0} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {δ : ℝ} (hδ : 0 < δ)
    (h : (∫⁻ x, ENNReal.ofReal (‖f x - g x‖^2) ∂μ) < ENNReal.ofReal (δ^2)) :
    ‖hf.toLp f - hg.toLp g‖ < δ := by
  let P := hf.toLp f - hg.toLp g
  have hP : (P : Point → S0) =ᵐ[μ] fun x => f x - g x := by
    filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp] with x h₁ h₂ h₃
    exact h₁.trans (congrArg₂ (· - ·) h₂ h₃)
  have hPSq : eLpNorm P 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (‖P x‖ ^ 2) ∂μ := by
    calc
      _ = ∫⁻ x, ‖P x‖ₑ ^ 2 ∂μ := by
        simpa only [ENNReal.rpow_two, NNReal.coe_two, ENNReal.coe_two] using
          (eLpNorm_nnreal_pow_eq_lintegral (f := (P : Point → S0)) (μ := μ) (p := (2 : ℝ≥0)) (by norm_num))
      _ = _ := by
        apply lintegral_congr
        intro x
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hLt : eLpNorm P 2 μ ^ 2 < ENNReal.ofReal (δ^2) := by
    rw [hPSq, lintegral_congr_ae (hP.mono fun x hx => by rw [hx])]
    exact h
  have hReal := (ENNReal.toReal_lt_toReal (ne_of_lt (hLt.trans ENNReal.ofReal_lt_top))
    ENNReal.ofReal_ne_top).2 hLt
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (sq_nonneg _), ← Lp.norm_def] at hReal
  exact (sq_lt_sq₀ (norm_nonneg P) hδ.le).1 hReal

/-- Intrinsic zero trace gives an element of the frozen Sobolev graph
with the original field and gradient columns as its almost-everywhere data. -/
theorem HasZeroTrace.exists_H10_with_ae_data
    {U : Set Point} (hU : IsOpen U) {u : Point → S0} {D : Point → Gradient}
    (h : HasZeroTrace U u D) :
    ∃ v : H10 U, h10Value v =ᵐ[volume.restrict U] u ∧
      h10Gradient v =ᵐ[volume.restrict U] D := by
  let μ := volume.restrict U
  let X : H1Graph U := (h.1.1.toLp u, fun j => (h.1.2.1 j).toLp (fun x => D x j))
  have hX : X ∈ h10Submodule U := by
    change X ∈ closure _
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    obtain ⟨φ, hφ, hc, hSupp, hClose⟩ := h.2 (ENNReal.ofReal (δ^2))
      (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hδ))
    have hφH : MemH1 U φ (ClassicalGradient φ) :=
      (hasZeroTrace_of_contDiff_hasCompactSupport hU hφ hc hSupp).1
    let Y : H1Graph U := (hφH.1.toLp φ, fun j => (hφH.2.1 j).toLp (fun x => coordDeriv j φ x))
    have hGen : Y ∈ Submodule.span ℝ {p : H1Graph U | ∃ ψ : Point → S0,
        ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U ∧
          (p.1 : Point → S0) =ᵐ[μ] ψ ∧
          ∀ j, (p.2 j : Point → S0) =ᵐ[μ] coordDeriv j ψ} :=
      Submodule.subset_span ⟨φ, hφ, hc, hSupp, hφH.1.coeFn_toLp, fun j => (hφH.2.1 j).coeFn_toLp⟩
    refine ⟨Y, hGen, ?_⟩
    have hValue :
        (∫⁻ x, ENNReal.ofReal (‖u x - φ x‖^2) ∂μ) ≤ h1Deviation U u φ D (ClassicalGradient φ) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    have hColumn (j : Fin 3) :
        (∫⁻ x, ENNReal.ofReal (‖D x j - coordDeriv j φ x‖^2) ∂μ) ≤
          h1Deviation U u φ D (ClassicalGradient φ) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal ((Finset.single_le_sum
        (f := fun i : Fin 3 => ‖D x i - coordDeriv i φ x‖^2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j)).trans (le_add_of_nonneg_left (sq_nonneg _)))
    have h₁ : ‖X.1 - Y.1‖ < δ :=
      norm_twoLp_sub_lt_of_lintegral_lt h.1.1 hφH.1 hδ (hValue.trans_lt hClose)
    have h₂ (j : Fin 3) : ‖X.2 j - Y.2 j‖ < δ :=
      norm_twoLp_sub_lt_of_lintegral_lt (h.1.2.1 j) (hφH.2.1 j) hδ ((hColumn j).trans_lt hClose)
    rw [dist_eq_norm, Prod.norm_def, max_lt_iff]
    exact ⟨h₁, (pi_norm_lt_iff hδ).2 h₂⟩
  let v : H10 U := ⟨X, hX⟩
  refine ⟨v, h.1.1.coeFn_toLp, ?_⟩
  have hD (j : Fin 3) :
      (fun x => h10Gradient v x j) =ᵐ[μ] fun x => D x j := (h.1.2.1 j).coeFn_toLp
  filter_upwards [Filter.eventually_all.mpr hD] with x hx
  exact funext hx

/-- Subtraction and scaling in the frozen graph keep the literal
weak data and avoid changing the common boundary trace. -/
theorem exists_scaled_H10_difference_of_sameTrace
    {U : Set Point} (hU : IsOpen U) {u q b : Point → S0} {Du Dq Db : Point → Gradient}
    (hu : SameTrace U u b Du Db) (hq : SameTrace U q b Dq Db) (c : ℝ) :
    ∃ v : H10 U,
      h10Value v =ᵐ[volume.restrict U] (fun x => c • (u x - q x)) ∧
      h10Gradient v =ᵐ[volume.restrict U] (fun x => c • (Du x - Dq x)) := by
  obtain ⟨v₁, hVal₁, hGrad₁⟩ := hu.exists_H10_with_ae_data hU
  obtain ⟨v₂, hVal₂, hGrad₂⟩ := hq.exists_H10_with_ae_data hU
  let v := c • (v₁ - v₂)
  refine ⟨v, ?_, ?_⟩
  · filter_upwards [hVal₁, hVal₂, Lp.coeFn_sub v₁.val.1 v₂.val.1,
      Lp.coeFn_smul c (v₁.val.1 - v₂.val.1)] with x h₁ h₂ hSub hc
    change (c • (v₁.val.1 - v₂.val.1)) x = c • (u x - q x)
    rw [hc]
    change c • (v₁.val.1 - v₂.val.1) x = _
    rw [hSub]
    have h₁' : v₁.val.1 x = u x - b x := h₁
    have h₂' : v₂.val.1 x = q x - b x := h₂
    change c • (v₁.val.1 x - v₂.val.1 x) = _
    rw [h₁', h₂', sub_sub_sub_cancel_right]
  · have hSub (j : Fin 3) := Lp.coeFn_sub (v₁.val.2 j) (v₂.val.2 j)
    have hc (j : Fin 3) := Lp.coeFn_smul c (v₁.val.2 j - v₂.val.2 j)
    filter_upwards [hGrad₁, hGrad₂, Filter.eventually_all.mpr hSub, Filter.eventually_all.mpr hc]
      with x h₁ h₂ hsub hscale
    funext j
    change (c • (v₁.val.2 j - v₂.val.2 j)) x = c • (Du x j - Dq x j)
    rw [hscale j]
    change c • (v₁.val.2 j - v₂.val.2 j) x = _
    rw [hsub j]
    have h₁' : v₁.val.2 j x = Du x j - Db x j := congrFun h₁ j
    have h₂' : v₂.val.2 j x = Dq x j - Db x j := congrFun h₂ j
    change c • (v₁.val.2 j x - v₂.val.2 j x) = _
    rw [h₁', h₂', sub_sub_sub_cancel_right]

/-- Compactly supported smooth data determine continuous functionals on
the actual zero-trace graph. -/
theorem H10.continuousLinearMap_eq_of_smooth_tests
    {U : Set Point} (F G : H10 U →L[ℝ] ℝ)
    (h : ∀ (v : H10 U) (φ : Point → S0), ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      h10Value v =ᵐ[volume.restrict U] φ →
      (∀ j, (fun x => h10Gradient v x j) =ᵐ[volume.restrict U] coordDeriv j φ) →
      F v = G v) : F = G := by
  let S : Set (H1Graph U) := {p | ∃ φ : Point → S0,
    ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
      (p.1 : Point → S0) =ᵐ[volume.restrict U] φ ∧
      ∀ j, (p.2 j : Point → S0) =ᵐ[volume.restrict U] coordDeriv j φ}
  let T : Set (H10 U) := Subtype.val ⁻¹' S
  have hS : S ⊆ (h10Submodule U : Set (H1Graph U)) := fun u hu =>
    Submodule.le_topologicalClosure (Submodule.span ℝ S) (Submodule.subset_span hu)
  have hImage : (Subtype.val : H10 U → H1Graph U) '' T = S := by
    ext p
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hp
      exact ⟨⟨p, hS hp⟩, hp, rfl⟩
  have hSpan : (Subtype.val : H10 U → H1Graph U) '' (Submodule.span ℝ T : Set (H10 U)) =
      (Submodule.span ℝ S : Set (H1Graph U)) := by
    change ((Submodule.span ℝ T).map (h10Submodule U).subtype : Set (H1Graph U)) = _
    rw [Submodule.map_span]
    exact congrArg (fun V : Set (H1Graph U) => (Submodule.span ℝ V : Set (H1Graph U))) hImage
  have hDense : Dense (Submodule.span ℝ T : Set (H10 U)) := by
    intro v
    rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, hSpan]
    exact v.property
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.eqOn_closure_span ?_ (hDense v)
  intro u hu
  obtain ⟨φ, hφ, hc, hSupp, hVal, hD⟩ := hu
  exact h u φ hφ hc hSupp hVal hD

end Thesis

end
