module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Completeness

/-! Differentiating the coefficient average along a straight segment. -/

public section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff Interval

set_option autoImplicit false
noncomputable section

namespace Thesis

universe u

private theorem mem_closedBall_of_pair_nearby
    {H : Type*} [NormedAddCommGroup H] {x y : H} (hy : y ∈ Metric.ball x 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (y,t) ∈ Metric.closedBall (0 : H × ℝ) (‖x‖ + 1) := by
  apply mem_closedBall_zero_iff.mpr
  rw [Prod.norm_def, Real.norm_of_nonneg ht.1]
  refine max_le ?_ (ht.2.trans (le_add_of_nonneg_left (norm_nonneg _)))
  have hD : ‖y - x‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hy
  have hT := norm_add_le (y-x) x
  rw [sub_add_cancel] at hT
  linarith only [hT, hD]

private theorem continuous_intervalAverage_of_contDiff_joint
    {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (J : H × ℝ → F) (hJ : ContDiff ℝ 1 J) :
    Continuous (fun p : H => ∫ t in (0 : ℝ)..1, J (p,t)) := by
  apply continuous_iff_continuousAt.2
  intro p
  let K := Metric.closedBall (0 : H × ℝ) (‖p‖ + 1)
  obtain ⟨L, hL⟩ := hJ.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (0 : H × ℝ) (‖p‖ + 1)) (isCompact_closedBall _ _)
  have hInt (q : H) : IntervalIntegrable (fun t => J (q,t)) volume (0 : ℝ) 1 :=
    (hJ.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  have hBound : ∀ᶠ q in 𝓝 p,
      ‖(∫ t in (0 : ℝ)..1, J (q,t)) - ∫ t in (0 : ℝ)..1, J (p,t)‖ ≤ (L : ℝ) * ‖q-p‖ := by
    filter_upwards [Metric.ball_mem_nhds p zero_lt_one] with q hq
    have hTerm (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) : ‖J (q,t) - J (p,t)‖ ≤ (L : ℝ)*‖q-p‖ := by
      have ht' : t ∈ Icc (0 : ℝ) 1 :=
        Ioc_subset_Icc_self ((Set.uIoc_of_le (zero_le_one (α := ℝ))) ▸ ht)
      have hQ : (q,t) ∈ K := mem_closedBall_of_pair_nearby hq ht'
      have hP : (p,t) ∈ K := mem_closedBall_of_pair_nearby (Metric.mem_ball_self zero_lt_one) ht'
      have h := hL.dist_le_mul (q,t) hQ (p,t) hP
      rw [dist_eq_norm (J (q,t)) (J (p,t)), Prod.dist_eq, dist_self,
        max_eq_left (dist_nonneg : 0 ≤ dist q p),
        dist_eq_norm] at h
      exact h
    rw [← intervalIntegral.integral_sub (hInt q) (hInt p)]
    simpa only [sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hTerm
  have hZero : Tendsto (fun q : H => (L : ℝ) * ‖q-p‖) (𝓝 p) (𝓝 0) := by
    have hN : Continuous (fun q : H => ‖q-p‖) := (continuous_id.sub continuous_const).norm
    have hMul : Continuous (fun q : H => (L : ℝ) * ‖q-p‖) := continuous_const.mul hN
    simpa only [sub_self, norm_zero, mul_zero] using (hMul.continuousAt (x := p)).tendsto
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hZero
    (Eventually.of_forall fun _ => norm_nonneg _) hBound

private theorem hasFDerivAt_intervalAverage_of_smooth_joint
    {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (J : H×ℝ → F) (hJ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) J) (q : H) :
    HasFDerivAt (fun p : H => ∫ t in (0 : ℝ)..1, J (p,t))
      (∫ t in (0 : ℝ)..1, (fderiv ℝ J (q,t)).comp (ContinuousLinearMap.inl ℝ H ℝ)) q := by
  let L := ContinuousLinearMap.inl ℝ H ℝ
  let J₁ (x : H × ℝ) := (fderiv ℝ J x).comp L
  have hJ₁ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) J₁ :=
    (hJ.fderiv_right (m := (↑(⊤ : ℕ∞) : ℕ∞ω)) (by simp)).clm_comp contDiff_const
  have hC (p : H) : Continuous (fun t => J (p,t)) :=
    hJ.continuous.comp (continuous_const.prodMk continuous_id)
  have hC₁ : Continuous (fun t => J₁ (q,t)) := hJ₁.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : H×ℝ) (‖q‖+1)).exists_bound_of_continuousOn
    hJ₁.continuous.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun p t => J₁ (p,t)) (bound := fun _ => B) (Metric.ball_mem_nhds q zero_lt_one)
    (Eventually.of_forall fun p => (hC p).aestronglyMeasurable)
    ((hC q).intervalIntegrable 0 1) hC₁.aestronglyMeasurable
  · exact Eventually.of_forall fun t ht p hp =>
      hB _ (mem_closedBall_of_pair_nearby hp
        (Ioc_subset_Icc_self ((Set.uIoc_of_le (zero_le_one (α := ℝ))) ▸ ht)))
  · exact intervalIntegrable_const
  · apply Eventually.of_forall
    intro t _ p _
    have hL : HasFDerivAt (fun v : H => (v,t)) L p := by
      have h := (L.hasFDerivAt (x := p)).add_const ((0 : H), t)
      exact h.congr_of_eventuallyEq (Eventually.of_forall fun y => by
        change (y,t) = (y,(0 : ℝ)) + ((0 : H),t)
        simp)
    exact ((hJ.differentiable (by simp) (p,t)).hasFDerivAt.comp p hL)

private theorem contDiff_nat_intervalAverage_of_smooth_joint
    (n : ℕ) {H F : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (J : H×ℝ → F) (hJ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) J) :
    ContDiff ℝ n (fun p : H => ∫ t in (0 : ℝ)..1, J (p,t)) := by
  induction n generalizing F with
  | zero =>
    exact contDiff_zero.2 (continuous_intervalAverage_of_contDiff_joint J
      (hJ.of_le (WithTop.coe_le_coe.mpr le_top)))
  | succ n ih =>
    let L := ContinuousLinearMap.inl ℝ H ℝ
    let J₁ (x : H × ℝ) := (fderiv ℝ J x).comp L
    have hJ₁ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) J₁ :=
      (hJ.fderiv_right (m := (↑(⊤ : ℕ∞) : ℕ∞ω)) (by simp)).clm_comp contDiff_const
    let A (p : H) := ∫ t in (0 : ℝ)..1, J (p,t)
    let A₁ (p : H) := ∫ t in (0 : ℝ)..1, J₁ (p,t)
    have hDer (p : H) : HasFDerivAt A (A₁ p) p := hasFDerivAt_intervalAverage_of_smooth_joint J hJ p
    have hD : fderiv ℝ A = A₁ := funext fun p => (hDer p).fderiv
    have hA₁ : ContDiff ℝ n A₁ := ih J₁ hJ₁
    have hA : ContDiff ℝ ((n : ℕ∞ω) + 1) A :=
      contDiff_succ_iff_fderiv.2 ⟨fun p => (hDer p).differentiableAt, by simp, hD.symm ▸ hA₁⟩
    simpa only [Nat.cast_succ] using hA

/-- All derivatives of the coefficient average follow from the
corresponding derivatives of the joint endpoint integrand. -/
theorem contDiff_affineSegmentAverage
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : E → F) (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) g) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω)
      (fun p : E × E => ∫ t in (0 : ℝ)..1, g ((1-t) • p.1 + t • p.2)) := by
  let J (x : (E×E)×ℝ) := g ((1-x.2) • x.1.1 + x.2 • x.1.2)
  have h₁ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fun x : (E×E)×ℝ => x.1.1) :=
    contDiff_fst.comp contDiff_fst
  have h₂ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fun x : (E×E)×ℝ => x.1.2) :=
    contDiff_snd.comp contDiff_fst
  have hJ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) J :=
    hg.comp (((contDiff_const.sub contDiff_snd).smul h₁).add (contDiff_snd.smul h₂))
  exact contDiff_infty.2 (fun n => contDiff_nat_intervalAverage_of_smooth_joint n J hJ)

end Thesis

end
