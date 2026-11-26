module

public import Thesis.Variational.OddWallReflection
public import Thesis.Variational.WholeSpaceLipschitzColumnsHessian

/-! The global Hessian estimate in a flat half-space with zero wall values. -/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal Topology

namespace Thesis

theorem laplacian_eventuallyEq_eq {u v : Point → ℝ} {x : Point}
    (h : u =ᶠ[𝓝 x] v) : laplacian u x = laplacian v x := by
  unfold laplacian
  refine Finset.sum_congr rfl fun i _ => ?_
  have hD : coordDeriv i u =ᶠ[𝓝 x] coordDeriv i v := (h.fderiv (𝕜 := ℝ)).mono
    fun _ hy => DFunLike.congr_fun hy (axis i)
  exact DFunLike.congr_fun (hD.fderiv_eq (𝕜 := ℝ)) (axis i)

private theorem oddWallReflection_eventuallyEq_pos {f : Point → ℝ}
    {x : Point} (hx : x ∈ positiveWallHalf) :
    oddWallReflection f =ᶠ[𝓝 x] f :=
  mem_of_superset (isOpen_positiveWallHalf.mem_nhds hx) fun y hy =>
    oddWallReflection_eqOn_closed (show y ∈ closedWallHalf from (show 0 < y 2 from hy).le)

private theorem oddWallReflection_eventuallyEq_neg {f : Point → ℝ}
    (h0 : EqOn f 0 flatWall) {x : Point} (hx : x ∈ negativeWallHalf) :
    oddWallReflection f =ᶠ[𝓝 x] -(f ∘ normalReflection) :=
  mem_of_superset (isOpen_negativeWallHalf.mem_nhds hx) fun y hy =>
    oddWallReflection_eqOn_lower h0 (show y ∈ lowerClosedWallHalf from (show y 2 < 0 from hy).le)

private theorem laplacian_reflect_neg {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f (normalReflection x)) :
    laplacian (-(f ∘ normalReflection)) x = -laplacian f (normalReflection x) := by
  let B := EuclideanSpace.basisFun (Fin 3) ℝ
  have hC : ContDiffAt ℝ 2 (f ∘ normalReflection) x := hf.comp x normalReflection.contDiff.contDiffAt
  have hTr := laplacian_eq_second_derivative_basis_of_contDiffAt hC.neg B
  change laplacian (-(f ∘ normalReflection)) x = _ at hTr
  rw [hTr,
    laplacian_eq_second_derivative_basis_of_contDiffAt hf (B.map normalReflection), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  change iteratedFDeriv ℝ 2 (-(f ∘ normalReflection)) x ![B j,B j] = _
  rw [iteratedFDeriv_neg_apply,neg_apply]
  congr 1
  rw [iteratedFDeriv_two_comp_apply_of_contDiffAt hf normalReflection.contDiff.contDiffAt]
  have hR : fderiv ℝ normalReflection x = normalReflection.toContinuousLinearMap :=
    normalReflection.toContinuousLinearMap.hasFDerivAt.fderiv
  have h0 : iteratedFDeriv ℝ 2 normalReflection x = 0 := by
    have hr : fderiv ℝ (⇑normalReflection) = fun _ => normalReflection.toContinuousLinearMap :=
      funext fun y => normalReflection.toContinuousLinearMap.hasFDerivAt.fderiv
    apply ContinuousMultilinearMap.ext
    intro m
    simp only [iteratedFDeriv_two_apply,hr,fderiv_fun_const,Pi.zero_apply,zero_apply]
  rw [hR,h0]
  simp [B]

/-- The reflected Laplacian is odd away from the null wall. -/
theorem laplacian_oddWallReflection_eqOn_negative {f : Point → ℝ}
    (hf : ContDiffOn ℝ 2 f closedWallHalf) (h0 : EqOn f 0 flatWall) :
    EqOn (laplacian (oddWallReflection f)) (fun x => -laplacian f (normalReflection x)) negativeWallHalf := by
  intro x hx
  rw [laplacian_eventuallyEq_eq (oddWallReflection_eventuallyEq_neg h0 hx)]
  have hp : normalReflection x ∈ positiveWallHalf := by
    change 0 < normalReflection x 2
    rw [normalReflection_height]
    exact neg_pos.mpr hx
  have nh : closedWallHalf ∈ 𝓝 (normalReflection x) :=
    mem_of_superset (isOpen_positiveWallHalf.mem_nhds hp) fun y hy => (show 0 < y 2 from hy).le
  exact laplacian_reflect_neg ((hf _ (show 0 ≤ normalReflection x 2 from (show 0 < normalReflection x 2 from hp).le)).contDiffAt nh)

theorem measurable_laplacian_scalar {f : Point → ℝ} : Measurable (laplacian f) := by
  unfold laplacian
  exact Finset.measurable_sum _ (fun j _ => measurable_coordDeriv_scalar j)

private theorem eLpNorm_laplacian_oddWallReflection_le {f : Point → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hf : ContDiffOn ℝ 2 f closedWallHalf) (h0 : EqOn f 0 flatWall) :
    eLpNorm (laplacian (oddWallReflection f)) (ENNReal.ofReal p) volume ≤
    2 * eLpNorm (laplacian f) (ENNReal.ofReal p) (volume.restrict positiveWallHalf) := by
  let q := ENNReal.ofReal p
  let D := laplacian (oddWallReflection f)
  let A := positiveWallHalf.indicator (laplacian f)
  let B := negativeWallHalf.indicator (fun x => -laplacian f (normalReflection x))
  have hAE : ∀ᵐ x ∂(volume : Measure Point), x ∉ flatWall := by
    change ∀ᵐ x ∂(volume : Measure Point), x ∉ {x | x 2 = 0}
    rw [ae_iff]
    simpa only [not_not,mem_setOf_eq] using normal_plane_volume_zero
  have hDecomp : D =ᵐ[volume] A + B := by
    filter_upwards [hAE] with x hx
    have hx' : x 2 ≠ 0 := hx
    rcases lt_or_gt_of_ne hx' with hNeg|hPos
    · change D x = A x + B x
      rw [show A x = 0 from indicator_of_notMem (show x ∉ positiveWallHalf from not_lt_of_ge hNeg.le) _,
        show B x = -laplacian f (normalReflection x) from indicator_of_mem (show x ∈ negativeWallHalf from hNeg) _,
        zero_add]
      exact laplacian_oddWallReflection_eqOn_negative hf h0 hNeg
    · change D x = A x + B x
      rw [show A x = laplacian f x from indicator_of_mem (show x ∈ positiveWallHalf from hPos) _,
        show B x = 0 from indicator_of_notMem (show x ∉ negativeWallHalf from not_lt_of_ge hPos.le) _, add_zero]
      exact laplacian_eventuallyEq_eq (oddWallReflection_eventuallyEq_pos hPos)
  have hA : Measurable A := measurable_laplacian_scalar.indicator isOpen_positiveWallHalf.measurableSet
  have hB : Measurable B :=
    (measurable_laplacian_scalar.comp normalReflection.continuous.measurable).neg.indicator
      isOpen_negativeWallHalf.measurableSet
  have hReflect : eLpNorm B q volume = eLpNorm A q volume := by
    have he : B = -(A ∘ normalReflection) := by
      funext x
      by_cases hx : x ∈ negativeWallHalf
      · have hr : normalReflection x ∈ positiveWallHalf := by
          change 0 < normalReflection x 2
          rw [normalReflection_height]
          exact neg_pos.mpr hx
        simp only [B,A,indicator_of_mem hx,Pi.neg_apply,Function.comp_apply,indicator_of_mem hr]
      · have hr : normalReflection x ∉ positiveWallHalf := by
          rw [show normalReflection x ∈ positiveWallHalf ↔ -(x 2) > 0 by rfl]
          exact fun h => hx (neg_pos.mp h)
        simp only [B,A,indicator_of_notMem hx,Pi.neg_apply,Function.comp_apply,indicator_of_notMem hr,neg_zero]
    rw [he,eLpNorm_neg]
    exact eLpNorm_comp_measurePreserving hA.aestronglyMeasurable normalReflection.measurePreserving
  rw [eLpNorm_congr_ae hDecomp]
  calc
    _ ≤ eLpNorm A q volume + eLpNorm B q volume :=
      eLpNorm_add_le hA.aestronglyMeasurable hB.aestronglyMeasurable
        (by simpa only [q, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
    _ = _ := by rw [hReflect,← two_mul]; simp only [A,q,eLpNorm_indicator_eq_eLpNorm_restrict isOpen_positiveWallHalf.measurableSet]

/-- The actual Hessian of a compactly supported classical field on the closed
half-space is controlled on the open side by its actual Laplacian. -/
theorem exists_halfSpace_scalarPoissonHessianLp (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Point → ℝ), ContDiffOn ℝ 2 f closedWallHalf →
      EqOn f 0 flatWall → HasCompactSupport f →
      eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 f x‖) (ENNReal.ofReal p) (volume.restrict positiveWallHalf) ≤
        ENNReal.ofReal C * eLpNorm (laplacian f) (ENNReal.ofReal p) (volume.restrict positiveWallHalf) := by
  obtain ⟨W,hW,hWhole⟩ := exists_wholeSpace_scalarPoissonHessianLp_lipschitz_columns p hp
  refine ⟨2*W,by positivity,?_⟩
  intro f hf h0 hc
  let F := oddWallReflection f
  let q := ENNReal.ofReal p
  obtain ⟨K,hK⟩ := exists_lipschitzWith_oddWallReflection (hf.of_le (by norm_num)) h0 hc
  have hAE : ∀ᵐ x ∂(volume : Measure Point), ContDiffAt ℝ 2 F x := by
    have hn : ∀ᵐ x ∂(volume : Measure Point), x ∉ flatWall := by
      rw [ae_iff]
      rw [show {a : Point | ¬ a ∉ flatWall} = flatWall by ext a; simp]
      exact normal_plane_volume_zero
    filter_upwards [hn] with x hx
    exact oddWallReflection_contDiffAt_two_off_wall hf h0 hx
  have hEq : (fun x => ‖iteratedFDeriv ℝ 2 f x‖) =ᵐ[volume.restrict positiveWallHalf]
      (fun x => ‖iteratedFDeriv ℝ 2 F x‖) := by
    filter_upwards [ae_restrict_mem isOpen_positiveWallHalf.measurableSet] with x hx
    exact congrArg norm ((((oddWallReflection_eventuallyEq_pos hx).iteratedFDeriv ℝ 2).eq_of_nhds).symm)
  rw [eLpNorm_congr_ae hEq]
  calc
    _ ≤ eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 F x‖) q volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ ENNReal.ofReal W * eLpNorm (laplacian F) q volume :=
      hWhole F hK (oddWallReflection_hasCompactSupport hc)
        (exists_lipschitzWith_oddWallReflection_column hf h0 hc) hAE
    _ ≤ ENNReal.ofReal W * (2 * eLpNorm (laplacian f) q (volume.restrict positiveWallHalf)) :=
      mul_le_mul_right (eLpNorm_laplacian_oddWallReflection_le hp.le hf h0) _
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [q,ENNReal.ofReal_ofNat]
      rw [← mul_assoc,mul_comm (ENNReal.ofReal W) (2 : ℝ≥0∞)]

end Thesis
