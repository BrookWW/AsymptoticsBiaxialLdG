module

public import Thesis.Definitions
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Average

/-! Inverse-square averaging for projections from centers in the target ball. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal

namespace Thesis

private def inverseSquareKernel (z : QuaternionCoordinates) : ℝ≥0∞ :=
  ENNReal.ofReal ((‖z‖ ^ 2)⁻¹)

private theorem measurable_inverseSquareKernel : Measurable inverseSquareKernel := by
  unfold inverseSquareKernel
  fun_prop

private theorem inverseSquareKernel_neg (z : QuaternionCoordinates) :
    inverseSquareKernel (-z) = inverseSquareKernel z := by
  simp [inverseSquareKernel]

private theorem lintegral_inverseSquareKernel_lt_top :
    (∫⁻ z in ball (0 : QuaternionCoordinates) 2, inverseSquareKernel z) < ∞ := by
  let U := ({(0 : QuaternionCoordinates)}ᶜ : Set QuaternionCoordinates)
  let f := (ball (0 : QuaternionCoordinates) 2).indicator inverseSquareKernel
  let g : sphere (0 : QuaternionCoordinates) 1 × Ioi (0 : ℝ) → ℝ≥0∞ :=
    fun p => (Iio (2 : ℝ)).indicator (fun r : ℝ => ENNReal.ofReal ((r ^ 2)⁻¹)) p.2.1
  have hg : Measurable g :=
    ((measurable_id.pow_const 2).inv.ennreal_ofReal.indicator measurableSet_Iio).comp
      (measurable_subtype_coe.comp measurable_snd)
  have hU : MeasurableSet U := (measurableSet_singleton _).compl
  have hpolar := (volume : Measure QuaternionCoordinates).measurePreserving_homeomorphUnitSphereProd
  have hcomp := hpolar.lintegral_comp hg
  have hdim : Module.finrank ℝ QuaternionCoordinates - 1 = 3 := by
    simp [QuaternionCoordinates]
  rw [hdim] at hcomp
  have hgf : (fun x : U => g (homeomorphUnitSphereProd QuaternionCoordinates x)) =
      fun x => f x.val := by
    funext x
    simp only [g, f, homeomorphUnitSphereProd_apply_snd_coe]
    by_cases hx : ‖x.val‖ < 2
    · rw [indicator_of_mem (show ‖x.val‖ ∈ Iio (2 : ℝ) from hx),
        indicator_of_mem (show x.val ∈ ball (0 : QuaternionCoordinates) 2 from
          by simpa only [mem_ball, dist_zero_right] using hx)]
      rfl
    · rw [indicator_of_notMem (show ‖x.val‖ ∉ Iio (2 : ℝ) from hx),
        indicator_of_notMem (show x.val ∉ ball (0 : QuaternionCoordinates) 2 from
          by simpa only [mem_ball, dist_zero_right] using hx)]
  rw [hgf, lintegral_subtype_comap hU, restrict_compl_singleton] at hcomp
  rw [← lintegral_indicator measurableSet_ball]
  change (∫⁻ z, f z ∂volume) < ∞
  rw [hcomp, lintegral_prod _ hg.aemeasurable]
  have hRadial :
      (∫⁻ r : Ioi (0 : ℝ), (Iio (2 : ℝ)).indicator
        (fun s : ℝ => ENNReal.ofReal ((s ^ 2)⁻¹)) r.1 ∂Measure.volumeIoiPow 3) < ∞ := by
    have hMeas : Measurable (fun r : Ioi (0 : ℝ) => (Iio (2 : ℝ)).indicator
        (fun s : ℝ => ENNReal.ofReal ((s ^ 2)⁻¹)) r.1) :=
      ((measurable_id.pow_const 2).inv.ennreal_ofReal.indicator measurableSet_Iio).comp
        measurable_subtype_coe
    rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hMeas]
    have hPoint : ∀ r : Ioi (0 : ℝ), ENNReal.ofReal (r.1 ^ 3) *
        (Iio (2 : ℝ)).indicator (fun s : ℝ => ENNReal.ofReal ((s ^ 2)⁻¹)) r.1 ≤
          (Iio (2 : ℝ)).indicator (fun _ : ℝ => ENNReal.ofReal 2) r.1 := by
      intro r
      by_cases hr : r.1 ∈ Iio (2 : ℝ)
      · have hpos : 0 < r.1 := r.property
        rw [indicator_of_mem hr, indicator_of_mem hr,
          ← ENNReal.ofReal_mul (pow_nonneg hpos.le _)]
        apply ENNReal.ofReal_le_ofReal
        calc
          r.1 ^ 3 * (r.1 ^ 2)⁻¹ = r.1 := by field_simp
          _ ≤ 2 := le_of_lt hr
      · simp [indicator_of_notMem hr]
    calc
      _ ≤ ∫⁻ r : Ioi (0 : ℝ),
          (Iio (2 : ℝ)).indicator (fun _ : ℝ => ENNReal.ofReal 2) r.1
            ∂(volume.comap Subtype.val) :=
        lintegral_mono hPoint
      _ < ∞ := by
        rw [lintegral_subtype_comap measurableSet_Ioi]
        rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          lintegral_const]
        rw [inter_comm, Ioi_inter_Iio]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp [Real.volume_Ioo])
  have hSphere : (volume : Measure QuaternionCoordinates).toSphere univ < ∞ := measure_lt_top _ _
  simp only [g, lintegral_const]
  exact ENNReal.mul_lt_top hRadial hSphere

private theorem lintegral_inverseSquareKernel_sub_bound (z : QuaternionCoordinates) (hz : ‖z‖ ≤ 1) :
    (∫⁻ y in ball (0 : QuaternionCoordinates) (1 / 4), inverseSquareKernel (z - y)) ≤
      ∫⁻ y in ball (0 : QuaternionCoordinates) 2, inverseSquareKernel y := by
  let B := ball (0 : QuaternionCoordinates) 2
  let f := B.indicator inverseSquareKernel
  have hf : Measurable f := measurable_inverseSquareKernel.indicator measurableSet_ball
  have htr := (measurePreserving_add_right (volume : Measure QuaternionCoordinates) (-z)).lintegral_comp hf
  change (∫⁻ y, f (y + -z) ∂volume) = ∫⁻ y, f y ∂volume at htr
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
  calc
    _ ≤ ∫⁻ y, f (y + -z) ∂volume := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ ball (0 : QuaternionCoordinates) (1 / 4)
      · have hnorm : ‖y‖ < 1 / 4 := by simpa only [mem_ball, dist_zero_right] using hy
        have hyz : y + -z ∈ B := by
          rw [show B = ball 0 2 by rfl, mem_ball, dist_zero_right]
          exact (norm_add_le _ _).trans_lt (by rw [norm_neg]; linarith)
        rw [indicator_of_mem hy]
        change inverseSquareKernel (z - y) ≤ f (y + -z)
        rw [show f (y + -z) = inverseSquareKernel (y + -z) from indicator_of_mem hyz _]
        rw [show z - y = -(y + -z) by abel, inverseSquareKernel_neg]
      · rw [indicator_of_notMem hy]; exact bot_le
    _ = ∫⁻ y, f y ∂volume := htr

/-- A bounded field has a projection center in the ball of radius `1/4` with
a uniform inverse-square energy budget. The chosen center has null preimage. -/
theorem exists_sphereProjection_center : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
      (u : X → QuaternionCoordinates) (w : X → ℝ≥0∞),
      Measurable u → Measurable w → (∀ᵐ x ∂μ, ‖u x‖ ≤ 1) →
      ∃ y : QuaternionCoordinates, ‖y‖ < 1 / 4 ∧ (∀ᵐ x ∂μ, u x ≠ y) ∧
        (∫⁻ x, w x * ENNReal.ofReal ((‖u x - y‖ ^ 2)⁻¹) ∂μ) ≤ C * (∫⁻ x, w x ∂μ) := by
  let B := ball (0 : QuaternionCoordinates) (1 / 4)
  let ν := volume.restrict B
  let K := ∫⁻ z in ball (0 : QuaternionCoordinates) 2, inverseSquareKernel z
  have hν : ν univ = volume B := Measure.restrict_apply_univ B
  have hνpos : 0 < ν univ := by rw [hν]; exact measure_ball_pos volume 0 (by norm_num)
  have hνtop : ν univ < ∞ := by rw [hν]; exact measure_ball_lt_top
  letI : IsFiniteMeasure ν := ⟨hνtop⟩
  have hνne : ν ≠ 0 := Measure.measure_univ_ne_zero.1 hνpos.ne'
  refine ⟨(ν univ)⁻¹ * K, ENNReal.mul_lt_top (by simpa using hνpos.ne')
    lintegral_inverseSquareKernel_lt_top, ?_⟩
  intro X _ μ _ u w hu hw huB
  let k : X × QuaternionCoordinates → ℝ≥0∞ :=
    fun p => w p.1 * inverseSquareKernel (u p.1 - p.2)
  let F : QuaternionCoordinates → ℝ≥0∞ := fun y => ∫⁻ x, k (x, y) ∂μ
  have hk : Measurable k := (hw.comp measurable_fst).mul
    (measurable_inverseSquareKernel.comp ((hu.comp measurable_fst).sub measurable_snd))
  have hF : Measurable F := hk.lintegral_prod_left'
  have hInt : (∫⁻ y, F y ∂ν) ≤ K * (∫⁻ x, w x ∂μ) := by
    change (∫⁻ y, ∫⁻ x, k (x,y) ∂μ ∂ν) ≤ _
    rw [← lintegral_prod_symm _ hk.aemeasurable, lintegral_prod _ hk.aemeasurable]
    calc
      _ ≤ ∫⁻ x, K * w x ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [huB] with x hx
        change (∫⁻ y, w x * inverseSquareKernel (u x - y) ∂ν) ≤ K * w x
        have hMeas : Measurable (fun y => inverseSquareKernel (u x - y)) :=
          measurable_inverseSquareKernel.comp (measurable_const.sub measurable_id)
        rw [lintegral_const_mul _ hMeas, mul_comm K]
        gcongr
        exact lintegral_inverseSquareKernel_sub_bound _ hx
      _ = _ := lintegral_const_mul _ hw
  have hAvoid : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, u x ≠ y := by
    apply (Measure.ae_ae_comm (p := fun x y => u x ≠ y)
      (measurableSet_eq_fun (hu.comp measurable_fst) measurable_snd).compl).1
    exact ae_of_all _ fun x => ae_iff.2 (by
      change ν {y | ¬u x ≠ y} = 0
      simp [ν, eq_comm])
  let N := {y | ¬(y ∈ B ∧ ∀ᵐ x ∂μ, u x ≠ y)}
  have hN : ν N = 0 := ae_iff.1 ((ae_restrict_mem measurableSet_ball).and hAvoid)
  obtain ⟨y, hyN, hyF⟩ := exists_notMem_null_le_laverage hνne hF.aemeasurable hN
  have hy : y ∈ B ∧ ∀ᵐ x ∂μ, u x ≠ y := by simpa only [N, mem_setOf_eq, not_not] using hyN
  refine ⟨y, by simpa only [B, mem_ball, dist_zero_right] using hy.1, hy.2, ?_⟩
  change F y ≤ _
  calc
    F y ≤ ⨍⁻ z, F z ∂ν := hyF
    _ ≤ ((ν univ)⁻¹ * K) * (∫⁻ x, w x ∂μ) := by
      rw [laverage_eq, ENNReal.div_eq_inv_mul, mul_assoc]
      gcongr

theorem exists_sphereProjection_center_ae : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
      (u : X → QuaternionCoordinates) (w : X → ℝ≥0∞),
      AEMeasurable u μ → AEMeasurable w μ → (∀ᵐ x ∂μ, ‖u x‖ ≤ 1) →
      ∃ y : QuaternionCoordinates, ‖y‖ < 1 / 4 ∧ (∀ᵐ x ∂μ, u x ≠ y) ∧
        (∫⁻ x, w x * ENNReal.ofReal ((‖u x - y‖ ^ 2)⁻¹) ∂μ) ≤ C * (∫⁻ x, w x ∂μ) := by
  obtain ⟨C, hC, h⟩ := exists_sphereProjection_center
  refine ⟨C, hC, ?_⟩
  intro X _ μ _ u w hu hw hB
  obtain ⟨y, hy, hyAvoid, hyBudget⟩ := h μ (hu.mk u) (hw.mk w) hu.measurable_mk hw.measurable_mk
    (by filter_upwards [hu.ae_eq_mk, hB] with x hEq hx; simpa only [← hEq] using hx)
  refine ⟨y, hy, ?_, ?_⟩
  · filter_upwards [hu.ae_eq_mk, hyAvoid] with x hEq hx
    simpa only [hEq] using hx
  · rw [lintegral_congr_ae hw.ae_eq_mk]
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hyBudget
    filter_upwards [hu.ae_eq_mk, hw.ae_eq_mk] with x hux hwx
    rw [hux, hwx]

end Thesis
