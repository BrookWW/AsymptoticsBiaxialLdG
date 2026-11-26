module

public import Thesis.Definitions
public import HarmonicMaps.Representative
import Thesis.Interpolation.LipschitzSobolevPullback
import HarmonicMaps.Analysis.MorreyRepresentative
import HarmonicMaps.Analysis.VariableMollificationL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! The unit-ball Hölder bound obtained from an (L^p) bound for actual derivatives. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Thesis

private theorem memLp_lipschitz_columns_on_unitBall {q : ℕ} {f : Point → Ambient q}
    {L : ℝ≥0} (hf : LipschitzWith L f) (j : Fin 3) :
    MemLp (fun x => fderiv ℝ f x (axis j)) 2 (volume.restrict (ball (0 : Point) 1)) := by
  letI : IsFiniteMeasure ((volume : Measure Point).restrict (ball 0 1)) :=
    isFiniteMeasure_restrict.2 measure_ball_ne_top
  refine MemLp.of_bound (measurable_fderiv_apply_const ℝ f (axis j)).aestronglyMeasurable (L : ℝ)
    (Eventually.of_forall fun x => ?_)
  have hj : ‖axis j‖ = 1 := by
    simpa only [axis, norm_one] using PiLp.norm_single 2 (fun _ : Fin 3 => ℝ) j (1 : ℝ)
  exact ((fderiv ℝ f x).le_opNorm _).trans (by
    rw [hj, mul_one]
    exact norm_fderiv_le_of_lipschitz ℝ hf)

private theorem unitBall_square_growth_of_lp {p β H : ℝ} (hp : 3 < p) (hH : 0 ≤ H)
    (hβ : β = 1 - 3 / p) {g : Point → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict (ball (0 : Point) 1)))
    (hG : eLpNorm g (ENNReal.ofReal p) (volume.restrict (ball (0 : Point) 1)) ≤ ENNReal.ofReal H)
    {x : Point} {r : ℝ} (hr : 0 < r) (hsub : ball x r ⊆ ball (0 : Point) 1) :
    (∫ y in ball x r, ‖g y‖ ^ 2) ≤
      H ^ 2 * (volume.real (ball (0 : Point) 1)) ^ (1 - 2 / p) * r ^ (1 + 2 * β) := by
  let ν := (volume : Measure Point).restrict (ball x r)
  let k := 1 / (2 : ℝ) - 1 / p
  have hp0 : 0 ≤ p := by linarith
  have hk : 0 ≤ k := by
    dsimp [k]
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hνμ := Measure.restrict_mono_set (volume : Measure Point) hsub
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_ball_ne_top
  have h₂p : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hgν := hg.mono_measure hνμ
  have hg₂ := hgν.mono_exponent h₂p
  have hEst := eLpNorm_le_eLpNorm_mul_rpow_measure_univ h₂p hgν.1
  rw [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hp0] at hEst
  have hBound : eLpNorm g 2 ν ≤ ENNReal.ofReal H * ν univ ^ k :=
    hEst.trans (mul_le_mul_left ((eLpNorm_mono_measure g hνμ).trans hG) _)
  have hNotTop : ν univ ^ k ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hk (measure_ne_top ν univ)
  have hReal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hNotTop) hBound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hH, ← ENNReal.toReal_rpow,
    Measure.restrict_apply_univ] at hReal
  have hVol : (volume (ball x r)).toReal = r ^ (3 : ℕ) * (volume (ball (0 : Point) 1)).toReal :=
    morrey_ball_volume x hr
  rw [hVol, Real.mul_rpow (pow_nonneg hr.le _) ENNReal.toReal_nonneg, ← Real.rpow_natCast_mul hr.le] at hReal
  rw [integral_norm_sq_eq_eLpNorm_two_toReal_sq hg₂]
  refine (pow_le_pow_left₀ ENNReal.toReal_nonneg hReal 2).trans_eq ?_
  have hExponent : ((3 : ℕ) : ℝ) * k * ((2 : ℕ) : ℝ) = 1 + 2 * β := by
    rw [hβ]; unfold k; push_cast; ring
  have hExponent' : k * ((2 : ℕ) : ℝ) = 1 - 2 / p := by unfold k; push_cast; ring
  rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hr.le, hExponent,
    ← Real.rpow_mul_natCast (ENNReal.toReal_nonneg (a := volume (ball (0 : Point) 1))),
    hExponent', mul_comm (r ^ (1 + 2 * β)), ← mul_assoc]
  simp only [measureReal_def]

/-- A weak graph with (L^p) derivative columns has a Hölder representative
on the inner ball. The gradient estimate uses the displayed weak columns. -/
theorem exists_unitBall_holder_representative_of_lp_columns {β : ℝ} (hβ : 0 < β) (hβ₁ : β < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (w : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q),
      MemW12 (ballDomain (0 : Point) 1) w D →
      ∀ (p H : ℝ), 3 < p → β = 1 - 3 / p → 0 ≤ H →
      ∀ (g : Point → ℝ), MemLp g (ENNReal.ofReal p) (volume.restrict (ball (0 : Point) 1)) →
      eLpNorm g (ENNReal.ofReal p) (volume.restrict (ball (0 : Point) 1)) ≤ ENNReal.ofReal H →
      (∀ᵐ x ∂volume.restrict (ball (0 : Point) 1), ∀ j : Fin 3, ‖D x j‖ ≤ ‖g x‖) →
      ∃ W : ball (0 : Point) (1 / 2) → Ambient q,
        IsContinuousRepresentative (ballDomain (0 : Point) (1 / 2)) w W ∧
        ∀ x y : ball (0 : Point) (1 / 2),
          ‖W x-W y‖ ≤ C*H*dist (x : Point) (y : Point)^β := by
  obtain ⟨C₀, hC₀⟩ := morrey_representative 3 (by norm_num) β hβ hβ₁
  let A := 3 * (volume.real (ball (0 : Point) 1)) ^ ((1 + 2 * β) / 3)
  have hA : 0 ≤ A := mul_nonneg (by norm_num) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  refine ⟨max 1 ((C₀ : ℝ) * Real.sqrt A), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro q w D hwSob p H hp hβp hH g hg hNorm hDeriv
  let μ := (volume : Measure Point).restrict (ball 0 1)
  have hGrowth (z : Point) (hz : z ∈ ball (0 : Point) (1 / 2))
      (r : PositiveRadius) (hr : r.val ≤ 1 / 2) :
      (∫ z' in ball z r.val, hsNormSq (D z')) ≤
        (A * H ^ 2) * Real.rpow r.val ((3 : ℝ) - 2 + 2 * β) := by
    have hsub : ball z r.val ⊆ ball (0 : Point) 1 :=
      ball_subset_ball' (by linarith only [hr, show dist z 0 < (1 : ℝ) / 2 from hz])
    let ν := (volume : Measure Point).restrict (ball z r.val)
    have hνμ := Measure.restrict_mono_set (volume : Measure Point) hsub
    letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_ball_ne_top
    have hg₂ : MemLp g 2 ν := (hg.mono_measure hνμ).mono_exponent (by
      rw [← ENNReal.ofReal_ofNat]
      exact ENNReal.ofReal_le_ofReal (by linarith))
    have hI := setIntegral_mono_ae_restrict
      (integrable_hsNormSq_of_memLp_columns (fun j => (hwSob.2.2 j).mono_measure hνμ))
      ((hg₂.norm.integrable_sq).const_mul (3 : ℝ))
      (show ∀ᵐ z' ∂ν, hsNormSq (D z') ≤ 3 * ‖g z'‖ ^ 2 from by
        filter_upwards [(ae_mono hνμ) hDeriv] with z' hz'
        calc
          _ ≤ ∑ _j : Fin 3, ‖g z'‖ ^ 2 := Finset.sum_le_sum fun j _ =>
            pow_le_pow_left₀ (norm_nonneg _) (hz' j) 2
          _ = _ := by simp [Finset.sum_const])
    rw [integral_const_mul] at hI
    refine hI.trans ((mul_le_mul_of_nonneg_left
      (unitBall_square_growth_of_lp hp hH hβp hg hNorm r.property hsub) (by norm_num)).trans_eq ?_)
    have hE : 1 - 2 / p = (1 + 2 * β) / 3 := by rw [hβp]; ring
    rw [hE]
    change 3 * (H ^ 2 * (volume.real (ball (0 : Point) 1)) ^ ((1 + 2 * β) / 3) * r.val ^ (1 + 2 * β)) =
      A * H ^ 2 * r.val ^ ((3 : ℝ) - 2 + 2 * β)
    rw [show (3 : ℝ) - 2 = 1 by norm_num]
    dsimp [A]
    ring
  obtain ⟨W, hW, _, hHold, _, _⟩ :=
    hC₀ q w D hwSob (A * H ^ 2) (mul_nonneg hA (sq_nonneg _)) hGrowth
  refine ⟨W,hW,fun x y => ?_⟩
  have hh := hHold x y
  have hSqrt : Real.sqrt (A * H ^ 2) = Real.sqrt A * H := by
    rw [Real.sqrt_mul hA, Real.sqrt_sq hH]
  rw [hSqrt] at hh
  exact hh.trans (by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hH)
      (Real.rpow_nonneg dist_nonneg _))

/-- The actual locally Lipschitz map is Hölder on the inner unit ball when its
Fréchet columns are dominated by a single (L^p) function. -/
theorem exists_unitBall_holder_of_lp_columns {β : ℝ} (hβ : 0 < β) (hβ₁ : β < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (f : Point → Ambient q)
      (_ : ∃ L : ℝ≥0, LipschitzOnWith L f (ball (0 : Point) 1))
      (p H : ℝ) (_ : 3 < p) (_ : β = 1 - 3 / p) (_ : 0 ≤ H)
      (g : Point → ℝ), MemLp g (ENNReal.ofReal p) (volume.restrict (ball (0 : Point) 1)) →
      eLpNorm g (ENNReal.ofReal p) (volume.restrict (ball (0 : Point) 1)) ≤ ENNReal.ofReal H →
      (∀ᵐ x ∂volume.restrict (ball (0 : Point) 1), ∀ j : Fin 3, ‖fderiv ℝ f x (axis j)‖ ≤ ‖g x‖) →
      ∀ x ∈ ball (0 : Point) (1 / 2), ∀ y ∈ ball (0 : Point) (1 / 2),
        ‖f x - f y‖ ≤ C * H * dist x y ^ β := by
  obtain ⟨C,hC,hRep⟩ := exists_unitBall_holder_representative_of_lp_columns hβ hβ₁
  refine ⟨C,hC,?_⟩
  rintro q f ⟨L, hL⟩ p H hp hβp hH g hg hNorm hPoint x hx y hy
  obtain ⟨w, hwLip, hwf⟩ := hL.extend_finite_dimension
  let μ := (volume : Measure Point).restrict (ball 0 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_ball_ne_top
  let D (z : Point) (j : Fin 3) := fderiv ℝ w z (axis j)
  have hwD (j : Fin 3) : MemLp (fun z => D z j) 2 μ :=
    memLp_lipschitz_columns_on_unitBall hwLip j
  have hwL : MemLp w 2 μ := by
    refine MemLp.of_bound hwLip.continuous.aestronglyMeasurable
      (‖w 0‖ + (lipschitzExtensionConstant (Ambient q) * L : ℝ≥0)) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hzw := hwLip.dist_le_mul z 0
    rw [dist_eq_norm, dist_zero_right] at hzw
    have hr := mul_le_of_le_one_right
      (show 0 ≤ ((lipschitzExtensionConstant (Ambient q) * L : ℝ≥0) : ℝ) from NNReal.coe_nonneg _)
      (mem_ball_zero_iff.mp hz).le
    calc
      ‖w z‖ ≤ ‖w z - w 0‖ + ‖w 0‖ := by
        simpa only [sub_add_cancel] using norm_add_le (w z - w 0) (w 0)
      _ ≤ _ := by linarith only [hzw, hr]
  have hwSob : MemW12 (ballDomain (0 : Point) 1) w D :=
    ⟨hasWeakGradient_of_lipschitz _ hwLip, hwL, hwD⟩
  have hDeriv : ∀ᵐ z ∂μ, ∀ j, ‖D z j‖ ≤ ‖g z‖ := by
    filter_upwards [hPoint, ae_restrict_mem measurableSet_ball] with z hz hBall j
    have hEq : f =ᶠ[𝓝 z] w :=
      Filter.mem_of_superset (isOpen_ball.mem_nhds hBall) hwf
    change ‖fderiv ℝ w z (axis j)‖ ≤ _
    rw [← hEq.fderiv_eq]
    exact hz j
  obtain ⟨W,hW,hHold⟩ := hRep q w D hwSob p H hp hβp hH g hg hNorm hDeriv
  have hActual : IsContinuousRepresentative (ballDomain (0 : Point) (1 / 2)) w
      (fun z : ball (0 : Point) (1 / 2) => w z) :=
    ⟨hwLip.continuous.comp continuous_subtype_val, by
      exact Eventually.of_forall fun _ _ => rfl⟩
  have hWactual := hW.unique hActual
  have hx' := ball_subset_ball (show (1 : ℝ) / 2 ≤ 1 by norm_num) hx
  have hy' := ball_subset_ball (show (1 : ℝ) / 2 ≤ 1 by norm_num) hy
  have hh := hHold ⟨x, hx⟩ ⟨y, hy⟩
  rw [hWactual] at hh
  rw [hwf hx', hwf hy']
  exact hh

end Thesis
