module

public import Thesis.Variational.CollarDyadicAverages
public import Thesis.Variational.CollarGraphMass
public import Thesis.External.FractionalDirichlet

/-! The physical wall slab estimate with the actual fractional
Dirichlet test norm. -/

public section

open Filter Function MeasureTheory Metric Set Topology
open scoped BigOperators ContDiff ENNReal Matrix Matrix.Norms.Frobenius NNReal

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem sq_sum_fin3_le_nine_sum_sq
    (x y : Fin 3 → ℝ) (h : ∀ j, |x j| ≤ y j) :
    (∑ j, x j)^2 ≤ 9 * ∑ j, (y j)^2 := by
  let S := ∑ j : Fin 3, (y j)^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hInd (j : Fin 3) : |x j| ≤ Real.sqrt S :=
    (h j).trans (Real.le_sqrt_of_sq_le
      (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)))
  have hSum : |∑ j, x j| ≤ 3 * Real.sqrt S := by
    calc
      _ ≤ ∑ j, |x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 3, Real.sqrt S := Finset.sum_le_sum fun j _ => hInd j
      _ = _ := by simp
  rw [← sq_abs]
  exact (pow_le_pow_left₀ (abs_nonneg _) hSum 2).trans_eq (by rw [mul_pow,Real.sq_sqrt hS]; norm_num [S])

theorem wallGraphGradientSize_nonneg {U : Set Point} (v : H10 U) (x : Point) :
    0 ≤ wallGraphGradientSize v x :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem wallGraphGradientSize_memLp {U : Set Point} (v : H10 U) :
    MemLp (wallGraphGradientSize v) 2 (volume.restrict U) := by
  unfold wallGraphGradientSize h10Gradient
  exact memLp_finsetSum _ (fun j _ => (Lp.memLp (v.val.2 j)).norm)

private theorem ofReal_sq_wallGraphGradientSize_le {U : Set Point} (v : H10 U) (x : Point) :
    ENNReal.ofReal ((wallGraphGradientSize v x)^2) ≤
      9 * ∑ j : Fin 3, ENNReal.ofReal (‖h10Gradient v x j‖^2) := by
  have h := sq_sum_fin3_le_nine_sum_sq
    (fun j => ‖h10Gradient v x j‖) (fun j => ‖h10Gradient v x j‖)
    (fun j => (abs_of_nonneg (norm_nonneg _)).le)
  calc
    _ ≤ ENNReal.ofReal (9 * ∑ j : Fin 3, ‖h10Gradient v x j‖^2) :=
      ENNReal.ofReal_le_ofReal h
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]; norm_num

private theorem ofReal_sq_wallGraphGradientSize_sub_div_le
    {U : Set Point} (v : H10 U) (r : ℝ) (z : Point × Point) :
    ENNReal.ofReal ((wallGraphGradientSize v z.1-wallGraphGradientSize v z.2)^2 /
      dist z.1 z.2 ^ (3+2*r)) ≤
      9 * ∑ j : Fin 3, fractionalPairEnergy r (fun x => h10Gradient v x j) z := by
  let x (j : Fin 3) := ‖h10Gradient v z.1 j‖-‖h10Gradient v z.2 j‖
  let y (j : Fin 3) := ‖h10Gradient v z.1 j - h10Gradient v z.2 j‖
  let D := dist z.1 z.2 ^ (3+2*r)
  have hD : 0 ≤ D := Real.rpow_nonneg dist_nonneg _
  have h := sq_sum_fin3_le_nine_sum_sq x y (fun j => abs_norm_sub_norm_le _ _)
  have hE : (wallGraphGradientSize v z.1-wallGraphGradientSize v z.2)^2 =
      (∑ j, x j)^2 := by dsimp only [x,wallGraphGradientSize]; rw [Finset.sum_sub_distrib]
  calc
    _ ≤ ENNReal.ofReal ((9*∑ j,y j^2)/D) :=
      ENNReal.ofReal_le_ofReal (by rw [hE]; exact div_le_div_of_nonneg_right h hD)
    _ = ENNReal.ofReal (9*∑ j,y j^2/D) := by rw [← Finset.sum_div]; congr 1; ring
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => div_nonneg (sq_nonneg _) hD)]
      simp only [fractionalPairEnergy, y, D]
      norm_num

private theorem lintegral_sq_wallGraphGradientSize_le_testEnergy
    {U : Set Point} (v : H10 U) (s : ℝ) :
    (∫⁻ x in U, ENNReal.ofReal ((wallGraphGradientSize v x)^2)) ≤
      9 * dirichletFractionalTestEnergy s U v := by
  let μ := volume.restrict U
  let D (j : Fin 3) (x : Point) := h10Gradient v x j
  let b (j : Fin 3) (x : Point) := ENNReal.ofReal (‖D j x‖^2)
  have hMeas (j : Fin 3) : AEMeasurable (b j) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((Lp.aestronglyMeasurable (v.val.2 j)).norm.aemeasurable.pow_const _)
  calc
    _ ≤ ∫⁻ x, 9 * (∑ j, b j x) ∂μ := lintegral_mono (ofReal_sq_wallGraphGradientSize_le v)
    _ = 9 * ∑ j, ∫⁻ x, b j x ∂μ := by
      rw [lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum _ fun j _ => hMeas j)]
      rw [lintegral_finsetSum' _ (fun j _ => hMeas j)]
    _ ≤ 9 * ∑ j, fractionalEnergy (1-s) U (D j) :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => self_le_add_right _ _)
    _ ≤ _ := mul_le_mul' le_rfl (self_le_add_left _ _)

private theorem scalarFractionalPairEnergy_wallGraphGradientSize_le_testEnergy
    {U : Set Point} (v : H10 U) (s : ℝ) :
    scalarFractionalPairEnergy (1-s) (volume.restrict U) (wallGraphGradientSize v) ≤
      9 * dirichletFractionalTestEnergy s U v := by
  let μ := volume.restrict U
  let D (j : Fin 3) (x : Point) := h10Gradient v x j
  let b (j : Fin 3) := fractionalPairEnergy (1-s) (D j)
  have hMeas (j : Fin 3) : AEMeasurable (b j) (μ.prod μ) :=
    fractionalPairEnergy_aemeasurable _ (Lp.aestronglyMeasurable (v.val.2 j))
  have hE (j : Fin 3) : (∫⁻ z, b j z ∂μ.prod μ) ≤ fractionalEnergy (1-s) U (D j) := by
    rw [lintegral_prod _ (hMeas j)]
    exact self_le_add_left _ _
  calc
    _ ≤ ∫⁻ z, 9 * (∑ j, b j z) ∂μ.prod μ :=
      lintegral_mono (ofReal_sq_wallGraphGradientSize_sub_div_le v _)
    _ = 9 * ∑ j, ∫⁻ z, b j z ∂μ.prod μ := by
      rw [lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum _ fun j _ => hMeas j)]
      rw [lintegral_finsetSum' _ (fun j _ => hMeas j)]
    _ ≤ 9 * ∑ j, fractionalEnergy (1-s) U (D j) :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => hE j)
    _ ≤ _ := mul_le_mul' le_rfl (self_le_add_left _ _)

private theorem wallGraphGradientSize_sqrt_sum_le
    {U : Set Point} (v : H10 U) (s : ℝ) (hFin : dirichletFractionalTestEnergy s U v < ⊤) :
    scalarFractionalPairEnergy (1-s) (volume.restrict U) (wallGraphGradientSize v) < ⊤ ∧
    Real.sqrt (∫ x in U, (wallGraphGradientSize v x)^2) +
      Real.sqrt (scalarFractionalPairEnergy (1-s) (volume.restrict U) (wallGraphGradientSize v)).toReal ≤
        6 * dirichletFractionalTestNorm s U v := by
  let μ := volume.restrict U
  let g := wallGraphGradientSize v
  let E := dirichletFractionalTestEnergy s U v
  let S := scalarFractionalPairEnergy (1-s) μ g
  have hE : (9:ℝ≥0∞)*E < ⊤ := ENNReal.mul_lt_top (by norm_num) hFin
  have hScalar := scalarFractionalPairEnergy_wallGraphGradientSize_le_testEnergy v s
  have hIntegral := lintegral_sq_wallGraphGradientSize_le_testEnergy v s
  have hIntSq : Integrable (fun x => (g x)^2) μ := (wallGraphGradientSize_memLp v).integrable_sq
  have hI := (ofReal_integral_eq_lintegral_ofReal hIntSq (.of_forall fun _ => sq_nonneg _)).le.trans hIntegral
  have h0 : 0 ≤ ∫ x, (g x)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hIR := ENNReal.toReal_mono hE.ne hI
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal h0] at hIR
  have hSR := ENNReal.toReal_mono hE.ne hScalar
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofNat] at hSR
  have hi := Real.sqrt_le_sqrt hIR
  have hs := Real.sqrt_le_sqrt hSR
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 9),show Real.sqrt (9:ℝ) = 3 by norm_num] at hi hs
  refine ⟨hScalar.trans_lt hE,?_⟩
  change Real.sqrt (∫ x, (g x)^2 ∂μ)+Real.sqrt S.toReal ≤ 6*Real.sqrt E.toReal
  exact (add_le_add hi hs).trans_eq (by ring)

/-- The actual zero-trace value has quadratic mass in a physical
epigraph slab, controlled by the unchanged fractional test norm. -/
theorem exists_wallChartSlab_h10Value_mass_le
    {U : Set Point} (hU : IsBoundedDomain U) {b s : ℝ} (hb : 0 < b) (hs : s < 1/2)
    (Φ : WallChartPoint ≃ₜ Point) (hΦ : MeasurePreserving Φ)
    (hInside : Φ '' wallChartSlab b b ⊆ U)
    {K : ℝ≥0} (hK : 0 < (K : ℝ)) (hLip : LipschitzOnWith K Φ (wallChartClosedBox b))
    (ν : Point) (hν : ‖ν‖ = 1)
    (hV : ∀ y : ℝ×ℝ, ∀ t : ℝ, Φ (y,t) = Φ (y,0)+t • ν)
    (hW : ∀ y ∈ wallChartHorizontal b, Φ (y,0) ∈ frontier U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : H10 U), dirichletFractionalTestEnergy s U v < ⊤ →
      ∀ t : ℝ, 0 < t → t ≤ b →
        (∫ x in Φ '' wallChartSlab b t, ‖h10Value v x‖ ∂volume.restrict U) ≤
          C * t^2 * dirichletFractionalTestNorm s U v := by
  have hr : 1/2 < 1-s := by linarith
  obtain ⟨C,hC,hMass⟩ := exists_wallChartSlab_mass_le hU hb hr Φ hΦ hInside hK hLip
  refine ⟨6*C,mul_nonneg (by norm_num) hC,?_⟩
  intro v hFin t ht htB
  have hSub : Φ '' wallChartSlab b t ⊆ U := by
    apply (image_mono ?_).trans hInside
    intro z hz
    exact ⟨hz.1,hz.2.1,hz.2.2.trans htB⟩
  obtain ⟨hEn,hSqrt⟩ := wallGraphGradientSize_sqrt_sum_le v s hFin
  have hM := hMass (wallGraphGradientSize v) (wallGraphGradientSize_memLp v)
    (wallGraphGradientSize_nonneg v) hEn t ht htB
  calc
    _ ≤ t * ∫ x in Φ '' wallChartSlab b t, wallGraphGradientSize v x ∂volume.restrict U :=
      wallChartSlab_h10Value_integral_le hU ht Φ hΦ hSub ν hν hV hW v
    _ ≤ t*(C*t*(6*dirichletFractionalTestNorm s U v)) :=
      mul_le_mul_of_nonneg_left
        (hM.trans (mul_le_mul_of_nonneg_left hSqrt (mul_nonneg hC ht.le))) ht.le
    _ = _ := by ring

end Thesis

end
