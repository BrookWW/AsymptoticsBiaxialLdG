module

public import Thesis.Variational.SmoothDomainVolumeDensity
public import Thesis.Variational.H10FractionalEmbedding
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Finite ball averages approximate bounded fractional energy in L². -/

public section

open Filter MeasureTheory Metric Set Topology
open scoped BigOperators ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance fractionalAveragesContinuousENorm : ContinuousENorm S0 :=
  SeminormedAddGroup.toContinuousENorm

private theorem exists_finite_ball_partition
    {U : Set Point} (hU : IsBoundedDomain U) {r : ℝ} (hr : 0 < r) :
    ∃ (m : ℕ) (c : Fin m → Point) (V : Fin m → Set Point),
      (∀ i, c i ∈ closure U) ∧ (∀ i, MeasurableSet (V i)) ∧
      (∀ i, V i ⊆ U ∩ ball (c i) r) ∧
      Pairwise (Function.onFun Disjoint V) ∧ (⋃ i, V i) = U := by
  classical
  let W (a : closure U) := ball (a : Point) r
  have hCover : closure U ⊆ ⋃ a : closure U, W a :=
    fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self hr⟩
  obtain ⟨I,hI⟩ := hU.2.2.isCompact_closure.elim_finite_subcover W (fun _ => isOpen_ball) hCover
  let m := Fintype.card ↥I
  let e : ↥I ≃ Fin m := Fintype.equivFin ↥I
  let c (i : Fin m) := ((e.symm i).val : Point)
  let V (i : Fin m) := (U ∩ ball (c i) r) \ ⋃ j : Fin m, ⋃ _ : j < i, ball (c j) r
  have hC (i : Fin m) : c i ∈ closure U := (e.symm i).val.property
  have hV (i : Fin m) : MeasurableSet (V i) :=
    (hU.1.measurableSet.inter measurableSet_ball).diff
      (MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => measurableSet_ball)
  have hSub (i : Fin m) : V i ⊆ U ∩ ball (c i) r := sdiff_subset
  have hPair : Pairwise (Function.onFun Disjoint V) := by
    intro i j hij
    change Disjoint (V i) (V j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with h | h
    · exact hxj.2 (mem_iUnion₂.2 ⟨i,h,hxi.1.2⟩)
    · exact hxi.2 (mem_iUnion₂.2 ⟨j,h,hxj.1.2⟩)
  refine ⟨m,c,V,hC,hV,hSub,hPair,?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact hi.1.1
  · intro hx
    obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (hI (subset_closure hx))
    let J := Finset.univ.filter (fun i : Fin m => x ∈ ball (c i) r)
    have hJ : J.Nonempty := by
      refine ⟨e ⟨a,ha⟩,Finset.mem_filter.2 ⟨Finset.mem_univ _,?_⟩⟩
      simpa only [c,e.symm_apply_apply] using hxa
    let i := J.min' hJ
    have hi : x ∈ ball (c i) r := (Finset.mem_filter.mp (J.min'_mem hJ)).2
    refine mem_iUnion.mpr ⟨i, ⟨⟨hx,hi⟩,?_⟩⟩
    intro h
    obtain ⟨j,hji,hxj⟩ := mem_iUnion₂.mp h
    have hj : j ∈ J := Finset.mem_filter.2 ⟨Finset.mem_univ _,hxj⟩
    exact (not_lt_of_ge (J.min'_le j hj)) hji

private theorem ofReal_sq_sub_setAverage_le
    {μ : Measure Point} [IsFiniteMeasure μ] {V : Set Point}
    (hV₀ : 0 < μ V) (f : Lp S0 2 μ) (x : Point) :
    ENNReal.ofReal (‖f x - ⨍ y in V, f y ∂μ‖ ^ 2) ≤
      (μ V)⁻¹ * (∫⁻ y in V, ENNReal.ofReal (‖f x - f y‖ ^ 2) ∂μ) := by
  let w (y : Point) := f x - f y
  let ν := μ.restrict V
  have hν : ν univ = μ V := by simp [ν]
  have hFin : μ V < ⊤ := measure_lt_top _ _
  have hf : MemLp (f : Point → S0) 2 ν := (Lp.memLp f).restrict V
  have hw : MemLp w 2 ν :=
    (memLp_const (μ := ν) (p := 2) (f x)).sub hf
  have hf₁ : Integrable (f : Point → S0) ν := hf.integrable (by norm_num)
  have hw₁ : Integrable w ν := hw.integrable (by norm_num)
  have hw₂ : Integrable (fun y => ‖w y‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hw.1).1 hw
  have hConv : ConvexOn ℝ (univ : Set S0) (fun a => ‖a‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
  have hSq := hConv.map_set_average_le ((continuous_norm.pow 2).continuousOn)
    isClosed_univ hV₀.ne' hFin.ne (.of_forall fun _ => mem_univ _) hw₁ hw₂
  have hW : (⨍ y in V, w y ∂μ) = f x - (⨍ y in V, f y ∂μ) := by
    change (⨍ y, w y ∂ν) = f x - (⨍ y, f y ∂ν)
    rw [average_eq, average_eq]
    have hI : (∫ y, w y ∂ν) = (ν.real univ) • f x - ∫ y, f y ∂ν := by
      rw [show w = fun y => f x - f y from rfl, integral_sub (integrable_const _) hf₁, integral_const]
    rw [hI, smul_sub, smul_smul, inv_mul_cancel₀, one_smul]
    rw [Measure.real, hν]
    exact (ENNReal.toReal_pos hV₀.ne' hFin.ne).ne'
  have hSq' := ENNReal.ofReal_le_ofReal hSq
  rw [hW, ofReal_setAverage hw₂ (.of_forall fun _ => sq_nonneg _), ENNReal.div_eq_inv_mul] at hSq'
  exact hSq'

private def piecewiseConstantLp
    {ι : Type*} [Fintype ι] {μ : Measure Point} [IsFiniteMeasure μ]
    (V : ι → Set Point) (hV : ∀ i, MeasurableSet (V i)) :
    (ι → S0) →ₗ[ℝ] Lp S0 2 μ where
  toFun a := ∑ i, indicatorConstLp 2 (hV i) (measure_ne_top μ _) (a i)
  map_add' a b := by
    simp only [Pi.add_apply, ← indicatorConstLp_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (μ := μ) (p := 2) (hs := hV i) (hμs := measure_ne_top μ _) (c := c • a i),
      Lp.coeFn_smul c (indicatorConstLp 2 (hV i) (measure_ne_top μ _) (a i)),
      indicatorConstLp_coeFn (μ := μ) (p := 2) (hs := hV i) (hμs := measure_ne_top μ _) (c := a i)] with x h₁ h₂ h₃
    rw [h₁,h₂]
    change (V i).indicator (fun _ => c • a i) x = c • indicatorConstLp 2 (hV i) (measure_ne_top μ _) (a i) x
    rw [h₃]
    by_cases hx : x ∈ V i <;> simp [hx]

private theorem piecewiseConstantLp_ae_on_cell
    {ι : Type*} [Fintype ι] {μ : Measure Point} [IsFiniteMeasure μ]
    (V : ι → Set Point) (hV : ∀ i, MeasurableSet (V i))
    (hPair : Pairwise (Function.onFun Disjoint V)) (a : ι → S0) (i : ι) :
    ∀ᵐ x ∂μ.restrict (V i), piecewiseConstantLp (μ := μ) V hV a x = a i := by
  classical
  have hCoefs (j : ι) := indicatorConstLp_coeFn (μ := μ) (p := 2) (hs := hV j) (hμs := measure_ne_top μ _) (c := a j)
  have hSum := Lp.coeFn_fun_finsetSum Finset.univ
    (fun j : ι => indicatorConstLp 2 (hV j) (measure_ne_top μ _) (a j))
  have hAe : ∀ᵐ x ∂μ, x ∈ V i → piecewiseConstantLp (μ := μ) V hV a x = a i := by
    filter_upwards [hSum, ae_all_iff.mpr hCoefs] with x hx hC hxi
    change (∑ j, indicatorConstLp 2 (hV j) (measure_ne_top μ _) (a j)) x = a i
    rw [hx]
    change (∑ j, indicatorConstLp 2 (hV j) (measure_ne_top μ _) (a j) x) = a i
    simp_rw [hC]
    rw [Finset.sum_eq_single i, indicator_of_mem hxi]
    · intro j _ hji
      have hxj : x ∉ V j := fun hh => (Set.disjoint_left.mp (hPair hji)) hh hxi
      exact indicator_of_notMem hxj _
    · simp
  filter_upwards [ae_restrict_of_ae hAe, ae_restrict_mem (hV i)] with x hx hxi
  exact hx hxi

private theorem ofReal_square_le_kernel_mul
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) {x y : Point} (hXY : dist x y ≤ 2 * r) (u : Point → S0) :
    ENNReal.ofReal (‖u x - u y‖ ^ 2) ≤ ENNReal.ofReal ((2 * r) ^ (3 + 2 * s)) *
      ENNReal.ofReal (‖u x - u y‖ ^ 2 / dist x y ^ (3 + 2 * s)) := by
  by_cases h : x = y
  · subst y
    simp
  have hD : 0 < dist x y ^ (3 + 2 * s) := Real.rpow_pos_of_pos (dist_pos.mpr h) _
  have hR : 0 ≤ (2 * r) ^ (3 + 2 * s) := Real.rpow_nonneg (by positivity) _
  have hPow : dist x y ^ (3 + 2 * s) ≤ (2 * r) ^ (3 + 2 * s) :=
    Real.rpow_le_rpow dist_nonneg hXY (by linarith)
  rw [← ENNReal.ofReal_mul hR]
  apply ENNReal.ofReal_le_ofReal
  exact (mul_div_cancel₀ (‖u x-u y‖ ^ 2) hD.ne').symm.le.trans
    (mul_le_mul_of_nonneg_right hPow (div_nonneg (sq_nonneg _) hD.le))

private theorem inv_volume_mul_ball_kernel_le
    {s r : ℝ} (hr : 0 < r) {C M : ℝ≥0∞} (hC : 0 < C) (hC₁ : C < ⊤)
    (hMass : C * ENNReal.ofReal (r ^ 3) ≤ M) :
    M⁻¹ * ENNReal.ofReal ((2 * r) ^ (3 + 2 * s)) ≤
      (C⁻¹ * ENNReal.ofReal (2 ^ (3 + 2 * s))) * ENNReal.ofReal (r ^ (2 * s)) := by
  have hR0 : ENNReal.ofReal (r ^ 3) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
  have hR1 : ENNReal.ofReal (r ^ 3) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hD : ENNReal.ofReal ((2 * r) ^ (3 + 2 * s)) =
      ENNReal.ofReal (r ^ 3) * ENNReal.ofReal (2 ^ (3 + 2 * s)) * ENNReal.ofReal (r ^ (2 * s)) := by
    have hPow : r ^ (3 + 2 * s) = r ^ (3 : ℕ) * r ^ (2 * s) := by
      rw [Real.rpow_add hr, Real.rpow_ofNat]
    rw [Real.mul_rpow (by norm_num) hr.le, hPow,
      ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _),
      ENNReal.ofReal_mul (pow_nonneg hr.le _)]
    ac_rfl
  calc
    _ ≤ (C * ENNReal.ofReal (r ^ 3))⁻¹ * ENNReal.ofReal ((2 * r) ^ (3 + 2 * s)) :=
      mul_le_mul' (ENNReal.inv_le_inv.2 hMass) le_rfl
    _ = _ := by
      rw [hD, ENNReal.mul_inv (.inl hC.ne') (.inl hC₁.ne)]
      let q := ENNReal.ofReal (r ^ (3 : ℕ))
      have hCancel : q⁻¹ * q = 1 := ENNReal.inv_mul_cancel hR0 hR1
      calc
        _ = C⁻¹ * (ENNReal.ofReal (2 ^ (3 + 2 * s)) * ENNReal.ofReal (r ^ (2 * s))) *
          (q⁻¹ * q) := by dsimp only [q]; ac_rfl
        _ = _ := by rw [hCancel, mul_one, mul_assoc]

private def fractionalEnergyDensity (s : ℝ) (u : Point → S0) (x y : Point) : ℝ≥0∞ :=
  ENNReal.ofReal (‖u x - u y‖ ^ 2 / dist x y ^ (3 + 2 * s))

private theorem fractionalEnergyDensity_aemeasurable_pair
    {μ : Measure Point} (s : ℝ) {u : Point → S0} (hu : AEStronglyMeasurable u μ) :
    AEMeasurable (Function.uncurry (fractionalEnergyDensity s u)) (μ.prod μ) :=
  fractionalPairEnergy_aemeasurable s hu

private theorem fractionalEnergyDensity_aemeasurable_at_point
    {μ : Measure Point} (s : ℝ) {u : Point → S0} (hu : AEStronglyMeasurable u μ) (x : Point) :
    AEMeasurable (fractionalEnergyDensity s u x) μ := by
  have hNum : AEStronglyMeasurable (fun y => u x - u y) μ :=
    aestronglyMeasurable_const.sub hu
  have hDen : Measurable (fun y : Point => dist x y ^ (3 + 2 * s)) := by fun_prop
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    ((hNum.norm.aemeasurable.pow_const _).div hDen.aemeasurable)

private theorem square_error_of_cell_mean_le
    {μ : Measure Point} [IsFiniteMeasure μ] {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    {C : ℝ≥0∞} (hC : 0 < C) (hC₁ : C < ⊤) {c : Point}
    (hMass : C * ENNReal.ofReal (r ^ 3) ≤ μ (ball c r))
    (u : Lp S0 2 μ) {x : Point} (hx : x ∈ ball c r) :
    ENNReal.ofReal (‖u x - ⨍ y in ball c r, u y ∂μ‖ ^ 2) ≤
      (C⁻¹ * ENNReal.ofReal (2 ^ (3 + 2 * s))) * ENNReal.ofReal (r ^ (2 * s)) *
        (∫⁻ y, fractionalEnergyDensity s u x y ∂μ) := by
  let W := ball c r
  let B := ENNReal.ofReal ((2 * r) ^ (3 + 2 * s))
  have hμW : 0 < μ W := (ENNReal.mul_pos hC.ne' (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne').trans_le hMass
  have hJ := ofReal_sq_sub_setAverage_le hμW u x
  have hA := fractionalEnergyDensity_aemeasurable_at_point s (Lp.aestronglyMeasurable u) x
  have hAm : AEMeasurable (fractionalEnergyDensity s u x) (μ.restrict W) :=
    hA.mono_measure Measure.restrict_le_self
  have hPoint (y : Point) (hy : y ∈ W) :
      ENNReal.ofReal (‖u x - u y‖ ^ 2) ≤ B * fractionalEnergyDensity s u x y := by
    have hXY : dist x y ≤ 2 * r := by
      have hd := dist_triangle_right x y c
      linarith only [hd, mem_ball.mp hx, mem_ball.mp hy]
    exact ofReal_square_le_kernel_mul hs hr hXY u
  calc
    _ ≤ (μ W)⁻¹ * (∫⁻ y in W, ENNReal.ofReal (‖u x - u y‖ ^ 2) ∂μ) := hJ
    _ ≤ (μ W)⁻¹ * (∫⁻ y in W, B * fractionalEnergyDensity s u x y ∂μ) :=
      mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_ball hPoint)
    _ = ((μ W)⁻¹ * B) * (∫⁻ y in W, fractionalEnergyDensity s u x y ∂μ) := by
      rw [lintegral_const_mul'' _ hAm, mul_assoc]
    _ ≤ _ := mul_le_mul' (inv_volume_mul_ball_kernel_le hr hC hC₁ hMass)
      (lintegral_mono' Measure.restrict_le_self le_rfl)

private theorem lintegral_sq_lp_sub_eq_dist
    {μ : Measure Point} (u v : Lp S0 2 μ) :
    (∫⁻ x, ENNReal.ofReal (‖u x - v x‖ ^ 2) ∂μ) = ENNReal.ofReal (dist u v ^ 2) := by
  rw [dist_eq_norm, ← lintegral_sq_norm_lp μ (u-v)]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub u v] with x hx
  exact congrArg (fun z : S0 => ENNReal.ofReal (‖z‖ ^ 2)) hx.symm

/-- Finite subspaces of genuine L² fields approximate the fractional
energy ball at the stated scale. -/
theorem exists_fractionalEnergy_L2_approximation
    {U : Set Point} (hU : IsSmoothDomain U) (s : ℝ) (hs : 0 < s) :
    ∃ (B : ℝ≥0∞) (R : ℝ), B < ⊤ ∧ 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      ∃ V : Submodule ℝ (Lp S0 2 (volume.restrict U)), FiniteDimensional ℝ V ∧
        ∀ u : Lp S0 2 (volume.restrict U),
          ∃ v : V, ENNReal.ofReal (dist u (v : Lp S0 2 (volume.restrict U)) ^ 2) ≤
            (B * ENNReal.ofReal (r ^ (2 * s))) * fractionalEnergy s U u := by
  obtain ⟨C,R,hC,hC₁,hR,hDensity⟩ := hU.exists_uniform_volume_density
  let B := C⁻¹ * ENNReal.ofReal (2 ^ (3 + 2 * s))
  have hB : B < ⊤ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr hC) ENNReal.ofReal_lt_top
  refine ⟨B,R,hB,hR,?_⟩
  intro r hr hsmall
  obtain ⟨m,c,V,hCenters,hV,hSub,hPair,hCov⟩ := exists_finite_ball_partition hU.1 hr
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := ⟨by
    rw [show μ univ = volume U by simp [μ]]
    exact hU.1.2.2.measure_lt_top⟩
  let L := piecewiseConstantLp (μ := μ) V hV
  refine ⟨L.range, LinearMap.finiteDimensional_range L, ?_⟩
  intro u
  let a (i : Fin m) := ⨍ y in ball (c i) r, u y ∂μ
  let v : Lp S0 2 μ := L a
  let K := B * ENNReal.ofReal (r ^ (2 * s))
  let G (x : Point) := ∫⁻ y, fractionalEnergyDensity s u x y ∂μ
  refine ⟨⟨v, LinearMap.mem_range_self L a⟩, ?_⟩
  change ENNReal.ofReal (dist u v ^ 2) ≤ K * fractionalEnergy s U u
  rw [← lintegral_sq_lp_sub_eq_dist]
  have hSingle (i : Fin m) :
      (∫⁻ x in V i, ENNReal.ofReal (‖u x - v x‖ ^ 2) ∂μ) ≤ (∫⁻ x in V i, K * G x ∂μ) := by
    have hAE := piecewiseConstantLp_ae_on_cell (μ := μ) V hV hPair a i
    have hE : (fun x => ENNReal.ofReal (‖u x - v x‖ ^ 2)) =ᵐ[μ.restrict (V i)]
        fun x => ENNReal.ofReal (‖u x - a i‖ ^ 2) :=
      hAE.mono fun x hx => congrArg (fun z : S0 => ENNReal.ofReal (‖u x-z‖^2)) hx
    rw [lintegral_congr_ae hE]
    apply setLIntegral_mono' (hV i)
    intro x hx
    have hMass : C * ENNReal.ofReal (r ^ 3) ≤ μ (ball (c i) r) := by
      dsimp only [μ]
      rw [Measure.restrict_apply measurableSet_ball, inter_comm]
      exact hDensity (c i) (hCenters i) r hr hsmall
    exact square_error_of_cell_mean_le hs hr hC hC₁ hMass u (hSub i hx).2
  have hRes : μ.restrict U = μ := by
    dsimp only [μ]
    rw [Measure.restrict_restrict hU.1.1.measurableSet, inter_self]
  have hPartition (f : Point → ℝ≥0∞) :
      (∫⁻ x, f x ∂μ) = ∑ i : Fin m, ∫⁻ x in V i, f x ∂μ := by
    calc
      _ = ∫⁻ x in U, f x ∂μ := by rw [hRes]
      _ = _ := by rw [← hCov, lintegral_iUnion hV hPair, tsum_fintype]
  have hG : AEMeasurable G μ :=
    (fractionalEnergyDensity_aemeasurable_pair s (Lp.aestronglyMeasurable u)).lintegral_prod_right
  calc
    _ = ∑ i : Fin m, ∫⁻ x in V i, ENNReal.ofReal (‖u x - v x‖ ^ 2) ∂μ := hPartition _
    _ ≤ ∑ i : Fin m, ∫⁻ x in V i, K * G x ∂μ := Finset.sum_le_sum (fun i _ => hSingle i)
    _ = ∫⁻ x, K * G x ∂μ := (hPartition _).symm
    _ = K * ∫⁻ x, G x ∂μ := lintegral_const_mul'' _ hG
    _ ≤ _ := mul_le_mul' le_rfl (self_le_add_left _ _)

theorem exists_small_positive_ofReal_rpow_mul
    {t R : ℝ} (ht : 0 < t) (hR : 0 < R) {A δ : ℝ≥0∞} (hA : A < ⊤) (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ A * ENNReal.ofReal (r ^ t) < δ := by
  have hPow : Tendsto (fun r : ℝ => r ^ t) (𝓝 0) (𝓝 0) := by
    simpa only [Real.zero_rpow ht.ne'] using (Real.continuousAt_rpow_const 0 t (.inr ht.le)).tendsto
  have hNR : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ t)) (𝓝 0) (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hPow
  have hM : Tendsto (fun r : ℝ => A * ENNReal.ofReal (r ^ t)) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using (ENNReal.continuous_const_mul hA.ne).continuousAt.tendsto.comp hNR
  have hNear : {r : ℝ | A * ENNReal.ofReal (r ^ t) < δ} ∈ 𝓝 0 := hM (Iio_mem_nhds hδ)
  obtain ⟨b,hb,hBall⟩ := Metric.mem_nhds_iff.mp hNear
  let r := min (R / 2) (b / 2)
  have hr : 0 < r := lt_min (half_pos hR) (half_pos hb)
  have hrR : r ≤ R := (min_le_left _ _).trans (half_le_self hR.le)
  have hrB : r ∈ ball (0 : ℝ) b := by
    rw [mem_ball, dist_zero_right, Real.norm_of_nonneg hr.le]
    exact (min_le_right _ _).trans_lt (half_lt_self hb)
  exact ⟨r,hr,hrR,hBall hrB⟩

private theorem norm_lp_le_sqrt_fractionalEnergy_bound
    {U : Set Point} (s : ℝ) (u : Lp S0 2 (volume.restrict U)) {C : ℝ≥0∞}
    (hC : C < ⊤) (h : fractionalEnergy s U u ≤ C) :
    ‖u‖ ≤ Real.sqrt C.toReal := by
  apply Real.le_sqrt_of_sq_le
  have hSq : ENNReal.ofReal (‖u‖ ^ 2) ≤ C :=
    (lintegral_sq_norm_lp (volume.restrict U) u).symm.le.trans
      ((self_le_add_right _ _ : (∫⁻ x in U, ENNReal.ofReal (‖u x‖ ^ 2)) ≤ fractionalEnergy s U u).trans h)
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.toReal_mono hC.ne hSq

/-- A sequence bounded in the intrinsic fractional norm admits an L²
convergent subsequence on the actual smooth domain. -/
theorem exists_L2_subsequence_of_bounded_fractionalEnergy
    {U : Set Point} (hU : IsSmoothDomain U) (s : ℝ) (hs : 0 < s)
    (u : ℕ → Lp S0 2 (volume.restrict U)) (C : ℝ≥0∞) (hC : C < ⊤)
    (hBound : ∀ n, fractionalEnergy s U (u n) ≤ C) :
    ∃ (κ : ℕ → ℕ) (v : Lp S0 2 (volume.restrict U)), StrictMono κ ∧
      Tendsto (u ∘ κ) atTop (𝓝 v) := by
  let μ := volume.restrict U
  let L := Real.sqrt C.toReal
  obtain ⟨B,R,hB,hR,hApprox⟩ := exists_fractionalEnergy_L2_approximation hU s hs
  have hTB : TotallyBounded (range u) := by
    apply Metric.totallyBounded_iff.mpr
    intro e he
    let d := e/3
    have hd : 0 < d := div_pos he (by norm_num)
    obtain ⟨r,hr,hrR,hrSmall⟩ := exists_small_positive_ofReal_rpow_mul
      (by positivity : 0 < 2*s) hR (ENNReal.mul_lt_top hB hC)
        (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hd))
    obtain ⟨V,hV,hApp⟩ := hApprox r hr hrR
    letI : FiniteDimensional ℝ V := hV
    let S : Set (Lp S0 2 μ) := (Subtype.val : V → Lp S0 2 μ) '' closedBall (0 : V) (L + d)
    have hS : IsCompact S := (isCompact_closedBall _ _).image continuous_subtype_val
    obtain ⟨T,hT,hCov⟩ := (Metric.totallyBounded_iff.mp hS.totallyBounded) d hd
    refine ⟨T,hT,?_⟩
    rintro _ ⟨n,rfl⟩
    obtain ⟨v,hDist⟩ := hApp (u n)
    have hvClose : dist (u n) (v : Lp S0 2 μ) < d := by
      have hFin : ENNReal.ofReal (dist (u n) (v : Lp S0 2 μ) ^ 2) < ENNReal.ofReal (d^2) :=
        ((hDist.trans (mul_le_mul' le_rfl (hBound n))).trans_eq
          (mul_right_comm B (ENNReal.ofReal (r ^ (2*s))) C)).trans_lt hrSmall
      exact (sq_lt_sq₀ dist_nonneg hd.le).mp ((ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hd)).1 hFin)
    have hvNorm : ‖v‖ ≤ L + d := by
      have hT := dist_triangle (v : Lp S0 2 μ) (u n) (0 : Lp S0 2 μ)
      rw [dist_zero_right, dist_zero_right, dist_comm (v : Lp S0 2 μ) (u n)] at hT
      exact hT.trans ((add_le_add hvClose.le (norm_lp_le_sqrt_fractionalEnergy_bound s (u n) hC (hBound n))).trans_eq (add_comm _ _))
    have hvS : (v : Lp S0 2 μ) ∈ S := ⟨v,mem_closedBall_zero_iff.mpr hvNorm,rfl⟩
    obtain ⟨w,hw,hvw⟩ := mem_iUnion₂.mp (hCov hvS)
    refine mem_iUnion₂.mpr ⟨w,hw,mem_ball.mpr ?_⟩
    have htri := dist_triangle (u n) (v : Lp S0 2 μ) w
    dsimp only [d] at hvClose hvw
    linarith only [htri,hvClose,mem_ball.mp hvw,he]
  have hK : IsCompact (closure (range u)) :=
    hTB.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨v,_,κ,hκ,hLim⟩ := hK.isSeqCompact (x := u) (fun n => subset_closure (mem_range_self n))
  exact ⟨κ,v,hκ,hLim⟩

end Thesis

end
