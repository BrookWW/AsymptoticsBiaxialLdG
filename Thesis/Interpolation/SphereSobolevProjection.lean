module

public import Thesis.Interpolation.RegularizedSphereProjection
public import HarmonicMaps.Sobolev
public import HarmonicMaps.Energy
import Thesis.Interpolation.SphereProjectionAveraging
import StratificationTheory.Foundation.CylinderPostcomposition
import HarmonicMaps.Analysis.SobolevL2Closure
import HarmonicMaps.EnergyLemmas
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.L2Space

/-! Sobolev projection to the quaternion sphere with a uniform Dirichlet budget. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory
open scoped ContDiff ENNReal Topology

namespace Thesis

private theorem aeStronglyMeasurable_hsNormSq {n : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient 4} {Du : Domain n → HarmonicMaps.Gradient n 4} (hu : MemW12 Ω u Du) :
    AEStronglyMeasurable (fun x => hsNormSq (Du x)) (volume.restrict Ω.val) :=
  hu.integrable_hsNormSq.aestronglyMeasurable

private theorem hsNormSq_div_distance_memLp {n : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient 4} {Du : Domain n → HarmonicMaps.Gradient n 4} (hu : MemW12 Ω u Du)
    (y : QuaternionCoordinates)
    (hE : (∫⁻ x in Ω.val, ENNReal.ofReal (hsNormSq (Du x)) *
      ENNReal.ofReal ((‖u x - y‖ ^ 2)⁻¹)) < ⊤) :
    MemLp (fun x => Real.sqrt (hsNormSq (Du x)) / ‖u x - y‖) 2 (volume.restrict Ω.val) := by
  have hmeas : AEStronglyMeasurable (fun x => Real.sqrt (hsNormSq (Du x)) / ‖u x - y‖)
      (volume.restrict Ω.val) := by
    have hNum := (Real.continuous_sqrt.comp_aestronglyMeasurable (aeStronglyMeasurable_hsNormSq hu)).aemeasurable
    have hDen := (hu.2.1.aemeasurable.sub (aemeasurable_const (b := y))).norm
    exact (hNum.div hDen).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  refine ⟨hmeas.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)]
  convert hE using 1
  apply lintegral_congr
  intro x
  rw [div_pow, Real.sq_sqrt (hsNormSq_nonneg _), div_eq_mul_inv,
    ENNReal.ofReal_mul (hsNormSq_nonneg _)]

private theorem norm_gradient_correctedSphereProjection_le {y z v : QuaternionCoordinates}
    {δ C : ℝ} (hR : ContDiff ℝ ∞ (restoreSphereDirection y))
    (hC : 0 < C) (hDR : ∀ ξ, ‖ξ‖ ≤ 1 → ‖fderiv ℝ (restoreSphereDirection y) ξ‖ ≤ C)
    (hz : z ≠ y) :
    ‖fderiv ℝ (correctedSphereProjection y δ) z v‖ ≤ (2 * C / ‖z - y‖) * ‖v‖ := by
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  refine (norm_fderiv_correctedSphereProjection_le hR hDR (Or.inl hz)).trans ?_
  exact div_le_div_of_nonneg_left (by positivity) (norm_pos_iff.2 (sub_ne_zero.2 hz))
    (norm_sub_le_regularizedSphereRadius _ _ _)

/-- A bounded finite Sobolev field in four target coordinates admits the
corrected translated projection into the unit sphere, with its actual weak
gradient and a uniform Dirichlet energy bound. -/
theorem exists_correctedSphereProjection_memW12 :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {n : ℕ} (Ω : OpenDomain n)
      [IsFiniteMeasure (volume.restrict Ω.val)]
      {u : Domain n → Ambient 4} {Du : Domain n → HarmonicMaps.Gradient n 4},
      MemW12 Ω u Du → (∀ᵐ x ∂volume.restrict Ω.val, ‖u x‖ ≤ 1) →
      ∃ y : QuaternionCoordinates, ‖y‖ < 1 / 4 ∧
        let w := correctedSphereProjection y 0 ∘ u
        let Dw : Domain n → HarmonicMaps.Gradient n 4 := fun x i =>
          fderiv ℝ (correctedSphereProjection y 0) (u x) (Du x i)
        MemW12 Ω w Dw ∧ (∀ᵐ x ∂volume.restrict Ω.val, ‖w x‖ = 1) ∧
        HarmonicMaps.dirichletEnergy Dw Ω.val ≤ C * HarmonicMaps.dirichletEnergy Du Ω.val := by
  obtain ⟨K, hK, hChoose⟩ := exists_sphereProjection_center_ae
  obtain ⟨C, hC, hRestore⟩ := exists_fderiv_restoreSphereDirection_bound
  let M := ENNReal.ofReal ((2 * C) ^ 2)
  refine ⟨M * K, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK, ?_⟩
  intro n Ω _ u Du hu hB
  let μ := volume.restrict Ω.val
  let e : Domain n → ℝ≥0∞ := fun x => ENNReal.ofReal (hsNormSq (Du x))
  have he : AEMeasurable e μ := (aeStronglyMeasurable_hsNormSq hu).aemeasurable.ennreal_ofReal
  have heFin : (∫⁻ x, e x ∂μ) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => hsNormSq_nonneg (Du x))).1
      hu.integrable_hsNormSq.2
  obtain ⟨y, hy, hyAvoid, hyBudget⟩ := hChoose μ u e hu.2.1.aemeasurable he hB
  obtain ⟨hR, hDR⟩ := hRestore y hy.le
  let F := correctedSphereProjection y
  let w : ℝ → Domain n → Ambient 4 := fun δ => F δ ∘ u
  let D : ℝ → Domain n → HarmonicMaps.Gradient n 4 := fun δ x i => fderiv ℝ (F δ) (u x) (Du x i)
  let g : Domain n → ℝ := fun x => Real.sqrt (hsNormSq (Du x)) / ‖u x - y‖
  have hg : MemLp g 2 μ := hsNormSq_div_distance_memLp hu y
    (hyBudget.trans_lt (ENNReal.mul_lt_top hK heFin))
  have hg0 (x : Domain n) : 0 ≤ g x := div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hwM (δ : ℝ) : AEStronglyMeasurable (w δ) μ := by
    have hp : Measurable (regularizedSphereDirection y δ) := by
      unfold regularizedSphereDirection regularizedSphereRadius
      fun_prop
    exact ((hR.continuous.measurable.comp hp).comp_aemeasurable hu.2.1.aemeasurable).aestronglyMeasurable
  have hDM (δ : ℝ) (i : Fin n) : AEStronglyMeasurable (fun x => D δ x i) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (((measurable_fderiv ℝ (F δ)).comp_aemeasurable hu.2.1.aemeasurable).aestronglyMeasurable.prodMk
        (hu.2.2 i).aestronglyMeasurable)
  have hDom (δ : ℝ) (i : Fin n) : ∀ᵐ x ∂μ, ‖D δ x i‖ ≤ (2 * C) * ‖g x‖ := by
    filter_upwards [hyAvoid] with x hx
    have hI : ‖Du x i‖ ≤ Real.sqrt (hsNormSq (Du x)) := by
      rw [Real.le_sqrt (norm_nonneg _) (hsNormSq_nonneg _)]
      exact Finset.single_le_sum (f := fun j => ‖Du x j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    calc
      _ ≤ (2 * C / ‖u x - y‖) * ‖Du x i‖ :=
        norm_gradient_correctedSphereProjection_le hR hC hDR hx
      _ ≤ (2 * C / ‖u x - y‖) * Real.sqrt (hsNormSq (Du x)) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
      _ = _ := by dsimp only [g]; ring
  have hwBound (δ : ℝ) (x : Domain n) : ‖w δ x‖ ≤ 2 := norm_correctedSphereProjection_le_two hy.le δ _
  have hwp (δ : ℝ) : MemLp (w δ) 2 μ := MemLp.of_bound (hwM δ) 2 (ae_of_all _ (hwBound δ))
  have hDp (δ : ℝ) (i : Fin n) : MemLp (fun x => D δ x i) 2 μ := hg.of_le_mul (hDM δ i) (hDom δ i)
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hSmooth (j : ℕ) : MemW12 Ω (w (δ j)) (D (δ j)) := by
    have hd : 0 < δ j := by dsimp only [δ]; positivity
    refine StratificationTheory.MemW12.postcompose_finite hu (F (δ j))
      (hR.comp (contDiff_regularizedSphereDirection y hd.ne')) (2 * C / δ j) fun z => ?_
    refine (norm_fderiv_correctedSphereProjection_le hR hDR (Or.inr hd.ne')).trans ?_
    apply div_le_div_of_nonneg_left (by positivity) hd
    simpa only [abs_of_nonneg hd.le] using abs_le_regularizedSphereRadius y (δ j) z
  have hWconv : Tendsto (fun j => eLpNorm (w (δ j) - w 0) 2 μ) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_two_zero_of_dominated (fun j => (hwM _).sub (hwM _))
      (memLp_const 1 : MemLp (fun _ : Domain n => (1 : ℝ)) 2 μ) (C := 4) ?_ ?_
    · intro j
      exact ae_of_all _ fun x => by
        simpa only [Pi.sub_apply, norm_one, mul_one] using
          ((norm_sub_le _ _).trans (add_le_add (hwBound (δ j) x) (hwBound 0 x))).trans
            (show (2 : ℝ) + 2 ≤ 4 by norm_num)
    · filter_upwards [hyAvoid] with x hx
      have h := (continuousAt_correctedSphereProjection_scale hR hx).tendsto.comp hδ
      change Tendsto (fun j => w (δ j) x) atTop (𝓝 (w 0 x)) at h
      simpa only [Pi.sub_apply, sub_self] using h.sub (tendsto_const_nhds (x := w 0 x))
  have hDconv (i : Fin n) : Tendsto
      (fun j => eLpNorm (fun x => D (δ j) x i - D 0 x i) 2 μ) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_two_zero_of_dominated (fun j => (hDM _ i).sub (hDM _ i)) hg
      (C := 4 * C) ?_ ?_
    · intro j
      filter_upwards [hDom (δ j) i, hDom 0 i] with x hx hx₀
      calc
        _ ≤ ‖D (δ j) x i‖ + ‖D 0 x i‖ := norm_sub_le _ _
        _ ≤ (2 * C) * ‖g x‖ + (2 * C) * ‖g x‖ := add_le_add hx hx₀
        _ = _ := by ring
    · filter_upwards [hyAvoid] with x hx
      have h := (continuousAt_fderiv_correctedSphereProjection_scale hR hx (Du x i)).tendsto.comp hδ
      change Tendsto (fun j => D (δ j) x i) atTop (𝓝 (D 0 x i)) at h
      simpa only [sub_self] using h.sub (tendsto_const_nhds (x := D 0 x i))
  refine ⟨y, hy, MemW12.of_L2_limit hSmooth (hwp 0) (hDp 0) hWconv hDconv, ?_, ?_⟩
  · exact hyAvoid.mono fun _ hx => norm_correctedSphereProjection_zero hy.le hx
  change (∫⁻ x, ENNReal.ofReal (hsNormSq (D 0 x)) ∂μ) ≤ (M * K) * ∫⁻ x, e x ∂μ
  let W : Domain n → ℝ≥0∞ := fun x => e x * ENNReal.ofReal ((‖u x - y‖ ^ 2)⁻¹)
  have hW : AEMeasurable W μ := he.mul
    (ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      ((hu.2.1.aemeasurable.sub aemeasurable_const).norm.pow_const 2).inv)
  calc
    _ ≤ ∫⁻ x, M * W x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hyAvoid] with x hx
      let B := 2 * C / ‖u x - y‖
      have hB0 : 0 ≤ B := by dsimp only [B]; positivity
      have hSq : hsNormSq (D 0 x) ≤ B ^ 2 * hsNormSq (Du x) := by
        simp only [hsNormSq, Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _)
            (norm_gradient_correctedSphereProjection_le hR hC hDR hx) 2
      refine (ENNReal.ofReal_le_ofReal hSq).trans_eq ?_
      have hEq : B ^ 2 * hsNormSq (Du x) =
          (2 * C) ^ 2 * (hsNormSq (Du x) * (‖u x - y‖ ^ 2)⁻¹) := by
        dsimp only [B]
        rw [div_pow, div_eq_mul_inv]
        ring
      rw [hEq, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (hsNormSq_nonneg _)]
    _ = M * (∫⁻ x, W x ∂μ) := lintegral_const_mul'' M hW
    _ ≤ (M * K) * (∫⁻ x, e x ∂μ) := by rw [mul_assoc]; gcongr

end Thesis
