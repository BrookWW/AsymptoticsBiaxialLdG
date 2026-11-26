module

public import Thesis.Interpolation.SphericalVacuumMollification
import StratificationTheory.Foundation.SphereInteriorCutoff
import StratificationTheory.Foundation.CompactSobolevCutoff
import StratificationTheory.Foundation.PolarJointConvergence
import HarmonicMaps.Analysis.InteriorSobolevApproximation
import HarmonicMaps.Analysis.MollificationChangeVariables
import HarmonicMaps.Analysis.VariableMollificationL2
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! A common strong Sobolev slice of the uniformly tube-valued mollifications. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Frobenius

namespace Thesis

private theorem euclideanMollification_fixedKernel_of_sampling
    {n q : ℕ} (U : OpenDomain n) (u : Domain n → Ambient q) (hu : IntegrableOn u U.val)
    (h : PositiveRadius) (x : Domain n) (hSample : ∀ y ∈ ball (0 : Domain n) 1, x-h.val • y ∈ U.val) :
    euclideanMollification U u hu h x =
      ∫ y in ball (0 : Domain n) 1, fixedMollifierKernel n y • u (x-h.val • y) := by
  let f (z : Domain n) := scaledMollifierKernel n h z • zeroExtensionOn U u (x-z)
  have hScale : (∫ z, f z) = (h.val^n) • ∫ y, f (h.val • y) := by
    rw [Measure.integral_comp_smul_of_nonneg volume f h.val (hR := h.property.le),
      finrank_euclideanSpace_fin,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ h.property.ne'),one_smul]
  change (∫ z, f z) = _
  rw [hScale,← integral_smul]
  have he (y : Domain n) : (h.val^n) • f (h.val • y) =
      fixedMollifierKernel n y • zeroExtensionOn U u (x-h.val • y) := by
    dsimp only [f]
    rw [scaledMollifierKernel_smul,smul_smul,← mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ h.property.ne'),one_mul]
  simp only [he]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : Domain n) 1)
    (fun y hy => by rw [fixedMollifierKernel_zero_of_not_mem_unitBall hy,zero_smul])]
  apply setIntegral_congr_fun measurableSet_ball
  intro y hy
  change fixedMollifierKernel n y • zeroExtensionOn U u (x-h.val • y) =
    fixedMollifierKernel n y • u (x-h.val • y)
  rw [zeroExtensionOn,indicator_of_mem (hSample y hy)]

private theorem finiteSphereMollification_restrict {n q : ℕ} {U V : OpenDomain n}
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hu : MemW12 U u D) (hV : V.val ⊆ U.val) : MemW12 V u D :=
  ⟨hu.1.mono hV,hu.2.1.mono_measure (Measure.restrict_mono_set _ hV),
    fun i => (hu.2.2 i).mono_measure (Measure.restrict_mono_set _ hV)⟩

/-- The radial graph admits one sampling radius and one sequence of smooth
ambient approximants whose values enter the tube and whose angular L² map
and scaled derivative errors converge to zero on that same sphere. -/
theorem exists_sphericalVacuum_mollified_ray_data
    (a : BulkCoefficients) (base : UnitBoundarySphere 3)
    {v : UnitBoundarySphere 3 → Ambient 5} {w : Point → Ambient 5}
    {D : Point → HarmonicMaps.Gradient 3 5} {A : UnitBoundarySphere 3 → HarmonicMaps.Gradient 3 5}
    (hw : MemW12Loc ⟨({0}ᶜ : Set Point),isOpen_compl_singleton⟩ w D)
    (hv : ∀ θ, v θ ∈ (vacuumCompactSmoothEmbeddedTarget a).carrierSet)
    (hRay : ∀ (r : PositiveRadius) (θ : UnitBoundarySphere 3), w (r.val • θ.val) = v θ)
    (hD : ∀ (r : PositiveRadius) (θ : UnitBoundarySphere 3) (i : Fin 3), D (r.val • θ.val) i = r.val⁻¹ • A θ i)
    (hA : ∀ i : Fin 3, MemLp (fun θ => A θ i) 2 (unitBoundarySurface 3))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r ∈ Ioo (7/8 : ℝ) (9/8), ∃ m : ℕ → Point → Ambient 5,
      ∃ hm : ∀ k, ContDiff ℝ ∞ (m k),
      (∀ (k : ℕ) (θ : UnitBoundarySphere 3), Metric.infDist (m k (r • θ.val))
        (vacuumCompactSmoothEmbeddedTarget a).carrierSet < ρ) ∧
      (∀ k, MemLp (fun θ : UnitBoundarySphere 3 => m k (r • θ.val)) 2 (unitBoundarySurface 3)) ∧
      Tendsto (fun k => eLpNorm (fun θ : UnitBoundarySphere 3 => m k (r • θ.val)-v θ) 2
        (unitBoundarySurface 3)) atTop (𝓝 0) ∧
      (∀ k i, MemLp (fun θ : UnitBoundarySphere 3 => r • coordinateDerivative (m k) (hm k) i (r • θ.val))
        2 (unitBoundarySurface 3)) ∧
      ∀ i, Tendsto (fun k => eLpNorm (fun θ : UnitBoundarySphere 3 =>
        r • coordinateDerivative (m k) (hm k) i (r • θ.val)-A θ i) 2 (unitBoundarySurface 3)) atTop (𝓝 0) := by
  let U := (⟨({0}ᶜ : Set Point),isOpen_compl_singleton⟩ : OpenDomain 3)
  have hWVac (x : Point) (hx : x ≠ 0) : w x ∈ (vacuumCompactSmoothEmbeddedTarget a).carrierSet := by
    let z := sphereRadialDirection base x
    have hDecomp : ‖x‖ • z.val = x := by
      change ‖x‖ • (sphereRadialDirection base x).val = _
      rw [sphereRadialDirection,dif_pos hx]
      exact NormedSpace.norm_smul_normalize x
    have he : w x = v z := (congrArg w hDecomp).symm.trans (hRay ⟨‖x‖,norm_pos_iff.mpr hx⟩ z)
    rw [he]
    exact hv z
  obtain ⟨δ,hδ,hTube⟩ := exists_uniform_sphericalVacuum_mollificationTube a base hw hWVac hD hA hρ
  have hClosed : {x : Point | 1-(3/8 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 1+3/8} ⊆ U.val := by
    intro x hx h
    have he : x = 0 := mem_singleton_iff.mp h
    have hN : 1-(3/8 : ℝ) ≤ ‖x‖ := hx.1
    rw [he,norm_zero] at hN
    norm_num at hN
  obtain ⟨χ,hχ,hχc,_,_,hχU,hχOne,hχD⟩ := exists_sphere_interior_cutoff_in_openDomain
    (δ := 3/8) (by norm_num) (by norm_num) U hClosed
  let u (x : Point) := χ x • w x
  let Du (x : Point) (i : Fin 3) := coordinateDerivative χ hχ i x • w x+χ x • D x i
  have huGlobal : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u Du :=
    hw.smoothCutoff_univ hχ hχc hχU
  have huBall : MemW12 (ballDomain (0 : Point) 2) u Du :=
    finiteSphereMollification_restrict huGlobal (subset_univ _)
  let e := min δ (1/32 : ℝ)/2
  have he : 0 < e := half_pos (lt_min hδ (by norm_num))
  let h (k : ℕ) : PositiveRadius := ⟨e/((k : ℝ)+1),by positivity⟩
  have hle (k : ℕ) : (h k).val ≤ e := by
    change e/((k : ℝ)+1) ≤ e
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ)+1)).mpr
    nlinarith only [mul_nonneg he.le (Nat.cast_nonneg (α := ℝ) k)]
  have hsmall (k : ℕ) : (h k).val ≤ 1/32 :=
    (hle k).trans ((half_lt_self (lt_min hδ (by norm_num))).le.trans (min_le_right _ _))
  have hTubeSmall (k : ℕ) : (h k).val < δ :=
    (hle k).trans_lt ((half_lt_self (lt_min hδ (by norm_num))).trans_le (min_le_left _ _))
  have hLim : Tendsto h atTop (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) := by
    apply tendsto_comap_iff.mpr
    simpa only [Function.comp_def,h,div_eq_mul_inv,one_mul,mul_zero] using
      (tendsto_const_nhds (x := e)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  let m (k : ℕ) := euclideanMollification (ballDomain (0 : Point) 2) u huBall.integrable_ball (h k)
  have hm (k : ℕ) : ContDiff ℝ ∞ (m k) := euclideanMollification_contDiff _ _ huBall.integrable_ball _
  let G : Option (Fin 3) → ℕ → Point → Ambient 5 := fun i k =>
    match i with
    | none => m k
    | some i => coordinateDerivative (m k) (hm k) i
  let g : Option (Fin 3) → Point → Ambient 5 := fun i =>
    match i with
    | none => u
    | some i => fun x => Du x i
  let μ : Measure Point := volume.restrict (ball (0 : Point) (3/2))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hSub : μ ≤ volume.restrict (ball (0 : Point) 2) :=
    Measure.restrict_mono_set _ (ball_subset_ball (by norm_num : (3/2 : ℝ) ≤ 2))
  have hGcont (i : Option (Fin 3)) (k : ℕ) : Continuous (G i k) := by
    cases i with
    | none => exact (hm k).continuous
    | some i => exact ((hm k).continuous_fderiv (by simp)).clm_apply continuous_const
  have hGmem (i : Option (Fin 3)) (k : ℕ) : MemLp (G i k) 2 μ := by
    obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : Point) (3/2)).exists_bound_of_continuousOn
      (hGcont i k).continuousOn
    exact MemLp.of_bound (hGcont i k).aestronglyMeasurable M
      ((ae_restrict_mem measurableSet_ball).mono fun x hx => hM x (ball_subset_closedBall hx))
  have hgMem (i : Option (Fin 3)) : MemLp (g i) 2 μ := by
    cases i with
    | none => exact huBall.2.1.mono_measure hSub
    | some i => exact (huBall.2.2 i).mono_measure hSub
  have hConv (i : Option (Fin 3)) : Tendsto (fun k => eLpNorm (G i k-g i) 2 μ) atTop (𝓝 0) := by
    cases i with
    | none =>
      change Tendsto (fun k => eLpNorm (fun x => m k x-u x) 2 μ) atTop (𝓝 0)
      simpa only [Function.comp_def,m] using (huBall.tendsto_eLpNorm_mollification_inner_ball
        (by norm_num : (3/2 : ℝ) < 2)).comp hLim
    | some i =>
      change Tendsto (fun k => eLpNorm (fun x => coordinateDerivative (m k) (hm k) i x-Du x i) 2 μ) atTop (𝓝 0)
      simpa only [Function.comp_def,m] using (huBall.tendsto_eLpNorm_mollification_column_inner_ball
        (by norm_num : (3/2 : ℝ) < 2) i).comp hLim
  obtain ⟨κ,hκ,hκae⟩ := exists_subseq_ae_tendsto_polar_l2_family_ball (by decide : 0 < 3)
    (a := (0 : Point)) (R := 3/2) hGmem hgMem hConv
  have hRad : Ioo (7/8 : ℝ) (9/8) ⊆ Ioo 0 (3/2) := Ioo_subset_Ioo (by norm_num) (by norm_num)
  have hMass : volume (Ioo (7/8 : ℝ) (9/8)) ≠ 0 := by rw [Real.volume_Ioo]; norm_num
  obtain ⟨r,hr,hRayData⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hMass
    (hκae.filter_mono (ae_mono (Measure.restrict_mono_set volume hRad)))
  have hr₀ : 0 < r := (by norm_num : 0 < (7/8 : ℝ)).trans hr.1
  have hθnorm (θ : UnitBoundarySphere 3) : ‖r • θ.val‖ = r := by
    rw [norm_smul,Real.norm_of_nonneg hr₀.le,mem_sphere_zero_iff_norm.mp θ.property,mul_one]
  have hUS (θ : UnitBoundarySphere 3) : u (0+r • θ.val) = v θ := by
    have hχ₀ : χ (r • θ.val) = 1 := hχOne _ (by
      change 1-3/8/2 < ‖r • θ.val‖ ∧ ‖r • θ.val‖ < 1+3/8/2
      rw [hθnorm]
      exact ⟨by linarith only [hr.1],by linarith only [hr.2]⟩)
    simp only [zero_add,u,hχ₀,one_smul,hRay ⟨r,hr₀⟩ θ]
  have hUD (θ : UnitBoundarySphere 3) (i : Fin 3) : Du (0+r • θ.val) i = r⁻¹ • A θ i := by
    have hS : r • θ.val ∈ {x : Point | (1 : ℝ)-3/8/2 < ‖x‖ ∧ ‖x‖ < 1+3/8/2} := by
      change _ < ‖r • θ.val‖ ∧ ‖r • θ.val‖ < _
      rw [hθnorm]
      exact ⟨by linarith only [hr.1],by linarith only [hr.2]⟩
    simp only [Du,zero_add,hχD _ hS i,zero_smul,zero_add,hχOne _ hS,one_smul,hD ⟨r,hr₀⟩ θ i]
  have hμeq : unitBoundarySurface 3 = (volume : Measure Point).toSphere :=
    euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 3)
  refine ⟨r,hr,m ∘ κ,fun k => hm (κ k),?_,?_,?_,?_,?_⟩
  · intro k θ
    let x := r • θ.val
    have hScale : (h (κ k)).val ≤ 1/32 := hsmall (κ k)
    have hSample (y : Point) (hy : y ∈ ball (0 : Point) 1) :
        1-3/8/2 < ‖x-(h (κ k)).val • y‖ ∧
          ‖x-(h (κ k)).val • y‖ < 1+3/8/2 := by
      have hy' : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
      have hyN : ‖(h (κ k)).val • y‖ ≤ 1/32 := by
        rw [norm_smul,Real.norm_of_nonneg (h (κ k)).property.le]
        exact (mul_le_of_le_one_right (h (κ k)).property.le hy'.le).trans hScale
      have hL := norm_le_norm_sub_add x ((h (κ k)).val • y)
      have hU := norm_sub_le x ((h (κ k)).val • y)
      have hxN : ‖x‖ = r := hθnorm θ
      rw [hxN] at hL hU
      exact ⟨by linarith only [hL,hyN,hr.1],by linarith only [hU,hyN,hr.2]⟩
    have hEq : m (κ k) x =
        ∫ y in ball (0 : Point) 1, fixedMollifierKernel 3 y • w (x-(h (κ k)).val • y) := by
      change euclideanMollification (ballDomain (0 : Point) 2) u huBall.integrable_ball (h (κ k)) x = _
      rw [euclideanMollification_fixedKernel_of_sampling _ _ _ _ _ (fun y hy =>
        mem_ball_zero_iff.mpr ((hSample y hy).2.trans (by norm_num : (1 : ℝ)+3/8/2 < 2)))]
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      change fixedMollifierKernel 3 y • (χ (x-(h (κ k)).val • y) • w (x-(h (κ k)).val • y)) = _
      rw [hχOne _ (hSample y hy),one_smul]
    show Metric.infDist (m (κ k) x) (vacuumCompactSmoothEmbeddedTarget a).carrierSet < ρ
    rw [hEq]
    exact hTube (h (κ k)) (hTubeSmall (κ k)) x (by
      show ‖x‖ ∈ Icc (3/4 : ℝ) (5/4)
      rw [hθnorm θ]
      exact ⟨by linarith only [hr.1], by linarith only [hr.2]⟩)
  · intro k
    simpa only [hμeq,Function.comp_def,G,zero_add] using (hRayData none).1 (κ k)
  · rw [hμeq]
    apply tendsto_eLpNorm_two_zero_of_integral_norm_sq
    · intro k
      have h := ((hRayData none).1 (κ k)).sub (hRayData none).2.1
      have he : (fun θ : UnitBoundarySphere 3 => G none (κ k) (0+r • θ.val))-
          (fun θ => g none (0+r • θ.val)) =
          fun θ => m (κ k) (r • θ.val)-v θ := by
        funext θ
        change m (κ k) (0+r • θ.val)-u (0+r • θ.val) = _
        rw [hUS,zero_add]
      exact he ▸ h
    · have h := (hRayData none).2.2.2
      simpa only [Function.comp_def,G,g,zero_add] using (show Tendsto (fun k =>
        ∫ θ : UnitBoundarySphere 3, ‖m (κ k) (0+r • θ.val)-u (0+r • θ.val)‖^2
          ∂(volume : Measure Point).toSphere) atTop (𝓝 0) from h).congr
        (fun k => integral_congr_ae (Eventually.of_forall fun θ => by rw [hUS,zero_add]))
  · intro k i
    rw [hμeq]
    have h := ((hRayData (some i)).1 (κ k)).const_smul r
    change MemLp (fun θ : UnitBoundarySphere 3 => r • coordinateDerivative (m (κ k))
      (hm (κ k)) i (0+r • θ.val)) 2 (volume : Measure Point).toSphere at h
    simpa only [Function.comp_apply,zero_add] using h
  · intro i
    rw [hμeq]
    let E (k : ℕ) (θ : UnitBoundarySphere 3) :=
      coordinateDerivative (m (κ k)) (hm (κ k)) i (0+r • θ.val)-Du (0+r • θ.val) i
    have hE (k : ℕ) : MemLp (E k) 2 (volume : Measure Point).toSphere :=
      ((hRayData (some i)).1 (κ k)).sub (hRayData (some i)).2.1
    have hConv : Tendsto (fun k => eLpNorm (E k) 2 (volume : Measure Point).toSphere) atTop (𝓝 0) :=
      tendsto_eLpNorm_two_zero_of_integral_norm_sq hE (hRayData (some i)).2.2.2
    have hScale := ENNReal.Tendsto.const_mul (a := ‖r‖ₑ) hConv (Or.inr (by finiteness))
    have hUpper : Tendsto (fun k => ‖r‖ₑ * eLpNorm (E k) 2 (volume : Measure Point).toSphere)
        atTop (𝓝 0) := by simpa only [mul_zero] using hScale
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper (fun _ => bot_le)
    intro k
    have hEq : (fun θ : UnitBoundarySphere 3 =>
      r • coordinateDerivative (m (κ k)) (hm (κ k)) i (r • θ.val)-A θ i) = r • E k := by
      funext θ
      have hA' : r • Du (0+r • θ.val) i = A θ i := by
        rw [hUD,smul_smul,mul_inv_cancel₀ hr₀.ne',one_smul]
      change r • coordinateDerivative (m (κ k)) (hm (κ k)) i (r • θ.val)-A θ i =
        r • (coordinateDerivative (m (κ k)) (hm (κ k)) i (0+r • θ.val)-Du (0+r • θ.val) i)
      rw [smul_sub,hA',zero_add]
    change eLpNorm (fun θ : UnitBoundarySphere 3 =>
      r • coordinateDerivative (m (κ k)) (hm (κ k)) i (r • θ.val)-A θ i) 2
      (volume : Measure Point).toSphere ≤ ‖r‖ₑ*eLpNorm (E k) 2 (volume : Measure Point).toSphere
    rw [hEq]
    exact eLpNorm_const_smul_le
end Thesis
