module

public import Thesis.Interpolation.CylinderBoundaryTrace
import Thesis.MeasureGeometry.CylinderSliceEnergy
import StratificationTheory.Foundation.AngularL2Membership
import HarmonicMaps.Analysis.BallPolarIntegral
import HarmonicMaps.Analysis.SobolevAECongruence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Zero horizontal classes and quantitative vanishing of the original lateral collars. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ENNReal Topology

namespace Thesis.MeasureGeometry

/-- The difference of two given horizontal traces represents the actual difference. -/
theorem RepresentsCylinderHeightL2Trace.sub {q : ℕ} {R lo hi : ℝ}
    {B : OrthonormalBasis (Fin 3) ℝ Point} {c : Point} {u v : Point → Ambient q}
    {P Q : CylinderHeightL2Trace q R lo hi}
    (hP : RepresentsCylinderHeightL2Trace B c u P) (hQ : RepresentsCylinderHeightL2Trace B c v Q) :
    RepresentsCylinderHeightL2Trace B c (u - v) (P - Q) := by
  filter_upwards [hP, hQ] with t htP htQ ht
  obtain ⟨hpu, hp⟩ := htP ht
  obtain ⟨hpv, hq⟩ := htQ ht
  refine ⟨hpu.sub hpv, ?_⟩
  change P _ - Q _ = _
  rw [hp, hq, ← hpu.toLp_sub hpv]
  rfl

/-- The difference of two given lateral traces represents the actual difference. -/
theorem RepresentsCylinderSideL2Trace.sub {q : ℕ} {R lo hi : ℝ}
    {B : OrthonormalBasis (Fin 3) ℝ Point} {c : Point} {u v : Point → Ambient q}
    {P Q : CylinderSideL2Trace q R lo hi}
    (hP : RepresentsCylinderSideL2Trace B c u P) (hQ : RepresentsCylinderSideL2Trace B c v Q) :
    RepresentsCylinderSideL2Trace B c (u - v) (P - Q) := by
  filter_upwards [hP, hQ] with t htP htQ ht
  obtain ⟨hpu, hp⟩ := htP ht
  obtain ⟨hpv, hq⟩ := htQ ht
  refine ⟨hpu.sub hpv, ?_⟩
  change P _ - Q _ = _
  rw [hp, hq, ← hpu.toLp_sub hpv]
  rfl

private theorem zero_cylinderHeight_trace {q : ℕ} (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (R lo hi : ℝ) : RepresentsCylinderHeightL2Trace B c (0 : Point → Ambient q)
      (0 : CylinderHeightL2Trace q R lo hi) := by
  let h : MemLp (0 : Plane → Ambient q) 2 (volume.restrict (ball (0 : Plane) R)) := MemLp.zero
  exact Eventually.of_forall fun _ _ => ⟨h, h.toLp_zero.symm⟩

/-- Zero horizontal endpoint classes give the literal axial zero extension
on a wider cylinder, with the same zero-extended weak columns. -/
theorem memW12_cylinder_axial_zeroExtend {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R : ℝ) {lo hi : ℝ} (hI : lo < hi)
    (w : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q)
    (hw : MemW12 (translatedAxisCylinderDomain B c R lo hi) w D)
    (P : CylinderHeightL2Trace q R lo hi) (hP : RepresentsCylinderHeightL2Trace B c w P)
    (hLo : P ⟨lo, le_rfl, hI.le⟩ = 0) (hHi : P ⟨hi, hI.le, le_rfl⟩ = 0) :
    let A := {x : Point | (cylinderRecoveryCoordinates B c x).2 ∈ Ioo lo hi}
    MemW12 (translatedAxisCylinderDomain B c R (lo - 1) (hi + 1)) (A.indicator w) (A.indicator D) := by
  intro A
  have hBelow : lo - 1 < lo := by linarith
  have hAbove : hi < hi + 1 := by linarith
  have hZeroBelow : MemW12 (translatedAxisCylinderDomain B c R (lo - 1) lo)
      (0 : Point → Ambient q) (0 : Point → HarmonicMaps.Gradient 3 q) := MemW12.zero _
  have hZeroAbove : MemW12 (translatedAxisCylinderDomain B c R hi (hi + 1))
      (0 : Point → Ambient q) (0 : Point → HarmonicMaps.Gradient 3 q) := MemW12.zero _
  have hG := (memW12_cylinderThreePiecewise B c R hBelow hI hAbove 0 w 0 0 D 0
    hZeroBelow hw hZeroAbove 0 P 0 (zero_cylinderHeight_trace B c R (lo - 1) lo) hP
      (zero_cylinderHeight_trace B c R hi (hi + 1)) hLo.symm hHi).1
  have hEq {E : Type} [Zero E] (f : Point → E) :
      cylinderThreePiecewise B c lo hi 0 f 0 =ᵐ[volume.restrict (translatedAxisCylinder c (B 2) R (lo - 1) (hi + 1))]
        A.indicator f := by
    filter_upwards [ae_cylinderHeight_ne B c R (lo - 1) (hi + 1) lo] with x hx
    let z := (cylinderRecoveryCoordinates B c x).2
    change (if z < hi then (if z < lo then (0 : E) else f x) else 0) = A.indicator f x
    by_cases hzh : z < hi
    · by_cases hzl : z < lo
      · have hA : x ∉ A := fun h => (not_lt_of_ge h.1.le) hzl
        simp [hzh, hzl, hA]
      · have hA : x ∈ A := ⟨lt_of_le_of_ne (le_of_not_gt hzl) hx.symm, hzh⟩
        simp [hzh, hzl, hA]
    · have hA : x ∉ A := fun h => hzh h.2
      simp [hzh, hA]
  exact hG.congr_ae (hEq w) (hEq D)

private theorem integral_norm_le_Lp_two_const {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → E} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ (eLpNorm f 2 μ).toReal * (μ univ ^ (1 / 2 : ℝ)).toReal := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf.aestronglyMeasurable
  have hPow : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
  rw [hPow] at h
  have hR := ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ))) h
  rw [ENNReal.toReal_mul] at hR
  have hL : (eLpNorm f 1 μ).toReal = ∫ x, ‖f x‖ ∂μ := by
    rw [eLpNorm_one_eq_lintegral_enorm, integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun _ => norm_nonneg _) hf.aestronglyMeasurable.norm]
    simp only [ofReal_norm]
  exact hL ▸ hR

/-- Continuity of a genuine zero radial endpoint makes the original collar
fibers uniformly small in native `L¹` for almost every near-wall radius. -/
theorem lateral_integral_norm_small_near_zeroTrace {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hR : 0 < R)
    (w : Point → Ambient q) (P : CylinderSideL2Trace q R lo hi)
    (hP : RepresentsCylinderSideL2Trace B c w P) (hZero : P ⟨R, half_le_self hR.le, le_rfl⟩ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ Icc (R / 2) R, a < R ∧ ∀ᵐ r : ℝ ∂volume, r ∈ Ioo a R →
      (∫ p : NativeCircle × ℝ, ‖w (c + axisChart B (r • p.1.val, p.2))‖ ∂cylinderSideTraceMeasure lo hi) ≤ ε := by
  let μ := cylinderSideTraceMeasure lo hi
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo lo hi)) := isFiniteMeasure_restrict.mpr
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  letI : IsFiniteMeasure μ := by dsimp only [μ, cylinderSideTraceMeasure]; infer_instance
  let C := (μ univ ^ (1 / 2 : ℝ)).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  let r₁ : Icc (R / 2) R := ⟨R, half_le_self hR.le, le_rfl⟩
  obtain ⟨δ, hδ, hClose⟩ := Metric.continuousAt_iff.mp (P.continuous.continuousAt (x := r₁))
    (ε / (C + 1)) (div_pos hε (by positivity))
  let a := max (R / 2) (R - δ / 2)
  have haR : a < R := max_lt (half_lt_self hR) (by linarith)
  have hHalf : R / 2 ≤ a := le_max_left _ _
  refine ⟨a, ⟨hHalf, haR.le⟩, haR, ?_⟩
  filter_upwards [hP] with r hr hrA
  let hrP : r ∈ Ioo (R / 2) R := ⟨hHalf.trans_lt hrA.1, hrA.2⟩
  let r' : Icc (R / 2) R := ⟨r, hrP.1.le, hrP.2.le⟩
  have hNear : dist r' r₁ < δ := by
    change dist r R < δ
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hrA.2.le)]
    have hLower : R - δ / 2 < r := (le_max_right _ _).trans_lt hrA.1
    linarith
  obtain ⟨hf, hF⟩ := hr hrP
  have hNorm : (eLpNorm (fun p : NativeCircle × ℝ => w (c + axisChart B (r • p.1.val, p.2))) 2 μ).toReal <
      ε / (C + 1) := by
    have hSmall := hClose hNear
    change dist (P r') (P r₁) < _ at hSmall
    rw [show P r₁ = 0 from hZero, dist_zero_right, hF, Lp.norm_toLp] at hSmall
    exact hSmall
  calc
    _ ≤ _ := integral_norm_le_Lp_two_const μ hf
    _ ≤ (ε / (C + 1)) * C := mul_le_mul_of_nonneg_right hNorm.le hC
    _ ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < C + 1)]
      nlinarith only [hε, hC]

/-- The actual physical wall collar between two specified radial levels. -/
@[expose] def translatedAxisCylinderWallCollar (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (a R lo hi : ℝ) : Set Point :=
  translatedAxisCylinder c (B 2) R lo hi ∩ {x | a < ‖(cylinderRecoveryCoordinates B c x).1‖}

private theorem measurePreserving_disk_positive_polar_annulus (a R : ℝ) :
    MeasurePreserving (fun p : NativeCircle × Ioi (0 : ℝ) => p.2.val • p.1.val)
      ((volume : Measure Plane).toSphere.prod ((Measure.volumeIoiPow 1).restrict
        ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Ioo a R)))
      (volume.restrict {y : Plane | ‖y‖ ∈ Ioo a R}) := by
  let X := ({(0 : Plane)}ᶜ : Set Plane)
  let H := homeomorphUnitSphereProd Plane
  have h := (volume : Measure Plane).measurePreserving_homeomorphUnitSphereProd.symm H.toMeasurableEquiv
  have hc := measurePreserving_subtype_coe ((measurableSet_singleton (0 : Plane)).compl)
    (μa := (volume : Measure Plane))
  rw [restrict_compl_singleton] at hc
  have hm : MeasurePreserving (fun p : NativeCircle × Ioi (0 : ℝ) => p.2.val • p.1.val)
      ((volume : Measure Plane).toSphere.prod (Measure.volumeIoiPow 1)) (volume : Measure Plane) := by
    simpa only [H, Function.comp_def, Homeomorph.toMeasurableEquiv_symm_coe,
      homeomorphUnitSphereProd_symm_apply_coe, finrank_euclideanSpace_fin, Nat.reduceSub] using hc.comp h
  have hC : MeasurableSet {y : Plane | ‖y‖ ∈ Ioo a R} := measurableSet_Ioo.preimage continuous_norm.measurable
  have hP : (fun p : NativeCircle × Ioi (0 : ℝ) => p.2.val • p.1.val) ⁻¹' {y : Plane | ‖y‖ ∈ Ioo a R} =
      univ ×ˢ ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Ioo a R) := by
    ext p
    have hNorm : ‖p.2.val • p.1.val‖ = p.2.val := by
      rw [norm_smul, Real.norm_of_nonneg p.2.property.le, mem_sphere_zero_iff_norm.mp p.1.property, mul_one]
    simp only [mem_preimage, mem_setOf_eq, mem_prod, mem_univ, true_and, hNorm]
  have hr := hm.restrict_preimage hC
  rw [hP, ← Measure.prod_restrict, Measure.restrict_univ] at hr
  exact hr

theorem measurePreserving_cylinderWallCollar_polar
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (a R lo hi : ℝ) :
    MeasurePreserving (fun p : (NativeCircle × ℝ) × Ioi (0 : ℝ) =>
      c + axisChart B (p.2.val • p.1.1.val, p.1.2))
      ((cylinderSideTraceMeasure lo hi).prod ((Measure.volumeIoiPow 1).restrict
        ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Ioo a R)))
      (volume.restrict (translatedAxisCylinderWallCollar B c a R lo hi)) := by
  let σ := (volume : Measure Plane).toSphere
  let ν := (volume : Measure ℝ).restrict (Ioo lo hi)
  let C := {y : Plane | ‖y‖ ∈ Ioo a R}
  let J := ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Ioo a R)
  let η := (Measure.volumeIoiPow 1).restrict J
  have hσ : cylinderSideTraceMeasure lo hi = σ.prod ν := rfl
  have hm := measurePreserving_disk_positive_polar_annulus a R
  have hReorder := ((measurePreserving_prodAssoc σ η ν).symm MeasurableEquiv.prodAssoc).comp
    (((MeasurePreserving.id σ).prod (Measure.measurePreserving_swap (μ := ν) (ν := η))).comp
      (measurePreserving_prodAssoc σ ν η))
  let T (p : Plane × ℝ) := c + axisChart B p
  have hT : MeasurePreserving T ((volume : Measure Plane).prod (volume : Measure ℝ)) volume := by
    simpa only [T, Function.comp_def, add_comm c] using
      (measurePreserving_add_left (volume : Measure Point) c).comp (measurePreserving_axisChart B)
  have hC : MeasurableSet (translatedAxisCylinderWallCollar B c a R lo hi) := by
    have hM := (measurePreserving_cylinderRecoveryCoordinates B c R lo hi).measurable
    exact (isOpen_translatedAxisCylinder _ _ _ _ _).measurableSet.inter
      (measurableSet_Ioi.preimage hM.fst.norm)
  have hPre : T ⁻¹' translatedAxisCylinderWallCollar B c a R lo hi = C ×ˢ Ioo lo hi := by
    ext p
    change (T p ∈ translatedAxisCylinder c (B 2) R lo hi ∧ a < ‖(cylinderRecoveryCoordinates B c (T p)).1‖) ↔ _
    rw [mem_translatedAxisCylinder_iff_recoveryCoordinates, cylinderRecoveryCoordinates_axisChart]
    simp only [mem_prod, C, mem_setOf_eq, mem_Ioo, mem_ball_zero_iff]
    tauto
  have hRect := hT.restrict_preimage hC
  rw [hPre, ← Measure.prod_restrict] at hRect
  rw [hσ]
  exact hRect.comp ((hm.prod (MeasurePreserving.id ν)).comp hReorder)

/-- Actual ambient collar integration equals radial integration of the
native wall fibers with the precise cylindrical Jacobian. -/
theorem integral_cylinderWallCollar_eq_polar
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {a R lo hi : ℝ} (ha : 0 < a)
    (f : Point → ℝ) (hf : IntegrableOn f (translatedAxisCylinderWallCollar B c a R lo hi)) :
    let F (r : ℝ) := r * ∫ p : NativeCircle × ℝ, f (c + axisChart B (r • p.1.val, p.2))
      ∂cylinderSideTraceMeasure lo hi
    IntegrableOn F (Ioo a R) ∧
      (∫ x in translatedAxisCylinderWallCollar B c a R lo hi, f x) = ∫ t in Ioo a R, F t := by
  intro F
  let σ := cylinderSideTraceMeasure lo hi
  let P := Ioi (0 : ℝ)
  let J := ((Subtype.val : P → ℝ) ⁻¹' Ioo a R)
  let η := (Measure.volumeIoiPow 1).restrict J
  let G (p : (NativeCircle × ℝ) × P) := f (c + axisChart B (p.2.val • p.1.1.val, p.1.2))
  let g (r : P) := ∫ p : NativeCircle × ℝ, f (c + axisChart B (r.val • p.1.val, p.2)) ∂σ
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo lo hi)) := isFiniteMeasure_restrict.mpr
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  letI : IsFiniteMeasure σ := by dsimp only [σ, cylinderSideTraceMeasure]; infer_instance
  have hM := measurePreserving_cylinderWallCollar_polar B c a R lo hi
  have hG : Integrable G (σ.prod η) := hM.integrable_comp_of_integrable hf
  have hIg : IntegrableOn g J (Measure.volumeIoiPow 1) := hG.integral_prod_right
  have hJ : MeasurableSet J := measurableSet_Ioo.preimage measurable_subtype_coe
  have hρ : Measurable (fun r : P => ENNReal.ofReal (r.val ^ (1 : ℕ))) :=
    (measurable_subtype_coe.pow_const _).ennreal_ofReal
  have hFinite : ∀ᵐ r ∂(volume.comap (Subtype.val : P → ℝ)).restrict J, ENNReal.ofReal (r.val ^ (1 : ℕ)) ≠ ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_ne_top
  have hFrom : Ioo a R ⊆ range (Subtype.val : P → ℝ) := by
    rw [Subtype.range_val]
    exact fun _ h => ha.trans h.1
  have hSub := MeasurableEmbedding.subtype_coe (measurableSet_Ioi (a := (0 : ℝ)))
  have hJacs (r : P) : (ENNReal.ofReal (r.val ^ (1 : ℕ))).toReal • g r = F r.val := by
    rw [pow_one, ENNReal.toReal_ofReal r.property.le, smul_eq_mul]
  have hFI : IntegrableOn F (Ioo a R) := by
    apply (hSub.integrableOn_iff_comap (f := F) (μ := volume) hFrom).mpr
    unfold IntegrableOn at hIg
    rw [Measure.volumeIoiPow, restrict_withDensity hJ,
      integrable_withDensity_iff_integrable_smul' hρ (hFinite.mono fun _ h => lt_top_iff_ne_top.mpr h)] at hIg
    exact hIg.congr (Eventually.of_forall hJacs)
  refine ⟨hFI, ?_⟩
  calc
    _ = ∫ p, G p ∂σ.prod η := by
      rw [← hM.map_eq]
      exact integral_map hM.aemeasurable (hM.map_eq.symm ▸ hf.aestronglyMeasurable)
    _ = ∫ r : P in J, g r ∂Measure.volumeIoiPow 1 := integral_prod_symm _ hG
    _ = _ := by
      rw [Measure.volumeIoiPow, setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hρ.aemeasurable
        (hFinite.mono fun _ h => lt_top_iff_ne_top.mpr h) _ hJ]
      simp_rw [hJacs]
      rw [← hSub.setIntegral_map F (Ioo a R), hSub.map_comap, Subtype.range_val,
        Measure.restrict_restrict_of_subset (show Ioo a R ⊆ Ioi (0 : ℝ) from fun _ h => ha.trans h.1)]

private theorem cylinderSideTraceMeasure_le_sum_of_ae_cover {n : ℕ} {lo hi : ℝ}
    (l h : Fin n → ℝ) (hSub : ∀ i, Ioo (l i) (h i) ⊆ Ioo lo hi)
    (hCover : ∀ᵐ z : ℝ ∂volume.restrict (Ioo lo hi), ∃ i, z ∈ Ioo (l i) (h i)) :
    cylinderSideTraceMeasure lo hi ≤ ∑ i, cylinderSideTraceMeasure (l i) (h i) := by
  let σ := (volume : Measure Plane).toSphere
  let μ (i : Fin n) := (volume : Measure ℝ).restrict (Ioo (l i) (h i))
  letI : ∀ i : Fin n, IsFiniteMeasure (μ i) := fun i =>
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hSet : (⋃ i : Fin n, Ioo (l i) (h i)) =ᵐ[(volume : Measure ℝ)] Ioo lo hi := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hCover] with z hz
    exact propext ⟨fun hz' => by obtain ⟨i, hi⟩ := mem_iUnion.mp hz'; exact hSub i hi,
      fun hz' => by obtain ⟨i, hi⟩ := hz hz'; exact mem_iUnion_of_mem i hi⟩
  have hDom : volume.restrict (Ioo lo hi) ≤ Measure.sum μ := by
    rw [← Measure.restrict_congr_set hSet]
    exact Measure.restrict_iUnion_le
  change σ.prod (volume.restrict (Ioo lo hi)) ≤ ∑ i, σ.prod (μ i)
  calc
    _ ≤ σ.prod (Measure.sum μ) := Measure.prod_mono le_rfl hDom
    _ = _ := by rw [Measure.prod_sum_right, Measure.sum_fintype]

private theorem lateral_integral_norm_small_of_cover {n q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hR : 0 < R)
    (w : Point → Ambient q) (l h : Fin n → ℝ) (hSub : ∀ i, Ioo (l i) (h i) ⊆ Ioo lo hi)
    (hCover : ∀ᵐ z : ℝ ∂volume.restrict (Ioo lo hi), ∃ i, z ∈ Ioo (l i) (h i))
    (T : ∀ i : Fin n, CylinderSideL2Trace q R (l i) (h i))
    (hT : ∀ i, RepresentsCylinderSideL2Trace B c w (T i))
    (hZero : ∀ i, T i ⟨R, half_le_self hR.le, le_rfl⟩ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ Ico (R / 2) R, ∀ᵐ r : ℝ ∂volume, r ∈ Ioo a R →
      (∫ p : NativeCircle × ℝ, ‖w (c + axisChart B (r • p.1.val, p.2))‖ ∂cylinderSideTraceMeasure lo hi) ≤ ε := by
  let η := ε / ((n : ℝ) + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  choose a ha haR haSmall using fun i : Fin n =>
    lateral_integral_norm_small_near_zeroTrace B c hR w (T i) (hT i) (hZero i) hη
  have haAll : ∀ᶠ r in 𝓝[<] R, ∀ i, r ∈ Ioo (a i) R :=
    Filter.eventually_all.2 (fun i => Ioo_mem_nhdsLT (haR i))
  obtain ⟨b, hb, hNear⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset (half_lt_self hR)).mp haAll
  refine ⟨b, hb, ?_⟩
  filter_upwards [ae_all_iff.mpr haSmall, ae_all_iff.mpr hT] with r hrSmall hrT hr
  let f (p : NativeCircle × ℝ) := ‖w (c + axisChart B (r • p.1.val, p.2))‖
  let μ (i : Fin n) := cylinderSideTraceMeasure (l i) (h i)
  letI : ∀ i : Fin n, IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo (l i) (h i))) := fun i =>
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  letI : ∀ i : Fin n, IsFiniteMeasure (μ i) := fun i => by dsimp only [μ, cylinderSideTraceMeasure]; infer_instance
  have hInt (i : Fin n) : Integrable f (μ i) := ((hrT i ⟨hb.1.trans_lt hr.1, hr.2⟩).choose.integrable (by norm_num)).norm
  have hDom := cylinderSideTraceMeasure_le_sum_of_ae_cover l h hSub hCover
  change (∫ p, f p ∂cylinderSideTraceMeasure lo hi) ≤ ε
  calc
    _ ≤ ∫ p, f p ∂(∑ i, μ i) := integral_mono_measure hDom
      (Eventually.of_forall fun _ => norm_nonneg _) (integrable_finsetSum_measure.2 fun i _ => hInt i)
    _ = ∑ i, ∫ p, f p ∂μ i := integral_finsetSum_measure fun i _ => hInt i
    _ ≤ ∑ _ : Fin n, η := Finset.sum_le_sum (fun i _ => hrSmall i (hNear hr i))
    _ ≤ ε := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, η]
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
      nlinarith only [hε]

/-- Matching zero lateral classes on an a.e. height cover force the
original wall-layer `L¹` norm to be arbitrarily small per unit thickness. -/
theorem integral_norm_wallCollar_le_of_zeroTrace_cover {n q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hR : 0 < R)
    (w : Point → Ambient q) (hw : MemLp w 2 (volume.restrict (translatedAxisCylinder c (B 2) R lo hi)))
    (l h : Fin n → ℝ) (hSub : ∀ i, Ioo (l i) (h i) ⊆ Ioo lo hi)
    (hCover : ∀ᵐ z : ℝ ∂volume.restrict (Ioo lo hi), ∃ i, z ∈ Ioo (l i) (h i))
    (T : ∀ i : Fin n, CylinderSideL2Trace q R (l i) (h i))
    (hT : ∀ i, RepresentsCylinderSideL2Trace B c w (T i))
    (hZero : ∀ i, T i ⟨R, half_le_self hR.le, le_rfl⟩ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ Ico (R / 2) R, ∀ r ∈ Ico a R,
      (∫ x in translatedAxisCylinderWallCollar B c r R lo hi, ‖w x‖) ≤ ε * (R - r) := by
  let η := ε / (R + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨a, ha, hNear⟩ := lateral_integral_norm_small_of_cover B c hR w l h hSub hCover T hT hZero hη
  refine ⟨a, ha, ?_⟩
  intro r hr
  have hPos : 0 < r := (half_pos hR).trans_le (ha.1.trans hr.1)
  let U := translatedAxisCylinder c (B 2) R lo hi
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top (isCompact_translatedClosedAxisCylinder (B.orthonormal.norm_eq_one 2) R lo hi).measure_lt_top.ne
      (measure_mono (translatedAxisCylinder_subset_closed _ _ _ _ _)))
  have hW₀ : IntegrableOn (fun x => ‖w x‖) U := (hw.integrable (by norm_num)).norm
  have hW : IntegrableOn (fun x => ‖w x‖) (translatedAxisCylinderWallCollar B c r R lo hi) :=
    hW₀.mono_set inter_subset_left
  obtain ⟨hI, hEq⟩ := integral_cylinderWallCollar_eq_polar B c hPos (fun x => ‖w x‖) hW
  rw [hEq]
  have hAe : ∀ᵐ t ∂volume.restrict (Ioo r R),
      t * (∫ p : NativeCircle × ℝ, ‖w (c + axisChart B (t • p.1.val, p.2))‖
      ∂cylinderSideTraceMeasure lo hi) ≤ ε := by
    filter_upwards [ae_restrict_of_ae hNear, ae_restrict_mem measurableSet_Ioo] with t ht htr
    have hSmall := ht ⟨hr.1.trans_lt htr.1, htr.2⟩
    have hT : 0 ≤ t := hPos.le.trans htr.1.le
    have hMul := mul_le_mul htr.2.le hSmall (integral_nonneg fun _ => norm_nonneg _) hR.le
    refine hMul.trans ?_
    dsimp only [η]
    rw [← mul_div_assoc, div_le_iff₀ (by linarith : 0 < R + 1)]
    nlinarith only [hε]
  have hUpper := integral_mono_ae hI (integrable_const ε) hAe
  exact hUpper.trans_eq (by
    rw [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioo,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hr.2.le), smul_eq_mul, mul_comm])

end Thesis.MeasureGeometry

end
