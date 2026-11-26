module

public import Thesis.Interpolation.CylinderTraceBoundaryCollars
import Thesis.Interpolation.AbsolutelyContinuousTest
import Thesis.Interpolation.FiniteL2TraceEstimate
import Thesis.Interpolation.LipschitzSobolevPullback
import Thesis.MeasureGeometry.CylinderRescaling
import HarmonicMaps.Analysis.RadialIntegrability
import Mathlib.Analysis.Calculus.Rademacher

/-! Native unweighted cylinder wall coordinates and Lipschitz Sobolev traces. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ContDiff ENNReal NNReal Topology

namespace Thesis.MeasureGeometry

private theorem unweighted_positive_radial_collar_le {a R : ℝ} (ha : 0 < a) :
    let J := (Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Ioo a R
    (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)).restrict J ≤
      ENNReal.ofReal a⁻¹ • (Measure.volumeIoiPow 1).restrict J := by
  intro J
  let ν := (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)).restrict J
  have hJ : MeasurableSet J := measurableSet_Ioo.preimage measurable_subtype_coe
  change ν ≤ ENNReal.ofReal a⁻¹ •
    ((volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)).withDensity
      (fun r => ENNReal.ofReal (r.val ^ (1 : ℕ)))).restrict J
  rw [restrict_withDensity hJ, ← withDensity_smul]
  · conv_lhs => rw [← withDensity_one (μ := ν)]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hJ] with r hr
    change 1 ≤ ENNReal.ofReal a⁻¹ * ENNReal.ofReal (r.val ^ (1 : ℕ))
    rw [pow_one, ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)]
    exact ENNReal.one_le_ofReal.mpr ((le_inv_mul_iff₀ ha).2 (by simpa only [mul_one] using hr.1.le))
  · exact (measurable_subtype_coe.pow_const _).ennreal_ofReal

/-- The actual unweighted radial cylinder coordinates have volume distortion
at most the reciprocal inner radius. -/
theorem map_cylinderWallCollar_unweighted_le
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {a R lo hi : ℝ} (ha : 0 < a) :
    Measure.map (fun z : (NativeCircle × ℝ) × ℝ => c + axisChart B (z.2 • z.1.1.val, z.1.2))
        ((cylinderSideTraceMeasure lo hi).prod (volume.restrict (Icc a R))) ≤
      ENNReal.ofReal a⁻¹ • volume.restrict (translatedAxisCylinderWallCollar B c a R lo hi) := by
  let σ := cylinderSideTraceMeasure lo hi
  let P := Ioi (0 : ℝ)
  let J := (Subtype.val : P → ℝ) ⁻¹' Ioo a R
  let ν := (volume.comap (Subtype.val : P → ℝ)).restrict J
  let η := (Measure.volumeIoiPow 1).restrict J
  let f (z : (NativeCircle × ℝ) × ℝ) := c + axisChart B (z.2 • z.1.1.val, z.1.2)
  let g := Prod.map (id : NativeCircle × ℝ → NativeCircle × ℝ) (Subtype.val : P → ℝ)
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo lo hi)) := isFiniteMeasure_restrict.mpr
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  letI : IsFiniteMeasure σ := by dsimp only [σ, cylinderSideTraceMeasure]; infer_instance
  have hBot : MeasurePreserving (Subtype.val : P → ℝ) ν (volume.restrict (Ioo a R)) := by
    have h := (measurePreserving_subtype_coe (measurableSet_Ioi (a := (0 : ℝ)))
      (μa := (volume : Measure ℝ))).restrict_preimage (measurableSet_Ioo (a := a) (b := R))
    rwa [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr (show Ioo a R ⊆ Ioi (0 : ℝ) from
      fun _ h => ha.trans h.1)] at h
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo a R)) := isFiniteMeasure_restrict.mpr
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  letI : SigmaFinite ν := hBot.sigmaFinite
  have hG : MeasurePreserving g (σ.prod ν) (σ.prod (volume.restrict (Ioo a R))) :=
    (MeasurePreserving.id σ).prod hBot
  have hF : Measurable f := by
    have hSide : Continuous (fun z : (NativeCircle × ℝ) × ℝ => (z.2 • z.1.1.val, z.1.2)) := by fun_prop
    exact (continuous_const.add ((continuous_axisChart B).comp hSide)).measurable
  have hMP := measurePreserving_cylinderWallCollar_polar B c a R lo hi
  change Measure.map f (σ.prod (volume.restrict (Icc a R))) ≤ _
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc, ← hG.map_eq, Measure.map_map hF hG.measurable]
  have hD : σ.prod ν ≤ ENNReal.ofReal a⁻¹ • (σ.prod η) := by
    rw [← Measure.prod_smul_right]
    exact Measure.prod_mono le_rfl (unweighted_positive_radial_collar_le ha)
  have hMapEq : Measure.map (f ∘ g) (σ.prod η) = volume.restrict (translatedAxisCylinderWallCollar B c a R lo hi) :=
    hMP.map_eq
  exact (Measure.map_mono hD (hF.comp hG.measurable)).trans_eq (by rw [Measure.map_smul, hMapEq])

/-- A square-integrable cylinder field has the actual unweighted radial
product data and the corresponding squared-norm estimate. -/
theorem memLp_cylinderWallCollar_radial_product {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {a R lo hi : ℝ} (ha : 0 < a)
    {w : Point → Ambient q} (hw : MemLp w 2 (volume.restrict (translatedAxisCylinder c (B 2) R lo hi))) :
    let μ := (cylinderSideTraceMeasure lo hi).prod (volume.restrict (Icc a R))
    let f (p : (NativeCircle × ℝ) × ℝ) := w (c + axisChart B (p.2 • p.1.1.val, p.1.2))
    MemLp f 2 μ ∧ (∫ p, ‖f p‖ ^ 2 ∂μ) ≤ a⁻¹ * ∫ x in translatedAxisCylinder c (B 2) R lo hi, ‖w x‖ ^ 2 := by
  intro μ f
  let T (p : (NativeCircle × ℝ) × ℝ) := c + axisChart B (p.2 • p.1.1.val, p.1.2)
  have hT : Measurable T := by
    have hSide : Continuous (fun z : (NativeCircle × ℝ) × ℝ => (z.2 • z.1.1.val, z.1.2)) := by fun_prop
    exact (continuous_const.add ((continuous_axisChart B).comp hSide)).measurable
  let U := translatedAxisCylinder c (B 2) R lo hi
  let ν := (volume : Measure Point).restrict U
  have hDom : Measure.map T μ ≤ ENNReal.ofReal a⁻¹ • ν := by
    apply (map_cylinderWallCollar_unweighted_le B c ha).trans
    apply Measure.le_iff'.mpr
    intro s
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right ((Measure.restrict_mono_set volume inter_subset_left) s) _
  have hF : MemLp f 2 μ := memLp_comp_of_map_le_smul hT.aemeasurable ENNReal.ofReal_ne_top hDom hw
  refine ⟨hF, ?_⟩
  let g (x : Point) := ‖w x‖ ^ 2
  have hg : Integrable g ν := hw.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hg' : Integrable g (ENNReal.ofReal a⁻¹ • ν) := hg.smul_measure ENNReal.ofReal_ne_top
  calc
    _ = ∫ x, g x ∂Measure.map T μ := (integral_map hT.aemeasurable (hg'.mono_measure hDom).aestronglyMeasurable).symm
    _ ≤ ∫ x, g x ∂(ENNReal.ofReal a⁻¹ • ν) := integral_mono_measure hDom (Eventually.of_forall fun _ => sq_nonneg _) hg'
    _ = _ := by rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le), smul_eq_mul]

private theorem physical_radial_wall_ray (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (p : NativeCircle × ℝ) (r : ℝ) :
    c + axisChart B (r • p.1.val, p.2) = (c + p.2 • B 2) + r • axisChartPlane B p.1.val := by
  rw [axisChart_eq_plane_add_axis, map_smul]
  abel

private theorem memLp_radial_wall_direction_coordinate (B : OrthonormalBasis (Fin 3) ℝ Point)
    (i : Fin 3) (μ : Measure ((NativeCircle × ℝ) × ℝ)) :
    MemLp (fun p : (NativeCircle × ℝ) × ℝ => axisChartPlane B p.1.1.val i) ⊤ μ := by
  have hC : Continuous (fun p : (NativeCircle × ℝ) × ℝ => axisChartPlane B p.1.1.val i) :=
    (EuclideanSpace.proj i).continuous.comp ((axisChartPlane B).continuous.comp
      (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)))
  apply memLp_top_of_bound hC.measurable.aestronglyMeasurable 1
  exact ae_of_all _ (fun p => (PiLp.norm_apply_le (axisChartPlane B p.1.1.val) i).trans_eq
    ((norm_axisChartPlane B p.1.1.val).trans (mem_sphere_zero_iff_norm.mp p.1.1.property)))

private theorem cylinder_radial_lipschitz_weak {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {a R lo hi : ℝ} (ha : 0 < a) (haR : a < R)
    (w : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q)
    {L : ℝ≥0} (hLip : LipschitzWith L w)
    (hw : MemW12 (translatedAxisCylinderDomain B c R lo hi) w D)
    (F G : (NativeCircle × ℝ) × ℝ → Ambient q)
    (hF : ∀ p : (NativeCircle × ℝ) × ℝ, F p = w (c + axisChart B (p.2 • p.1.1.val, p.1.2)))
    (hG : ∀ p : (NativeCircle × ℝ) × ℝ, G p = ∑ i : Fin 3, axisChartPlane B p.1.1.val i •
      D (c + axisChart B (p.2 • p.1.1.val, p.1.2)) i)
    (hFL : MemLp F 2 ((cylinderSideTraceMeasure lo hi).prod (volume.restrict (Icc a R))))
    (hGL : MemLp G 2 ((cylinderSideTraceMeasure lo hi).prod (volume.restrict (Icc a R)))) :
    ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a R →
      ∀ᵐ p ∂cylinderSideTraceMeasure lo hi,
        (∫ t in Icc a R, deriv φ t • F (p, t)) = -(∫ t in Icc a R, φ t • G (p, t)) := by
  let U := translatedAxisCylinderDomain B c R lo hi
  let σ := cylinderSideTraceMeasure lo hi
  let ν := (volume : Measure ℝ).restrict (Icc a R)
  let νO := (volume : Measure ℝ).restrict (Ioo a R)
  let Z (p : (NativeCircle × ℝ) × ℝ) := c + axisChart B (p.2 • p.1.1.val, p.1.2)
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo lo hi)) := isFiniteMeasure_restrict.mpr
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  letI : IsFiniteMeasure σ := by dsimp only [σ, cylinderSideTraceMeasure]; infer_instance
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hν : νO = ν := Measure.restrict_congr_set Ioo_ae_eq_Icc
  have hM := map_cylinderWallCollar_unweighted_le B c (R := R) (lo := lo) (hi := hi) ha
  have hAC : Measure.map Z (σ.prod ν) ≪ (volume : Measure Point).restrict U.val :=
    (Measure.absolutelyContinuous_of_le_smul hM).trans
      (Measure.restrict_mono_set volume inter_subset_left).absolutelyContinuous
  have hZC : Continuous Z := by
    have hSide : Continuous (fun z : (NativeCircle × ℝ) × ℝ => (z.2 • z.1.1.val, z.1.2)) := by fun_prop
    exact continuous_const.add ((continuous_axisChart B).comp hSide)
  have hZ : Measure.QuasiMeasurePreserving Z (σ.prod ν) (volume.restrict U.val) := ⟨hZC.measurable, hAC⟩
  have hDiff : ∀ᵐ x ∂volume.restrict U.val, DifferentiableAt ℝ w x :=
    ae_restrict_of_ae (hLip.ae_differentiableAt (μ := (volume : Measure Point)))
  have hCols : D =ᵐ[volume.restrict U.val] (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) :=
    hw.1.ae_eq_of_ae_eq_map (hasWeakGradient_of_lipschitz U hLip) EventuallyEq.rfl
  have hDeriv : ∀ᵐ p ∂σ, (deriv (fun t => F (p, t))) =ᵐ[ν] (fun t => G (p, t)) := by
    filter_upwards [Measure.ae_ae_of_ae_prod (hZ.ae (hDiff.and hCols))] with p hp
    filter_upwards [hp] with t ht
    let v := axisChartPlane B p.1.val
    have hLine : HasDerivAt (fun s => Z (p, s)) v t := by
      have hRay : (fun s => Z (p, s)) = fun s => (c + p.2 • B 2) + s • v :=
        funext (physical_radial_wall_ray B c p)
      rw [hRay]
      simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_add (c + p.2 • B 2)
    have hDiffAt := ht.1.hasFDerivAt.comp_hasDerivAt t hLine
    have hFun : (fun s => F (p, s)) = w ∘ (fun s => Z (p, s)) := funext fun s => hF (p, s)
    rw [hFun, hDiffAt.deriv, hG]
    have hSum : (∑ i : Fin 3, v i • EuclideanSpace.single i 1) = v := by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
    change fderiv ℝ w (Z (p, t)) v = ∑ i : Fin 3, v i • D (Z (p, t)) i
    rw [show D (Z (p, t)) = _ from ht.2]
    conv_lhs => rw [← hSum, map_sum]
    simp only [map_smul]
  intro φ hφ hc hs
  have hFInt := (hFL.integrable (by norm_num)).prod_right_ae
  have hGInt := (hGL.integrable (by norm_num)).prod_right_ae
  filter_upwards [hDeriv, hFInt, hGInt] with p hp hpF hpG
  let f (t : ℝ) := F (p, t)
  let v := axisChartPlane B p.1.val
  have hRayLip : LipschitzWith 1 (fun t => Z (p, t)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (Z (p, x)) (Z (p, y)) ≤ _
    have hRay (s : ℝ) : Z (p, s) = (c + p.2 • B 2) + s • v := physical_radial_wall_ray B c p s
    rw [hRay, hRay, dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, norm_axisChartPlane,
      mem_sphere_zero_iff_norm.mp p.1.property, mul_one, NNReal.coe_one, one_mul, dist_eq_norm]
  have hFLip : LipschitzWith L f := by
    rw [show f = w ∘ (fun t => Z (p, t)) from funext fun t => hF (p, t)]
    simpa only [mul_one] using hLip.comp hRayLip
  have hφ₁ : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hEnd : φ a • f a = φ R • f R := by
    have hL : φ a = 0 := image_eq_zero_of_notMem_tsupport (fun h => lt_irrefl _ (hs h).1)
    have hR : φ R = 0 := image_eq_zero_of_notMem_tsupport (fun h => lt_irrefl _ (hs h).2)
    rw [hL, hR, zero_smul, zero_smul]
  obtain ⟨_, hIBP⟩ := absolutelyContinuous_integral_parts haR
    hFLip.lipschitzOnWith.absolutelyContinuousOnInterval hφ₁ hEnd
  have hφL : MemLp φ ⊤ ν := hφ.continuous.memLp_top_of_hasCompactSupport hc ν
  have hdφL : MemLp (deriv φ) ⊤ ν := (hφ.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport hc.deriv ν
  have hFI : Integrable (fun t => deriv φ t • F (p, t)) ν := hpF.smul_of_top_right hdφL
  have hGI : Integrable (fun t => φ t • G (p, t)) ν := hpG.smul_of_top_right hφL
  have hEq : (fun t => deriv φ t • f t + φ t • deriv f t) =ᵐ[νO]
      fun t => deriv φ t • F (p, t) + φ t • G (p, t) := by
    rw [hν]
    filter_upwards [hp] with t ht
    change deriv φ t • f t + φ t • deriv f t = deriv φ t • f t + φ t • G (p, t)
    rw [ht]
  change (∫ t, deriv φ t • f t + φ t • deriv f t ∂νO) = 0 at hIBP
  rw [integral_congr_ae hEq, hν, integral_add hFI hGI] at hIBP
  exact eq_neg_of_add_eq_zero_left hIBP

/-- The genuine radial trace of a Lipschitz cylinder graph is uniformly
controlled at every original radius, with the same physical weak columns. -/
theorem exists_cylinderSide_trace_with_estimate_of_lipschitz {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hR : 0 < R)
    (w : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q) {L : ℝ≥0} (hLip : LipschitzWith L w)
    (hw : MemW12 (translatedAxisCylinderDomain B c R lo hi) w D) :
    ∃ H : CylinderSideL2Trace q R lo hi, RepresentsCylinderSideL2Trace B c w H ∧
      ∀ t : Icc (R / 2) R, ‖H t‖ ^ 2 ≤
        (2 / (R - R / 2)) * ((R / 2)⁻¹ * ∫ x in translatedAxisCylinder c (B 2) R lo hi, ‖w x‖ ^ 2) +
          2 * (R - R / 2) * ((R / 2)⁻¹ * ∫ x in translatedAxisCylinder c (B 2) R lo hi, hsNormSq (D x)) := by
  let a := R / 2
  let σ := cylinderSideTraceMeasure lo hi
  let μ := σ.prod (volume.restrict (Icc a R))
  let T (p : (NativeCircle × ℝ) × ℝ) := c + axisChart B (p.2 • p.1.1.val, p.1.2)
  let F := w ∘ T
  let G (p : (NativeCircle × ℝ) × ℝ) := ∑ i : Fin 3, axisChartPlane B p.1.1.val i • D (T p) i
  have ha : 0 < a := half_pos hR
  have haR : a < R := half_lt_self hR
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo lo hi)) := isFiniteMeasure_restrict.mpr
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  letI : IsFiniteMeasure σ := by dsimp only [σ, cylinderSideTraceMeasure]; infer_instance
  letI : MeasurableSpace.CountablyGenerated (NativeCircle × ℝ) := BorelSpace.countablyGenerated
  letI : IsSeparable σ := inferInstance
  obtain ⟨hF, hFBound⟩ := memLp_cylinderWallCollar_radial_product B c ha hw.2.1
  have hD (i : Fin 3) := memLp_cylinderWallCollar_radial_product B c ha (hw.2.2 i)
  have hG : MemLp G 2 μ := by
    have h := memLp_finsetSum Finset.univ (fun i (_ : i ∈ Finset.univ) =>
      ((hD i).1).smul (r := 2) (memLp_radial_wall_direction_coordinate B i μ))
    simpa only [G, T, Finset.sum_apply, Pi.smul_apply'] using h
  have hInt (i : Fin 3) : Integrable (fun p => ‖D (T p) i‖ ^ 2) μ :=
    (hD i).1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hPoint (p : (NativeCircle × ℝ) × ℝ) : ‖G p‖ ^ 2 ≤ hsNormSq (D (T p)) := by
    have h := norm_sq_sum_gradient_le (D (T p)) (axisChartPlane B p.1.1.val)
    rw [norm_axisChartPlane, mem_sphere_zero_iff_norm.mp p.1.1.property, one_pow, one_mul] at h
    exact h
  let U := translatedAxisCylinder c (B 2) R lo hi
  have hGradBound : (∫ p, ‖G p‖ ^ 2 ∂μ) ≤ a⁻¹ * ∫ x in U, hsNormSq (D x) := by
    calc
      _ ≤ ∫ p, ∑ i : Fin 3, ‖D (T p) i‖ ^ 2 ∂μ := integral_mono
        (hG.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)) (integrable_finsetSum _ (fun i _ => hInt i)) hPoint
      _ = ∑ i : Fin 3, ∫ p, ‖D (T p) i‖ ^ 2 ∂μ := integral_finsetSum _ (fun i _ => hInt i)
      _ ≤ ∑ i : Fin 3, a⁻¹ * ∫ x in U, ‖D x i‖ ^ 2 := Finset.sum_le_sum (fun i _ => (hD i).2)
      _ = _ := by
        have hUi (i : Fin 3) : IntegrableOn (fun x => ‖D x i‖ ^ 2) U :=
          (hw.2.2 i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
        rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => hUi i)]
        rfl
  have hWeak := cylinder_radial_lipschitz_weak B c ha haR w D hLip hw F G (fun _ => rfl) (fun _ => rfl) hF hG
  obtain ⟨H, hH, hBound⟩ := exists_finite_L2_trace_with_endpoint_estimate σ haR hF hG hWeak
  refine ⟨H, hH, fun t => (hBound t).trans ?_⟩
  exact add_le_add (mul_le_mul_of_nonneg_left hFBound (by positivity [sub_pos.mpr haR]))
    (mul_le_mul_of_nonneg_left hGradBound (by linarith only [haR]))

end Thesis.MeasureGeometry

end
