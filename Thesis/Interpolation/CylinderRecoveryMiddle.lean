module

public import Thesis.Interpolation.CylinderRecoveryBand
public import Thesis.Interpolation.CylinderRecoveryCompetitor

/-! One fixed planar recovery core and its original side collar, usable
at every selected horizontal height in the regular band. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

/-- Data for the actual middle recovery. The same side, core, and
constants are used for the whole band and every selected height interval. -/
structure CylinderRecoveryMiddleData (a : BulkCoefficients) (ε : ElasticScale)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (r s : ℝ)
    (p : C(NativeCircle, vacuum a)) (W Ref : Point → S0) (V : Set Point) (C₀ C M : ℝ) where
  core : Plane → Ambient 5
  coreDerivative : Plane → HarmonicMaps.Gradient 2 5
  core_memW12 : MemW12 (ballDomain (0 : Plane) (r / 2)) core coreDerivative
  core_range : ∀ᵐ y ∂volume.restrict (ball (0 : Plane) (r / 2)), ‖core y‖ ≤ Real.sqrt 2 * vacuumRadius a
  core_collar : ∀ ρ ≥ (7 / 16 : ℝ) * r, ∀ θ : NativeCircle,
    core (ρ • θ.val) = frobeniusCoordinateEquiv (p θ).val
  core_bulk : IntegrableOn (fun y => planarCoordinateBulkPotential a (core y)) (ball (0 : Plane) (r / 2))
  core_cost : planarWeakEnergy a (ε : ℝ) core coreDerivative (r / 2) ≤
    nativeVacuumCircleCost a p * Real.log ((r / 2) / (ε : ℝ)) + C₀
  side_smooth : ContDiffOn ℝ ∞ W V
  side_range : ∀ x ∈ cylinderRecoveryBand B c r s, ‖W x‖ ≤ max M (Real.sqrt 2 * vacuumRadius a)
  side_cost : ∀ x ∈ cylinderRecoveryBand B c r s, energyDensity a ε (W x) (ClassicalGradient W x) ≤ C
  side_inner : ∀ x ∈ cylinderRecoveryBand B c r s, ‖(axisCoordinates B c x).1‖ ≤ (5 / 8 : ℝ) * r →
    W x = (p (sphereRadialDirection nativeCircleLoopBase (axisCoordinates B c x).1)).val
  side_outer : ∀ x ∈ cylinderRecoveryBand B c r s, ‖(axisCoordinates B c x).1‖ = r → W x = Ref x
  slice_range : ∀ z ∈ Icc (-s) s, ∀ᵐ y ∂volume.restrict (ball (0 : Plane) r),
    ‖cylinderMiddleSlice B c r core W z y‖ ≤ max M (Real.sqrt 2 * vacuumRadius a)
  slice : ∀ z ∈ Icc (-s) s, ∃ E : Plane → HarmonicMaps.Gradient 2 5,
    MemW12 (ballDomain (0 : Plane) r) (cylinderMiddleSlice B c r core W z) E ∧
    planarWeakEnergy a (ε : ℝ) (cylinderMiddleSlice B c r core W z) E r ≤
      planarWeakEnergy a (ε : ℝ) core coreDerivative (r / 2) + C * (volume (ball (0 : Plane) r)).toReal
  volume : ∀ {lo hi : ℝ}, -s ≤ lo → lo < hi → hi ≤ s →
    MemH1 (translatedAxisCylinder c (B 2) r lo hi) (cylinderMiddleField B c r core W)
      (cylinderMiddleGradient B c r coreDerivative W) ∧
    energy a ε (translatedAxisCylinder c (B 2) r lo hi) (cylinderMiddleField B c r core W)
      (cylinderMiddleGradient B c r coreDerivative W) ≤
        ENNReal.ofReal ((hi - lo) * planarWeakEnergy a (ε : ℝ) core coreDerivative (r / 2)) +
          ENNReal.ofReal (C * (volume (cylinderRecoveryBand B c r s)).toReal)
  traces : ∀ {lo hi : ℝ}, -s ≤ lo → lo < hi → hi ≤ s →
    ∃ (P : CylinderHeightL2Trace 5 r lo hi) (Q : CylinderSideL2Trace 5 r lo hi),
      RepresentsCylinderHeightL2Trace B c (frobeniusField (cylinderMiddleField B c r core W)) P ∧
      RepresentsCylinderSideL2Trace B c (frobeniusField (cylinderMiddleField B c r core W)) Q ∧
      (∀ t, (P t : Plane → Ambient 5) =ᵐ[(MeasureTheory.volume : Measure Plane).restrict (ball (0 : Plane) r)]
        cylinderMiddleSlice B c r core W t.val) ∧
      (∀ t : Icc (r / 2) r, t.val = r →
        (Q t : NativeCircle × ℝ → Ambient 5) =ᵐ[cylinderSideTraceMeasure lo hi]
        fun η => frobeniusField Ref (c + axisChart B (r • η.1.val, η.2)))

abbrev CylinderRecoveryMiddleData.field {a : BulkCoefficients} {ε : ElasticScale}
    {B : OrthonormalBasis (Fin 3) ℝ Point} {c : Point} {r s : ℝ}
    {p : C(NativeCircle, vacuum a)} {W Ref : Point → S0} {V : Set Point} {C₀ C M : ℝ}
    (G : CylinderRecoveryMiddleData a ε B c r s p W Ref V C₀ C M) : Point → S0 :=
  cylinderMiddleField B c r G.core W

abbrev CylinderRecoveryMiddleData.gradient {a : BulkCoefficients} {ε : ElasticScale}
    {B : OrthonormalBasis (Fin 3) ℝ Point} {c : Point} {r s : ℝ}
    {p : C(NativeCircle, vacuum a)} {W Ref : Point → S0} {V : Set Point} {C₀ C M : ℝ}
    (G : CylinderRecoveryMiddleData a ε B c r s p W Ref V C₀ C M) : Point → Thesis.Gradient :=
  cylinderMiddleGradient B c r G.coreDerivative W

/-- The middle slice retains the actual smooth side on its entire
closed outer collar. -/
theorem CylinderRecoveryMiddleData.slice_continuousOn_collar {a : BulkCoefficients} {ε : ElasticScale}
    {B : OrthonormalBasis (Fin 3) ℝ Point} {c : Point} {r s : ℝ}
    {p : C(NativeCircle, vacuum a)} {W Ref : Point → S0} {V : Set Point} {C₀ C M : ℝ}
    (G : CylinderRecoveryMiddleData a ε B c r s p W Ref V C₀ C M)
    (hr : 0 < r) (hCV : cylinderRecoveryBand B c r s ⊆ V) {z : ℝ} (hz : z ∈ Icc (-s) s) :
    ContinuousOn (cylinderMiddleSlice B c r G.core W z) (closedPlanarRadialCollar (r / 2) r) := by
  let F (y : Plane) := c + axisChart B (y, z)
  have hF : Continuous F := continuous_const.add
    ((continuous_axisChart B).comp (continuous_id.prodMk continuous_const))
  have hMap : MapsTo F (closedPlanarRadialCollar (r / 2) r) V := by
    intro y hy
    exact hCV (axisChart_mem_cylinderRecoveryBand B c
      ((show r / 4 ≤ r / 2 by linarith only [hr]).trans hy.1) hy.2 hz)
  have hC : ContinuousOn (fun y => frobeniusField W (F y)) (closedPlanarRadialCollar (r / 2) r) :=
    (frobeniusCoordinateEquiv.continuous.comp_continuousOn G.side_smooth.continuousOn).comp hF.continuousOn hMap
  apply hC.congr
  intro y hy
  simp only [cylinderMiddleSlice, if_neg (not_lt_of_ge hy.1), cylinderSliceMap, frobeniusField, F]

/-- The actual outer rim of a middle slice is the original reference wall. -/
theorem CylinderRecoveryMiddleData.slice_rim_eq_ref {a : BulkCoefficients} {ε : ElasticScale}
    {B : OrthonormalBasis (Fin 3) ℝ Point} {c : Point} {r s : ℝ}
    {p : C(NativeCircle, vacuum a)} {W Ref : Point → S0} {V : Set Point} {C₀ C M : ℝ}
    (G : CylinderRecoveryMiddleData a ε B c r s p W Ref V C₀ C M)
    (hr : 0 < r) {z : ℝ} (hz : z ∈ Icc (-s) s) (θ : NativeCircle) :
    cylinderMiddleSlice B c r G.core W z (r • θ.val) =
      frobeniusField Ref (c + axisChart B (r • θ.val, z)) := by
  have hRad : ‖r • θ.val‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr.le, mem_sphere_zero_iff_norm.1 θ.property, mul_one]
  have hK : c + axisChart B (r • θ.val, z) ∈ cylinderRecoveryBand B c r s := by
    apply axisChart_mem_cylinderRecoveryBand B c
    · rw [hRad]; linarith only [hr]
    · rw [hRad]
    · exact hz
  have hW := G.side_outer _ hK (by rw [axisCoordinates_axisChart, hRad])
  have hN : ¬ r < r / 2 := not_lt_of_ge (half_le_self hr.le)
  rw [cylinderMiddleSlice, hRad, if_neg hN, cylinderSliceMap, hW]

private theorem exists_cylinderMiddle_radialTrace (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {r s lo hi : ℝ} (hr : 0 < r) (hlo : -s ≤ lo) (hhi : hi ≤ s)
    (u : Plane → Ambient 5) {W Ref : Point → S0} {V : Set Point}
    (hW : ContDiffOn ℝ ∞ W V) (hAV : cylinderRecoveryBand B c r s ⊆ V)
    (hOut : ∀ x ∈ cylinderRecoveryBand B c r s, ‖(axisCoordinates B c x).1‖ = r → W x = Ref x) :
    ∃ Q : CylinderSideL2Trace 5 r lo hi,
      RepresentsCylinderSideL2Trace B c (frobeniusField (cylinderMiddleField B c r u W)) Q ∧
      ∀ t : Icc (r / 2) r, t.val = r →
        (Q t : NativeCircle × ℝ → Ambient 5) =ᵐ[cylinderSideTraceMeasure lo hi]
          fun η => frobeniusField Ref (c + axisChart B (r • η.1.val, η.2)) := by
  let f (q : (NativeCircle × ℝ) × ℝ) := frobeniusField W (c + axisChart B (q.2 • q.1.1.val, q.1.2))
  let F (q : (NativeCircle × ℝ) × ℝ) := c + axisChart B (q.2 • q.1.1.val, q.1.2)
  have hF : Continuous F :=
    continuous_const.add ((continuous_axisChart B).comp
      ((continuous_snd.smul (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))).prodMk
        (continuous_snd.comp continuous_fst)))
  have hFC : MapsTo F (cylinderSideParameterCollar r lo hi) (cylinderRecoveryBand B c r s) := by
    intro q hq
    have hθ := mem_sphere_zero_iff_norm.1 q.1.1.property
    have hT : 0 ≤ q.2 := (half_pos hr).le.trans hq.2.1
    have hρ : ‖q.2 • q.1.1.val‖ = q.2 := by rw [norm_smul, Real.norm_of_nonneg hT, hθ, mul_one]
    apply axisChart_mem_cylinderRecoveryBand B c
    · rw [hρ]
      exact (show r / 4 ≤ r / 2 by linarith only [hr]).trans hq.2.1
    · rw [hρ]
      exact hq.2.2
    · exact ⟨hlo.trans hq.1.2.1, hq.1.2.2.trans hhi⟩
  have hf : ContinuousOn f (cylinderSideParameterCollar r lo hi) :=
    (frobeniusCoordinateEquiv.continuous.comp_continuousOn hW.continuousOn).comp hF.continuousOn
      (fun x hx => hAV (hFC hx))
  have hRaw (θ : NativeCircle) (z : ℝ) (_hz : z ∈ Ioo lo hi) (t : ℝ) (ht : t ∈ Ioo (r / 2) r) :
      f ((θ, z), t) = frobeniusField (cylinderMiddleField B c r u W) (c + axisChart B (t • θ.val, z)) := by
    have hN : ‖t • θ.val‖ = t := by
      rw [norm_smul, Real.norm_of_nonneg ((half_pos hr).trans ht.1).le, mem_sphere_zero_iff_norm.1 θ.property, mul_one]
    have hNot : ¬ ‖t • θ.val‖ < r / 2 := by rw [hN]; exact not_lt_of_ge ht.1.le
    change _ = frobeniusCoordinateEquiv (cylinderMiddleField B c r u W (c + axisChart B (t • θ.val, z)))
    rw [frobenius_cylinderMiddleField_axisChart]
    simp only [f, cylinderMiddleSlice, hNot, if_false, cylinderSliceMap, frobeniusField]
  obtain ⟨Q, hQ, hRawQ⟩ := exists_cylinderSideTrace_of_continuousOn_parameterCollar B c hr
    (frobeniusField (cylinderMiddleField B c r u W)) f hf hRaw
  refine ⟨Q, hQ, fun t ht => (hRawQ t).trans ?_⟩
  filter_upwards [ae_cylinderSideTraceMeasure_height_mem lo hi] with η hη
  rw [ht]
  have hρ : ‖r • η.1.val‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr.le, mem_sphere_zero_iff_norm.1 η.1.property, mul_one]
  have hx : c + axisChart B (r • η.1.val, η.2) ∈ cylinderRecoveryBand B c r s := by
    apply axisChart_mem_cylinderRecoveryBand B c
    · rw [hρ]; linarith only [hr]
    · rw [hρ]
    · exact ⟨hlo.trans hη.1.le, hη.2.le.trans hhi⟩
  exact congrArg frobeniusCoordinateEquiv (hOut _ hx (by rw [axisCoordinates_axisChart, hρ]))

/-- A given planar core and regular side produce all the native middle
graphs and traces without selecting any new height or changing fields. -/
theorem cylinderRecoveryMiddleData_of_core_side (a : BulkCoefficients) (ε : ElasticScale)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {r s : ℝ} (hr : 0 < r)
    (p : C(NativeCircle, vacuum a)) (u : Plane → Ambient 5) (Du : Plane → HarmonicMaps.Gradient 2 5)
    (hu : MemW12 (ballDomain (0 : Plane) (r / 2)) u Du)
    (huB : ∀ᵐ y ∂volume.restrict (ball (0 : Plane) (r / 2)), ‖u y‖ ≤ Real.sqrt 2 * vacuumRadius a)
    (hCore : ∀ ρ ≥ (7 / 16 : ℝ) * r, ∀ θ : NativeCircle, u (ρ • θ.val) = frobeniusCoordinateEquiv (p θ).val)
    {C₀ C M : ℝ} (hCost : planarWeakEnergy a (ε : ℝ) u Du (r / 2) ≤
      nativeVacuumCircleCost a p * Real.log ((r / 2) / (ε : ℝ)) + C₀)
    {W Ref : Point → S0} {V : Set Point} (hV : IsOpen V) (hCV : cylinderRecoveryBand B c r s ⊆ V)
    (hW : ContDiffOn ℝ ∞ W V)
    (hSideRange : ∀ x ∈ cylinderRecoveryBand B c r s, ‖W x‖ ≤ max M (Real.sqrt 2 * vacuumRadius a))
    (hSideCost : ∀ x ∈ cylinderRecoveryBand B c r s, energyDensity a ε (W x) (ClassicalGradient W x) ≤ C)
    (hInner : ∀ x ∈ cylinderRecoveryBand B c r s, ‖(axisCoordinates B c x).1‖ ≤ (5 / 8 : ℝ) * r →
      W x = (p (sphereRadialDirection nativeCircleLoopBase (axisCoordinates B c x).1)).val)
    (hOuter : ∀ x ∈ cylinderRecoveryBand B c r s, ‖(axisCoordinates B c x).1‖ = r → W x = Ref x) :
    ∃ G : CylinderRecoveryMiddleData a ε B c r s p W Ref V C₀ C M,
      G.core = u ∧ G.coreDerivative = Du := by
  let K := cylinderRecoveryBand B c r s
  have hK : IsCompact K := isCompact_cylinderRecoveryBand B c r s
  letI : IsFiniteMeasure ((volume : Measure Plane).restrict (ball (0 : Plane) (r / 2))) :=
    finite_planarVolume_restrict_ball _
  have hBulk : IntegrableOn (fun y => planarCoordinateBulkPotential a (u y)) (ball (0 : Plane) (r / 2)) :=
    integrable_planarCoordinateBulkPotential_of_bound a hu.2.1.aestronglyMeasurable huB
  have hSlice (z : ℝ) (hz : z ∈ Icc (-s) s) : ∃ E : Plane → HarmonicMaps.Gradient 2 5,
      MemW12 (ballDomain (0 : Plane) r) (cylinderMiddleSlice B c r u W z) E ∧
      planarWeakEnergy a (ε : ℝ) (cylinderMiddleSlice B c r u W z) E r ≤
        planarWeakEnergy a (ε : ℝ) u Du (r / 2) + C * (volume (ball (0 : Plane) r)).toReal := by
    have hSliceK (y : Plane) (hlo : (7 / 16 : ℝ) * r ≤ ‖y‖) (hhi : ‖y‖ ≤ r) :
        c + axisChart B (y, z) ∈ K :=
      axisChart_mem_cylinderRecoveryBand B c ((show r / 4 ≤ (7 / 16 : ℝ) * r by linarith only [hr]).trans hlo) hhi hz
    exact cylinderMiddleSlice_memW12_energy a ε B c hr z hu hBulk hCore hV hW hCV hSliceK hInner hSideCost
  have hRange (z : ℝ) (hz : z ∈ Icc (-s) s) : ∀ᵐ y ∂volume.restrict (ball (0 : Plane) r),
      ‖cylinderMiddleSlice B c r u W z y‖ ≤ max M (Real.sqrt 2 * vacuumRadius a) := by
    have hU : ∀ᵐ y ∂volume, y ∈ ball (0 : Plane) (r / 2) → ‖u y‖ ≤ Real.sqrt 2 * vacuumRadius a :=
      (ae_restrict_iff' measurableSet_ball).mp huB
    filter_upwards [ae_restrict_of_ae hU, ae_restrict_mem (μ := volume) measurableSet_ball] with y hy hY
    by_cases h : ‖y‖ < r / 2
    · rw [cylinderMiddleSlice, if_pos h]
      exact (hy (mem_ball_zero_iff.2 h)).trans (le_max_right _ _)
    · have hK' : c + axisChart B (y, z) ∈ K :=
        axisChart_mem_cylinderRecoveryBand B c
          ((show r / 4 ≤ r / 2 by linarith only [hr]).trans (le_of_not_gt h)) (mem_ball_zero_iff.1 hY).le hz
      simpa only [cylinderMiddleSlice, if_neg h, cylinderSliceMap, Function.comp_apply,
        LinearIsometryEquiv.norm_map] using hSideRange _ hK'
  refine ⟨{ core := u
            coreDerivative := Du
            core_memW12 := hu
            core_range := huB
            core_collar := hCore
            core_bulk := hBulk
            core_cost := hCost
            side_smooth := hW
            side_range := hSideRange
            side_cost := hSideCost
            side_inner := hInner
            side_outer := hOuter
            slice_range := hRange
            slice := hSlice
            volume := ?_
            traces := ?_ }, rfl, rfl⟩
  · intro lo hi hlo hI hhi
    have hSideK := cylinderMiddleSideDomain_subset_recoveryBand B c hr hlo hhi
    exact ⟨cylinderMiddleMemH1 B c hr hu hCore hV hW hK hCV hSideK hInner,
      cylinderMiddle_energy_le a ε B c hr hI.le hu hBulk hK hSideK hSideCost⟩
  · intro lo hi hlo _ hhi
    have hZK (z : ℝ) (hz : z ∈ Icc lo hi) : z ∈ Icc (-s) s := ⟨hlo.trans hz.1, hz.2.trans hhi⟩
    have hWallK (z : ℝ) (hz : z ∈ Icc lo hi) (y : Plane) (hy : y ∈ ball (0 : Plane) r) (hlo' : r / 2 ≤ ‖y‖) :
        c + axisChart B (y, z) ∈ K :=
      axisChart_mem_cylinderRecoveryBand B c ((show r / 4 ≤ r / 2 by linarith only [hr]).trans hlo')
        (mem_ball_zero_iff.1 hy).le (hZK z hz)
    have hLpSlice (z : ℝ) (hz : z ∈ Icc lo hi) :
        MemLp (cylinderMiddleSlice B c r u W z) 2 (volume.restrict (ball (0 : Plane) r)) := by
      obtain ⟨E, hE, _⟩ := hSlice z (hZK z hz)
      exact hE.2.1
    obtain ⟨P, hP⟩ := exists_cylinderMiddle_horizontalTrace B c r lo hi u hK
      (hW.continuousOn.mono hCV) hWallK hLpSlice
    obtain ⟨Q, hQ, hQout⟩ := exists_cylinderMiddle_radialTrace B c hr hlo hhi u hW hCV hOuter
    refine ⟨P, Q, ?_, hQ, ?_, hQout⟩
    · exact Eventually.of_forall fun t ht => hP ⟨t, ht.1.le, ht.2.le⟩
    · intro t
      obtain ⟨hL, hE⟩ := hP t
      rw [hE]
      exact hL.coeFn_toLp.trans (Eventually.of_forall fun y =>
        frobenius_cylinderMiddleField_axisChart B c r u W t.val y)

/-- The regular lateral sequence and the splitting-cost recovery of its
fixed middle circle give actual middle fields for all selected heights. -/
theorem exists_cylinderRecoveryMiddle_of_regular_band (a : BulkCoefficients)
    (hPolar : External.PeriodicAngularSobolev)
    {U K : Set Point} (hU : IsOpen U) (hKU : K ⊆ U)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {r s M D : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hD : 0 ≤ D)
    (hLat : ∀ z ∈ Icc (-s) s, ∀ θ : NativeCircle, c + axisChart B (r • θ.val, z) ∈ K)
    (ε : ℕ → ElasticScale) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    {q : Point → S0} {Q : ℕ → Point → S0}
    (hq : ContDiffOn ℝ ∞ q U) (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) U)
    (hVac : MapsTo q K (vacuum a)) (hConv : TendstoUniformlyOn Q q atTop K)
    (hRange : ∀ n x, x ∈ K → ‖Q n x‖ ≤ M)
    (hDensity : ∀ n x, x ∈ K → energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ D)
    (p : C(NativeCircle, vacuum a)) (hp : ∀ θ, (p θ).val = q (c + axisChart B (r • θ.val, 0))) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 ≤ C ∧ ∃ V : Set Point, IsOpen V ∧ cylinderRecoveryBand B c r s ⊆ V ∧
      ∀ᶠ n : ℕ in atTop,
        Nonempty (CylinderRecoveryMiddleData a (ε n) B c r s p
          (cylinderSideRecovery a B c r 0 q (Q n)) (Q n) V C₀ C M) := by
  have hZ : (0 : ℝ) ∈ Icc (-s) s := ⟨by linarith only [hs], hs.le⟩
  have hSphere := memSphereW12_of_regular_cylinder_circle a B c r 0 hq (fun θ => hKU (hLat 0 hZ θ)) p hp
  obtain ⟨C₀, hC₀, hCore⟩ := exists_planarWeakRecovery_on_ball_of_splittingCost a hPolar p hSphere
  obtain ⟨C, hC, V, hV, hCV, hSide⟩ := exists_cylinderRecoverySide_of_regular_band a hU hKU B c hr hs hD hLat
    ε hq hQ hVac hConv hRange hDensity p hp
  refine ⟨C₀, C, hC₀, hC, V, hV, hCV, ?_⟩
  have hSmall : 0 < (3 / 16 : ℝ) * (r / 2) := by positivity
  filter_upwards [hε (Iio_mem_nhds hSmall), hSide] with n hn hW
  obtain ⟨u, Du, hu, hUB, hRay, hCost⟩ := hCore (0 : Plane) (half_pos hr) (ε n).2.1 hn
  have hRay' (ρ : ℝ) (hρ : (7 / 16 : ℝ) * r ≤ ρ) (θ : NativeCircle) :
      u (ρ • θ.val) = frobeniusCoordinateEquiv (p θ).val := by
    have hh : (7 / 8 : ℝ) * (r / 2) ≤ ρ := by linarith only [hρ]
    simpa only [zero_add] using hRay ρ hh θ
  obtain ⟨G, _, _⟩ := cylinderRecoveryMiddleData_of_core_side a (ε n) B c hr p u Du hu hUB hRay'
    hCost hV hCV hW.1 (fun x hx => (hW.2 x hx).1) (fun x hx => (hW.2 x hx).2.1)
    (fun x hx => (hW.2 x hx).2.2.1) (fun x hx => (hW.2 x hx).2.2.2)
  exact ⟨G⟩

end Thesis.MeasureGeometry

end
