module

public import Thesis.Interpolation.CylinderSideRecovery
public import Thesis.MeasureGeometry.CylinderRecoveryExtrusion
import Thesis.Upstream.MinimizingSobolev
import Thesis.Interpolation.OpenOverlapGluing
import Thesis.Variational.GlobalComparison
import HolderToCK.Analysis.ClassicalEquation
import HarmonicMaps.Analysis.SobolevAECongruence
import Mathlib.Topology.UniformSpace.HeineCantor

/-! The actual middle-cylinder comparison and its horizontal traces. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis.MeasureGeometry

theorem axisCoordinates_eq_recoveryCoordinates (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c x : Point) : axisCoordinates B c x = cylinderRecoveryCoordinates B c x := by
  let p := axisCoordinates B c x
  calc
    _ = cylinderRecoveryCoordinates B c (c + axisChart B p) :=
      (cylinderRecoveryCoordinates_axisChart B c p).symm
    _ = _ := congrArg (cylinderRecoveryCoordinates B c) (axisChart_axisCoordinates B c x)

theorem axisCoordinates_radius (B : OrthonormalBasis (Fin 3) ℝ Point) (c x : Point) :
    ‖(axisCoordinates B c x).1‖ = cylinderTransverseRadius (B 2) (x - c) := by
  let p := axisCoordinates B c x
  have he := congrArg (fun y : Point => y - c) (axisChart_axisCoordinates B c x)
  rw [add_sub_cancel_left] at he
  exact (cylinderTransverseRadius_axisChart B p.1 p.2).symm.trans (congrArg _ he)

theorem axisCoordinates_height (B : OrthonormalBasis (Fin 3) ℝ Point) (c x : Point) :
    (axisCoordinates B c x).2 = cylinderHeight (B 2) (x - c) := by
  let p := axisCoordinates B c x
  have he := congrArg (fun y : Point => y - c) (axisChart_axisCoordinates B c x)
  rw [add_sub_cancel_left] at he
  exact (cylinderHeight_axisChart B p.1 p.2).symm.trans (congrArg _ he)

theorem mem_translatedAxisCylinder_iff_coordinates (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c x : Point) (r lo hi : ℝ) :
    x ∈ translatedAxisCylinder c (B 2) r lo hi ↔
      ‖(axisCoordinates B c x).1‖ < r ∧ (axisCoordinates B c x).2 ∈ Ioo lo hi := by
  simp only [translatedAxisCylinder, openAxisCylinder, mem_preimage, mem_setOf_eq, axisCoordinates_radius,
    axisCoordinates_height]
  rfl

theorem memW12_of_smooth_on_compact_neighborhood {n q : ℕ} {f : Domain n → Ambient q}
    {U : Set (Domain n)} {D : OpenDomain n} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ f U)
    {K : Set (Domain n)} (hK : IsCompact K) (hKU : K ⊆ U) (hDK : D.val ⊆ K) :
    MemW12 D f (fun x i => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  let Ω : OpenDomain n := ⟨U, hU⟩
  have hLoc := HolderToCK.memW12Loc_of_contDiffOn_one Ω (hF.of_le (by simp))
  exact ⟨hLoc.1.mono (hDK.trans hKU),
    (hLoc.2.1 K hK hKU).mono_measure (Measure.restrict_mono_set _ hDK),
    fun i => (hLoc.2.2 i K hK hKU).mono_measure (Measure.restrict_mono_set _ hDK)⟩

/-- The side part overlaps the inner disk in the collar where both
maps retain the same constant-in-height vacuum angular datum. -/
@[expose] def cylinderMiddleSideDomain (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (r lo hi : ℝ) : OpenDomain 3 :=
  ⟨translatedAxisCylinder c (B 2) r lo hi ∩
      {x | (7 / 16 : ℝ) * r < ‖(axisCoordinates B c x).1‖},
    (isOpen_translatedAxisCylinder _ _ _ _ _).inter
      (isOpen_lt continuous_const (contDiff_axisCoordinates B c).fst.continuous.norm)⟩

def cylinderMiddleField (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (r : ℝ)
    (u : Plane → Ambient 5) (W : Point → S0) (x : Point) : S0 :=
  if ‖(axisCoordinates B c x).1‖ < r / 2 then cylinderRecoveryTensorField B c u x else W x

def cylinderMiddleGradient (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (r : ℝ)
    (Du : Plane → HarmonicMaps.Gradient 2 5) (W : Point → S0) (x : Point) : Gradient :=
  if ‖(axisCoordinates B c x).1‖ < r / 2 then cylinderRecoveryTensorDerivative B c Du x else ClassicalGradient W x

private theorem side_memW12_frobenius_of_smooth {W : Point → S0} {V K : Set Point} {S : OpenDomain 3}
    (hV : IsOpen V) (hSmooth : ContDiffOn ℝ ∞ W V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hSK : S.val ⊆ K) :
    MemW12 S (frobeniusField W) (frobeniusGradient (ClassicalGradient W)) := by
  have hF : ContDiffOn ℝ ∞ (frobeniusField W) V :=
    frobeniusCoordinateEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn hSmooth
  have hW := memW12_of_smooth_on_compact_neighborhood (D := S) hV hF hK hKV hSK
  have hCols : (fun x i => fderiv ℝ (frobeniusField W) x (EuclideanSpace.single i 1)) =
      frobeniusGradient (ClassicalGradient W) := by
    funext x i
    rw [show frobeniusField W = frobeniusCoordinateEquiv ∘ W from rfl, LinearIsometryEquiv.comp_fderiv]
    rfl
  exact hCols ▸ hW

/-- A disk extruded with fixed height data and the actual regular side
collar yield the native weak graph of the middle recovery. -/
theorem cylinderMiddleMemH1 (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {r lo hi : ℝ} (hr : 0 < r)
    {u : Plane → Ambient 5} {Du : Plane → HarmonicMaps.Gradient 2 5}
    (hu : MemW12 (ballDomain (0 : Plane) (r / 2)) u Du)
    {a : BulkCoefficients} {b : C(NativeCircle, vacuum a)}
    (hCore : ∀ ρ ≥ (7 / 16 : ℝ) * r, ∀ θ : NativeCircle, u (ρ • θ.val) = frobeniusCoordinateEquiv (b θ).val)
    {W : Point → S0} {V K : Set Point} (hV : IsOpen V) (hW : ContDiffOn ℝ ∞ W V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hSideK : (cylinderMiddleSideDomain B c r lo hi).val ⊆ K)
    (hWall : ∀ x ∈ K, ‖(axisCoordinates B c x).1‖ ≤ (5 / 8 : ℝ) * r →
      W x = (b (sphereRadialDirection nativeCircleLoopBase (axisCoordinates B c x).1)).val) :
    MemH1 (translatedAxisCylinder c (B 2) r lo hi) (cylinderMiddleField B c r u W)
      (cylinderMiddleGradient B c r Du W) := by
  classical
  let Ω := translatedAxisCylinderDomain B c r lo hi
  let A := translatedAxisCylinderDomain B c (r / 2) lo hi
  let E := cylinderMiddleSideDomain B c r lo hi
  let u₀ := cylinderRecoveryField B c u
  let D₀ := cylinderRecoveryDerivative B c Du
  have hA : MemW12 A u₀ D₀ := cylinderRecovery_memW12 B c _ lo hi hu
  have hE : MemW12 E (frobeniusField W) (frobeniusGradient (ClassicalGradient W)) :=
    side_memW12_frobenius_of_smooth hV hW hK hKV hSideK
  have hCover : Ω.val ⊆ A.val ∪ E.val := by
    intro x hx
    have ht := (mem_translatedAxisCylinder_iff_coordinates B c x r lo hi).1 hx
    by_cases h : ‖(axisCoordinates B c x).1‖ < r / 2
    · exact Or.inl ((mem_translatedAxisCylinder_iff_coordinates B c x _ lo hi).2 ⟨h, ht.2⟩)
    · exact Or.inr ⟨hx, (show (7 / 16 : ℝ) * r < r / 2 by linarith).trans_le (le_of_not_gt h)⟩
  have hAgree : EqOn u₀ (frobeniusField W) (A.val ∩ E.val) := by
    intro x hx
    let y := (axisCoordinates B c x).1
    let θ := sphereRadialDirection nativeCircleLoopBase y
    have hLow : (7 / 16 : ℝ) * r < ‖y‖ := hx.2.2
    have hHi : ‖y‖ < r / 2 := ((mem_translatedAxisCylinder_iff_coordinates B c x _ lo hi).1 hx.1).1
    have hy : y ≠ 0 := norm_pos_iff.1 ((by positivity : 0 < (7 / 16 : ℝ) * r).trans hLow)
    have hY : ‖y‖ • θ.val = y := by
      change ‖y‖ • (sphereRadialDirection nativeCircleLoopBase y).val = y
      rw [sphereRadialDirection, dif_pos hy, NormedSpace.norm_smul_normalize]
    have huY : u₀ x = u y := by
      unfold u₀ cylinderRecoveryField
      rw [← axisCoordinates_eq_recoveryCoordinates]
    have hWθ : W x = (b θ).val :=
      hWall x (hSideK hx.2) (hHi.le.trans (by linarith only [hr]))
    calc
      _ = u (‖y‖ • θ.val) := huY.trans (congrArg u hY.symm)
      _ = frobeniusCoordinateEquiv (b θ).val := hCore _ hLow.le θ
      _ = _ := congrArg frobeniusCoordinateEquiv hWθ.symm
  have hGlued := memW12_openOverlap_piecewise hA hE hCover hAgree
  let w := cylinderMiddleField B c r u W
  let D := cylinderMiddleGradient B c r Du W
  have hEq : (fun x : Point => if x ∈ A.val then u₀ x else frobeniusField W x) =ᵐ[volume.restrict Ω.val]
      frobeniusField w := by
    filter_upwards [ae_restrict_mem Ω.property.measurableSet] with x hx
    have hAxis := (mem_translatedAxisCylinder_iff_coordinates B c x r lo hi).1 hx
    have hSub : x ∈ A.val ↔ ‖(axisCoordinates B c x).1‖ < r / 2 :=
      (mem_translatedAxisCylinder_iff_coordinates B c x _ lo hi).trans (and_iff_left hAxis.2)
    by_cases h : ‖(axisCoordinates B c x).1‖ < r / 2
    · simp only [if_pos (hSub.2 h), frobeniusField, w, cylinderMiddleField, if_pos h, u₀, cylinderRecoveryTensorField,
        frobeniusCoordinateEquiv.apply_symm_apply]
    · simp only [if_neg (fun hA => h (hSub.1 hA)), frobeniusField, w, cylinderMiddleField, if_neg h]
  have hEqD : (fun x : Point => if x ∈ A.val then D₀ x else frobeniusGradient (ClassicalGradient W) x)
      =ᵐ[volume.restrict Ω.val] frobeniusGradient D := by
    filter_upwards [ae_restrict_mem Ω.property.measurableSet] with x hx
    have hAxis := (mem_translatedAxisCylinder_iff_coordinates B c x r lo hi).1 hx
    have hSub : x ∈ A.val ↔ ‖(axisCoordinates B c x).1‖ < r / 2 :=
      (mem_translatedAxisCylinder_iff_coordinates B c x _ lo hi).trans (and_iff_left hAxis.2)
    funext i
    by_cases h : ‖(axisCoordinates B c x).1‖ < r / 2
    · simp only [if_pos (hSub.2 h), frobeniusGradient, D, cylinderMiddleGradient, if_pos h, D₀,
        cylinderRecoveryTensorDerivative, frobeniusCoordinateEquiv.apply_symm_apply]
    · simp only [if_neg (fun hA => h (hSub.1 hA)), frobeniusGradient, D, cylinderMiddleGradient, if_neg h]
  exact (memH1_iff_memW12 Ω w D).2 (hGlued.congr_ae hEq hEqD)

/-- The middle comparison pays the exact height times the planar
energy, plus the scale-independent side budget on the fixed compact. -/
theorem cylinderMiddle_energy_le (a : BulkCoefficients) (ε : ElasticScale)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {r lo hi : ℝ}
    (hr : 0 < r) (hHeight : lo ≤ hi)
    {u : Plane → Ambient 5} {Du : Plane → HarmonicMaps.Gradient 2 5}
    (hu : MemW12 (ballDomain (0 : Plane) (r / 2)) u Du)
    (hBulk : IntegrableOn (fun y => planarCoordinateBulkPotential a (u y)) (ball (0 : Plane) (r / 2)))
    {W : Point → S0} {K : Set Point} (hK : IsCompact K)
    (hSideK : (cylinderMiddleSideDomain B c r lo hi).val ⊆ K)
    {C : ℝ}
    (hBound : ∀ x ∈ K, energyDensity a ε (W x) (ClassicalGradient W x) ≤ C) :
    energy a ε (translatedAxisCylinder c (B 2) r lo hi) (cylinderMiddleField B c r u W)
      (cylinderMiddleGradient B c r Du W) ≤
        ENNReal.ofReal ((hi - lo) * planarWeakEnergy a (ε : ℝ) u Du (r / 2)) +
          ENNReal.ofReal (C * (volume K).toReal) := by
  let Ω := translatedAxisCylinder c (B 2) r lo hi
  let A := translatedAxisCylinder c (B 2) (r / 2) lo hi
  let X := cylinderRecoveryTensorField B c u
  let DX := cylinderRecoveryTensorDerivative B c Du
  have hΩ := (isOpen_translatedAxisCylinder c (B 2) r lo hi).measurableSet
  have hA := (isOpen_translatedAxisCylinder c (B 2) (r / 2) lo hi).measurableSet
  have hSub : A ⊆ Ω := by
    intro x hx
    have h := (mem_translatedAxisCylinder_iff_coordinates B c x _ lo hi).1 hx
    exact (mem_translatedAxisCylinder_iff_coordinates B c x _ lo hi).2 ⟨h.1.trans (half_lt_self hr), h.2⟩
  have hEq : energy a ε Ω (cylinderMiddleField B c r u W) (cylinderMiddleGradient B c r Du W) =
      energy a ε Ω (replaceOn A W X) (replaceOn A (ClassicalGradient W) DX) := by
    unfold energy
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) hΩ] with x hx
    have hz := ((mem_translatedAxisCylinder_iff_coordinates B c x r lo hi).1 hx).2
    have hA' : x ∈ A ↔ ‖(axisCoordinates B c x).1‖ < r / 2 :=
      (mem_translatedAxisCylinder_iff_coordinates B c x _ lo hi).trans (and_iff_left hz)
    by_cases h : x ∈ A
    · simp only [cylinderMiddleField, cylinderMiddleGradient, if_pos (hA'.1 h), replaceOn_of_mem h, X, DX]
    · simp only [cylinderMiddleField, cylinderMiddleGradient, if_neg (fun hρ => h (hA'.2 hρ)), replaceOn_of_notMem h]
  have hSideSub : Ω \ A ⊆ K := by
    intro x hx
    have hz := ((mem_translatedAxisCylinder_iff_coordinates B c x r lo hi).1 hx.1).2
    have hρ : r / 2 ≤ ‖(axisCoordinates B c x).1‖ :=
      le_of_not_gt (fun h => hx.2 ((mem_translatedAxisCylinder_iff_coordinates B c x _ lo hi).2 ⟨h, hz⟩))
    exact hSideK ⟨hx.1, (show (7 / 16 : ℝ) * r < r / 2 by linarith).trans_le hρ⟩
  have hSide : energy a ε (Ω \ A) W (ClassicalGradient W) ≤ ENNReal.ofReal (C * (volume K).toReal) := by
    unfold energy
    calc
      _ ≤ ∫⁻ x in Ω \ A, ENNReal.ofReal C := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (μ := volume) (hΩ.diff hA)] with x hx
        exact ENNReal.ofReal_le_ofReal (hBound x (hSideSub hx))
      _ ≤ ∫⁻ x in K, ENNReal.ofReal C := lintegral_mono_set hSideSub
      _ = ENNReal.ofReal (C * (volume K).toReal) := by
        rw [lintegral_const, Measure.restrict_apply_univ, ENNReal.ofReal_mul'
          ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK.measure_lt_top.ne]
  rw [hEq, energy_replaceOn a ε hΩ hA hSub,
    cylinderRecovery_tensorEnergy_eq_height_mul_planarWeakEnergy a ε B c _ lo hi hHeight hu hBulk]
  exact add_le_add le_rfl hSide

/-- Actual horizontal slice of the middle comparison in Frobenius coordinates. -/
@[expose] def cylinderMiddleSlice (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (r : ℝ)
    (u : Plane → Ambient 5) (W : Point → S0) (z : ℝ) (y : Plane) : Ambient 5 :=
  if ‖y‖ < r / 2 then u y else frobeniusCoordinateEquiv (cylinderSliceMap B c W z y)

theorem frobenius_cylinderMiddleField_axisChart (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (r : ℝ) (u : Plane → Ambient 5) (W : Point → S0) (z : ℝ) (y : Plane) :
    frobeniusCoordinateEquiv (cylinderMiddleField B c r u W (c + axisChart B (y, z))) =
      cylinderMiddleSlice B c r u W z y := by
  classical
  by_cases h : ‖y‖ < r / 2
  · rw [cylinderMiddleField, axisCoordinates_axisChart, if_pos h, cylinderMiddleSlice, if_pos h,
      cylinderRecoveryTensorField, frobeniusCoordinateEquiv.apply_symm_apply,
      cylinderRecoveryField_axisChart]
  · rw [cylinderMiddleField, axisCoordinates_axisChart, if_neg h, cylinderMiddleSlice, if_neg h]
    rfl

theorem planarSmoothEnergyDensity_eq_native_columns (a : BulkCoefficients) (ε : ℝ)
    {W : Plane → S0} {x : Plane} (hW : DifferentiableAt ℝ W x) :
    planarSmoothEnergyDensity a ε W x =
      (1 / 2 : ℝ) * hsNormSq (fun i =>
        fderiv ℝ (frobeniusCoordinateEquiv ∘ W) x (EuclideanSpace.single i 1)) +
        ε⁻¹ ^ 2 * planarCoordinateBulkPotential a (frobeniusCoordinateEquiv (W x)) := by
  have hf : fderiv ℝ (fun y => (W y : Tensor)) x =
      symmetricTraceless.subtypeL.comp (fderiv ℝ W x) :=
    (symmetricTraceless.subtypeL.hasFDerivAt.comp x hW.hasFDerivAt).fderiv
  have hDir : planarSmoothDirichletDensity W x =
      (1 / 2 : ℝ) * hsNormSq (fun i =>
        fderiv ℝ (frobeniusCoordinateEquiv ∘ W) x (EuclideanSpace.single i 1)) := by
    unfold planarSmoothDirichletDensity hsNormSq
    rw [hf, LinearIsometryEquiv.comp_fderiv]
    apply congrArg ((1 / 2 : ℝ) * ·)
    apply Finset.sum_congr rfl
    intro i _
    let Z := fderiv ℝ W x (EuclideanSpace.single i 1)
    change ‖Z‖ ^ 2 = ‖frobeniusCoordinateEquiv Z‖ ^ 2
    rw [frobeniusCoordinateEquiv.norm_map]
  have hBulk : planarCoordinateBulkPotential a (frobeniusCoordinateEquiv (W x)) = bulkPotential a (W x) :=
    congrArg (bulkPotential a) (frobeniusCoordinateEquiv.symm_apply_apply (W x))
  unfold planarSmoothEnergyDensity
  rw [hDir, hBulk]
  ring

/-- Each actual horizontal comparison slice pays the planar recovery
cost and the fixed bounded side contribution. -/
theorem cylinderMiddleSlice_memW12_energy (a : BulkCoefficients) (ε : ElasticScale)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {r : ℝ} (hr : 0 < r) (z : ℝ)
    {u : Plane → Ambient 5} {Du : Plane → HarmonicMaps.Gradient 2 5}
    (hu : MemW12 (ballDomain (0 : Plane) (r / 2)) u Du)
    (hBulk : IntegrableOn (fun y => planarCoordinateBulkPotential a (u y)) (ball (0 : Plane) (r / 2)))
    {b : C(NativeCircle, vacuum a)}
    (hCore : ∀ ρ ≥ (7 / 16 : ℝ) * r, ∀ θ : NativeCircle, u (ρ • θ.val) = frobeniusCoordinateEquiv (b θ).val)
    {W : Point → S0} {V K : Set Point} (hV : IsOpen V) (hW : ContDiffOn ℝ ∞ W V)
    (hKV : K ⊆ V)
    (hSideK : ∀ y : Plane, (7 / 16 : ℝ) * r ≤ ‖y‖ → ‖y‖ ≤ r → c + axisChart B (y, z) ∈ K)
    (hWall : ∀ x ∈ K, ‖(axisCoordinates B c x).1‖ ≤ (5 / 8 : ℝ) * r →
      W x = (b (sphereRadialDirection nativeCircleLoopBase (axisCoordinates B c x).1)).val)
    {C : ℝ} (hBound : ∀ x ∈ K, energyDensity a ε (W x) (ClassicalGradient W x) ≤ C) :
    ∃ E : Plane → HarmonicMaps.Gradient 2 5,
      MemW12 (ballDomain (0 : Plane) r) (cylinderMiddleSlice B c r u W z) E ∧
      planarWeakEnergy a (ε : ℝ) (cylinderMiddleSlice B c r u W z) E r ≤
        planarWeakEnergy a (ε : ℝ) u Du (r / 2) + C * (volume (ball (0 : Plane) r)).toReal := by
  classical
  let Ω := ballDomain (0 : Plane) r
  let A := ballDomain (0 : Plane) (r / 2)
  let G (y : Plane) := c + axisChart B (y, z)
  let S : OpenDomain 2 := ⟨Ω.val ∩ {y | (7 / 16 : ℝ) * r < ‖y‖},
    Ω.property.inter (isOpen_lt continuous_const continuous_norm)⟩
  let T : Set Plane := closedBall 0 r \ ball 0 ((7 / 16 : ℝ) * r)
  let q (y : Plane) := cylinderSliceMap B c W z y
  let v := frobeniusCoordinateEquiv ∘ q
  let Dv (y : Plane) (i : Fin 2) := fderiv ℝ v y (EuclideanSpace.single i 1)
  have hT : IsCompact T := (isCompact_closedBall _ _).diff isOpen_ball
  have hG : ContDiff ℝ ∞ G := contDiff_axisChart_horizontal_affine B c z
  have hGP : T ⊆ G ⁻¹' V := fun y hy =>
    hKV (hSideK y (le_of_not_gt fun h => hy.2 (mem_ball_zero_iff.2 h))
      (mem_closedBall_zero_iff.1 hy.1))
  have hST : S.val ⊆ T := fun _ hy =>
    ⟨ball_subset_closedBall hy.1, fun h => hy.2.not_ge (mem_ball_zero_iff.1 h).le⟩
  have hQ : ContDiffOn ℝ ∞ q (G ⁻¹' V) := hW.comp hG.contDiffOn (fun _ hx => hx)
  have hvS : MemW12 S v Dv := memW12_of_smooth_on_compact_neighborhood
    (hV.preimage hG.continuous) (frobeniusCoordinateEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn hQ)
      hT hGP hST
  have hAΩ : A.val ⊆ Ω.val := ball_subset_ball (half_le_self hr.le)
  have hCover : Ω.val ⊆ A.val ∪ S.val := by
    intro y hy
    by_cases h : y ∈ A.val
    · exact Or.inl h
    · exact Or.inr ⟨hy, (show (7 / 16 : ℝ) * r < r / 2 by linarith).trans_le
        (le_of_not_gt fun hl => h (mem_ball_zero_iff.2 hl))⟩
  have hAgree : EqOn u v (A.val ∩ S.val) := by
    intro y hy
    let θ := sphereRadialDirection nativeCircleLoopBase y
    have hLo : (7 / 16 : ℝ) * r < ‖y‖ := hy.2.2
    have hHi : ‖y‖ < r / 2 := mem_ball_zero_iff.1 hy.1
    have hN : y ≠ 0 := norm_pos_iff.1 ((by positivity : 0 < (7 / 16 : ℝ) * r).trans hLo)
    have hY : ‖y‖ • θ.val = y := by
      change ‖y‖ • (sphereRadialDirection nativeCircleLoopBase y).val = y
      rw [sphereRadialDirection, dif_pos hN, NormedSpace.norm_smul_normalize]
    have hWq := hWall (G y) (hSideK y hLo.le (hHi.trans (half_lt_self hr)).le)
    dsimp only [G] at hWq
    rw [axisCoordinates_axisChart] at hWq
    have hQb : q y = (b θ).val := hWq (hHi.le.trans (by linarith only [hr]))
    exact ((congrArg u hY).symm.trans (hCore _ hLo.le θ)).trans (congrArg frobeniusCoordinateEquiv hQb.symm)
  let f := cylinderMiddleSlice B c r u W z
  let E (y : Plane) := if y ∈ A.val then Du y else Dv y
  have hf : MemW12 Ω f E := by
    have h := memW12_openOverlap_piecewise hu hvS hCover hAgree
    refine h.congr_ae ?_ (EventuallyEq.refl _ _)
    exact ae_of_all _ fun y => by
      have hAx : y ∈ A.val ↔ ‖y‖ < r / 2 := mem_ball_zero_iff
      change (if y ∈ A.val then u y else v y) = f y
      simp only [f, cylinderMiddleSlice, hAx, v, Function.comp_apply, q]
  refine ⟨E, hf, ?_⟩
  let A' := Ω.val \ A.val
  have hA'T : A' ⊆ T := fun y hy =>
    ⟨ball_subset_closedBall hy.1, fun hin => hy.2 (mem_ball_zero_iff.2
      ((mem_ball_zero_iff.1 hin).trans (by linarith only [hr])))⟩
  have hPotA : IntegrableOn (fun y => planarCoordinateBulkPotential a (f y)) A.val :=
    hBulk.congr_fun (fun y hy => by
      simp only [f, cylinderMiddleSlice, if_pos (mem_ball_zero_iff.1 hy)]) A.property.measurableSet
  have hPotA' : IntegrableOn (fun y => planarCoordinateBulkPotential a (f y)) A' := by
    have hvT : ContinuousOn v T := (frobeniusCoordinateEquiv.continuous.comp_continuousOn hQ.continuousOn).mono hGP
    have h := ((continuous_planarCoordinateBulkPotential a).comp_continuousOn hvT).integrableOn_compact
      (μ := (volume : Measure Plane)) hT
    apply (h.mono_set hA'T).congr_fun _ (Ω.property.measurableSet.diff A.property.measurableSet)
    intro y hy
    simp only [f, cylinderMiddleSlice, v, q, Function.comp_apply, if_neg (fun h => hy.2 (mem_ball_zero_iff.2 h))]
  have hPot : IntegrableOn (fun y => planarCoordinateBulkPotential a (f y)) Ω.val := by
    have h := hPotA'.union hPotA
    rwa [sdiff_union_of_subset hAΩ] at h
  let fD (y : Plane) := (1 / 2 : ℝ) * hsNormSq (E y) +
    (ε : ℝ)⁻¹ ^ 2 * planarCoordinateBulkPotential a (f y)
  let uD (y : Plane) := (1 / 2 : ℝ) * hsNormSq (Du y) +
    (ε : ℝ)⁻¹ ^ 2 * planarCoordinateBulkPotential a (u y)
  have hfI₁ := hf.integrable_hsNormSq.const_mul (1 / 2 : ℝ)
  have hfI₂ := hPot.const_mul ((ε : ℝ)⁻¹ ^ 2)
  have hfD : IntegrableOn fD Ω.val := hfI₁.add hfI₂
  have huI₁ := hu.integrable_hsNormSq.const_mul (1 / 2 : ℝ)
  have huI₂ := hBulk.const_mul ((ε : ℝ)⁻¹ ^ 2)
  have hInner : (∫ y in A.val, fD y) = ∫ y in A.val, uD y := by
    apply setIntegral_congr_fun A.property.measurableSet
    intro y hy
    simp only [fD, uD, E, if_pos hy, f, cylinderMiddleSlice, if_pos (mem_ball_zero_iff.1 hy)]
  have hOuter (y : Plane) (hy : y ∈ A') : fD y ≤ C := by
    have ht := hA'T hy
    have hLo : (7 / 16 : ℝ) * r ≤ ‖y‖ := le_of_not_gt fun hl => ht.2 (mem_ball_zero_iff.2 hl)
    have hHi : ‖y‖ ≤ r := mem_closedBall_zero_iff.1 ht.1
    have hGY : G y ∈ K := hSideK y hLo hHi
    have hQy : DifferentiableAt ℝ q y :=
      ((hQ y (hGP ht)).contDiffAt ((hV.preimage hG.continuous).mem_nhds (hGP ht))).differentiableAt (by simp)
    have hWy : DifferentiableAt ℝ W (G y) :=
      ((hW (G y) (hKV hGY)).contDiffAt (hV.mem_nhds (hKV hGY))).differentiableAt (by simp)
    have hEq : fD y = planarSmoothEnergyDensity a (ε : ℝ) q y := by
      simp only [fD, E, if_neg hy.2, f, cylinderMiddleSlice, if_neg (fun h => hy.2 (mem_ball_zero_iff.2 h))]
      exact (planarSmoothEnergyDensity_eq_native_columns a (ε : ℝ) hQy).symm
    exact hEq.le.trans ((planarSmoothEnergyDensity_slice_le (B := B) (c := c) (z := z) a ε hWy).trans (hBound _ hGY))
  have hC : 0 ≤ C := by
    let y : Plane := EuclideanSpace.single 0 r
    have hY : ‖y‖ = r := by rw [show y = EuclideanSpace.single 0 r from rfl, PiLp.norm_single, Real.norm_of_nonneg hr.le]
    have hKG := hSideK y (by rw [hY]; linarith) (le_of_eq hY)
    exact (energyDensity_nonneg a ε _ _).trans (hBound _ hKG)
  have hOuterInt : (∫ y in A', fD y) ≤ C * (volume Ω.val).toReal := by
    letI : IsFiniteMeasure (volume.restrict A') :=
      isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono sdiff_subset))
    calc
      _ ≤ ∫ _ in A', C := integral_mono_ae (hfD.mono_set sdiff_subset) (integrable_const _)
        ((ae_restrict_mem (Ω.property.measurableSet.diff A.property.measurableSet)).mono
          fun _ hy => hOuter _ hy)
      _ = C * (volume A').toReal := by simp [measureReal_def, smul_eq_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (ENNReal.toReal_mono measure_ball_ne_top (measure_mono sdiff_subset)) hC
  have hfD_eq : planarWeakEnergy a (ε : ℝ) f E r = ∫ y in Ω.val, fD y := by
    unfold planarWeakEnergy fD
    rw [integral_add hfI₁ hfI₂, integral_const_mul, integral_const_mul]
    rfl
  have huD_eq : planarWeakEnergy a (ε : ℝ) u Du (r / 2) = ∫ y in A.val, uD y := by
    unfold planarWeakEnergy uD
    rw [integral_add huI₁ huI₂, integral_const_mul, integral_const_mul]
    rfl
  rw [hfD_eq, huD_eq, ← hInner]
  have hSplit := setIntegral_sdiff A.property.measurableSet hfD hAΩ
  change (∫ y in A', fD y) = (∫ y in Ω.val, fD y) - ∫ y in A.val, fD y at hSplit
  change (∫ y in A', fD y) ≤ C * (volume (ball (0 : Plane) r)).toReal at hOuterInt
  linarith only [hSplit, hOuterInt]

private theorem continuous_toLp_of_ae_uniform_modulus {X Y F : Type*} [PseudoMetricSpace X]
    [MeasurableSpace Y] [NormedAddCommGroup F] {μ : Measure Y} [IsFiniteMeasure μ]
    (u : X → Y → F) (hu : ∀ x, MemLp (u x) 2 μ)
    (hMod : ∀ η > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x z, dist x z < δ →
      ∀ᵐ y ∂μ, ‖u x y - u z y‖ ≤ η) :
    Continuous (fun x => (hu x).toLp (u x)) := by
  apply Metric.continuous_iff.2
  intro t e he
  let K := (μ univ) ^ ((2 : ℝ≥0∞).toReal)⁻¹
  have hK : K ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (measure_ne_top _ _)
  let η := e / (K.toReal + 1)
  have hK₀ : 0 ≤ K.toReal := ENNReal.toReal_nonneg
  have hDen : 0 < K.toReal + 1 := by positivity
  have hη : 0 < η := div_pos he hDen
  obtain ⟨δ, hδ, h⟩ := hMod η hη
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have hClass : ((fun y => ((hu x).toLp (u x)) y) - (fun y => ((hu t).toLp (u t)) y)) =ᵐ[μ]
      (u x - u t) := (hu x).coeFn_toLp.sub (hu t).coeFn_toLp
  rw [Lp.dist_def, eLpNorm_congr_ae hClass]
  have hNorm : eLpNorm (u x - u t) 2 μ ≤ K * ENNReal.ofReal η := eLpNorm_le_of_ae_bound (h x t hx)
  have hReal := ENNReal.toReal_mono (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top) hNorm
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hη.le] at hReal
  refine hReal.trans_lt ?_
  dsimp only [η]
  rw [← mul_div_assoc]
  exact (div_lt_iff₀ hDen).2 (by nlinarith only [he])

private theorem dist_axisChart_height (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (y : Plane) (s t : ℝ) :
    dist (c + axisChart B (y, s)) (c + axisChart B (y, t)) = dist s t := by
  rw [dist_eq_norm, axisChart_eq_plane_add_axis, axisChart_eq_plane_add_axis]
  have h : (c + (axisChartPlane B y + s • B 2)) - (c + (axisChartPlane B y + t • B 2)) =
      (s - t) • B 2 := by rw [sub_smul]; abel
  rw [h, norm_smul, B.orthonormal.norm_eq_one, mul_one, Real.norm_eq_abs, Real.dist_eq]

/-- The middle comparison has one continuous native horizontal L²
trace over the whole closed interval, including both actual cap slices. -/
theorem exists_cylinderMiddle_horizontalTrace (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (r lo hi : ℝ) (u : Plane → Ambient 5) {W : Point → S0}
    {K : Set Point} (hK : IsCompact K) (hW : ContinuousOn W K)
    (hWallK : ∀ z ∈ Icc lo hi, ∀ y ∈ ball (0 : Plane) r, r / 2 ≤ ‖y‖ → c + axisChart B (y, z) ∈ K)
    (hSlices : ∀ z ∈ Icc lo hi,
      MemLp (cylinderMiddleSlice B c r u W z) 2 (volume.restrict (ball (0 : Plane) r))) :
    ∃ H : C(Icc lo hi, Lp (Ambient 5) 2 (volume.restrict (ball (0 : Plane) r))),
      ∀ t : Icc lo hi,
        ∃ ht : MemLp (fun y => frobeniusCoordinateEquiv
          (cylinderMiddleField B c r u W (c + axisChart B (y, t.val)))) 2
          (volume.restrict (ball (0 : Plane) r)), H t = ht.toLp _ := by
  let μ := volume.restrict (ball (0 : Plane) r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_ball_ne_top
  let f (t : Icc lo hi) := cylinderMiddleSlice B c r u W t.val
  have hf (t : Icc lo hi) : MemLp (f t) 2 μ := hSlices t.val t.property
  have hMod (η : ℝ) (hη : 0 < η) :
      ∃ δ > (0 : ℝ), ∀ s t : Icc lo hi, dist s t < δ → ∀ᵐ y ∂μ, ‖f s y - f t y‖ ≤ η := by
    have hUF := hK.uniformContinuousOn_of_continuous (frobeniusCoordinateEquiv.continuous.comp_continuousOn hW)
    obtain ⟨δ, hδ, hUF⟩ := Metric.uniformContinuousOn_iff.1 hUF η hη
    refine ⟨δ, hδ, fun s t hDist => ?_⟩
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_ball] with y hy
    by_cases h : ‖y‖ < r / 2
    · simp only [f, cylinderMiddleSlice, if_pos h, sub_self, norm_zero]
      exact hη.le
    · have hsK := hWallK s.val s.property y hy (le_of_not_gt h)
      have htK := hWallK t.val t.property y hy (le_of_not_gt h)
      have he : dist (c + axisChart B (y, s.val)) (c + axisChart B (y, t.val)) < δ :=
        (dist_axisChart_height B c y s.val t.val).symm ▸ hDist
      have hClose := hUF (c + axisChart B (y, s.val)) hsK (c + axisChart B (y, t.val)) htK he
      simpa only [f, cylinderMiddleSlice, if_neg h, cylinderSliceMap, Function.comp_apply, ← dist_eq_norm] using hClose.le
  let H : C(Icc lo hi, Lp (Ambient 5) 2 μ) :=
    ⟨fun t => (hf t).toLp _, continuous_toLp_of_ae_uniform_modulus f hf hMod⟩
  refine ⟨H, fun t => ?_⟩
  have he := funext (frobenius_cylinderMiddleField_axisChart B c r u W t.val)
  have ht : MemLp (fun y => frobeniusCoordinateEquiv
      (cylinderMiddleField B c r u W (c + axisChart B (y, t.val)))) 2 μ := he.symm ▸ hf t
  exact ⟨ht, MemLp.toLp_congr (hf t) ht (Eventually.of_forall (congrFun he.symm))⟩

end Thesis.MeasureGeometry
