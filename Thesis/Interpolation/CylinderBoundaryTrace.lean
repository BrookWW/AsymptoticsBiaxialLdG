module

public import Thesis.Interpolation.CylinderVolumeGluing
import StratificationTheory.Foundation.BoundedFiberL2Trace

/-! Physical disk and lateral trace classes for the translated cylinder. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix Matrix.Norms.Frobenius RealInnerProductSpace Topology

namespace Thesis.MeasureGeometry

def cylinderSideTraceMeasure (lo hi : ℝ) : Measure (NativeCircle × ℝ) :=
  ((volume : Measure Plane).toSphere).prod (volume.restrict (Ioo lo hi))

theorem ae_cylinderSideTraceMeasure_height_mem (lo hi : ℝ) :
    ∀ᵐ p : NativeCircle × ℝ ∂cylinderSideTraceMeasure lo hi, p.2 ∈ Ioo lo hi := by
  unfold cylinderSideTraceMeasure
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_snd)).mpr
    (Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioo)

def cylinderSideParameterCollar (R lo hi : ℝ) : Set ((NativeCircle × ℝ) × ℝ) :=
  (univ ×ˢ Icc lo hi) ×ˢ Icc (R / 2) R

abbrev CylinderSideL2Trace (q : ℕ) (R lo hi : ℝ) :=
  C(Icc (R / 2) R, Lp (Ambient q) 2 (cylinderSideTraceMeasure lo hi))

/-- The lateral class represents the raw radial slices of the same field
on the literal cylinder over the prescribed height interval. -/
def RepresentsCylinderSideL2Trace {q : ℕ} {R lo hi : ℝ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (u : Point → Ambient q)
    (T : CylinderSideL2Trace q R lo hi) : Prop :=
  ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (R / 2) R,
    ∃ hs : MemLp (fun p : NativeCircle × ℝ => u (c + axisChart B (t • p.1.val, p.2))) 2
      (cylinderSideTraceMeasure lo hi),
      T ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun p : NativeCircle × ℝ => u (c + axisChart B (t • p.1.val, p.2)))

/-- Matching lateral native classes at the actual physical wall of one
height band. -/
def MatchingCylinderSideTraces {q : ℕ} (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {R : ℝ} (hR : 0 < R) (lo hi : ℝ) (u v : Point → Ambient q) : Prop :=
  ∃ P Q : CylinderSideL2Trace q R lo hi,
    RepresentsCylinderSideL2Trace B c u P ∧ RepresentsCylinderSideL2Trace B c v Q ∧
      P ⟨R, half_le_self hR.le, le_rfl⟩ = Q ⟨R, half_le_self hR.le, le_rfl⟩

abbrev NativeSphereRadialL2Trace (q : ℕ) (a b : ℝ) :=
  C(Icc a b, Lp (Ambient q) 2 tensorSphereMeasure)

def RepresentsNativeSphereRadialTrace {q : ℕ} {a b : ℝ} (u : Point → Ambient q)
    (T : NativeSphereRadialL2Trace q a b) : Prop :=
  ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
    ∃ hs : MemLp (fun θ : UnitTensorSphere => u (t • θ.val)) 2 tensorSphereMeasure,
      T ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun θ : UnitTensorSphere => u (t • θ.val))

/-- The center of a terminal cylinder in the same physical frame as the
whole cylinder. -/
def cylinderTerminalCenter (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (lo hi : ℝ) : Point :=
  c + ((lo + hi) / 2) • B 2

theorem terminalCylinderCap_eq_translatedAxisCylinder (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (R lo hi : ℝ) :
    terminalCylinderCap (B 2) (cylinderTerminalCenter B c lo hi) R ((hi - lo) / 2) =
      translatedAxisCylinder c (B 2) R lo hi := by
  let z := (lo + hi) / 2
  let e := B 2
  have he : ‖e‖ = 1 := B.orthonormal.norm_eq_one 2
  ext x
  have hX : x - cylinderTerminalCenter B c lo hi = (x - c) - z • e := by
    dsimp only [cylinderTerminalCenter, z, e]
    abel
  have hHeight : cylinderHeight e ((x - c) - z • e) = cylinderHeight e (x - c) - z := by
    unfold cylinderHeight
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he, one_pow, mul_one]
  have hRad : cylinderTransverseRadius e ((x - c) - z • e) = cylinderTransverseRadius e (x - c) := by
    unfold cylinderTransverseRadius
    rw [hHeight, sub_smul]
    congr 1
    abel
  change ((x - cylinderTerminalCenter B c lo hi) ∈ openAxisCylinder e R (-((hi - lo) / 2)) ((hi - lo) / 2)) ↔
    x - c ∈ openAxisCylinder e R lo hi
  rw [hX]
  simp only [openAxisCylinder, hRad, hHeight, mem_setOf_eq]
  refine and_congr_right (fun _ => ⟨?_, ?_⟩)
  · rintro ⟨h₁, h₂⟩
    dsimp only [z] at h₁ h₂
    exact ⟨by linarith only [h₁], by linarith only [h₂]⟩
  · rintro ⟨h₁, h₂⟩
    dsimp only [z]
    exact ⟨by linarith only [h₁], by linarith only [h₂]⟩

/-- A continuous representative on the physical lateral collar produces
one genuine radial trace of the original weak field. -/
theorem exists_cylinderSideTrace_of_continuousOn_parameterCollar {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hR : 0 < R)
    (u : Point → Ambient q) (f : (NativeCircle × ℝ) × ℝ → Ambient q)
    (hF : ContinuousOn f (cylinderSideParameterCollar R lo hi))
    (hRaw : ∀ (θ : NativeCircle) (z : ℝ), z ∈ Ioo lo hi → ∀ t ∈ Ioo (R / 2) R,
      f ((θ, z), t) = u (c + axisChart B (t • θ.val, z))) :
    ∃ H : CylinderSideL2Trace q R lo hi,
      RepresentsCylinderSideL2Trace B c u H ∧
      ∀ t, (H t : NativeCircle × ℝ → Ambient q) =ᵐ[cylinderSideTraceMeasure lo hi]
        fun p => f (p, t.val) := by
  let μ := cylinderSideTraceMeasure lo hi
  let A : Set (NativeCircle × ℝ) := univ ×ˢ Icc lo hi
  let I := Icc (R / 2) R
  have hA : MeasurableSet A := MeasurableSet.univ.prod measurableSet_Icc
  have hAcompact : IsCompact A := isCompact_univ.prod isCompact_Icc
  have hAE : ∀ᵐ p ∂μ, p ∈ A :=
    (ae_cylinderSideTraceMeasure_height_mem lo hi).mono fun p hp => ⟨mem_univ _, ⟨hp.1.le, hp.2.le⟩⟩
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo lo hi)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  letI : IsFiniteMeasure μ := by dsimp only [μ, cylinderSideTraceMeasure]; infer_instance
  obtain ⟨M, hM⟩ := (hAcompact.prod isCompact_Icc).exists_bound_of_continuousOn hF
  have hMeas : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (R / 2) R,
      AEStronglyMeasurable (fun p : NativeCircle × ℝ => f (p, t)) μ := by
    refine Eventually.of_forall fun t ht => ?_
    have hC : ContinuousOn (fun p : NativeCircle × ℝ => f (p, t)) A :=
      hF.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun p hp => ⟨hp, ⟨ht.1.le, ht.2.le⟩⟩)
    have h := hC.aestronglyMeasurable (μ := μ) hA
    rwa [Measure.restrict_eq_self_of_ae_mem hAE] at h
  have hCont : ∀ᵐ p : NativeCircle × ℝ ∂μ, ContinuousOn (fun t => f (p, t)) I :=
    hAE.mono fun p hp => hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hp, ht⟩)
  have hB : ∀ᵐ p : NativeCircle × ℝ ∂μ, ∀ t ∈ I, ‖f (p, t)‖ ≤ M :=
    hAE.mono fun p hp t ht => hM _ ⟨hp, ht⟩
  obtain ⟨H, hH, _⟩ := StratificationTheory.exists_continuous_L2_trace_of_bounded_fiber_continuity
    μ (half_lt_self hR) (f := f) hMeas hCont hB
  refine ⟨H, ?_, ?_⟩
  · refine Eventually.of_forall fun t ht => ?_
    obtain ⟨hs, hS⟩ := hH ⟨t, ht.1.le, ht.2.le⟩
    have hEq : (fun p : NativeCircle × ℝ => f (p, t)) =ᵐ[μ]
        (fun p => u (c + axisChart B (t • p.1.val, p.2))) :=
      (ae_cylinderSideTraceMeasure_height_mem lo hi).mono fun p hp => hRaw p.1 p.2 hp t ht
    let hs' := hs.ae_eq hEq
    exact ⟨hs', hS.trans (hs.toLp_congr hs' hEq)⟩
  · intro t
    obtain ⟨hs, hh⟩ := hH t
    rw [hh]
    exact hs.coeFn_toLp

private theorem axisChart_mem_translatedClosedCylinder
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ}
    {y : Plane} {z : ℝ} (hy : ‖y‖ ≤ R) (hz : z ∈ Icc lo hi) :
    c + axisChart B (y, z) ∈ translatedClosedAxisCylinder c (B 2) R lo hi := by
  change c + axisChart B (y, z) - c ∈ closedAxisCylinder (B 2) R lo hi
  rw [add_sub_cancel_left]
  exact ⟨by rw [cylinderTransverseRadius_axisChart]; exact hy,
    by rw [cylinderHeight_axisChart]; exact hz⟩

/-- A field continuous on the closed cylinder has both native traces,
and each endpoint class is the original evaluated boundary value. -/
theorem exists_cylinderBoundaryL2Traces_of_continuousOn_closed {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ}
    (hR : 0 < R) (hI : lo < hi) {u : Point → Ambient q}
    (hu : ContinuousOn u (translatedClosedAxisCylinder c (B 2) R lo hi)) :
    ∃ (H : CylinderHeightL2Trace q R lo hi) (S : CylinderSideL2Trace q R lo hi),
      RepresentsCylinderHeightL2Trace B c u H ∧ RepresentsCylinderSideL2Trace B c u S ∧
      (∀ t, (H t : Plane → Ambient q) =ᵐ[volume.restrict (ball (0 : Plane) R)]
        fun y => u (c + axisChart B (y, t.val))) ∧
      (∀ t, (S t : NativeCircle × ℝ → Ambient q) =ᵐ[cylinderSideTraceMeasure lo hi]
        fun p => u (c + axisChart B (t.val • p.1.val, p.2))) := by
  let μ := (volume : Measure Plane).restrict (ball 0 R)
  let F (p : Plane × ℝ) := c + axisChart B p
  have hF : Continuous F := continuous_const.add (continuous_axisChart B)
  let G (p : Plane × ℝ) := u (F p)
  have hCompact := isCompact_translatedClosedAxisCylinder (c := c) (B.orthonormal.norm_eq_one 2) R lo hi
  obtain ⟨M, hM⟩ := hCompact.exists_bound_of_continuousOn hu
  letI : IsFiniteMeasure μ := finite_planarVolume_restrict_ball R
  have hMeas : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo lo hi,
      AEStronglyMeasurable (fun y : Plane => G (y, t)) μ := by
    refine Eventually.of_forall fun t ht => ?_
    have hC : ContinuousOn (fun y : Plane => u (F (y, t))) (ball (0 : Plane) R) :=
      hu.comp (hF.comp (continuous_id.prodMk continuous_const)).continuousOn
        (fun y hy => axisChart_mem_translatedClosedCylinder B c (mem_ball_zero_iff.mp hy).le ⟨ht.1.le, ht.2.le⟩)
    exact hC.aestronglyMeasurable measurableSet_ball
  have hCont : ∀ᵐ y : Plane ∂μ, ContinuousOn (fun t => G (y, t)) (Icc lo hi) :=
    (ae_restrict_mem measurableSet_ball).mono fun y hy =>
      hu.comp (hF.comp (continuous_const.prodMk continuous_id)).continuousOn
        (fun t ht => axisChart_mem_translatedClosedCylinder B c (mem_ball_zero_iff.mp hy).le ht)
  have hBound : ∀ᵐ y : Plane ∂μ, ∀ t ∈ Icc lo hi, ‖G (y, t)‖ ≤ M :=
    (ae_restrict_mem measurableSet_ball).mono fun y hy t ht =>
      hM _ (axisChart_mem_translatedClosedCylinder B c (mem_ball_zero_iff.mp hy).le ht)
  obtain ⟨H, hH, _⟩ := StratificationTheory.exists_continuous_L2_trace_of_bounded_fiber_continuity
    μ hI (f := G) hMeas hCont hBound
  let f (p : (NativeCircle × ℝ) × ℝ) := u (F (p.2 • p.1.1.val, p.1.2))
  have hContS : ContinuousOn f (cylinderSideParameterCollar R lo hi) := by
    apply hu.comp
    · exact (hF.comp ((continuous_snd.smul (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))).prodMk
        (continuous_snd.comp continuous_fst))).continuousOn
    · intro p hp
      have hθ := mem_sphere_zero_iff_norm.mp p.1.1.property
      have hP : p.2 ∈ Icc (R / 2) R := hp.2
      have hT : 0 ≤ p.2 := (half_pos hR).le.trans hP.1
      refine axisChart_mem_translatedClosedCylinder B c ?_ hp.1.2
      rw [norm_smul, Real.norm_of_nonneg hT, hθ, mul_one]
      exact hP.2
  obtain ⟨S, hS, hST⟩ := exists_cylinderSideTrace_of_continuousOn_parameterCollar B c hR u f hContS
    (fun θ z hz t ht => rfl)
  refine ⟨H, S, Eventually.of_forall fun t ht => hH ⟨t, ht.1.le, ht.2.le⟩, hS, ?_, hST⟩
  intro t
  obtain ⟨hs, hh⟩ := hH t
  rw [hh]
  exact hs.coeFn_toLp

end Thesis.MeasureGeometry

namespace Thesis

open MeasureGeometry

/-- Standard Sobolev boundary trace transport under a bi-Lipschitz domain
chart. Its terminal values are evaluated in the original cylindrical
disk and lateral coordinates. -/
def External.CylinderBoundaryChartTraceTransport : Prop :=
  ∀ {q : ℕ} (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ},
    ∀ hR : 0 < R, ∀ hI : lo < hi, ∀ F : Point ≃ₜ Point,
      LipschitzWith 20 (F : Point → Point) → LipschitzWith 20 (F.symm : Point → Point) →
      translatedAxisCylinder c (B 2) R lo hi = F ⁻¹' ball (0 : Point) R →
      ∀ (u : Point → Ambient q) (Du : Point → HarmonicMaps.Gradient 3 q),
        MemW12 (translatedAxisCylinderDomain B c R lo hi) u Du →
      ∀ (g : Point → Ambient q) (T : NativeSphereRadialL2Trace q (R / 2) R),
        RepresentsNativeSphereRadialTrace (u ∘ F.symm) T →
        (T ⟨R, half_le_self hR.le, le_rfl⟩ : UnitTensorSphere → Ambient q) =ᵐ[tensorSphereMeasure]
          (fun θ => g (F.symm (R • θ.val))) →
        ∃ (H : CylinderHeightL2Trace q R lo hi) (S : CylinderSideL2Trace q R lo hi),
          RepresentsCylinderHeightL2Trace B c u H ∧ RepresentsCylinderSideL2Trace B c u S ∧
          ((H ⟨lo, le_rfl, hI.le⟩ : Plane → Ambient q) =ᵐ[volume.restrict (ball (0 : Plane) R)]
            fun y => g (c + axisChart B (y, lo))) ∧
          ((H ⟨hi, hI.le, le_rfl⟩ : Plane → Ambient q) =ᵐ[volume.restrict (ball (0 : Plane) R)]
            fun y => g (c + axisChart B (y, hi))) ∧
          ((S ⟨R, half_le_self hR.le, le_rfl⟩ : NativeCircle × ℝ → Ambient q) =ᵐ[cylinderSideTraceMeasure lo hi]
            fun p => g (c + axisChart B (R • p.1.val, p.2)))

/-- Standard zero-trace characterization on a Lipschitz cylinder. The
lateral trace can be checked on any finite height cover up to null seams. -/
def External.CylinderBoundaryTraceKernel : Prop :=
  ∀ (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ},
    ∀ hR : 0 < R, ∀ hI : lo < hi,
    ∀ (u v : Point → S0) (Du Dv : Point → Gradient),
      MemH1 (translatedAxisCylinder c (B 2) R lo hi) u Du →
      MemH1 (translatedAxisCylinder c (B 2) R lo hi) v Dv →
    ∀ (P Q : CylinderHeightL2Trace 5 R lo hi),
      RepresentsCylinderHeightL2Trace B c (frobeniusField u) P →
      RepresentsCylinderHeightL2Trace B c (frobeniusField v) Q →
      P ⟨lo, le_rfl, hI.le⟩ = Q ⟨lo, le_rfl, hI.le⟩ →
      P ⟨hi, hI.le, le_rfl⟩ = Q ⟨hi, hI.le, le_rfl⟩ →
    ∀ {n : ℕ} (l h : Fin n → ℝ),
      (∀ i, Ioo (l i) (h i) ⊆ Ioo lo hi) →
      (∀ᵐ z : ℝ ∂volume.restrict (Ioo lo hi), ∃ i, z ∈ Ioo (l i) (h i)) →
      (∀ i, MatchingCylinderSideTraces B c hR (l i) (h i) (frobeniusField u) (frobeniusField v)) →
      SameTrace (translatedAxisCylinder c (B 2) R lo hi) u v Du Dv

end Thesis

namespace Thesis.MeasureGeometry

theorem cylinderTerminalCenter_axisChart (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (lo hi : ℝ) (y : Plane) (t : ℝ) :
    cylinderTerminalCenter B c lo hi + axisChart B (y, t - (lo + hi) / 2) =
      c + axisChart B (y, t) := by
  rw [cylinderTerminalCenter, axisChart_add_axis B y (t - (lo + hi) / 2), axisChart_add_axis B y t, sub_smul]
  abel

/-- The assigned wall representative at a physical height in the
original cylinder is its literal annular parameter value. -/
theorem terminalCylinderSurfaceValue_axisWall_originalHeight {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hR : 0 < R) (hI : lo < hi)
    (D : TerminalCylinderBoundaryData q R hR) (θ : NativeCircle) {z : ℝ} (hz : z ∈ Ioo lo hi) :
    terminalCylinderSurfaceValue B (cylinderTerminalCenter B c lo hi) ((hi - lo) / 2) D
      (c + axisChart B (R • θ.val, z)) =
      D.wall ((R + R * ((z - lo) / (hi - lo))) • θ.val) := by
  let h := (hi - lo) / 2
  let t := z - (lo + hi) / 2
  have hLo : -h < t := by dsimp only [h, t]; linarith only [hz.1]
  have hHi : t < h := by dsimp only [h, t]; linarith only [hz.2]
  have hθ := mem_sphere_zero_iff_norm.mp θ.property
  have hN : NormedSpace.normalize (R • θ.val) = θ.val := by
    rw [NormedSpace.normalize, norm_smul, Real.norm_of_nonneg hR.le, hθ,
      mul_one, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  have hRad : terminalWallParameterRadius R h t = R + R * ((z - lo) / (hi - lo)) := by
    dsimp only [terminalWallParameterRadius, h, t]
    field_simp [(sub_pos.mpr hI).ne']
    ring
  rw [← cylinderTerminalCenter_axisChart B c lo hi (R • θ.val) z, terminalCylinderSurfaceValue,
    cylinderRecoveryCoordinates_axisChart]
  change (if t ≤ -h then D.lower (R • θ.val) else if h ≤ t then D.upper (R • θ.val) else
      D.wall (terminalWallParameterRadius R h t • NormedSpace.normalize (R • θ.val))) = _
  rw [if_neg (not_le_of_gt hLo), if_neg (not_le_of_gt hHi), hN, hRad]

/-- The terminal filling realizes its disk and wall classes in the same
height coordinates as the original cylinder. -/
theorem exists_penalized_terminalAxisCylinder_fill (a : BulkCoefficients)
    (hSurface : External.TerminalCylinderSurfaceSobolev)
    (hTransport : External.AmbientBiLipschitzSobolevPullback3)
    (hTraceTransport : External.CylinderBoundaryChartTraceTransport) :
    ∃ K : ℝ, 0 < K ∧ ∀ (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
      {R lo hi : ℝ} (hR : 0 < R) (hI : lo < hi)
      (_ : R / 4 ≤ (hi - lo) / 2) (_ : (hi - lo) / 2 ≤ R)
      (ε : ElasticScale) (D : TerminalCylinderBoundaryData 5 R hR) (M : ℝ), D.Bounded M →
      let V := translatedAxisCylinder c (B 2) R lo hi
      let c' := cylinderTerminalCenter B c lo hi
      let h := (hi - lo) / 2
      ∃ (w : Point → S0) (Dw : Point → Thesis.Gradient)
        (P : CylinderHeightL2Trace 5 R lo hi) (Q : CylinderSideL2Trace 5 R lo hi),
        MemH1 V w Dw ∧
          RepresentsCylinderHeightL2Trace B c (frobeniusField w) P ∧
          RepresentsCylinderSideL2Trace B c (frobeniusField w) Q ∧
          ((P ⟨lo, le_rfl, hI.le⟩ : Plane → Ambient 5) =ᵐ[volume.restrict (ball (0 : Plane) R)] D.lower) ∧
          ((P ⟨hi, hI.le, le_rfl⟩ : Plane → Ambient 5) =ᵐ[volume.restrict (ball (0 : Plane) R)] D.upper) ∧
          ((Q ⟨R, half_le_self hR.le, le_rfl⟩ : NativeCircle × ℝ → Ambient 5) =ᵐ[cylinderSideTraceMeasure lo hi]
            fun p => terminalCylinderSurfaceValue B c' h D (c + axisChart B (R • p.1.val, p.2))) ∧
          EqOn w (frobeniusCoordinateEquiv.symm ∘ terminalCylinderSurfaceValue B c' h D) (frontier V) ∧
          (∀ᵐ x ∂volume.restrict V, ‖w x‖ ≤ M) ∧
          energy a ε V w Dw ≤ ENNReal.ofReal (K * R) * terminalCylinderSurfacePenalizedEnergy a ε h D := by
  obtain ⟨K, hK, hFill⟩ := exists_penalized_terminalCylinder_fill_of_boundaryData a hSurface hTransport
  refine ⟨K, hK, ?_⟩
  intro B c R lo hi hR hI hLow hHigh ε D M hD V c' h
  have hh : 0 < h := half_pos (sub_pos.mpr hI)
  have hV : terminalCylinderCap (B 2) c' R h = V := terminalCylinderCap_eq_translatedAxisCylinder B c R lo hi
  let F := terminalCylinderBallChart (B.orthonormal.norm_eq_one 2) c' hR hLow hHigh
  let g := terminalCylinderSurfaceValue B c' h D
  obtain ⟨w, Dw, T, hw, hRaw, hTrace, hT, hBound, hEnergy⟩ := hFill B c' hR hLow hHigh ε D M hD
  have hW : MemH1 V w Dw := hV ▸ hw
  have hExact : V = F ⁻¹' ball (0 : Point) R := hV.symm.trans
    (terminalCylinderCap_eq_preimage_ball (B.orthonormal.norm_eq_one 2) c' hR hLow hHigh)
  have hFLip : LipschitzWith 20 (F : Point → Point) := by
    intro x y
    refine (lipschitz_terminalCylinderBallChart (B.orthonormal.norm_eq_one 2) c' hR hLow hHigh x y).trans ?_
    gcongr
    norm_num
  have hFInv : LipschitzWith 20 (F.symm : Point → Point) :=
    lipschitz_terminalCylinderBallChart_symm (B.orthonormal.norm_eq_one 2) c' hR hLow hHigh
  have hW' : MemW12 (translatedAxisCylinderDomain B c R lo hi) (frobeniusField w) (frobeniusGradient Dw) :=
    (memH1_iff_memW12 (translatedAxisCylinderDomain B c R lo hi) w Dw).1 hW
  have hTrace' : RepresentsNativeSphereRadialTrace ((frobeniusField w) ∘ F.symm) T := by
    simpa only [RepresentsNativeSphereRadialTrace, RepresentsRadialL2Trace, Function.comp_def, zero_add,
      frobeniusField] using hTrace
  obtain ⟨P, Q, hP, hQ, hLower, hUpper, hWall⟩ :=
    hTraceTransport B c hR hI F hFLip hFInv hExact _ _ hW' g T hTrace' (hT ⟨R, half_le_self hR.le, le_rfl⟩)
  have hl (y : Plane) : g (c + axisChart B (y, lo)) = D.lower y := by
    have hS : lo - (lo + hi) / 2 = -h := by dsimp only [h]; ring
    rw [← cylinderTerminalCenter_axisChart B c lo hi y lo, hS]
    exact terminalCylinderSurfaceValue_lower B c' h D y
  have hu (y : Plane) : g (c + axisChart B (y, hi)) = D.upper y := by
    have hS : hi - (lo + hi) / 2 = h := by dsimp only [h]; ring
    rw [← cylinderTerminalCenter_axisChart B c lo hi y hi, hS]
    exact terminalCylinderSurfaceValue_upper B c' hh D y
  exact ⟨w, Dw, P, Q, hW, hP, hQ, hLower.trans (Eventually.of_forall hl),
    hUpper.trans (Eventually.of_forall hu), hWall, hV ▸ hRaw, hV ▸ hBound, hV ▸ hEnergy⟩

private theorem representsCylinderSideL2Trace_congr {q : ℕ} {R lo hi : ℝ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {u v : Point → Ambient q}
    (T : CylinderSideL2Trace q R lo hi) (hT : RepresentsCylinderSideL2Trace B c u T)
    (hEq : ∀ (θ : NativeCircle) (z : ℝ), z ∈ Ioo lo hi → ∀ t ∈ Ioo (R / 2) R,
      u (c + axisChart B (t • θ.val, z)) = v (c + axisChart B (t • θ.val, z))) :
    RepresentsCylinderSideL2Trace B c v T := by
  filter_upwards [hT] with t ht ht'
  obtain ⟨hs, hC⟩ := ht ht'
  have hE : (fun p : NativeCircle × ℝ => u (c + axisChart B (t • p.1.val, p.2))) =ᵐ[cylinderSideTraceMeasure lo hi]
      (fun p : NativeCircle × ℝ => v (c + axisChart B (t • p.1.val, p.2))) :=
    (ae_cylinderSideTraceMeasure_height_mem lo hi).mono fun p hp => hEq p.1 p.2 hp t ht'
  let hs' := hs.ae_eq hE
  exact ⟨hs', hC.trans (hs.toLp_congr hs' hE)⟩

private theorem MatchingCylinderSideTraces.congr_left {q : ℕ} {R : ℝ} (hR : 0 < R)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {lo hi : ℝ}
    {u u' v : Point → Ambient q} (hM : MatchingCylinderSideTraces B c hR lo hi u v)
    (hEq : ∀ (θ : NativeCircle) (z : ℝ), z ∈ Ioo lo hi → ∀ t ∈ Ioo (R / 2) R,
      u (c + axisChart B (t • θ.val, z)) = u' (c + axisChart B (t • θ.val, z))) :
    MatchingCylinderSideTraces B c hR lo hi u' v := by
  obtain ⟨P, Q, hP, hQ, hMatch⟩ := hM
  exact ⟨P, Q, representsCylinderSideL2Trace_congr B c P hP hEq, hQ, hMatch⟩

/-- Three original cylindrical pieces give one Sobolev competitor with
the prescribed trace on both exterior disks and all outer wall bands. -/
theorem cylinderThreePiecewise_memH1_sameTrace (hKernel : External.CylinderBoundaryTraceKernel)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R : ℝ} (hR : 0 < R)
    {lo b d hi : ℝ} (hlb : lo < b) (hbd : b < d) (hdh : d < hi)
    (u v w g : Point → S0) (Du Dv Dw Dg : Point → Thesis.Gradient)
    (hu : MemH1 (translatedAxisCylinder c (B 2) R lo b) u Du)
    (hv : MemH1 (translatedAxisCylinder c (B 2) R b d) v Dv)
    (hw : MemH1 (translatedAxisCylinder c (B 2) R d hi) w Dw)
    (hg : MemH1 (translatedAxisCylinder c (B 2) R lo hi) g Dg)
    (P : CylinderHeightL2Trace 5 R lo b) (Q : CylinderHeightL2Trace 5 R b d)
    (S : CylinderHeightL2Trace 5 R d hi) (T : CylinderHeightL2Trace 5 R lo hi)
    (hP : RepresentsCylinderHeightL2Trace B c (frobeniusField u) P)
    (hQ : RepresentsCylinderHeightL2Trace B c (frobeniusField v) Q)
    (hS : RepresentsCylinderHeightL2Trace B c (frobeniusField w) S)
    (hT : RepresentsCylinderHeightL2Trace B c (frobeniusField g) T)
    (hPQ : P ⟨b, hlb.le, le_rfl⟩ = Q ⟨b, le_rfl, hbd.le⟩)
    (hQS : Q ⟨d, hbd.le, le_rfl⟩ = S ⟨d, le_rfl, hdh.le⟩)
    (hLow : P ⟨lo, le_rfl, hlb.le⟩ = T ⟨lo, le_rfl, (hlb.trans (hbd.trans hdh)).le⟩)
    (hHigh : S ⟨hi, hdh.le, le_rfl⟩ = T ⟨hi, (hlb.trans (hbd.trans hdh)).le, le_rfl⟩)
    (hSide₀ : MatchingCylinderSideTraces B c hR lo b (frobeniusField u) (frobeniusField g))
    (hSide₁ : MatchingCylinderSideTraces B c hR b d (frobeniusField v) (frobeniusField g))
    (hSide₂ : MatchingCylinderSideTraces B c hR d hi (frobeniusField w) (frobeniusField g)) :
    let U := translatedAxisCylinder c (B 2) R lo hi
    let f := cylinderThreePiecewise B c b d u v w
    let D := cylinderThreePiecewise B c b d Du Dv Dw
    MemH1 U f D ∧ SameTrace U f g D Dg := by
  let f := cylinderThreePiecewise B c b d u v w
  let D := cylinderThreePiecewise B c b d Du Dv Dw
  let U := translatedAxisCylinderDomain B c R lo hi
  obtain ⟨hW, J, hJ, hJL, hJR⟩ := memW12_cylinderThreePiecewise B c R hlb hbd hdh
    (frobeniusField u) (frobeniusField v) (frobeniusField w) (frobeniusGradient Du)
    (frobeniusGradient Dv) (frobeniusGradient Dw)
    ((memH1_iff_memW12 (translatedAxisCylinderDomain B c R lo b) _ _).1 hu)
    ((memH1_iff_memW12 (translatedAxisCylinderDomain B c R b d) _ _).1 hv)
    ((memH1_iff_memW12 (translatedAxisCylinderDomain B c R d hi) _ _).1 hw)
    P Q S hP hQ hS hPQ hQS
  have hF : frobeniusField f = cylinderThreePiecewise B c b d (frobeniusField u) (frobeniusField v) (frobeniusField w) := by
    funext x
    dsimp only [f, cylinderThreePiecewise, cylinderHeightPiecewise, frobeniusField]
    split_ifs <;> rfl
  have hD : frobeniusGradient D =
      cylinderThreePiecewise B c b d (frobeniusGradient Du) (frobeniusGradient Dv) (frobeniusGradient Dw) := by
    funext x i
    dsimp only [D, cylinderThreePiecewise, cylinderHeightPiecewise, frobeniusGradient]
    split_ifs <;> rfl
  have hf : MemH1 U.val f D := by
    apply (memH1_iff_memW12 U _ _).2
    rw [hF, hD]
    exact hW
  have hJ' : RepresentsCylinderHeightL2Trace B c (frobeniusField f) J := by rw [hF]; exact hJ
  refine ⟨hf, ?_⟩
  let l : Fin 3 → ℝ := ![lo, b, d]
  let h : Fin 3 → ℝ := ![b, d, hi]
  have hI : lo < hi := hlb.trans (hbd.trans hdh)
  have hIn (i : Fin 3) : Ioo (l i) (h i) ⊆ Ioo lo hi := by
    intro z hz
    fin_cases i
    · exact ⟨hz.1, hz.2.trans (hbd.trans hdh)⟩
    · exact ⟨hlb.trans hz.1, hz.2.trans hdh⟩
    · exact ⟨(hlb.trans hbd).trans hz.1, hz.2⟩
  have hCov : ∀ᵐ z : ℝ ∂volume.restrict (Ioo lo hi), ∃ i : Fin 3, z ∈ Ioo (l i) (h i) := by
    have hNe (s : ℝ) : ∀ᵐ z : ℝ ∂volume.restrict (Ioo lo hi), z ≠ s := by
      refine ae_iff.mpr ?_
      have hSet : {z : ℝ | ¬ z ≠ s} = {s} := by ext z; simp
      rw [hSet, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hNe b, hNe d] with z hz hb hd
    by_cases hzb : z < b
    · exact ⟨0, hz.1, hzb⟩
    have hbz := lt_of_le_of_ne (le_of_not_gt hzb) hb.symm
    by_cases hzd : z < d
    · exact ⟨1, hbz, hzd⟩
    exact ⟨2, lt_of_le_of_ne (le_of_not_gt hzd) hd.symm, hz.2⟩
  apply hKernel B c hR hI f g D Dg hf hg J T hJ' hT (hJL.trans hLow) (hJR.trans hHigh) l h hIn hCov
  intro i
  fin_cases i
  · refine MatchingCylinderSideTraces.congr_left hR B c hSide₀ ?_
    intro θ z hz t ht
    have hlo : z < b := hz.2
    have hhi : z < d := hlo.trans hbd
    simp only [f, frobeniusField, cylinderThreePiecewise, cylinderHeightPiecewise,
      cylinderRecoveryCoordinates_axisChart, hlo, hhi, if_true]
  · refine MatchingCylinderSideTraces.congr_left hR B c hSide₁ ?_
    intro θ z hz t ht
    have hlo : ¬ z < b := not_lt_of_ge hz.1.le
    have hhi : z < d := hz.2
    simp only [f, frobeniusField, cylinderThreePiecewise, cylinderHeightPiecewise,
      cylinderRecoveryCoordinates_axisChart, hlo, hhi, if_true, if_false]
  · refine MatchingCylinderSideTraces.congr_left hR B c hSide₂ ?_
    intro θ z hz t ht
    have hhi : ¬ z < d := not_lt_of_ge hz.1.le
    simp only [f, frobeniusField, cylinderThreePiecewise, cylinderHeightPiecewise,
      cylinderRecoveryCoordinates_axisChart, hhi, if_false]

end Thesis.MeasureGeometry

end
