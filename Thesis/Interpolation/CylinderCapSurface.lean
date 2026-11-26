module

public import Thesis.Interpolation.CylinderCapFill
public import Thesis.MeasureGeometry.CylinderRecoveryExtrusion
public import Thesis.Foundation.VacuumFreeHomotopy
import StratificationTheory.Foundation.BoundedFiberL2Trace
import StratificationTheory.Foundation.RadialPiecewiseSobolevData
import StratificationTheory.Frozen.RadialTraceGluing

/-! Genuine compatible disk and wall traces for the short terminal cylinder. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

/-- The planar annulus parametrizes the whole lateral face. Its inner and
outer circles correspond to the bottom and top rims. -/
def terminalWallAnnulus (R : ℝ) : OpenDomain 2 :=
  ⟨{y : Plane | ‖y‖ ∈ Ioo R (2 * R)}, isOpen_Ioo.preimage continuous_norm⟩

/-- The genuine radial circle trace represents the actual a.e. planar
slices as a continuous curve in L². -/
def RepresentsNativePlanarRadialTrace {q : ℕ} {a b : ℝ}
    (u : Plane → Ambient q)
    (T : C(Icc a b, Lp (Ambient q) 2 ((volume : Measure Plane).toSphere))) : Prop :=
  ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
    ∃ hSlice : MemLp (fun θ : NativeCircle => u (t • θ.val)) 2 ((volume : Measure Plane).toSphere),
      T ⟨t, ht.1.le, ht.2.le⟩ = hSlice.toLp (fun θ : NativeCircle => u (t • θ.val))

/-- Bounded radial fibers continuous up to the rim determine a genuine
native trace with the original value class at every radius. -/
theorem exists_nativePlanarRadialTrace_of_bounded_fiber_continuity {q : ℕ} {a b : ℝ} (hab : a < b)
    {u : Plane → Ambient q} {M : ℝ}
    (hMeas : ∀ᵐ t : ℝ ∂volume, ∀ _ : t ∈ Ioo a b,
      AEStronglyMeasurable (fun θ : NativeCircle => u (t • θ.val)) ((volume : Measure Plane).toSphere))
    (hCont : ∀ᵐ θ : NativeCircle ∂((volume : Measure Plane).toSphere),
      ContinuousOn (fun t => u (t • θ.val)) (Icc a b))
    (hBound : ∀ᵐ θ : NativeCircle ∂((volume : Measure Plane).toSphere),
      ∀ t ∈ Icc a b, ‖u (t • θ.val)‖ ≤ M) :
    ∃ T : C(Icc a b, Lp (Ambient q) 2 ((volume : Measure Plane).toSphere)),
      RepresentsNativePlanarRadialTrace u T ∧
      ∀ t : Icc a b, ∃ hSlice : MemLp (fun θ : NativeCircle => u (t.val • θ.val)) 2 ((volume : Measure Plane).toSphere),
        T t = hSlice.toLp (fun θ : NativeCircle => u (t.val • θ.val)) := by
  let σ := (volume : Measure Plane).toSphere
  obtain ⟨T, hT, _⟩ := StratificationTheory.exists_continuous_L2_trace_of_bounded_fiber_continuity
    σ hab (f := fun (p : NativeCircle × ℝ) => u (p.2 • p.1.val)) hMeas hCont hBound
  exact ⟨T, Eventually.of_forall fun t ht => hT ⟨t, ht.1.le, ht.2.le⟩, hT⟩

private theorem nativePlanarRadialTrace_of_annulus_piecewise {q : ℕ} {r R : ℝ} (hr : 0 < r)
    (u v : Plane → Ambient q)
    (Q : C(Icc r R, Lp (Ambient q) 2 ((volume : Measure Plane).toSphere)))
    (hQ : RepresentsNativePlanarRadialTrace v Q) :
    RepresentsNativePlanarRadialTrace (fun y => if ‖y‖ < r then u y else v y) Q := by
  filter_upwards [hQ] with t ht ht'
  have htpos : 0 < t := hr.trans ht'.1
  let F (θ : NativeCircle) := if ‖t • θ.val‖ < r then u (t • θ.val) else v (t • θ.val)
  have hEq : (fun θ : NativeCircle => v (t • θ.val)) =ᵐ[((volume : Measure Plane).toSphere)] F :=
    Eventually.of_forall fun θ => by
      have hN := mem_sphere_zero_iff_norm.mp θ.property
      have hRad : ‖t • θ.val‖ = t := by rw [norm_smul, Real.norm_of_nonneg htpos.le, hN, mul_one]
      simp only [F, hRad, if_neg (not_lt_of_ge ht'.1.le)]
  obtain ⟨hLp, hClass⟩ := ht ht'
  let hLF := hLp.ae_eq hEq
  exact ⟨hLF, hClass.trans (hLp.toLp_congr hLF hEq)⟩

/-- The original planar core and concentric annulus glue along their
common rim. The resulting disk keeps the outer annulus trace and the exact
sum of the original Dirichlet energies. -/
theorem memW12_planar_core_annulus_glue_of_lt {q : ℕ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (u v : Plane → Ambient q) (Du Dv : Plane → HarmonicMaps.Gradient 2 q)
    (hu : MemW12 (ballDomain (0 : Plane) r) u Du)
    (hv : MemW12 ⟨{y : Plane | ‖y‖ ∈ Ioo r R}, isOpen_Ioo.preimage continuous_norm⟩ v Dv)
    (P : C(Icc (r / 2) r, Lp (Ambient q) 2 ((volume : Measure Plane).toSphere)))
    (Q : C(Icc r R, Lp (Ambient q) 2 ((volume : Measure Plane).toSphere)))
    (hP : RepresentsNativePlanarRadialTrace u P) (hQ : RepresentsNativePlanarRadialTrace v Q)
    (hRim : P ⟨r, half_le_self hr.le, le_rfl⟩ =
      Q ⟨r, le_rfl, hrR.le⟩) :
    let f (y : Plane) := if ‖y‖ < r then u y else v y
    let Df (y : Plane) (i : Fin 2) := if ‖y‖ < r then Du y i else Dv y i
    MemW12 (ballDomain (0 : Plane) R) f Df ∧ RepresentsNativePlanarRadialTrace f Q ∧
      HarmonicMaps.dirichletEnergy Df (ball (0 : Plane) R) =
        HarmonicMaps.dirichletEnergy Du (ball (0 : Plane) r) +
          HarmonicMaps.dirichletEnergy Dv {y : Plane | ‖y‖ ∈ Ioo r R} := by
  let b := (r + R) / 2
  have hrb : r < b := by dsimp only [b]; linarith only [hrR]
  have hbR : b < R := by dsimp only [b]; linarith only [hrR]
  let Q' := Q.comp ⟨fun t : Icc r b => ⟨t.val, t.property.1, t.property.2.trans hbR.le⟩,
    continuous_subtype_val.subtype_mk _⟩
  have hQ' : RepresentsNativePlanarRadialTrace v Q' := by
    filter_upwards [hQ] with t ht ht'
    exact ht ⟨ht'.1, ht'.2.trans hbR⟩
  have hμ : (Measure.euclideanHausdorffMeasure (2 - 1) : Measure NativeCircle) = (volume : Measure Plane).toSphere :=
    StratificationTheory.euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide)
  have hv' : MemW12 ⟨{y : Plane | r < ‖y - 0‖ ∧ ‖y - 0‖ < R},
      isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm⟩ v Dv := by
    simpa only [sub_zero, mem_Ioo] using hv
  have hGlue := StratificationTheory.memW12_radial_trace_gluing (n := 2) (q := q) (le_refl 2)
    (0 : Plane) hr hrR u v Du Dv hu hv'
  dsimp only at hGlue
  rw [hμ] at hGlue
  simp only [zero_add, sub_zero] at hGlue
  have hMeet : P ⟨r, half_le_self hr.le, le_rfl⟩ = Q' ⟨r, le_rfl, hrb.le⟩ := hRim
  obtain ⟨hW, hE⟩ := hGlue P Q' hP hQ' hMeet
  let Df (y : Plane) (i : Fin 2) := if ‖y‖ < r then Du y i else Dv y i
  refine ⟨hW, nativePlanarRadialTrace_of_annulus_piecewise hr u v Q hQ, ?_⟩
  have hI : IntegrableOn (fun y => hsNormSq (Df y)) (ball (0 : Plane) R) := hW.integrable_hsNormSq
  have hU : IntegrableOn (fun y => hsNormSq (Du y)) (ball (0 : Plane) r) := hu.integrable_hsNormSq
  have hV : IntegrableOn (fun y => hsNormSq (Dv y)) {y : Plane | ‖y‖ ∈ Ioo r R} := hv.integrable_hsNormSq
  change HarmonicMaps.dirichletEnergy Df (ball (0 : Plane) R) =
    HarmonicMaps.dirichletEnergy Du (ball (0 : Plane) r) + HarmonicMaps.dirichletEnergy Dv {y : Plane | ‖y‖ ∈ Ioo r R}
  have hE' : (∫ y in ball (0 : Plane) R, hsNormSq (Df y)) =
       (∫ y in ball (0 : Plane) r, hsNormSq (Du y)) +
       (∫ y in {y : Plane | ‖y‖ ∈ Ioo r R}, hsNormSq (Dv y)) := hE
  rw [HarmonicMaps.dirichletEnergy_eq_ofReal_integral hI, HarmonicMaps.dirichletEnergy_eq_ofReal_integral hU,
    HarmonicMaps.dirichletEnergy_eq_ofReal_integral hV, hE',
    ENNReal.ofReal_add (integral_nonneg fun _ => hsNormSq_nonneg _)
      (integral_nonneg fun _ => hsNormSq_nonneg _)]

/-- The disk and annulus with inner radius half of the outer radius
retain their actual common trace and total Dirichlet energy. -/
theorem memW12_planar_core_annulus_glue {q : ℕ} {R : ℝ} (hR : 0 < R)
    (u v : Plane → Ambient q) (Du Dv : Plane → HarmonicMaps.Gradient 2 q)
    (hu : MemW12 (ballDomain (0 : Plane) (R / 2)) u Du)
    (hv : MemW12 ⟨{y : Plane | ‖y‖ ∈ Ioo (R / 2) R}, isOpen_Ioo.preimage continuous_norm⟩ v Dv)
    (P : C(Icc (R / 2 / 2) (R / 2), Lp (Ambient q) 2 ((volume : Measure Plane).toSphere)))
    (Q : C(Icc (R / 2) R, Lp (Ambient q) 2 ((volume : Measure Plane).toSphere)))
    (hP : RepresentsNativePlanarRadialTrace u P) (hQ : RepresentsNativePlanarRadialTrace v Q)
    (hRim : P ⟨R / 2, half_le_self (half_pos hR).le, le_rfl⟩ =
      Q ⟨R / 2, le_rfl, half_le_self hR.le⟩) :
    let f (y : Plane) := if ‖y‖ < R / 2 then u y else v y
    let Df (y : Plane) (i : Fin 2) := if ‖y‖ < R / 2 then Du y i else Dv y i
    MemW12 (ballDomain (0 : Plane) R) f Df ∧ RepresentsNativePlanarRadialTrace f Q ∧
      HarmonicMaps.dirichletEnergy Df (ball (0 : Plane) R) =
        HarmonicMaps.dirichletEnergy Du (ball (0 : Plane) (R / 2)) +
          HarmonicMaps.dirichletEnergy Dv {y : Plane | ‖y‖ ∈ Ioo (R / 2) R} :=
  memW12_planar_core_annulus_glue_of_lt (half_pos hR) (half_lt_self hR)
    u v Du Dv hu hv P Q hP hQ hRim

/-- The same radial split has exact additive volume integrals on the
disk, since the common rim has zero planar volume. -/
theorem lintegral_planar_core_annulus {q : ℕ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (u v : Plane → Ambient q) (φ : Ambient q → ℝ≥0∞) :
    (∫⁻ y in ball (0 : Plane) R, φ (if ‖y‖ < r then u y else v y)) =
      (∫⁻ y in ball (0 : Plane) r, φ (u y)) + ∫⁻ y in {y : Plane | ‖y‖ ∈ Ioo r R}, φ (v y) := by
  let A := ball (0 : Plane) r
  let B := {y : Plane | ‖y‖ ∈ Ioo r R}
  have hA : MeasurableSet A := measurableSet_ball
  have hB : MeasurableSet B := measurableSet_Ioo.preimage continuous_norm.measurable
  have hDis : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact (not_lt_of_ge (show r ≤ ‖x‖ from hxB.1.le)) (mem_ball_zero_iff.mp hxA)
  have hUnion : (A ∪ B : Set Plane) =ᵐ[(volume : Measure Plane)] (ball 0 R : Set Plane) := by
    filter_upwards [StratificationTheory.ae_norm_sub_ne_radius (0 : Plane) hr] with x hx
    simp only [sub_zero] at hx
    apply propext
    constructor
    · rintro (hxA | hxB)
      · exact ball_subset_ball hrR.le hxA
      · exact mem_ball_zero_iff.mpr (show ‖x‖ < R from hxB.2)
    · intro hxR
      by_cases h : ‖x‖ < r
      · exact Or.inl (mem_ball_zero_iff.mpr h)
      · exact Or.inr ⟨lt_of_le_of_ne (le_of_not_gt h) hx.symm, mem_ball_zero_iff.mp hxR⟩
  have hRestrict : (volume : Measure Plane).restrict (ball 0 R) = volume.restrict A + volume.restrict B :=
    (Measure.restrict_congr_set hUnion.symm).trans (Measure.restrict_union hDis hB)
  rw [hRestrict, lintegral_add_measure]
  congr 1
  · apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hA] with y hy
    rw [if_pos (mem_ball_zero_iff.mp hy)]
  · apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hB] with y hy
    rw [if_neg (not_lt_of_ge (show r ≤ ‖y‖ from hy.1.le))]

/-- The three actual weak graphs and the two common rim classes. -/
structure TerminalCylinderBoundaryData (q : ℕ) (R : ℝ) (hR : 0 < R) where
  lower : Plane → Ambient q
  upper : Plane → Ambient q
  wall : Plane → Ambient q
  lowerDerivative : Plane → HarmonicMaps.Gradient 2 q
  upperDerivative : Plane → HarmonicMaps.Gradient 2 q
  wallDerivative : Plane → HarmonicMaps.Gradient 2 q
  lower_memW12 : MemW12 (ballDomain (0 : Plane) R) lower lowerDerivative
  upper_memW12 : MemW12 (ballDomain (0 : Plane) R) upper upperDerivative
  wall_memW12 : MemW12 (terminalWallAnnulus R) wall wallDerivative
  lowerTrace : C(Icc (R / 2) R, Lp (Ambient q) 2 ((volume : Measure Plane).toSphere))
  upperTrace : C(Icc (R / 2) R, Lp (Ambient q) 2 ((volume : Measure Plane).toSphere))
  wallTrace : C(Icc R (2 * R), Lp (Ambient q) 2 ((volume : Measure Plane).toSphere))
  lowerTraceData : RepresentsNativePlanarRadialTrace lower lowerTrace
  upperTraceData : RepresentsNativePlanarRadialTrace upper upperTrace
  wallTraceData : RepresentsNativePlanarRadialTrace wall wallTrace
  lowerRim : lowerTrace ⟨R, half_le_self hR.le, le_rfl⟩ =
      wallTrace ⟨R, le_rfl, by linarith only [hR]⟩
  upperRim : upperTrace ⟨R, half_le_self hR.le, le_rfl⟩ =
      wallTrace ⟨2 * R, by linarith only [hR], le_rfl⟩

/-- The literal closed planar set used to recover the original trace
from a continuous representative. -/
def closedPlanarRadialCollar (a b : ℝ) : Set Plane := {y | ‖y‖ ∈ Icc a b}

/-- A continuous planar collar determines the genuine radial trace,
including the original classes at both rims. -/
theorem exists_nativePlanarRadialTrace_of_continuousOn_closedCollar {q : ℕ} {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) {u : Plane → Ambient q} (hu : ContinuousOn u (closedPlanarRadialCollar a b)) :
    ∃ T : C(Icc a b, Lp (Ambient q) 2 ((volume : Measure Plane).toSphere)),
      RepresentsNativePlanarRadialTrace u T ∧
      ∀ t, (T t : NativeCircle → Ambient q) =ᵐ[((volume : Measure Plane).toSphere)]
        (fun θ => u (t.val • θ.val)) := by
  let X := closedPlanarRadialCollar a b
  have hC : IsCompact X := (isCompact_closedBall (0 : Plane) b).of_isClosed_subset
    (isClosed_Icc.preimage continuous_norm) (fun y hy => mem_closedBall_zero_iff.mpr hy.2)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hu
  have hY (θ : NativeCircle) (t : ℝ) (ht : t ∈ Icc a b) : t • θ.val ∈ X := by
    have hθ := mem_sphere_zero_iff_norm.mp θ.property
    change ‖t • θ.val‖ ∈ Icc a b
    rwa [norm_smul, Real.norm_of_nonneg (ha.trans ht.1), hθ, mul_one]
  have hMeas : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      AEStronglyMeasurable (fun θ : NativeCircle => u (t • θ.val)) ((volume : Measure Plane).toSphere) := by
    refine Eventually.of_forall fun t ht => ?_
    have hrad : Continuous (fun θ : NativeCircle => t • θ.val) := by fun_prop
    have hc : ContinuousOn (fun θ : NativeCircle => u (t • θ.val)) univ :=
      hu.comp hrad.continuousOn (fun θ _ => hY θ t ⟨ht.1.le, ht.2.le⟩)
    simpa only [Measure.restrict_univ] using
      hc.aestronglyMeasurable (μ := (volume : Measure Plane).toSphere) MeasurableSet.univ
  have hCont : ∀ᵐ θ : NativeCircle ∂((volume : Measure Plane).toSphere),
      ContinuousOn (fun t => u (t • θ.val)) (Icc a b) :=
    Eventually.of_forall fun θ => hu.comp (continuous_id.smul continuous_const).continuousOn (fun t ht => hY θ t ht)
  have hB : ∀ᵐ θ : NativeCircle ∂((volume : Measure Plane).toSphere), ∀ t ∈ Icc a b, ‖u (t • θ.val)‖ ≤ M :=
    Eventually.of_forall fun θ t ht => hM _ (hY θ t ht)
  obtain ⟨T, hT, hVal⟩ := exists_nativePlanarRadialTrace_of_bounded_fiber_continuity hab hMeas hCont hB
  refine ⟨T, hT, fun t => ?_⟩
  obtain ⟨hs, hh⟩ := hVal t
  rw [hh]
  exact hs.coeFn_toLp

/-- Continuous, agreeing raw rim values supply the exact two common
native classes for three given planar weak graphs. -/
theorem exists_terminalCylinderBoundaryData_of_continuous_collars {q : ℕ} {R : ℝ} (hR : 0 < R)
    (u v w : Plane → Ambient q) (Du Dv Dw : Plane → HarmonicMaps.Gradient 2 q)
    (hu : MemW12 (ballDomain (0 : Plane) R) u Du) (hv : MemW12 (ballDomain (0 : Plane) R) v Dv)
    (hw : MemW12 (terminalWallAnnulus R) w Dw)
    (hUC : ContinuousOn u (closedPlanarRadialCollar (R / 2) R))
    (hVC : ContinuousOn v (closedPlanarRadialCollar (R / 2) R))
    (hWC : ContinuousOn w (closedPlanarRadialCollar R (2 * R)))
    (hLower : (fun θ : NativeCircle => u (R • θ.val)) =ᵐ[((volume : Measure Plane).toSphere)]
      fun θ => w (R • θ.val))
    (hUpper : (fun θ : NativeCircle => v (R • θ.val)) =ᵐ[((volume : Measure Plane).toSphere)]
      fun θ => w ((2 * R) • θ.val)) :
    ∃ D : TerminalCylinderBoundaryData q R hR,
      D.lower = u ∧ D.upper = v ∧ D.wall = w ∧
        D.lowerDerivative = Du ∧ D.upperDerivative = Dv ∧ D.wallDerivative = Dw := by
  obtain ⟨P, hP, hPval⟩ := exists_nativePlanarRadialTrace_of_continuousOn_closedCollar
    (half_pos hR).le (half_lt_self hR) hUC
  obtain ⟨Q, hQ, hQval⟩ := exists_nativePlanarRadialTrace_of_continuousOn_closedCollar
    (half_pos hR).le (half_lt_self hR) hVC
  have hR₂ : R < 2 * R := by linarith
  obtain ⟨S, hS, hSval⟩ := exists_nativePlanarRadialTrace_of_continuousOn_closedCollar hR.le hR₂ hWC
  have hLow : P ⟨R, half_le_self hR.le, le_rfl⟩ = S ⟨R, le_rfl, hR₂.le⟩ :=
    Lp.ext ((hPval ⟨R, half_le_self hR.le, le_rfl⟩).trans
      (hLower.trans (hSval ⟨R, le_rfl, hR₂.le⟩).symm))
  have hHigh : Q ⟨R, half_le_self hR.le, le_rfl⟩ = S ⟨2 * R, hR₂.le, le_rfl⟩ :=
    Lp.ext ((hQval ⟨R, half_le_self hR.le, le_rfl⟩).trans
      (hUpper.trans (hSval ⟨2 * R, hR₂.le, le_rfl⟩).symm))
  refine ⟨⟨u, v, w, Du, Dv, Dw, hu, hv, hw, P, Q, S, hP, hQ, hS, hLow, hHigh⟩,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

def terminalWallParameterRadius (R H z : ℝ) : ℝ :=
  R + R * ((z + H) / (2 * H))

/-- The literal map from the lateral annulus to the translated cylinder. -/
def terminalWallChart (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (R H : ℝ) (y : Plane) : Point :=
  c + axisChart B (R • NormedSpace.normalize y, (2 * H / R) * (‖y‖ - R) - H)

def planarQuarterTurn (y : Plane) : Plane :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then -y 1 else y 0)

/-- In the annular coordinates the wall area factor is 2H divided by the
parameter radius. The derivatives use the axial and circumferential scales. -/
def terminalWallDirichletDensity {q : ℕ} (R H : ℝ)
    (D : Plane → HarmonicMaps.Gradient 2 q) (y : Plane) : ℝ :=
  let θ := NormedSpace.normalize y
  let V (u : Plane) := ∑ i : Fin 2, u i • D y i
  (2 * H / ‖y‖) * ((R / (2 * H)) ^ 2 * ‖V θ‖ ^ 2 +
    (‖y‖ / R) ^ 2 * ‖V (planarQuarterTurn θ)‖ ^ 2)

/-- The sum of the three unhalved physical tangential energies. -/
def terminalCylinderSurfaceDirichlet {q : ℕ} {R : ℝ} {hR : 0 < R} (H : ℝ)
    (D : TerminalCylinderBoundaryData q R hR) : ℝ≥0∞ :=
  HarmonicMaps.dirichletEnergy D.lowerDerivative (ball 0 R) +
    HarmonicMaps.dirichletEnergy D.upperDerivative (ball 0 R) +
    ∫⁻ y in (terminalWallAnnulus R).val, ENNReal.ofReal (terminalWallDirichletDensity R H D.wallDerivative y)

/-- Integration of a function of the value with the original physical
surface measure in the three weak charts. -/
def terminalCylinderSurfaceValueIntegral {q : ℕ} {R : ℝ} {hR : 0 < R} (H : ℝ)
    (D : TerminalCylinderBoundaryData q R hR) (φ : Ambient q → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ y in ball (0 : Plane) R, φ (D.lower y)) +
    (∫⁻ y in ball (0 : Plane) R, φ (D.upper y)) +
    (∫⁻ y in (terminalWallAnnulus R).val, ENNReal.ofReal (2 * H / ‖y‖) * φ (D.wall y))

/-- The assigned boundary representative in the physical coordinates.
The selected rim values use the disk representative. -/
def terminalCylinderSurfaceValue {q : ℕ} {R : ℝ} {hR : 0 < R}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (H : ℝ)
    (D : TerminalCylinderBoundaryData q R hR) (x : Point) : Ambient q :=
  let yz := cylinderRecoveryCoordinates B c x
  if yz.2 ≤ -H then D.lower yz.1 else if H ≤ yz.2 then D.upper yz.1 else
    D.wall (terminalWallParameterRadius R H yz.2 • NormedSpace.normalize yz.1)

theorem terminalCylinderSurfaceValue_lower {q : ℕ} {R : ℝ} {hR : 0 < R}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (H : ℝ)
    (D : TerminalCylinderBoundaryData q R hR) (y : Plane) :
    terminalCylinderSurfaceValue B c H D (c + axisChart B (y, -H)) = D.lower y := by
  unfold terminalCylinderSurfaceValue
  rw [cylinderRecoveryCoordinates_axisChart]
  simp

theorem terminalCylinderSurfaceValue_upper {q : ℕ} {R : ℝ} {hR : 0 < R}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {H : ℝ} (hH : 0 < H)
    (D : TerminalCylinderBoundaryData q R hR) (y : Plane) :
    terminalCylinderSurfaceValue B c H D (c + axisChart B (y, H)) = D.upper y := by
  unfold terminalCylinderSurfaceValue
  rw [cylinderRecoveryCoordinates_axisChart]
  simp [show ¬ H ≤ -H by linarith]

theorem terminalCylinderSurfaceValue_wall {q : ℕ} {R : ℝ} {hR : 0 < R}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {H : ℝ} (hH : 0 < H)
    (D : TerminalCylinderBoundaryData q R hR) {y : Plane} (hy : y ∈ (terminalWallAnnulus R).val) :
    terminalCylinderSurfaceValue B c H D (terminalWallChart B c R H y) = D.wall y := by
  let z := (2 * H / R) * (‖y‖ - R) - H
  have hρ : ‖y‖ ∈ Ioo R (2 * R) := hy
  have hN : 0 < ‖y‖ := hR.trans hρ.1
  have hScale : 0 < 2 * H / R := by positivity
  have hlo : -H < z := by
    dsimp only [z]
    linarith only [mul_pos hScale (sub_pos.mpr hρ.1)]
  have hup : z < H := by
    have h := mul_lt_mul_of_pos_left (show ‖y‖ - R < R by linarith only [hρ.2]) hScale
    rw [div_mul_cancel₀ _ hR.ne'] at h
    dsimp only [z]
    linarith only [h]
  have hRad : terminalWallParameterRadius R H z = ‖y‖ := by
    dsimp only [terminalWallParameterRadius, z]
    field_simp [hR.ne', hH.ne']
    ring
  have hUnit : NormedSpace.normalize (R • NormedSpace.normalize y) = NormedSpace.normalize y := by
    have hy' : y ≠ 0 := norm_pos_iff.mp hN
    rw [NormedSpace.normalize, norm_smul, Real.norm_of_nonneg hR.le, NormedSpace.norm_normalize hy',
      mul_one, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  change terminalCylinderSurfaceValue B c H D (c + axisChart B (R • NormedSpace.normalize y, z)) = _
  unfold terminalCylinderSurfaceValue
  rw [cylinderRecoveryCoordinates_axisChart]
  simp only [not_le_of_gt hlo, if_false, not_le_of_gt hup, hRad, hUnit,
    NormedSpace.norm_smul_normalize]

def nativeTerminalSphereDirichlet {q : ℕ} (b : UnitTensorSphere → Ambient q)
    (hb : StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) b) : ℝ :=
  ∫ θ : UnitTensorSphere, ∑ i : Fin 3,
    ‖StratificationTheory.sphereGradient (by decide : 2 ≤ 3) b hb i θ‖ ^ 2 ∂tensorSphereMeasure

end Thesis.MeasureGeometry

namespace Thesis

open MeasureGeometry

/-- Standard finite surface trace gluing, followed by surface Sobolev and
area transport on the uniformly bi-Lipschitz terminal-cylinder chart. -/
def External.TerminalCylinderSurfaceSobolev : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ {q : ℕ} (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R)
    (D : TerminalCylinderBoundaryData q R hR),
    let F := terminalCylinderBallChart (B.orthonormal.norm_eq_one 2) c hR hLow hHigh
    let b (θ : UnitTensorSphere) := terminalCylinderSurfaceValue B c H D (F.symm (R • θ.val))
    ∃ hb : StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) b,
      ENNReal.ofReal (nativeTerminalSphereDirichlet b hb) ≤
        ENNReal.ofReal K * terminalCylinderSurfaceDirichlet H D ∧
      ∀ (φ : Ambient q → ℝ≥0∞), Measurable φ →
        (∫⁻ θ : UnitTensorSphere, φ (b θ) ∂tensorSphereMeasure) ≤
          ENNReal.ofReal (K / R ^ 2) * terminalCylinderSurfaceValueIntegral H D φ

end Thesis

namespace Thesis.MeasureGeometry

/-- Uniform range on the three original weak graphs. -/
def TerminalCylinderBoundaryData.Bounded {q : ℕ} {R : ℝ} {hR : 0 < R}
    (D : TerminalCylinderBoundaryData q R hR) (M : ℝ) : Prop :=
  (∀ᵐ y ∂volume.restrict (ball (0 : Plane) R), ‖D.lower y‖ ≤ M) ∧
  (∀ᵐ y ∂volume.restrict (ball (0 : Plane) R), ‖D.upper y‖ ≤ M) ∧
  (∀ᵐ y ∂volume.restrict (terminalWallAnnulus R).val, ‖D.wall y‖ ≤ M)

private theorem transport_terminalCylinderSurface_bound {q : ℕ} {R : ℝ} {hR : 0 < R} {H K M : ℝ}
    {D : TerminalCylinderBoundaryData q R hR} (hD : D.Bounded M)
    {b : UnitTensorSphere → Ambient q} (hb : StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) b)
    (hVal : ∀ φ : Ambient q → ℝ≥0∞, Measurable φ →
      (∫⁻ θ : UnitTensorSphere, φ (b θ) ∂tensorSphereMeasure) ≤
        ENNReal.ofReal (K / R ^ 2) * terminalCylinderSurfaceValueIntegral H D φ) :
    ∀ᵐ θ ∂tensorSphereMeasure, ‖b θ‖ ≤ M := by
  let S := {u : Ambient q | M < ‖u‖}
  let φ := S.indicator (fun _ => (1 : ℝ≥0∞))
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hφ : Measurable φ := measurable_const.indicator hS
  have hz {u : Ambient q} (hu : ‖u‖ ≤ M) : φ u = 0 :=
    indicator_of_notMem (show u ∉ S from not_lt_of_ge hu) _
  have h₁ : (∫⁻ y in ball (0 : Plane) R, φ (D.lower y)) = 0 := by
    rw [lintegral_congr_ae (hD.1.mono fun _ hy => hz hy), lintegral_zero]
  have h₂ : (∫⁻ y in ball (0 : Plane) R, φ (D.upper y)) = 0 := by
    rw [lintegral_congr_ae (hD.2.1.mono fun _ hy => hz hy), lintegral_zero]
  have h₃ : (∫⁻ y in (terminalWallAnnulus R).val, ENNReal.ofReal (2 * H / ‖y‖) * φ (D.wall y)) = 0 := by
    rw [lintegral_congr_ae (hD.2.2.mono fun y hy => by rw [hz hy, mul_zero]), lintegral_zero]
  have hZero : (∫⁻ θ : UnitTensorSphere, φ (b θ) ∂tensorSphereMeasure) = 0 := by
    have h := hVal φ hφ
    rw [terminalCylinderSurfaceValueIntegral, h₁, h₂, h₃, zero_add, zero_add, mul_zero] at h
    exact le_antisymm h zero_le
  have hA : AEMeasurable (φ ∘ b) tensorSphereMeasure := hφ.comp_aemeasurable hb.1.aemeasurable
  filter_upwards [(lintegral_eq_zero_iff' hA).mp hZero] with θ hθ
  by_contra! hB
  have hEq : (φ ∘ b) θ = 1 :=
    indicator_of_mem (show b θ ∈ S from hB) (fun _ : Ambient q => (1 : ℝ≥0∞))
  exact one_ne_zero (hEq.symm.trans hθ)

/-- The original physical surface energy, with the displayed weak
tangential derivatives and the actual potential on the three faces. -/
def terminalCylinderSurfacePenalizedEnergy (a : BulkCoefficients) (ε : ElasticScale)
    {R : ℝ} {hR : 0 < R} (H : ℝ) (D : TerminalCylinderBoundaryData 5 R hR) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / 2 : ℝ) * terminalCylinderSurfaceDirichlet H D +
    terminalCylinderSurfaceValueIntegral H D
      (fun u => ENNReal.ofReal ((ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm u)))

/-- Compatible physical disk and wall data give one terminal filling.
Its raw boundary values realize the chosen faces, and its energy is
bounded by one factor of the physical radius times the original surface cost. -/
theorem exists_penalized_terminalCylinder_fill_of_boundaryData (a : BulkCoefficients)
    (hSurface : External.TerminalCylinderSurfaceSobolev) (hTransport : External.AmbientBiLipschitzSobolevPullback3) :
    ∃ K : ℝ, 0 < K ∧ ∀ (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
      {R H : ℝ} (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R)
      (ε : ElasticScale) (D : TerminalCylinderBoundaryData 5 R hR) (M : ℝ), D.Bounded M →
      let U := terminalCylinderCap (B 2) c R H
      let F := terminalCylinderBallChart (B.orthonormal.norm_eq_one 2) c hR hLow hHigh
      ∃ (w : Point → S0) (Dw : Point → Thesis.Gradient) (T : RadialL2Trace (R / 2) R),
        MemH1 U w Dw ∧
          EqOn w (frobeniusCoordinateEquiv.symm ∘ terminalCylinderSurfaceValue B c H D) (frontier U) ∧
          RepresentsRadialL2Trace 0 (w ∘ F.symm) T ∧
          (∀ t, (T t : UnitTensorSphere → Ambient 5) =ᵐ[tensorSphereMeasure]
            fun θ => terminalCylinderSurfaceValue B c H D (F.symm (R • θ.val))) ∧
          (∀ᵐ x ∂volume.restrict U, ‖w x‖ ≤ M) ∧
          energy a ε U w Dw ≤ ENNReal.ofReal (K * R) * terminalCylinderSurfacePenalizedEnergy a ε H D := by
  obtain ⟨C, hC, hSurf⟩ := hSurface
  obtain ⟨K, hK, hFill⟩ := exists_penalized_terminalCylinder_fill a hTransport
  refine ⟨K * C, mul_pos hK hC, ?_⟩
  intro B c R H hR hLow hHigh ε D M hD U F
  let b₀ (θ : UnitTensorSphere) := terminalCylinderSurfaceValue B c H D (F.symm (R • θ.val))
  let b : UnitTensorSphere → S0 := frobeniusCoordinateEquiv.symm ∘ b₀
  obtain ⟨hb₀, hDir, hVal⟩ := hSurf B c hR hLow hHigh D
  have hBb : ∀ᵐ θ ∂tensorSphereMeasure, ‖b₀ θ‖ ≤ M := transport_terminalCylinderSurface_bound hD hb₀ hVal
  have hbEq : (fun θ => frobeniusCoordinateEquiv (b θ)) = b₀ :=
    funext fun θ => frobeniusCoordinateEquiv.apply_symm_apply _
  have hb : MemSphereH1 b := by
    change StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (b θ))
    rw [hbEq]
    exact hb₀
  have hB : ∀ᵐ θ ∂tensorSphereMeasure, ‖b θ‖ ≤ M := by
    simpa only [b, Function.comp_apply, LinearIsometryEquiv.norm_map] using hBb
  letI : IsFiniteMeasure tensorSphereMeasure := by
    change IsFiniteMeasure
      (Measure.euclideanHausdorffMeasure (3 - 1) : Measure (sphere (0 : Point) 1))
    rw [StratificationTheory.euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 3)]
    infer_instance
  let φ (u : Ambient 5) := ENNReal.ofReal ((ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm u))
  have hφ : Measurable φ := (ENNReal.continuous_ofReal.comp
    (((contDiff_bulkPotential a).continuous.comp frobeniusCoordinateEquiv.symm.continuous).const_mul _)).measurable
  have hBMeas : AEStronglyMeasurable b tensorSphereMeasure :=
    frobeniusCoordinateEquiv.symm.continuous.comp_aestronglyMeasurable hb₀.1.aestronglyMeasurable
  have hF := (integrable_bulkPotential_of_ae_norm_bound a M hBMeas hB).const_mul ((ε : ℝ)⁻¹ ^ 2)
  have hFpos (θ : UnitTensorSphere) : 0 ≤ (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (b θ) :=
    mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _)
  have hBulk : ENNReal.ofReal (sphereScaledBulkEnergy a ε b) ≤
      ENNReal.ofReal (C / R ^ 2) * terminalCylinderSurfaceValueIntegral H D φ := by
    unfold sphereScaledBulkEnergy
    rw [ofReal_integral_eq_lintegral_ofReal hF (Eventually.of_forall hFpos)]
    exact hVal φ hφ
  have hGradEq : sphereGradientEnergy b hb = nativeTerminalSphereDirichlet b₀ hb₀ := by
    have h := (StratificationTheory.sphereGradient_characterization (by decide : 2 ≤ 3) b₀ hb₀).2.2
      (fun θ => frobeniusCoordinateEquiv (b θ)) hb (Eventually.of_forall fun θ => (congrFun hbEq θ).symm)
    unfold sphereGradientEnergy nativeTerminalSphereDirichlet
    rw [h]
  have hDE : ENNReal.ofReal (sphereGradientEnergy b hb) ≤
      ENNReal.ofReal C * terminalCylinderSurfaceDirichlet H D := by rw [hGradEq]; exact hDir
  have hCO : ENNReal.ofReal (R ^ 2) * ENNReal.ofReal (C / R ^ 2) = ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_mul (sq_nonneg R)]
    congr 1
    field_simp
  have hCost : ENNReal.ofReal
      ((1 / 2 : ℝ) * sphereGradientEnergy b hb + R ^ 2 * sphereScaledBulkEnergy a ε b) ≤
      ENNReal.ofReal C * terminalCylinderSurfacePenalizedEnergy a ε H D := by
    rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) (nonneg_sphereGradientEnergy b hb))
      (mul_nonneg (sq_nonneg _) (nonneg_sphereScaledBulkEnergy a ε b)),
      ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ)), ENNReal.ofReal_mul (sq_nonneg R),
      terminalCylinderSurfacePenalizedEnergy, mul_add, mul_left_comm (ENNReal.ofReal C)]
    exact add_le_add (mul_le_mul_right hDE _) ((mul_le_mul_right hBulk _).trans_eq
      (by rw [← mul_assoc, hCO]))
  obtain ⟨w, Dw, T, hw, hBoundary, hTrace, hT, hRange, hEnergy⟩ :=
    hFill (B.orthonormal.norm_eq_one 2) c hR hLow hHigh ε b hb M hB
  refine ⟨w, Dw, T, hw, ?_, hTrace, ?_, hRange, ?_⟩
  · intro x hx
    have hSphere : F x ∈ sphere (0 : Point) R := by
      rw [terminalCylinderCap_frontier_eq_preimage_sphere (B.orthonormal.norm_eq_one 2) c hR hLow hHigh] at hx
      exact hx
    have hNorm := mem_sphere_zero_iff_norm.mp hSphere
    let θ : UnitTensorSphere := ⟨R⁻¹ • F x, mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), hNorm, inv_mul_cancel₀ hR.ne'])⟩
    have hRθ : R • θ.val = F x := by
      change R • (R⁻¹ • F x) = _
      rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    have hEq := hBoundary θ
    rw [hRθ, Homeomorph.symm_apply_apply] at hEq
    exact hEq.trans (by dsimp only [b, Function.comp_apply, b₀]; rw [hRθ, Homeomorph.symm_apply_apply])
  · intro t
    rw [hT t]
    exact hb.1.coeFn_toLp.trans (Eventually.of_forall fun θ => congrFun hbEq θ)
  · refine hEnergy.trans ?_
    rw [ENNReal.ofReal_mul (mul_nonneg hK.le hR.le)]
    refine (mul_le_mul_right hCost _).trans_eq ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hK.le hR.le)]
    congr 2
    ring

end Thesis.MeasureGeometry

end
