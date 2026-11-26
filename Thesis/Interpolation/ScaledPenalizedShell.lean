module

public import Thesis.Interpolation.PenalizedShell
public import Thesis.Variational.AffinePenalizedEnergy
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Exact physical rescaling of a unit penalized annular layer. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Matrix.Norms.Frobenius

namespace Thesis

/-- An annular layer on the unit sphere transfers to the physical shell,
with both trace classes and the exact three-dimensional energy scale. -/
theorem exists_physical_penalized_annular_layer (a : BulkCoefficients) (ε ε' : ElasticScale)
    (c : Point) {s r : ℝ} (hs : 0 < s) (_hr : 0 < r) (hrs : r < 1)
    (hε : (ε' : ℝ) = (ε : ℝ) / s)
    {v u : UnitTensorSphere → S0} {hv : MemSphereH1 v} {hu : MemSphereH1 u}
    (W : SphereAnnularLayer r 1 hrs.le v u hv hu) :
    ∃ (w : Point → S0) (D : Point → Gradient) (H : RadialL2Trace (s * r) s),
      MemH1 (radialAnnulus c (s * r) s) w D ∧ RepresentsRadialL2Trace c w H ∧
      H ⟨s * r, le_rfl, by simpa only [mul_one] using mul_le_mul_of_nonneg_left hrs.le hs.le⟩ =
        hv.1.toLp (fun θ => frobeniusCoordinateEquiv (v θ)) ∧
      H ⟨s, by simpa only [mul_one] using mul_le_mul_of_nonneg_left hrs.le hs.le, le_rfl⟩ =
        hu.1.toLp (fun θ => frobeniusCoordinateEquiv (u θ)) ∧
      energy a ε (radialAnnulus c (s * r) s) w D = ENNReal.ofReal s *
        energy a ε' (radialAnnulus 0 r 1) W.toFun W.gradient := by
  let t := s⁻¹
  have ht : 0 < t := inv_pos.2 hs
  have hsr : s * r < s := by simpa only [mul_one] using mul_lt_mul_of_pos_left hrs hs
  have htl : t * (s * r) = r := by dsimp only [t]; rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  have htu : t * s = 1 := inv_mul_cancel₀ hs.ne'
  let A (x : Point) := t • (x - c)
  have hPre : A ⁻¹' radialAnnulus 0 r 1 = radialAnnulus c (s * r) s := by
    ext x
    change (r < ‖t • (x - c) - 0‖ ∧ ‖t • (x - c) - 0‖ < 1) ↔ (s * r < ‖x - c‖ ∧ ‖x - c‖ < s)
    simp only [sub_zero, norm_smul, Real.norm_of_nonneg ht.le]
    have hLow : r < t * ‖x - c‖ ↔ s * r < ‖x - c‖ := by
      nth_rw 1 [← htl]
      exact mul_lt_mul_iff_of_pos_left ht
    have hUp : t * ‖x - c‖ < 1 ↔ ‖x - c‖ < s := by
      rw [← htu]
      exact mul_lt_mul_iff_of_pos_left ht
    rw [hLow, hUp]
  have hU : IsOpen (radialAnnulus (0 : Point) r 1) := isOpen_radialAnnulus 0 r 1
  have hFin : volume (radialAnnulus (0 : Point) r 1) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_ne_top (measure_mono (fun x hx => mem_ball_iff_norm.mpr hx.2))
  let w := W.toFun ∘ A
  let D (x : Point) (i : Fin 3) := t • W.gradient (A x) i
  have hw : MemH1 (radialAnnulus c (s * r) s) w D := by
    have h := memH1_affine_preimage hU hFin W.sobolev (0 : Point) c ht
    simp only [zero_add] at h
    rwa [hPre] at h
  have hT (x : Icc (s * r) s) : t * x.val ∈ Icc r 1 := by
    constructor
    · exact htl.ge.trans (mul_le_mul_of_nonneg_left x.property.1 ht.le)
    · exact (mul_le_mul_of_nonneg_left x.property.2 ht.le).trans htu.le
  let T : C(Icc (s * r) s, Icc r 1) :=
    ⟨fun x => ⟨t * x.val, hT x⟩, (continuous_const.mul continuous_subtype_val).subtype_mk hT⟩
  let H := W.trace.comp T
  have hRaw : RepresentsRadialL2Trace c w H := by
    have hPull := ((volume : Measure ℝ).quasiMeasurePreserving_smul ht.ne').ae W.traceData
    unfold RepresentsRadialL2Trace at hPull ⊢
    dsimp only [smul_eq_mul] at hPull
    filter_upwards [hPull] with p hp hps
    have hp' : t * p ∈ Ioo r 1 := by
      constructor
      · rw [← htl]; exact mul_lt_mul_of_pos_left hps.1 ht
      · rw [← htu]; exact mul_lt_mul_of_pos_left hps.2 ht
    obtain ⟨hLp, hEq⟩ := hp hp'
    have hFun : (fun θ : UnitTensorSphere => frobeniusField w (c + p • θ.val)) =
        fun θ : UnitTensorSphere => frobeniusField W.toFun (0 + (t * p) • θ.val) := by
      funext θ
      simp only [w, A, frobeniusField, Function.comp_apply, add_sub_cancel_left, smul_smul, zero_add]
    rw [hFun]
    exact ⟨hLp, hEq⟩
  refine ⟨w, D, H, hw, hRaw, ?_, ?_, ?_⟩
  · have h := congrArg W.trace (Subtype.ext htl : T ⟨s * r, le_rfl, hsr.le⟩ = ⟨r, le_rfl, hrs.le⟩)
    exact h.trans W.inner_eq
  · have h := congrArg W.trace (Subtype.ext htu : T ⟨s, hsr.le, le_rfl⟩ = ⟨1, hrs.le, le_rfl⟩)
    exact h.trans W.outer_eq
  · have hε₀ : (ε : ℝ) = (ε' : ℝ) / t := by rw [hε]; dsimp only [t]; field_simp
    have he := energy_affine_preimage a ε' ε ht hε₀ (0 : Point) c (radialAnnulus 0 r 1)
      W.toFun W.gradient
    simp only [zero_add] at he
    change energy a ε (A ⁻¹' radialAnnulus 0 r 1) w D = _ at he
    rw [hPre] at he
    simpa only [t, inv_inv] using he

end Thesis
