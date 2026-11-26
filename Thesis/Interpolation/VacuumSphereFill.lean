module

public import Thesis.Interpolation.QuaternionSphereFill
public import Thesis.Variational.VacuumExtension
import StratificationTheory.Foundation.CylinderPostcomposition
import StratificationTheory.Foundation.AngularL2Membership
import StratificationTheory.Interpolation.RadialCutoffConstruction
import HarmonicMaps.EnergyLemmas

/-! The quaternion cover transfers a sphere filling and its genuine trace to the vacuum. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace Thesis

/-- The frozen polynomial has a smooth ambient continuation with bounded
derivative which agrees with the actual cover on the quaternion sphere. -/
theorem exists_boundedDerivative_vacuumCover (a : BulkCoefficients) :
    ∃ (L : ℝ) (F : Ambient 4 → Ambient 5), 0 < L ∧ ContDiff ℝ ∞ F ∧
      (∀ z, ‖fderiv ℝ F z‖ ≤ L) ∧
      (∀ z : Sphere3, F z.val = frobeniusCoordinateEquiv (cover a z)) := by
  obtain ⟨χ, hχ, hχK, _, _, hχOne, _, _, _⟩ :=
    StratificationTheory.Interpolation.exists_quantitative_radial_cutoff
      (n := 4) (0 : QuaternionCoordinates) (r := 1) (ε := 1) zero_lt_one zero_lt_one
  let P := fun z : Ambient 4 => frobeniusCoordinateEquiv (ambientQuaternionCover a z)
  have hP : ContDiff ℝ ∞ P := frobeniusCoordinateEquiv.toContinuousLinearMap.contDiff.comp
    (contDiff_ambientQuaternionCover a)
  let F := fun z : Ambient 4 => χ z • P z
  have hF : ContDiff ℝ ∞ F := hχ.smul hP
  have hSupp : tsupport F ⊆ tsupport χ := by
    apply closure_minimal _ (isClosed_tsupport χ)
    intro x hx
    apply subset_closure
    intro h
    exact hx (by change χ x • P x = 0; rw [h, zero_smul])
  have hFSupp : HasCompactSupport F := hχK.of_isClosed_subset (isClosed_tsupport F) hSupp
  have hDCont := hF.continuous_fderiv (by simp)
  obtain ⟨L, hL⟩ := (hFSupp.fderiv (𝕜 := ℝ)).exists_bound_of_continuousOn hDCont.continuousOn
  refine ⟨max 1 L, F, lt_of_lt_of_le zero_lt_one (le_max_left _ _), hF, ?_, ?_⟩
  · intro z
    by_cases hz : z ∈ tsupport (fderiv ℝ F)
    · exact (hL _ hz).trans (le_max_right _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact zero_le_one.trans (le_max_left _ _)
  · intro z
    have hz := sphere_subset_closedBall z.property
    change χ z.val • P z.val = _
    rw [hχOne _ hz, one_smul]
    simp only [P, ambientQuaternionCover, cover]

abbrev VacuumBallTrace (n : ℕ) (b : ℝ) :=
  C(Icc b 1, Lp (Ambient 5) 2 (unitBoundarySurface n))

@[expose] def RepresentsVacuumBallTrace {n : ℕ} {b : ℝ} (u : Domain n → Ambient 5)
    (H : VacuumBallTrace n b) : Prop :=
  ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo b 1,
    ∃ htLp : MemLp (fun θ : UnitBoundarySphere n => u (t • θ.val)) 2 (unitBoundarySurface n),
      H ⟨t, ht.1.le, ht.2.le⟩ = htLp.toLp _

/-- Postcomposition by the actual cover preserves the actual boundary datum
and controls the volume Dirichlet energy by the quaternion energy. -/
theorem exists_vacuum_ball_fill_of_quaternion_fill (a : BulkCoefficients) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (_hn : 2 ≤ n) (v : UnitBoundarySphere n → Sphere3)
      (hv : MemLp (fun θ => (v θ).val) 2 (unitBoundarySurface n))
      {b : ℝ} (hb : b < 1) {u : Domain n → Ambient 4} {Du : Domain n → HarmonicMaps.Gradient n 4}
      (H : QuaternionBallTrace n b), MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖u x‖ = 1) →
      RepresentsQuaternionBallTrace u H → H ⟨1, hb.le, le_rfl⟩ = hv.toLp _ →
      ∃ (w : Domain n → Ambient 5) (Dw : Domain n → HarmonicMaps.Gradient n 5)
        (J : VacuumBallTrace n b),
        MemW12 (ballDomain (0 : Domain n) 1) w Dw ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), frobeniusCoordinateEquiv.symm (w x) ∈ vacuum a) ∧
        RepresentsVacuumBallTrace w J ∧
        (∃ hbLp : MemLp (fun θ => frobeniusCoordinateEquiv (cover a (v θ))) 2 (unitBoundarySurface n),
          J ⟨1, hb.le, le_rfl⟩ = hbLp.toLp _) ∧
        (∫ x in ball (0 : Domain n) 1, hsNormSq (Dw x)) ≤
          C * (∫ x in ball (0 : Domain n) 1, hsNormSq (Du x)) := by
  obtain ⟨L, F, hL, hF, hDF, hFCover⟩ := exists_boundedDerivative_vacuumCover a
  refine ⟨L ^ 2, sq_pos_of_pos hL, ?_⟩
  intro n hn v hv b hb u Du H hu hU hTrace hBoundary
  let Ω := ballDomain (0 : Domain n) 1
  letI : IsFiniteMeasure (volume.restrict Ω.val) := by
    refine ⟨?_⟩
    change ((volume : Measure (Domain n)).restrict (ball 0 1)) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  let σ := unitBoundarySurface n
  letI : IsFiniteMeasure σ := by
    dsimp only [σ, unitBoundarySurface]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by omega : 0 < n)]
    infer_instance
  let w := F ∘ u
  let Dw : Domain n → HarmonicMaps.Gradient n 5 := fun x i => fderiv ℝ F (u x) (Du x i)
  have hw : MemW12 Ω w Dw := StratificationTheory.MemW12.postcompose_finite hu F hF L hDF
  let T : C(Lp (Ambient 4) 2 σ, Lp (Ambient 5) 2 σ) :=
    ⟨fun f => (memLp_postcomposition (Lp.memLp f) hF hDF).toLp (F ∘ f),
      continuous_L2_smooth_postcomposition σ F hF L hDF⟩
  let J : VacuumBallTrace n b := T.comp H
  have hT {p : UnitBoundarySphere n → Ambient 4} (hp : MemLp p 2 σ) :
      T (hp.toLp p) = (memLp_postcomposition hp hF hDF).toLp (F ∘ p) := by
    exact MemLp.toLp_congr (memLp_postcomposition (Lp.memLp (hp.toLp p)) hF hDF)
      (memLp_postcomposition hp hF hDF) (hp.coeFn_toLp.mono fun x hx => congrArg F hx)
  refine ⟨w, Dw, J, hw, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hU] with x hx
    let z : Sphere3 := ⟨u x, by simpa only [mem_sphere, dist_zero_right] using hx⟩
    change frobeniusCoordinateEquiv.symm (F z.val) ∈ vacuum a
    rw [hFCover, LinearIsometryEquiv.symm_apply_apply]
    exact cover_mem_vacuum a z
  · filter_upwards [hTrace] with s hs hsr
    obtain ⟨hsLp, hEq⟩ := hs hsr
    let hF' := memLp_postcomposition hsLp hF hDF
    refine ⟨hF', ?_⟩
    change T (H ⟨s, hsr.1.le, hsr.2.le⟩) = _
    rw [hEq]
    exact hT hsLp
  · let hF' := memLp_postcomposition hv hF hDF
    have hEq : (F ∘ fun θ => (v θ).val) =ᵐ[σ]
        fun θ => frobeniusCoordinateEquiv (cover a (v θ)) :=
      ae_of_all _ fun θ => hFCover (v θ)
    let hB' := hF'.ae_eq hEq
    refine ⟨hB', ?_⟩
    change T (H ⟨1, hb.le, le_rfl⟩) = _
    rw [hBoundary]
    exact (hT hv).trans (MemLp.toLp_congr hF' hB' hEq)
  · rw [← integral_const_mul]
    apply integral_mono_ae hw.integrable_hsNormSq (hu.integrable_hsNormSq.const_mul _)
    filter_upwards [] with x
    simp only [hsNormSq, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      have hCol : ‖Dw x i‖ ≤ L * ‖Du x i‖ := (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hDF (u x)) (norm_nonneg _))
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hCol 2

end Thesis
