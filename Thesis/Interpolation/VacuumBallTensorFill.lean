module

public import Thesis.Interpolation.VacuumTwoSphereExtension
public import Thesis.Interpolation.PenalizedShell
import StratificationTheory.Foundation.RadialTraceCompatibility
import StratificationTheory.Foundation.RadialPiecewiseTrace
import StratificationTheory.Foundation.SphereAEClasses
import HarmonicMaps.EnergyLemmas
import HarmonicMaps.SobolevRestriction

/-! Tensor-valued vacuum filling with the radial trace used by variational comparison. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ENNReal Matrix.Norms.Frobenius

namespace Thesis

private theorem extend_unitBall_radialL2Trace {w : Point → S0} {D : Point → Gradient}
    (hw : MemH1 (ball (0 : Point) 1) w D) {b : ℝ} (hb : b < 1)
    (K : RadialL2Trace b 1) (hK : RepresentsRadialL2Trace 0 w K) :
    ∃ J : RadialL2Trace (1 / 2) 1, RepresentsRadialL2Trace 0 w J ∧
      J ⟨1, by norm_num, le_rfl⟩ = K ⟨1, hb.le, le_rfl⟩ := by
  let a : ℝ := 1 / 2
  let m := max a b
  have hm : m < 1 := max_lt (by norm_num) hb
  let r := (m + 1) / 2
  have hm_r : m < r := by dsimp only [r]; linarith
  have ha_r : a < r := (le_max_left _ _).trans_lt hm_r
  have hb_r : b < r := (le_max_right _ _).trans_lt hm_r
  have hr : r < 1 := by dsimp only [r]; linarith
  have hB : closedBall (0 : Point) r ⊆ ball 0 1 := closedBall_subset_ball hr
  let Ω := ballDomain (0 : Point) 1
  have hwLoc : MemH1Loc (ball (0 : Point) 1) w D :=
    (memH1Loc_iff_memW12Loc Ω w D).2 ((memH1_iff_memW12 Ω w D).1 hw).to_memW12Loc
  obtain ⟨H, hH, _⟩ := existsUnique_radialL2Trace_of_memH1Loc isOpen_ball hwLoc
    (0 : Point) (by norm_num : 0 < a) ha_r hB
  let K' := restrict_radialL2Trace K hb_r.le le_rfl
  have hK' := hK.restrict hb_r.le (le_refl (1 : ℝ))
  have hAgree := radial_representatives_eq_on_closed_overlap (n := 3) (q := 5)
    (u := frobeniusField w) (0 : Point) hm_r (le_max_left a b) (le_refl r)
    (le_max_right a b) hr.le H K hH hK ⟨r, hm_r.le, le_rfl⟩
  have hMatch : H ⟨r, ha_r.le, le_rfl⟩ = K' ⟨r, le_rfl, hr.le⟩ := hAgree
  obtain ⟨J, _, hRight, hRaw⟩ := exists_radial_trace_piecewise (0 : Point) tensorSphereMeasure
    (by norm_num : 0 < a) ha_r hr (frobeniusField w) (frobeniusField w) H K' hH hK' hMatch
  refine ⟨J, ?_, hRight ⟨1, hr.le, le_rfl⟩⟩
  simpa only [ite_self, RepresentsRadialL2Trace] using hRaw

/-- The two-sphere extension retains the original tensor trace, including
an almost-everywhere vacuum-valued representative, and the exact `1/2`
normalization of the comparison energy. -/
theorem exists_vacuum_twoSphere_tensor_fill (a : BulkCoefficients)
    (hDense : External.SmoothVacuumSphereDensity a)
    (hP : External.QuaternionSpherePoincare 3 (by decide : 2 ≤ 3)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : UnitTensorSphere → S0) (hp : MemSphereH1 p),
      (∀ᵐ θ ∂tensorSphereMeasure, p θ ∈ vacuum a) →
      ∃ (w : Point → S0) (D : Point → Thesis.Gradient) (H : RadialL2Trace (1 / 2) 1),
        MemH1 (ball (0 : Point) 1) w D ∧ TakesVacuumValues a (ball (0 : Point) 1) w ∧
        RepresentsRadialL2Trace 0 w H ∧
        H ⟨1, by norm_num, le_rfl⟩ = hp.1.toLp (fun θ => frobeniusCoordinateEquiv (p θ)) ∧
        dirichletEnergy (ball (0 : Point) 1) D ≤
          ENNReal.ofReal (C * Real.sqrt (sphereGradientEnergy p hp)) := by
  classical
  obtain ⟨C, hC, hFill⟩ := exists_vacuum_twoSphere_extension a hDense hP
  refine ⟨C / 2, div_pos hC (by norm_num), ?_⟩
  intro p hp hVac
  obtain ⟨z, hz⟩ := vacuum_nonempty a
  let Q (θ : UnitTensorSphere) : vacuum a := if h : p θ ∈ vacuum a then ⟨p θ, h⟩ else ⟨z, hz⟩
  have hEq : (fun θ => frobeniusCoordinateEquiv (p θ)) =ᵐ[tensorSphereMeasure]
      fun θ => frobeniusCoordinateEquiv (Q θ).val := by
    filter_upwards [hVac] with θ hθ
    dsimp only [Q]
    rw [dif_pos hθ]
  have hQ : MemSphereW12 (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (Q θ).val) :=
    memSphereW12_congr_ae (by decide : 2 ≤ 3) hp hEq
  let base : UnitTensorSphere := ⟨EuclideanSpace.single 0 1, by
    rw [mem_sphere_zero_iff_norm, PiLp.norm_single, norm_one]⟩
  obtain ⟨b, hb, w, Dw, K, hb₀, hW, hWV, hTrace, hEnd, hE⟩ := hFill base Q hQ
  let f (x : Point) := frobeniusCoordinateEquiv.symm (w x)
  let D (x : Point) (i : Fin 3) := frobeniusCoordinateEquiv.symm (Dw x i)
  have hF : frobeniusField f = w := funext fun x => frobeniusCoordinateEquiv.apply_symm_apply (w x)
  have hD : frobeniusGradient D = Dw := funext fun x => funext fun i =>
    frobeniusCoordinateEquiv.apply_symm_apply (Dw x i)
  have hf : MemH1 (ball (0 : Point) 1) f D := by
    apply (memH1_iff_memW12 (ballDomain (0 : Point) 1) f D).2
    rwa [hF, hD]
  have hFK : RepresentsRadialL2Trace 0 f K := by
    unfold RepresentsRadialL2Trace
    dsimp only
    rw [hF]
    simpa only [RepresentsVacuumBallTrace, zero_add, unitBoundarySurface, Nat.reduceSub] using hTrace
  obtain ⟨H, hH, hHR⟩ := extend_unitBall_radialL2Trace hf hb K hFK
  have hEnergyEq : vacuumSphereGradientEnergy (by decide : 2 ≤ 3) Q hQ = sphereGradientEnergy p hp := by
    have hg := (sphereGradient_characterization (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (p θ)) hp).2.2
      (fun θ => frobeniusCoordinateEquiv (Q θ).val) hQ hEq
    simp only [vacuumSphereGradientEnergy, sphereGradientEnergy, hg, unitBoundarySurface, Nat.reduceSub]
  refine ⟨f, D, H, hf, hWV, hH, hHR.trans (hEnd.trans (MemLp.toLp_congr hQ.1 hp.1 hEq.symm)), ?_⟩
  have hI : IntegrableOn (fun x => hsNormSq (Dw x)) (ball (0 : Point) 1) := hW.integrable_hsNormSq
  rw [dirichletEnergy_eq_half_upstream, hD, HarmonicMaps.dirichletEnergy_eq_ofReal_integral hI]
  rw [hEnergyEq] at hE
  rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  rw [show C / 2 * Real.sqrt (sphereGradientEnergy p hp) =
    (1 / 2 : ℝ) * (C * Real.sqrt (sphereGradientEnergy p hp)) by ring]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hE (by norm_num))

end Thesis
