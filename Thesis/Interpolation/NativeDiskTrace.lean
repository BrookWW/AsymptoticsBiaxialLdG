module

public import Thesis.Interpolation.VacuumSphereFill
import StratificationTheory.Foundation.AmbientRadialTrace
import StratificationTheory.Foundation.CoordinateL2Trace
import StratificationTheory.Foundation.AngularL2Membership
import HarmonicMaps.Analysis.L2TranslationContinuity

/-! The native full radial (L^2) trace on the closed half-radius collar. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace Thesis

private theorem memLp_native_disk_full_radial_product {E : Type*} [NormedAddCommGroup E]
    {f : Plane → E} (hf : MemLp f 2 (volume.restrict (ball (0 : Plane) 1))) :
    MemLp (fun p : UnitBoundarySphere 2 × ℝ => f (p.2 • p.1.val)) 2
      ((unitBoundarySurface 2).prod (volume.restrict (Icc (1 / 2 : ℝ) 1))) := by
  let F := (ball (0 : Plane) 1).indicator f
  have hF : MemLp F 2 (volume : Measure Plane) := memLp_zeroExtension measurableSet_ball hf
  have hProduct := memLp_two_radial_product_ball (by decide : 0 < 2) (c := (0 : Plane))
    (a := 1 / 2) (b := 1) (R := 2) (by norm_num) (by norm_num)
    (hF.mono_measure (Measure.restrict_le_self (s := ball (0 : Plane) 2)))
  have hZ : MemLp (fun p : UnitBoundarySphere 2 × ℝ => F (p.2 • p.1.val)) 2
      ((unitBoundarySurface 2).prod (volume.restrict (Icc (1 / 2 : ℝ) 1))) := by
    simpa only [zero_add] using hProduct
  apply hZ.ae_eq
  have hRay : ∀ᵐ r ∂volume.restrict (Icc (1 / 2 : ℝ) 1), r ∈ Ioo (1 / 2 : ℝ) 1 := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hRay] with p hp
  apply Set.indicator_of_mem
  rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (le_of_lt ((by norm_num : (0 : ℝ) < 1 / 2).trans hp.1)),
    mem_sphere_zero_iff_norm.mp p.1.property, mul_one]
  exact hp.2

private theorem disk_trace_test_support_local {φ : ℝ → ℝ}
    (hφ : HasCompactSupport φ) (hSupp : tsupport φ ⊆ Ioo (1 / 2 : ℝ) 1) :
    ∃ b : ℝ, 1 / 2 < b ∧ b < 1 ∧ tsupport φ ⊆ Ioo (1 / 2 : ℝ) b := by
  let K := tsupport φ ∪ {(1 / 2 : ℝ)}
  have hK : IsCompact K := hφ.union isCompact_singleton
  have hAt : (1 / 2 : ℝ) ∈ K := Or.inr rfl
  obtain ⟨m, hmK, hm⟩ := hK.exists_isGreatest ⟨1 / 2, hAt⟩
  have hm₀ : (1 / 2 : ℝ) ≤ m := hm hAt
  have hm₁ : m < 1 := by
    rcases hmK with h | h
    · exact (hSupp h).2
    · rw [mem_singleton_iff] at h
      linarith only [h]
  let b := (m + 1) / 2
  have hmb : m < b := by dsimp only [b]; linarith only [hm₁]
  refine ⟨b, hm₀.trans_lt hmb, by dsimp only [b]; linarith only [hm₁], ?_⟩
  intro t ht
  exact ⟨(hSupp ht).1, (hm (Or.inl ht)).trans_lt hmb⟩

/-- The actual weak graph on the unit disk has a continuous radial `L²`
trace through the endpoint, normalized by all original interior slices. -/
theorem exists_native_disk_radial_L2_trace {w : Plane → Ambient 5}
    {D : Plane → HarmonicMaps.Gradient 2 5} (hw : MemW12 (ballDomain (0 : Plane) 1) w D) :
    ∃ H : VacuumBallTrace 2 (1 / 2), RepresentsVacuumBallTrace w H := by
  let σ := unitBoundarySurface 2
  let ν := (volume : Measure ℝ).restrict (Icc (1 / 2 : ℝ) 1)
  let F (p : UnitBoundarySphere 2 × ℝ) := w (p.2 • p.1.val)
  let G (p : UnitBoundarySphere 2 × ℝ) := ∑ i : Fin 2, p.1.val i • D (p.2 • p.1.val) i
  letI : IsFiniteMeasure σ := by
    dsimp only [σ, unitBoundarySurface]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)]
    infer_instance
  letI : MeasurableSpace.CountablyGenerated (UnitBoundarySphere 2) := BorelSpace.countablyGenerated
  letI : IsSeparable σ := inferInstance
  have hF : MemLp F 2 (σ.prod ν) := memLp_native_disk_full_radial_product hw.2.1
  have hG : MemLp G 2 (σ.prod ν) := by
    have hT (i : Fin 2) : MemLp (fun p : UnitBoundarySphere 2 × ℝ => p.1.val i) ⊤ (σ.prod ν) := by
      have hCont : Continuous (fun p : UnitBoundarySphere 2 × ℝ => p.1.val i) :=
        (EuclideanSpace.proj i).continuous.comp (continuous_subtype_val.comp continuous_fst)
      apply memLp_top_of_bound hCont.measurable.aestronglyMeasurable 1
      exact ae_of_all _ fun p => (PiLp.norm_apply_le p.1.val i).trans_eq
        (mem_sphere_zero_iff_norm.mp p.1.property)
    have hD (i : Fin 2) : MemLp (fun p : UnitBoundarySphere 2 × ℝ => D (p.2 • p.1.val) i) 2 (σ.prod ν) :=
      memLp_native_disk_full_radial_product (hw.2.2 i)
    have hSum := memLp_finsetSum Finset.univ (fun i (_ : i ∈ Finset.univ) => (hD i).smul (r := 2) (hT i))
    simpa only [G, Finset.sum_apply, Pi.smul_apply'] using hSum
  apply ExistsUnique.exists
  refine exists_unique_finite_lp_continuous_representative_of_raw_time_identity σ
    (by norm_num : (1 / 2 : ℝ) < 1) hF hG ?_
  intro φ hφ hcφ hsφ
  obtain ⟨b, hb₀, hb₁, hs⟩ := disk_trace_test_support_local hcφ hsφ
  have hW := (radial_product_weak_identity_of_memW12_ball (by decide : 0 < 2) (by norm_num : (0 : ℝ) < 1 / 2)
    hb₀ hb₁ hw).2.2 φ hφ hcφ hs
  have hW' : ∀ᵐ θ ∂σ,
      (∫ t in Icc (1 / 2 : ℝ) b, deriv φ t • F (θ, t)) =
        -(∫ t in Icc (1 / 2 : ℝ) b, φ t • G (θ, t)) := by
    simpa only [F, G, zero_add] using hW
  filter_upwards [hW'] with θ hθ
  have hCut {ψ : ℝ → ℝ} (hψ : tsupport ψ ⊆ Ioo (1 / 2 : ℝ) b) (v : ℝ → Ambient 5) :
      (∫ t in Icc (1 / 2 : ℝ) b, ψ t • v t) = ∫ t in Icc (1 / 2 : ℝ) 1, ψ t • v t := by
    have hGlobal (d : ℝ) (hd : b ≤ d) :
        (∫ t in Icc (1 / 2 : ℝ) d, ψ t • v t) = ∫ t, ψ t • v t := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have hZero : ψ t = 0 := image_eq_zero_of_notMem_tsupport fun ht' =>
        ht ⟨(hψ ht').1.le, (hψ ht').2.le.trans hd⟩
      rw [hZero, zero_smul]
    rw [hGlobal b le_rfl, hGlobal 1 hb₁.le]
  rw [← hCut (tsupport_deriv_subset.trans hs) (fun t => F (θ, t)),
    ← hCut hs (fun t => G (θ, t))]
  exact hθ

end Thesis

end
