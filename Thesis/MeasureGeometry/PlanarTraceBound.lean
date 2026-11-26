module

public import Thesis.MeasureGeometry.PlanarRadialCollar
import StratificationTheory.Foundation.PolarAETransport
import StratificationTheory.Foundation.CircleNativeMeasure
import StratificationTheory.Foundation.AngularL2Membership
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! The original radial Sobolev trace inherits the disk's essential bound. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ENNReal Topology

namespace Thesis

/-- Ordinary angular Lebesgue integration with the original starting angle
equals the area-normalized native unit circle integral. -/
theorem nativeCircle_integral_angular (f : NativeCircle → ℝ)
    (hf : Integrable f (unitBoundarySurface 2)) :
    (∫ t in Ioo (0 : ℝ) (2 * Real.pi), f (circleNativeParam (t - Real.pi))) =
      ∫ θ : NativeCircle, f θ ∂unitBoundarySurface 2 := by
  have hσ : (Measure.euclideanHausdorffMeasure 1 : Measure NativeCircle) = unitBoundarySurface 2 :=
    rfl
  have h := (integrable_circleNativeParam_Ioc_and_integral f (hσ.symm ▸ hf)).2
  rw [hσ] at h
  rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * Real.pi)]
  let F (t : ℝ) := f (circleNativeParam t)
  change (∫ t in (0 : ℝ)..2 * Real.pi, F (t - Real.pi)) = _
  rw [intervalIntegral.integral_comp_sub_right]
  rw [zero_sub, show 2 * Real.pi - Real.pi = Real.pi by ring,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  exact h

private theorem isClosed_Lp_ae_norm_le (C : ℝ) :
    IsClosed {v : Lp (Ambient 5) 2 (unitBoundarySurface 2) |
      ∀ᵐ z ∂unitBoundarySurface 2, ‖v z‖ ≤ C} := by
  apply IsSeqClosed.isClosed
  intro v w hv hw
  have h := tendstoInMeasure_of_tendsto_Lp hw
  obtain ⟨κ, _, hκ⟩ := h.exists_seq_tendsto_ae
  filter_upwards [hκ, ae_all_iff.mpr (fun n => hv (κ n))] with z hz hzNorm
  exact le_of_tendsto' hz.norm hzNorm

private theorem norm_le_of_nativeCircle_ae {b : C(NativeCircle, Ambient 5)} {C : ℝ}
    (h : ∀ᵐ z ∂unitBoundarySurface 2, ‖b z‖ ≤ C) (z : NativeCircle) : ‖b z‖ ≤ C := by
  have hσ : (Measure.euclideanHausdorffMeasure 1 : Measure NativeCircle) = unitBoundarySurface 2 :=
    rfl
  have hAngles : ∀ᵐ t ∂volume.restrict (Ioc (-Real.pi) Real.pi), ‖b (circleNativeParam t)‖ ≤ C :=
    measurePreserving_circleNativeParam_Ioc.quasiMeasurePreserving.ae (hσ.symm ▸ h)
  let f (t : ℝ) := ‖b (circleNativeParam t)‖
  have hF : Continuous f := (b.continuous.comp continuous_circleNativeParam).norm
  have hG : Ioo (-Real.pi) Real.pi ⊆ {t | f t ≤ C} := by
    intro t ht
    change f t ≤ C
    by_contra! htc
    let B := Ioo (-Real.pi) Real.pi ∩ {y | C < f y}
    have hB : IsOpen B := isOpen_Ioo.inter (isOpen_lt continuous_const hF)
    have hBN : B.Nonempty := ⟨t, ht, htc⟩
    letI : NeBot (ae (volume.restrict B)) := ae_neBot.mpr (by
      intro hz
      have hu := congrArg (fun μ : Measure ℝ => μ univ) hz
      change (volume.restrict B) univ = (0 : Measure ℝ) univ at hu
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at hu
      exact hB.measure_ne_zero volume hBN (by simpa using hu))
    have hR : ∀ᵐ y ∂volume.restrict B, f y ≤ C :=
      ae_restrict_of_ae_restrict_of_subset (inter_subset_left.trans Ioo_subset_Ioc_self) hAngles
    obtain ⟨y, hy, hyl⟩ := ((ae_restrict_mem hB.measurableSet).and hR).exists
    exact hy.2.not_ge hyl
  have hClose : Icc (-Real.pi) Real.pi ⊆ {t | f t ≤ C} := by
    rw [← closure_Ioo (show -Real.pi ≠ Real.pi by linarith [Real.pi_pos])]
    exact closure_minimal hG (isClosed_le hF continuous_const)
  obtain ⟨t, rfl⟩ := nativeCircleLoopParam_surjective z
  rw [nativeCircleLoopParam_apply]
  exact hClose (show (2 * Real.pi * t.val - Real.pi) ∈ Icc (-Real.pi) Real.pi by
    constructor
    · linarith only [mul_nonneg (show 0 ≤ 2 * Real.pi by positivity) t.property.1]
    · nlinarith only [mul_le_mul_of_nonneg_left t.property.2 (show 0 ≤ 2 * Real.pi by positivity)])

/-- A continuous boundary datum that represents the actual radial Sobolev
trace inherits the essential norm bound in the open disk. -/
theorem norm_le_of_nativeBallTrace {u : Plane → Ambient 5}
    {s C : ℝ} (hs : s < 1) (H : VacuumBallTrace 2 s) (hH : RepresentsVacuumBallTrace u H)
    (b : C(NativeCircle, Ambient 5)) (hb : MemLp b 2 (unitBoundarySurface 2))
    (hEnd : H ⟨1, hs.le, le_rfl⟩ = hb.toLp b)
    (huB : ∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖u x‖ ≤ C) :
    ∀ z : NativeCircle, ‖b z‖ ≤ C := by
  let F : Set (Lp (Ambient 5) 2 (unitBoundarySurface 2)) :=
    {v | ∀ᵐ z ∂unitBoundarySurface 2, ‖v z‖ ≤ C}
  have hF : IsClosed F := isClosed_Lp_ae_norm_le C
  have hOpen : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) 1),
      ∀ᵐ z : NativeCircle ∂unitBoundarySurface 2, ‖u (r • z.val)‖ ≤ C := by
    have hp := ae_polar_slice_of_ae_ball huB
    rw [← euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)] at hp
    simpa only [zero_add] using hp
  let r₁ : Icc s (1 : ℝ) := ⟨1, hs.le, le_rfl⟩
  have hlast : r₁ ∈ closure (H ⁻¹' F) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let a := max 0 (max s (1 - ε))
    have ha : a < 1 := max_lt zero_lt_one (max_lt hs (by linarith))
    let I := Ioo a 1
    letI : NeBot (ae (volume.restrict I)) := ae_neBot.mpr (by
      intro hz
      have hu := congrArg (fun μ : Measure ℝ => μ univ) hz
      change (volume.restrict I) univ = (0 : Measure ℝ) univ at hu
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at hu
      have hz' : (0 : Measure ℝ) univ = 0 := by simp
      rw [hz'] at hu
      exact (isOpen_Ioo.measure_ne_zero volume (nonempty_Ioo.mpr ha)) hu)
    have hI : I ⊆ Ioo (0 : ℝ) 1 := fun t ht => ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩
    have hRaw : ∀ᵐ t ∂volume.restrict I, t ∈ I ∧
        (∀ ht : t ∈ Ioo s 1,
          ∃ htLp : MemLp (fun θ : NativeCircle => u (t • θ.val)) 2 (unitBoundarySurface 2),
            H ⟨t, ht.1.le, ht.2.le⟩ = htLp.toLp _) ∧
        (∀ᵐ z : NativeCircle ∂unitBoundarySurface 2, ‖u (t • z.val)‖ ≤ C) :=
      (ae_restrict_mem measurableSet_Ioo).and
        ((ae_restrict_of_ae hH).and (ae_restrict_of_ae_restrict_of_subset hI hOpen))
    obtain ⟨t, ht, hHt, hBt⟩ := hRaw.exists
    have hst : t ∈ Ioo s 1 :=
      ⟨((le_max_left s (1 - ε)).trans (le_max_right 0 _)).trans_lt ht.1, ht.2⟩
    let t' : Icc s (1 : ℝ) := ⟨t, hst.1.le, hst.2.le⟩
    refine ⟨t', ?_, ?_⟩
    · obtain ⟨htLp, hE⟩ := hHt hst
      change H t' ∈ F
      rw [show H t' = htLp.toLp _ from hE]
      show ∀ᵐ z ∂unitBoundarySurface 2, ‖(htLp.toLp _) z‖ ≤ C
      filter_upwards [hBt, htLp.coeFn_toLp] with z hz he
      rwa [he]
    · change dist (1 : ℝ) t < ε
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.2.le)]
      have hA : 1 - ε ≤ a := (le_max_right s (1 - ε)).trans (le_max_right 0 _)
      linarith only [hA, ht.1]
  have hEndF : H r₁ ∈ F := by
    have hClosed : IsClosed (H ⁻¹' F) := hF.preimage H.continuous
    exact closure_minimal (Subset.rfl : H ⁻¹' F ⊆ H ⁻¹' F) hClosed hlast
  apply norm_le_of_nativeCircle_ae
  rw [show H r₁ = hb.toLp b from hEnd] at hEndF
  filter_upwards [show ∀ᵐ z ∂unitBoundarySurface 2, ‖(hb.toLp b) z‖ ≤ C from hEndF, hb.coeFn_toLp] with z hz he
  simpa only [he] using hz

end Thesis
