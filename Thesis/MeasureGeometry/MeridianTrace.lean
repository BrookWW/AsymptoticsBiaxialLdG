module

public import Thesis.MeasureGeometry.PlanarVacuumAnnulus
import Thesis.Foundation.WeakGradient
import Thesis.Foundation.VacuumTarget

/-! The continuous vacuum meridian of the actual regular limit. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

/-- The closed vacuum constraint for a continuous representative on an
open set holds at each of its points. -/
theorem mapsTo_vacuum_of_continuousOn_of_takesVacuumValues (a : BulkCoefficients)
    {W : Set Point} (hW : IsOpen W) {Q : Point → S0}
    (hQ : ContinuousOn Q W) (hVac : TakesVacuumValues a W Q) : MapsTo Q W (vacuum a) := by
  intro x hx
  by_contra hOut
  have hN := ((hQ x hx).continuousAt (hW.mem_nhds hx))
    (((isCompact_vacuum a).isClosed.isOpen_compl).mem_nhds hOut)
  obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (hW.mem_nhds hx) hN)
  have hBW : ball x r ⊆ W := hB.trans inter_subset_left
  have hZ : (volume.restrict W) {x | Q x ∉ vacuum a} = 0 := by
    have h : ∀ᵐ x ∂volume.restrict W, Q x ∈ vacuum a := hVac
    exact ae_iff.mp h
  have hE : (volume.restrict W) (ball x r) = volume (ball x r) := by
    rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.2 hBW]
  exact ((measure_ball_pos volume x hr).ne') (le_antisymm
    (hE.symm.le.trans ((measure_mono (hB.trans inter_subset_right)).trans_eq hZ)) zero_le)

/-- The boundary of an injectively embedded disk that meets the support at
one interior point gives the actual continuous meridian of the regular map. -/
theorem exists_vacuumMeridianTrace (a : BulkCoefficients) {Ω S : Set Point}
    {Q : Point → S0} (hVac : TakesVacuumValues a (Ω \ S) Q)
    (hReg : ContDiffOn ℝ ∞ Q ((Ω \ S) \ singularSet (Ω \ S) Q))
    (d : Plane → Point) (hd : IsSmoothDiskEmbedding d) (hDΩ : d '' Disk ⊆ Ω)
    {y : Plane} (hy : y ∈ ball (0 : Plane) 1) (hMeet : d '' Disk ∩ S = {d y})
    (hSing : Disjoint (d '' sphere (0 : Plane) 1) (singularSet (Ω \ S) Q)) :
    ∃ b : C(NativeCircle, vacuum a), ∀ z : NativeCircle, (b z).val = Q (d z.val) := by
  let W := Ω \ S
  let R := W \ singularSet W Q
  have hR : IsOpen R := isOpen_diff_singularSet Q
  have hVacR : TakesVacuumValues a R Q := ae_restrict_of_ae_restrict_of_subset sdiff_subset hVac
  have hVal := mapsTo_vacuum_of_continuousOn_of_takesVacuumValues a hR hReg.continuousOn hVacR
  have hMaps : MapsTo d (sphere (0 : Plane) 1) R := by
    intro z hz
    have hzD : z ∈ Disk := sphere_subset_closedBall hz
    have hzΩ : d z ∈ Ω := hDΩ ⟨z, hzD, rfl⟩
    have hzS : d z ∉ S := by
      intro h
      have he : d z = d y := mem_singleton_iff.1 (hMeet ▸ ⟨⟨z, hzD, rfl⟩, h⟩)
      have hzy := hd.2.1 hzD (ball_subset_closedBall hy) he
      exact ((mem_sphere_zero_iff_norm.1 hz).not_lt) (hzy.symm ▸ mem_ball_zero_iff.1 hy)
    exact ⟨⟨hzΩ, hzS⟩, fun h => Set.disjoint_left.1 hSing ⟨z, hz, rfl⟩ h⟩
  have hc : Continuous (fun z : NativeCircle => Q (d z.val)) :=
    hReg.continuousOn.comp_continuous
      (hd.1.continuousOn.comp_continuous continuous_subtype_val (fun z => sphere_subset_closedBall z.property))
      (fun z => hMaps z.property)
  exact ⟨⟨fun z => ⟨Q (d z.val), hVal (hMaps z.property)⟩, hc.subtype_mk _⟩, fun _ => rfl⟩

/-- A continuous filling of the genuine meridian forces its quaternion
splitting energy to vanish. -/
theorem nativeVacuumCircleCost_eq_zero_of_meridianFilling (a : BulkCoefficients)
    {Q : Point → S0} {d : Plane → Point} (b : C(NativeCircle, vacuum a))
    (hb : ∀ z : NativeCircle, (b z).val = Q (d z.val)) (hFill : HasMeridianFilling a d Q) :
    nativeVacuumCircleCost a b = 0 := by
  obtain ⟨w, hwVac, hwEq⟩ := hFill
  let W : C(Disk, vacuum a) := ⟨fun z => ⟨w z, hwVac z⟩, w.continuous.subtype_mk _⟩
  let O : Disk := ⟨0, mem_closedBall_self zero_le_one⟩
  have hDisk (x : unitInterval × NativeCircle) : (1 - x.1.val) • x.2.val ∈ Disk := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 x.1.property.2),
      mem_sphere_zero_iff_norm.1 x.2.property, mul_one]
    exact sub_le_self _ x.1.property.1
  let F : C(unitInterval × NativeCircle, Disk) :=
    ⟨fun x => ⟨(1 - x.1.val) • x.2.val, hDisk x⟩, by
      apply Continuous.subtype_mk
      exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd)⟩
  let H : b.Homotopy (ContinuousMap.const NativeCircle (W O)) :=
    { toContinuousMap := W.comp F
      map_zero_left := by
        intro z
        let Z : Disk := ⟨z.val, sphere_subset_closedBall z.property⟩
        have hF : F (0, z) = Z := by
          apply Subtype.ext
          change (1 - (0 : ℝ)) • z.val = z.val
          rw [sub_zero, one_smul]
        apply Subtype.ext
        change w (F (0, z)) = (b z).val
        exact (congrArg w hF).trans
          ((hwEq Z (mem_sphere_zero_iff_norm.1 z.property)).trans (hb z).symm)
      map_one_left := by
        intro z
        have hF : F (1, z) = O := by
          apply Subtype.ext
          change ((1 : ℝ) - 1) • z.val = 0
          rw [sub_self, zero_smul]
        change W (F (1, z)) = W O
        exact congrArg W hF }
  exact (nativeVacuumCircleCost_homotopic a (f := b)
    (g := ContinuousMap.const NativeCircle (W O)) ⟨H⟩).trans (nativeVacuumCircleCost_const a (W O))

/-- A positive splitting energy obstructs a continuous vacuum filling
of the same embedded-disk boundary. -/
theorem not_hasMeridianFilling_of_positive_cost (a : BulkCoefficients)
    {Q : Point → S0} {d : Plane → Point} (b : C(NativeCircle, vacuum a))
    (hb : ∀ z : NativeCircle, (b z).val = Q (d z.val)) (hCost : 0 < nativeVacuumCircleCost a b) :
    ¬ HasMeridianFilling a d Q :=
  fun h => hCost.ne' (nativeVacuumCircleCost_eq_zero_of_meridianFilling a b hb h)

end Thesis.MeasureGeometry
