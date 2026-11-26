module

public import Thesis.Variational.SmoothDomainEpigraphBoxes
public import Thesis.Upstream.MinimizingSobolev
import StratificationTheory.Foundation.SmoothOpenDomainSobolevPullback
import StratificationTheory.Foundation.CoordinateRectangleTrace
import StratificationTheory.Foundation.ReflectedRectangleTraceGluing
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! The original Sobolev graph in the rectangular normal coordinates of a
smooth boundary. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Topology

namespace Thesis

variable {Ω : Set Point}

abbrev normalCoordinateEquiv :=
  EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)

namespace SmoothDomainEpigraphBox

variable (B : SmoothDomainEpigraphBox Ω)

@[expose] def planeDomain : OpenDomain 2 :=
  ⟨{y : Plane | y 0 ∈ Ioo (-B.radius) B.radius ∧ y 1 ∈ Ioo (-B.radius) B.radius},
    (isOpen_Ioo.preimage (EuclideanSpace.proj 0).continuous).inter
      (isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous)⟩

theorem isFiniteMeasure_planeDomain : IsFiniteMeasure (volume.restrict B.planeDomain.val) := by
  apply isFiniteMeasure_restrict.mpr
  have hSub : B.planeDomain.val ⊆ closedBall (0 : Plane) (2 * B.radius) := by
    intro y hy
    have hy₁ : |y 0| ≤ B.radius := abs_le.2 ⟨hy.1.1.le, hy.1.2.le⟩
    have hy₂ : |y 1| ≤ B.radius := abs_le.2 ⟨hy.2.1.le, hy.2.2.le⟩
    rw [mem_closedBall_zero_iff]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) B.radius_pos.le)).mp
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    nlinarith only [pow_le_pow_left₀ (abs_nonneg _) hy₁ 2,
      pow_le_pow_left₀ (abs_nonneg _) hy₂ 2, sq_abs (y 0), sq_abs (y 1), sq_nonneg B.radius]
  exact ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hSub)

@[expose] def normalParameter (y : Plane × ℝ) : Point :=
  B.chart ((y.1 0, y.1 1), y.2)

private def normalPointEquiv : Point ≃ₜ EpigraphCoordinates where
  toFun x := (((normalCoordinateEquiv x).1 0, (normalCoordinateEquiv x).1 1),
    (normalCoordinateEquiv x).2 0)
  invFun p := normalCoordinateEquiv.symm
    (WithLp.toLp 2 ![p.1.1,p.1.2], EuclideanSpace.single (0 : Fin 1) p.2)
  left_inv x := by
    apply normalCoordinateEquiv.injective
    rw [normalCoordinateEquiv.apply_symm_apply]
    apply Prod.ext
    · apply PiLp.ext
      intro j
      fin_cases j <;> rfl
    · apply PiLp.ext
      intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp only [PiLp.single_apply, if_true]
  right_inv p := by
    change ((((normalCoordinateEquiv (normalCoordinateEquiv.symm _)).1 0),
      ((normalCoordinateEquiv (normalCoordinateEquiv.symm _)).1 1)),
      ((normalCoordinateEquiv (normalCoordinateEquiv.symm _)).2 0)) = p
    rw [normalCoordinateEquiv.apply_symm_apply]
    apply Prod.ext
    · rfl
    · simp only [PiLp.single_apply, if_true]
  continuous_toFun :=
    (((EuclideanSpace.proj 0).continuous.comp (continuous_fst.comp normalCoordinateEquiv.continuous)).prodMk
      ((EuclideanSpace.proj 1).continuous.comp (continuous_fst.comp normalCoordinateEquiv.continuous))).prodMk
      ((EuclideanSpace.proj 0).continuous.comp (continuous_snd.comp normalCoordinateEquiv.continuous))
  continuous_invFun := by
    apply normalCoordinateEquiv.symm.continuous.comp
    apply Continuous.prodMk
    · apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro j
      fin_cases j
      · exact continuous_fst.comp continuous_fst
      · exact continuous_snd.comp continuous_fst
    · have hs : ContDiff ℝ ∞ (fun p : EpigraphCoordinates => EuclideanSpace.single (0 : Fin 1) p.2) := by
        apply (contDiff_piLp 2).2
        intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simpa only [PiLp.single_apply, if_true] using
          (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : EpigraphCoordinates → ℝ))
      exact hs.continuous

def normalEuclideanChart : Point ≃ₜ Point := normalPointEquiv.trans B.chart

theorem normalEuclideanChart_apply (p : Plane × ℝ) :
    B.normalEuclideanChart (normalCoordinateEquiv.symm (p.1, EuclideanSpace.single 0 p.2)) =
      B.normalParameter p := by
  change B.chart (((normalCoordinateEquiv (normalCoordinateEquiv.symm _)).1 0,
    (normalCoordinateEquiv (normalCoordinateEquiv.symm _)).1 1),
    (normalCoordinateEquiv (normalCoordinateEquiv.symm _)).2 0) = _
  rw [normalCoordinateEquiv.apply_symm_apply, PiLp.single_apply, if_pos rfl]
  rfl

theorem normalEuclideanChart_smooth : ContDiff ℝ ∞ (B.normalEuclideanChart : Point → Point) := by
  have hF : ContDiff ℝ ∞ (fun x : Point => (normalCoordinateEquiv x).1) :=
    contDiff_fst.comp normalCoordinateEquiv.contDiff
  have hI (j : Fin 2) : ContDiff ℝ ∞ fun x => (normalCoordinateEquiv x).1 j :=
    (contDiff_piLp_apply 2).comp hF
  have ht : ContDiff ℝ ∞ fun x => (normalCoordinateEquiv x).2 0 :=
    (contDiff_piLp_apply 2).comp (contDiff_snd.comp normalCoordinateEquiv.contDiff)
  exact B.chart_smooth.comp (((hI 0).prodMk (hI 1)).prodMk ht)

theorem normalEuclideanChart_inverse_smooth : ContDiff ℝ ∞ (B.normalEuclideanChart.symm : Point → Point) := by
  have hFlat : ContDiff ℝ ∞ (normalPointEquiv.symm : EpigraphCoordinates → Point) := by
    apply normalCoordinateEquiv.symm.contDiff.comp
    apply ContDiff.prodMk
    · apply (contDiff_piLp 2).2
      intro i
      fin_cases i
      · exact contDiff_fst.comp contDiff_fst
      · exact contDiff_snd.comp contDiff_fst
    · apply (contDiff_piLp 2).2
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simpa only [PiLp.single_apply, if_true] using
        (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : EpigraphCoordinates → ℝ))
  exact hFlat.comp B.chart_inverse_smooth

theorem normalParameter_measurePreserving :
    MeasurePreserving B.normalParameter ((volume : Measure Plane).prod (volume : Measure ℝ)) volume := by
  have hP : MeasurePreserving (fun y : Plane => (y 0,y 1)) (volume : Measure Plane)
      (volume : Measure (ℝ × ℝ)) :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  exact B.chart_volume.comp (hP.prod (MeasurePreserving.id (volume : Measure ℝ)))

theorem normalEuclideanChart_measurePreserving :
    MeasurePreserving B.normalEuclideanChart (volume : Measure Point) volume := by
  let R : Plane × ℝ → Point := fun p =>
    normalCoordinateEquiv.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)
  let S : Point → Plane × ℝ := fun x => ((normalCoordinateEquiv x).1, (normalCoordinateEquiv x).2 0)
  have hR : MeasurePreserving R ((volume : Measure Plane).prod (volume : Measure ℝ)) volume :=
    measurePreserving_cylinder_coordinates_inverse 2
  have hS : MeasurePreserving S (volume : Measure Point) ((volume : Measure Plane).prod (volume : Measure ℝ)) :=
    measurePreserving_cylinder_coordinates 2
  have hSR (x : Point) : R (S x) = x := cylinder_coordinates_inverse_left 2 x
  convert B.normalParameter_measurePreserving.comp hS using 1
  funext x
  exact (congrArg B.normalEuclideanChart (hSR x)).symm.trans (B.normalEuclideanChart_apply (S x))

@[expose] def flatRectangle (s t : ℝ) : OpenDomain 3 :=
  ⟨{y | (normalCoordinateEquiv y).1 ∈ B.planeDomain.val ∧
      (normalCoordinateEquiv y).2 0 ∈ Ioo s t},
    (B.planeDomain.property.preimage (continuous_fst.comp normalCoordinateEquiv.continuous)).inter
      (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp normalCoordinateEquiv.continuous)))⟩

abbrev flatSlab (t : ℝ) : OpenDomain 3 := B.flatRectangle 0 t

@[expose] def physicalRectangle (s t : ℝ) : OpenDomain 3 :=
  ⟨B.normalEuclideanChart '' (B.flatRectangle s t).val,
    B.normalEuclideanChart.isOpenMap _ (B.flatRectangle s t).property⟩

private theorem normalPointEquiv_mem_closedBox {x : Point} {t : ℝ} (ht : t ≤ B.radius)
    (hx : x ∈ (B.flatSlab t).val) :
    normalPointEquiv x ∈ closedBall (0 : EpigraphCoordinates) B.radius :=
  epigraphCoordinates_mem_closedBall_iff.2
    ⟨⟨⟨hx.1.1.1.le,hx.1.1.2.le⟩,⟨hx.1.2.1.le,hx.1.2.2.le⟩⟩,
      ⟨(neg_nonpos.mpr B.radius_pos.le).trans hx.2.1.le, hx.2.2.le.trans ht⟩⟩

theorem flatSlab_mapsTo_domain {t : ℝ} (ht : t ≤ B.radius) :
    MapsTo B.normalEuclideanChart (B.flatSlab t).val Ω :=
  fun _ hx => (B.mem_domain _ (B.normalPointEquiv_mem_closedBox ht hx)).2 hx.2.1

theorem flatSlab_measurePreserving (t : ℝ) :
    MeasurePreserving B.normalEuclideanChart (volume.restrict (B.flatSlab t).val)
      (volume.restrict (B.normalEuclideanChart '' (B.flatSlab t).val)) := by
  have hImg : MeasurableSet (B.normalEuclideanChart '' (B.flatSlab t).val) :=
    B.normalEuclideanChart.toMeasurableEquiv.measurableSet_image.2 (B.flatSlab t).property.measurableSet
  have h := B.normalEuclideanChart_measurePreserving.restrict_preimage hImg
  rwa [preimage_image_eq _ B.normalEuclideanChart.injective] at h

theorem flatRectangle_measurePreserving (s t : ℝ) :
    MeasurePreserving B.normalEuclideanChart (volume.restrict (B.flatRectangle s t).val)
      (volume.restrict (B.physicalRectangle s t).val) := by
  have h := B.normalEuclideanChart_measurePreserving.restrict_preimage
    (B.physicalRectangle s t).property.measurableSet
  have he : B.normalEuclideanChart ⁻¹' (B.physicalRectangle s t).val = (B.flatRectangle s t).val :=
    preimage_image_eq _ B.normalEuclideanChart.injective
  rwa [he] at h

theorem isBounded_flatSlab {t : ℝ} (ht : t ≤ B.radius) : Bornology.IsBounded (B.flatSlab t).val := by
  let K := closedBall (0 : EpigraphCoordinates) B.radius
  apply ((isCompact_closedBall (0 : EpigraphCoordinates) B.radius).image normalPointEquiv.symm.continuous).isBounded.subset
  intro x hx
  exact ⟨normalPointEquiv x, B.normalPointEquiv_mem_closedBox ht hx, normalPointEquiv.symm_apply_apply _⟩

/-- Pull back an original weak graph to the inner side of an actual normal
rectangle. Its columns are the chain-rule columns of the smooth chart. -/
theorem memW12_normalChart {q : ℕ} (hΩ : IsOpen Ω) {t : ℝ} (ht : t ≤ B.radius)
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 ⟨Ω,hΩ⟩ u D) :
    MemW12 (B.flatSlab t) (u ∘ B.normalEuclideanChart)
      (fun x i => ∑ j : Fin 3, (fderiv ℝ B.normalEuclideanChart x (EuclideanSpace.single i 1)) j •
        D (B.normalEuclideanChart x) j) := by
  let F := B.normalEuclideanChart
  let V := B.flatSlab t
  have hBound := B.isBounded_flatSlab ht
  obtain ⟨L,hL⟩ := hBound.isCompact_closure.exists_bound_of_continuousOn
    (B.normalEuclideanChart_smooth.continuous_fderiv (by simp)).continuousOn
  apply memW12_smooth_open_domain_pullback hu V F B.normalEuclideanChart_smooth.contDiffOn
    (B.flatSlab_mapsTo_domain ht) L (fun x hx => hL x (subset_closure hx)) 1 ENNReal.one_ne_top
  rw [one_smul, (B.flatSlab_measurePreserving t).map_eq]
  apply Measure.restrict_mono_set
  rintro _ ⟨x,hx,rfl⟩
  exact B.flatSlab_mapsTo_domain ht hx

theorem isBounded_flatRectangle {s t : ℝ} (hs : -B.radius ≤ s) (ht : t ≤ B.radius) :
    Bornology.IsBounded (B.flatRectangle s t).val := by
  apply ((isCompact_closedBall (0 : EpigraphCoordinates) B.radius).image normalPointEquiv.symm.continuous).isBounded.subset
  intro x hx
  refine ⟨normalPointEquiv x, epigraphCoordinates_mem_closedBall_iff.2 ?_, normalPointEquiv.symm_apply_apply x⟩
  exact ⟨⟨⟨hx.1.1.1.le,hx.1.1.2.le⟩,⟨hx.1.2.1.le,hx.1.2.2.le⟩⟩,
    ⟨hs.trans hx.2.1.le, hx.2.2.le.trans ht⟩⟩

theorem normalEuclideanChart_mem_domain_iff {s t : ℝ} (hs : -B.radius ≤ s) (ht : t ≤ B.radius)
    {x : Point} (hx : x ∈ (B.flatRectangle s t).val) :
    B.normalEuclideanChart x ∈ Ω ↔ 0 < (normalCoordinateEquiv x).2 0 :=
  B.mem_domain _ (epigraphCoordinates_mem_closedBall_iff.2
    ⟨⟨⟨hx.1.1.1.le,hx.1.1.2.le⟩,⟨hx.1.2.1.le,hx.1.2.2.le⟩⟩,
      ⟨hs.trans hx.2.1.le,hx.2.2.le.trans ht⟩⟩)

theorem isBounded_physicalRectangle {s t : ℝ} (hs : -B.radius ≤ s) (ht : t ≤ B.radius) :
    Bornology.IsBounded (B.physicalRectangle s t).val :=
  ((B.isBounded_flatRectangle hs ht).isCompact_closure.image B.normalEuclideanChart.continuous).isBounded.subset
    (image_mono subset_closure)

theorem memW12_physicalRectangle {q : ℕ} {s t : ℝ} (hs : -B.radius ≤ s) (ht : t ≤ B.radius)
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 (B.flatRectangle s t) u D) :
    MemW12 (B.physicalRectangle s t) (u ∘ B.normalEuclideanChart.symm)
      (fun x i => ∑ j : Fin 3, (fderiv ℝ B.normalEuclideanChart.symm x (EuclideanSpace.single i 1)) j •
        D (B.normalEuclideanChart.symm x) j) := by
  let F := B.normalEuclideanChart
  let V := B.physicalRectangle s t
  obtain ⟨L,hL⟩ := (B.isBounded_physicalRectangle hs ht).isCompact_closure.exists_bound_of_continuousOn
    (B.normalEuclideanChart_inverse_smooth.continuous_fderiv (by simp)).continuousOn
  have hMP := (B.flatRectangle_measurePreserving s t).symm F.toMeasurableEquiv
  have hMap : MapsTo F.symm V.val (B.flatRectangle s t).val := by
    rintro _ ⟨x,hx,rfl⟩
    change F.symm (F x) ∈ (B.flatRectangle s t).val
    rwa [F.symm_apply_apply]
  apply memW12_smooth_open_domain_pullback hu V F.symm B.normalEuclideanChart_inverse_smooth.contDiffOn
    hMap L (fun x hx => hL x (subset_closure hx)) 1 ENNReal.one_ne_top
  rw [one_smul]
  exact hMP.map_eq.le

theorem normalChart_mem_zero {a : Point} (hB : B.chart (0 : EpigraphCoordinates) = a) {t : ℝ} (ht : 0 < t) :
    a ∈ (B.physicalRectangle (-t) t).val := by
  refine ⟨0, ?_, ?_⟩
  · change (normalCoordinateEquiv (0 : Point)).1 ∈ B.planeDomain.val ∧
      (normalCoordinateEquiv (0 : Point)).2 0 ∈ Ioo (-t) t
    rw [map_zero]
    exact ⟨⟨⟨neg_lt_zero.mpr B.radius_pos, B.radius_pos⟩,⟨neg_lt_zero.mpr B.radius_pos, B.radius_pos⟩⟩,
      ⟨neg_lt_zero.mpr ht, ht⟩⟩
  · change B.chart (((normalCoordinateEquiv (0 : Point)).1 0,(normalCoordinateEquiv (0 : Point)).1 1),
      (normalCoordinateEquiv (0 : Point)).2 0) = a
    rw [map_zero]
    exact hB

/-- Every actual weak graph extends locally through the smooth boundary by
reflection across the flattened wall. It agrees pointwise with the given
representative on the interior part of the extended neighborhood. -/
theorem exists_local_reflected_memW12 {q : ℕ} (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t) (htR : t ≤ B.radius)
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 ⟨Ω,hΩ⟩ u D) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ t ∧ ∃ (w : Point → Ambient q) (G : Point → HarmonicMaps.Gradient 3 q),
      MemW12 (B.physicalRectangle (-δ) δ) w G ∧ EqOn w u (Ω ∩ (B.physicalRectangle (-δ) δ).val) := by
  letI := B.isFiniteMeasure_planeDomain
  let v : Point → Ambient q := u ∘ B.normalEuclideanChart
  let J (x : Point) (i : Fin 3) := ∑ j : Fin 3,
    (fderiv ℝ B.normalEuclideanChart x (EuclideanSpace.single i 1)) j • D (B.normalEuclideanChart x) j
  have hv : MemW12 (B.flatSlab t) v J := B.memW12_normalChart hΩ htR hu
  obtain ⟨H,hH,_⟩ := exists_unique_L2_trace_of_memW12_rectangle B.planeDomain ht hv
  obtain ⟨δ,hδ,G,hG⟩ := exists_reflected_rectangle_weak_gluing B.planeDomain ht ht v v J J hv hv H H hH hH rfl
  let d := min δ t
  have hd : 0 < d := lt_min hδ ht
  have hd' : d ≤ t := min_le_right _ _
  let w (y : Point) := if (normalCoordinateEquiv y).2 0 < 0 then
    v (normalCoordinateEquiv.symm ((normalCoordinateEquiv y).1,-(normalCoordinateEquiv y).2)) else v y
  have hSub : (B.flatRectangle (-d) d).val ⊆ (B.flatRectangle (-δ) δ).val := fun _ hx =>
    ⟨hx.1, (neg_le_neg (min_le_left _ _)).trans_lt hx.2.1, hx.2.2.trans_le (min_le_left _ _)⟩
  have hW : MemW12 (B.flatRectangle (-d) d) w G :=
    ⟨hG.1.mono hSub, hG.2.1.mono_measure (Measure.restrict_mono_set _ hSub),
      fun i => (hG.2.2 i).mono_measure (Measure.restrict_mono_set _ hSub)⟩
  have hdr := hd'.trans htR
  have hPhysical := B.memW12_physicalRectangle (neg_le_neg hdr) hdr hW
  refine ⟨d,hd,hd',w ∘ B.normalEuclideanChart.symm,_,hPhysical,?_⟩
  rintro x ⟨hxΩ,y,hy,rfl⟩
  have hyBox : normalPointEquiv y ∈ closedBall (0 : EpigraphCoordinates) B.radius :=
    epigraphCoordinates_mem_closedBall_iff.2
      ⟨⟨⟨hy.1.1.1.le,hy.1.1.2.le⟩,⟨hy.1.2.1.le,hy.1.2.2.le⟩⟩,
        ⟨(neg_le_neg hdr).trans hy.2.1.le, hy.2.2.le.trans hdr⟩⟩
  have hY : 0 < (normalCoordinateEquiv y).2 0 := (B.mem_domain _ hyBox).1 hxΩ
  change w (B.normalEuclideanChart.symm (B.normalEuclideanChart y)) = u (B.normalEuclideanChart y)
  rw [B.normalEuclideanChart.symm_apply_apply]
  exact if_neg (not_lt_of_gt hY)

end SmoothDomainEpigraphBox

end Thesis
