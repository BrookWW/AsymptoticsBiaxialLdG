module

public import Thesis.Variational.SmoothDomainZeroNormalTrace
import Thesis.Upstream.ZeroTraceSmoothTransport
import Thesis.Interpolation.ConvexZeroTrace
import StratificationTheory.Foundation.CompactSobolevCutoff
import StratificationTheory.Foundation.CoordinateTraceWeakGluing
import StratificationTheory.Foundation.CoordinatePiecewiseSobolevData
import HarmonicMaps.Analysis.SobolevAECongruence

/-! A localized zero normal trace lies in the original compact smooth
Dirichlet closure. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace Thesis.SmoothDomainEpigraphBox

variable {Ω : Set Point} (B : SmoothDomainEpigraphBox Ω)

private theorem memW12_flatSlab_zeroAcrossWall {q : ℕ} {t : ℝ} (ht : 0 < t)
    {v : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hv : MemW12 (B.flatSlab t) v D)
    (H : B.NormalTrace q t) (hH : B.RepresentsNormalTrace (fun p => v (B.normalEuclideanChart.symm p)) H)
    (hZero : H ⟨0,le_rfl,ht.le⟩ = 0) :
    MemW12 (B.flatRectangle (-t) t)
      (fun y => if 0 < (normalCoordinateEquiv y).2 0 then v y else 0)
      (fun y i => if 0 < (normalCoordinateEquiv y).2 0 then D y i else 0) := by
  letI := B.isFiniteMeasure_planeDomain
  let K : C(Icc (-t) (0 : ℝ), B.NormalTraceL2 q) := 0
  have hK : ∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo (-t) (0 : ℝ),
      ∃ hp : MemLp (0 : Plane → Ambient q) 2 (volume.restrict B.planeDomain.val),
        K ⟨s,hs.1.le,hs.2.le⟩ = hp.toLp (0 : Plane → Ambient q) := by
    let hp : MemLp (0 : Plane → Ambient q) 2 (volume.restrict B.planeDomain.val) := MemLp.zero
    exact Eventually.of_forall fun _ _ => ⟨hp,hp.toLp_zero.symm⟩
  have hRaw : ∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo (0 : ℝ) t,
      ∃ hp : MemLp (fun y => v (normalCoordinateEquiv.symm (y,EuclideanSpace.single 0 s)))
          2 (volume.restrict B.planeDomain.val),
        H ⟨s,hs.1.le,hs.2.le⟩ = hp.toLp _ := by
    have hEq (y : Plane) (s : ℝ) :
        B.normalEuclideanChart.symm (B.normalParameter (y,s)) =
          normalCoordinateEquiv.symm (y,EuclideanSpace.single 0 s) := by
      rw [← B.normalEuclideanChart_apply (y,s), B.normalEuclideanChart.symm_apply_apply]
    unfold RepresentsNormalTrace at hH
    simpa only [hEq] using hH
  have hMatch : K ⟨0,(neg_neg_of_pos ht).le,le_rfl⟩ = H ⟨0,le_rfl,ht.le⟩ := hZero.symm
  have hg := (memW12_coordinate_piecewise_of_matching_L2_traces B.planeDomain
    (neg_neg_of_pos ht) ht 0 v 0 D (MemW12.zero (B.flatRectangle (-t) 0)) hv K H hK hRaw hMatch).1
  have hne : ∀ᵐ x : Point ∂volume.restrict (B.flatRectangle (-t) t).val,
      (normalCoordinateEquiv x).2 0 ≠ 0 := ae_restrict_of_ae (ae_native_time_ne 2 0)
  apply hg.congr_ae
  · filter_upwards [hne] with x hx
    change (if (normalCoordinateEquiv x).2 0 < 0 then (0 : Ambient q) else v x) =
      (if 0 < (normalCoordinateEquiv x).2 0 then v x else 0)
    rcases lt_or_gt_of_ne hx with h | h
    · rw [if_pos h,if_neg (not_lt_of_gt h)]
    · rw [if_neg (not_lt_of_gt h),if_pos h]
  · filter_upwards [hne] with x hx
    funext i
    change (if (normalCoordinateEquiv x).2 0 < 0 then (0 : Ambient q) else D x i) =
      (if 0 < (normalCoordinateEquiv x).2 0 then D x i else 0)
    rcases lt_or_gt_of_ne hx with h | h
    · rw [if_pos h,if_neg (not_lt_of_gt h)]
    · rw [if_neg (not_lt_of_gt h),if_pos h]

theorem convex_flatSlab (t : ℝ) : Convex ℝ (B.flatSlab t).val := by
  have hBase : Convex ℝ B.planeDomain.val :=
    ((convex_Ioo (-B.radius) B.radius).linear_preimage (EuclideanSpace.proj 0).toLinearMap).inter
      ((convex_Ioo (-B.radius) B.radius).linear_preimage (EuclideanSpace.proj 1).toLinearMap)
  let E := normalCoordinateEquiv.toContinuousLinearMap
  let L := (ContinuousLinearMap.fst ℝ Plane (HarmonicMaps.Domain 1)).comp E
  let T := (EuclideanSpace.proj (0 : Fin 1)).comp ((ContinuousLinearMap.snd ℝ Plane (HarmonicMaps.Domain 1)).comp E)
  exact (hBase.linear_preimage L.toLinearMap).inter ((convex_Ioo 0 t).linear_preimage T.toLinearMap)

private theorem exists_mem_flatSlab {t : ℝ} (ht : 0 < t) : (B.flatSlab t).val.Nonempty := by
  refine ⟨normalCoordinateEquiv.symm (0,EuclideanSpace.single (0 : Fin 1) (t/2)),?_⟩
  change (normalCoordinateEquiv (normalCoordinateEquiv.symm _)).1 ∈ B.planeDomain.val ∧
    (normalCoordinateEquiv (normalCoordinateEquiv.symm _)).2 0 ∈ Ioo 0 t
  rw [normalCoordinateEquiv.apply_symm_apply, PiLp.single_apply, if_pos rfl]
  exact ⟨⟨⟨neg_lt_zero.mpr B.radius_pos,B.radius_pos⟩,⟨neg_lt_zero.mpr B.radius_pos,B.radius_pos⟩⟩,
    half_pos ht,half_lt_self ht⟩

/-- A compact physical cutoff of an original weak graph with zero normal
trace has the original Dirichlet zero trace on the entire domain. -/
theorem hasZeroBoundaryValues_cutoff_of_normalTrace_zero {q : ℕ} (hΩ : IsBoundedDomain Ω)
    {t : ℝ} (ht : 0 < t) (htR : t ≤ B.radius)
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 ⟨Ω,hΩ.1⟩ u D)
    (H : B.NormalTrace q t) (hH : B.RepresentsNormalTrace u H) (hZero : H ⟨0,le_rfl,ht.le⟩ = 0)
    {χ : Point → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hSupp : tsupport χ ⊆ (B.physicalRectangle (-t) t).val) :
    ∃ G : Point → HarmonicMaps.Gradient 3 q,
      HasZeroBoundaryValues ⟨Ω,hΩ.1⟩ (fun x => χ x • u x) G := by
  let E := B.normalEuclideanChart
  let V := B.flatSlab t
  let W := B.flatRectangle (-t) t
  let v : Point → Ambient q := u ∘ E
  let J (x : Point) (i : Fin 3) := ∑ j : Fin 3, (fderiv ℝ E x (EuclideanSpace.single i 1)) j • D (E x) j
  have hv : MemW12 V v J := B.memW12_normalChart hΩ.1 htR hu
  have hCompEq : (fun p => v (E.symm p)) = u := funext fun p => congrArg u (E.apply_symm_apply p)
  have hF := B.memW12_flatSlab_zeroAcrossWall ht hv H (hCompEq.symm ▸ hH) hZero
  let θ := χ ∘ E
  have hθ : ContDiff ℝ ∞ θ := hχ.comp B.normalEuclideanChart_smooth
  have hθts : tsupport θ = E ⁻¹' tsupport χ := tsupport_comp_eq_preimage χ E
  have hθc : HasCompactSupport θ := by
    rw [HasCompactSupport,hθts]
    exact E.isCompact_preimage.2 hc
  have hθW : tsupport θ ⊆ W.val := by
    intro x hx
    rw [hθts] at hx
    obtain ⟨y,hy,hEq⟩ := hSupp hx
    exact E.injective hEq ▸ hy
  let z (y : Point) := if 0 < (normalCoordinateEquiv y).2 0 then v y else 0
  let Z (y : Point) (i : Fin 3) := if 0 < (normalCoordinateEquiv y).2 0 then J y i else 0
  let w (y : Point) := θ y • z y
  let G (y : Point) (i : Fin 3) := coordinateDerivative θ hθ i y • z y + θ y • Z y i
  have hw : MemW12 ⟨univ,isOpen_univ⟩ w G := hF.to_memW12Loc.smoothCutoff_univ hθ hθc hθW
  have hVeq : ∀ x ∈ W.val, x ∉ V.val → ¬ 0 < (normalCoordinateEquiv x).2 0 :=
    fun _ hx hn hp => hn ⟨hx.1,hp,hx.2.2⟩
  have hOutside (x : Point) (hx : x ∉ V.val) : w x = 0 ∧ G x = 0 := by
    by_cases hxW : x ∈ W.val
    · have hFalse := hVeq x hxW hx
      refine ⟨by simp only [w,z,hFalse,if_false,smul_zero],funext fun i => ?_⟩
      simp only [G,z,Z,hFalse,if_false,smul_zero,add_zero,Pi.zero_apply]
    · have hθ₀ : θ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxW (hθW h))
      have hd (i : Fin 3) : coordinateDerivative θ hθ i x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hxW (hθW (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) h)))
      exact ⟨by simp only [w,hθ₀,zero_smul],funext fun i => by simp only [G,hθ₀,hd,zero_smul,add_zero,Pi.zero_apply]⟩
  have hwI : V.val.indicator w = w := indicator_eq_self.mpr (fun x hx => of_not_not fun hn => hx (hOutside x hn).1)
  have hGI : V.val.indicator G = G := indicator_eq_self.mpr (fun x hx => of_not_not fun hn => hx (hOutside x hn).2)
  have hZ : MemW12 ⟨univ,isOpen_univ⟩ (V.val.indicator w) (V.val.indicator G) := by rwa [hwI,hGI]
  have hVWk : MemW12 V w G := ⟨hw.1.mono (subset_univ _),
    hw.2.1.mono_measure (Measure.restrict_mono_set volume (subset_univ _)),
    fun i => (hw.2.2 i).mono_measure (Measure.restrict_mono_set volume (subset_univ _))⟩
  obtain ⟨c,hcV⟩ := B.exists_mem_flatSlab ht
  have hZeroFlat := hasZeroBoundaryValues_of_convex_zeroExtension V (B.convex_flatSlab t)
    (B.isBounded_flatSlab htR).isCompact_closure hcV hVWk hZ
  obtain ⟨A,hA⟩ := Thesis.HasZeroBoundaryValues.smoothPushforward_zeroExtension
    (V := (⟨Ω,hΩ.1⟩ : OpenDomain 3)) hZeroFlat hZ E B.normalEuclideanChart_inverse_smooth
    B.normalEuclideanChart_measurePreserving hΩ.2.2 (B.flatSlab_mapsTo_domain htR)
  refine ⟨A,hA.congr_ae ?_ EventuallyEq.rfl⟩
  filter_upwards [ae_restrict_mem hΩ.1.measurableSet] with x hx
  rw [hwI]
  change θ (E.symm x) • z (E.symm x) = χ x • u x
  have hθx : θ (E.symm x) = χ x := congrArg χ (E.apply_symm_apply x)
  rw [hθx]
  by_cases hχx : χ x = 0
  · rw [hχx,zero_smul,zero_smul]
  · obtain ⟨y,hy,hyEq⟩ := hSupp (subset_tsupport χ hχx)
    have hY : y = E.symm x := E.injective (hyEq.trans (E.apply_symm_apply x).symm)
    have hY' : E.symm x ∈ W.val := hY ▸ hy
    have hPos : 0 < (normalCoordinateEquiv (E.symm x)).2 0 :=
      (B.normalEuclideanChart_mem_domain_iff (neg_le_neg htR) htR hY').1 ((E.apply_symm_apply x).symm ▸ hx)
    rw [show z (E.symm x) = u x by
      change (if 0 < (normalCoordinateEquiv (E.symm x)).2 0 then u (E (E.symm x)) else 0) = _
      rw [if_pos hPos,E.apply_symm_apply]]

end Thesis.SmoothDomainEpigraphBox
