module

public import Thesis.MeasureGeometry.TransverseMeridian
public import Thesis.MeasureGeometry.NormalPlaneDeformation

/-! Comparing the actual transverse disk boundary with arbitrarily small
orthogonal meridians in the same regular region. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

private theorem exists_pos_lt_avoiding_countable {A : Set ℝ} (hA : A.Countable) {R : ℝ}
    (hR : 0 < R) : ∃ t ∈ Ioo (0 : ℝ) R, t ∉ A := by
  by_contra! h
  have hMass := (measure_mono (μ := (volume : Measure ℝ)) (show Ioo (0 : ℝ) R ⊆ A from h)).trans_eq
    (hA.measure_zero volume)
  rw [Real.volume_Ioo, sub_zero] at hMass
  exact (ENNReal.ofReal_pos.mpr hR).not_ge hMass

private theorem injective_axisChartPlane (B : OrthonormalBasis (Fin 3) ℝ Point) :
    Function.Injective (axisChartPlane B) := by
  intro y z h
  simpa only [axisChartTransverseCoordinates_axisChartPlane] using congrArg
    (axisChartTransverseCoordinates B) h

private theorem exists_vacuum_circle_restriction (a : BulkCoefficients)
    {W : Set Point} {Q : Point → S0} (hQ : ContinuousOn Q W) (hVac : MapsTo Q W (vacuum a))
    {F : NativeCircle → Point} (hF : Continuous F) (hFW : ∀ z, F z ∈ W) :
    ∃ b : C(NativeCircle, vacuum a), ∀ z, (b z).val = Q (F z) :=
  ⟨⟨fun z => ⟨Q (F z), hVac (hFW z)⟩, (hQ.comp_continuous hF hFW).subtype_mk _⟩, fun _ => rfl⟩

private theorem countable_bad_meridian_radii {P : Set Point} (hP : P.Countable)
    {u : Plane → Point} {D : Set Plane} (hI : InjOn u D) (y : Plane) :
    ((fun z : Plane => ‖z - y‖) '' (D ∩ (u ⁻¹' P))).Countable :=
  ((show MapsTo u (D ∩ (u ⁻¹' P)) P from fun _ h => h.2).countable_of_injOn
    (hI.mono inter_subset_left) hP).image _

/-- Each admissible embedded transverse disk gives the same free class,
up to circle reversal, as an arbitrarily small round orthogonal
meridian of the actual edge. -/
theorem transverse_disk_meridian_cost_eq_arbitrarily_small_orthogonal
    (hAvoid : External.RelativeAnnulusPointAvoidance) (a : BulkCoefficients)
    {Ω S Spt : Set Point} (hΩ : IsOpen Ω) (hS : IsClosed S)
    (hLoc : LocallyFiniteIn (Ω \ S) Spt) (hSpt : Spt ⊆ Ω \ S)
    {Q : Point → S0} (hQ : ContinuousOn Q ((Ω \ S) \ Spt))
    (hVac : MapsTo Q ((Ω \ S) \ Spt) (vacuum a))
    (B : OrthonormalBasis (Fin 3) ℝ Point) {d : Plane → Point} (hd : IsSmoothDiskEmbedding d)
    (hDΩ : d '' Disk ⊆ Ω) {y : Plane} (hy : y ∈ ball (0 : Plane) 1)
    (hMeet : d '' Disk ∩ S = {d y})
    (hTrans : B 2 ∉ LinearMap.range (fderiv ℝ d y).toLinearMap)
    (hOuter : Disjoint (d '' sphere (0 : Plane) 1) Spt)
    {R : ℝ} (hR : 0 < R) (hBΩ : ball (d y) R ⊆ Ω)
    (hGerm : ∀ x ∈ ball (d y) R, x ∈ S ↔ axisChartTransverseCoordinates B (x - d y) = 0)
    (b₀ : C(NativeCircle, vacuum a)) (hb₀ : ∀ z, (b₀ z).val = Q (d z.val)) :
    ∀ σ : ℝ, 0 < σ → ∃ δ ∈ Ioo 0 σ, ∃ b : C(NativeCircle, vacuum a),
      (∀ z, (b z).val = Q (d y + δ • axisChartPlane B z.val)) ∧
      (∀ z : NativeCircle, d y + δ • axisChartPlane B z.val ∉ Spt) ∧
      (∃ (w : ℂ) (hw : ‖w‖ = 1) (rev : Bool),
        b₀.Homotopic (b.comp (nativeCircle_unitComplex w hw rev))) ∧
      nativeVacuumCircleCost a b₀ = nativeVacuumCircleCost a b := by
  intro σ hσ
  let x := d y
  let A := (axisChartTransverseCoordinates B).comp (fderiv ℝ d y)
  let E := axisChartPlane B
  let W := (Ω \ S) \ Spt
  have hA : Function.Injective A := transverse_meridian_normal_derivative_injective B hd hy hTrans
  have hE : Function.Injective E := injective_axisChartPlane B
  obtain ⟨w, hw, rev, F, hF, hF₀, hFne, hF₁⟩ := exists_nondegenerate_normalPlane_deformation A hA
  obtain ⟨δ₀, hδ₀, hLocal⟩ := exists_small_meridian_homotopy_to_normal_ellipse
    hAvoid a hΩ hS hLoc hQ hVac B hd hy hTrans hR hBΩ hGerm
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ sphere (0 : Plane) 1) :=
    isCompact_Icc.prod (isCompact_sphere _ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hF.continuous.continuousOn
  let K := max 0 M
  have hK₀ : 0 ≤ K := le_max_left _ _
  have hKBound (t : unitInterval) (z : NativeCircle) : ‖F (t.val,z.val)‖ ≤ K := by
    have hp : (t.val,z.val) ∈ Icc (0 : ℝ) 1 ×ˢ sphere (0 : Plane) 1 := ⟨t.property,z.property⟩
    exact (hM (t.val,z.val) hp).trans (le_max_right 0 M)
  let δMax := min σ (min δ₀ (R / (K + 1)))
  have hδMax : 0 < δMax := lt_min hσ (lt_min hδ₀ (div_pos hR (by positivity)))
  have hPC := locallyFiniteIn_countable (hΩ.sdiff hS) hSpt hLoc
  let Dbad := (fun z : Plane => ‖z - y‖) '' (Disk ∩ d ⁻¹' Spt)
  let Ebad := (fun z : Plane => ‖z - (0 : Plane)‖) '' (univ ∩ (fun z : Plane => x + E (A z)) ⁻¹' Spt)
  let Cbad := (fun z : Plane => ‖z - (0 : Plane)‖) '' (univ ∩ (fun z : Plane => x + E z) ⁻¹' Spt)
  have hDcount : Dbad.Countable := countable_bad_meridian_radii hPC hd.2.1 y
  have hECi : Function.Injective (fun z : Plane => x + E (A z)) := fun u v hu =>
    hA (hE (add_left_cancel hu))
  have hCCi : Function.Injective (fun z : Plane => x + E z) := fun u v hu => hE (add_left_cancel hu)
  have hEcount : Ebad.Countable := countable_bad_meridian_radii hPC hECi.injOn 0
  have hCcount : Cbad.Countable := countable_bad_meridian_radii hPC hCCi.injOn 0
  obtain ⟨δ, hδ, hNo⟩ := exists_pos_lt_avoiding_countable (hDcount.union (hEcount.union hCcount)) hδMax
  have hδσ : δ < σ := hδ.2.trans_le (min_le_left _ _)
  have hδ₀' : δ < δ₀ := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδR : δ < R / (K + 1) := hδ.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hδR' : δ * (K + 1) < R := (lt_div_iff₀ (by positivity)).mp hδR
  have hδR₀ : δ < R := by
    have h := mul_nonneg hδ.1.le hK₀
    linarith only [h, hδR']
  let dSmall (z : NativeCircle) := d (y + δ • z.val)
  let ellipse (z : NativeCircle) := x + δ • E (A z.val)
  let normal (z : NativeCircle) := x + δ • E z.val
  have hδY : ‖y‖ + δ ≤ 1 := (hLocal δ ⟨hδ.1, hδ₀'⟩).1
  have hD (z : NativeCircle) : y + δ • z.val ∈ Disk := by
    apply mem_closedBall_zero_iff.mpr
    apply (norm_add_le _ _).trans
    rw [norm_smul, Real.norm_of_nonneg hδ.1.le, mem_sphere_zero_iff_norm.mp z.property, mul_one]
    exact hδY
  have hDsafe (z : NativeCircle) : dSmall z ∉ Spt := by
    intro h
    apply hNo
    refine Or.inl ⟨y + δ • z.val, ⟨hD z, h⟩, ?_⟩
    change ‖y + δ • z.val - y‖ = δ
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.1.le,
      mem_sphere_zero_iff_norm.mp z.property, mul_one]
  have hEsafe (z : NativeCircle) : ellipse z ∉ Spt := by
    intro h
    apply hNo
    refine Or.inr (Or.inl ⟨δ • z.val, ⟨mem_univ _, ?_⟩, ?_⟩)
    · change x + E (A (δ • z.val)) ∈ Spt
      rw [map_smul, map_smul]
      exact h
    · change ‖δ • z.val - (0 : Plane)‖ = δ
      rw [sub_zero, norm_smul, Real.norm_of_nonneg hδ.1.le,
        mem_sphere_zero_iff_norm.mp z.property, mul_one]
  have hCsafe (z : NativeCircle) : normal z ∉ Spt := by
    intro h
    apply hNo
    refine Or.inr (Or.inr ⟨δ • z.val, ⟨mem_univ _, ?_⟩, ?_⟩)
    · change x + E (δ • z.val) ∈ Spt
      rw [map_smul]
      exact h
    · change ‖δ • z.val - (0 : Plane)‖ = δ
      rw [sub_zero, norm_smul, Real.norm_of_nonneg hδ.1.le,
        mem_sphere_zero_iff_norm.mp z.property, mul_one]
  let H (p : unitInterval × NativeCircle) := x + δ • E (F (p.1.val,p.2.val))
  have hHcts : Continuous H := by
    dsimp only [H]
    have hParam : Continuous (fun p : unitInterval × NativeCircle => (p.1.val,p.2.val)) := by fun_prop
    exact continuous_const.add ((E.continuous.comp (hF.continuous.comp hParam)).const_smul δ)
  let H' : C(unitInterval × NativeCircle, Point) := ⟨H,hHcts⟩
  have hHBall (p : unitInterval × NativeCircle) : H' p ∈ ball x R := by
    rw [mem_ball, dist_eq_norm]
    change ‖x + δ • E (F (p.1.val,p.2.val)) - x‖ < R
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.1.le, norm_axisChartPlane]
    exact (mul_le_mul_of_nonneg_left ((hKBound p.1 p.2).trans (le_add_of_nonneg_right zero_le_one)) hδ.1.le).trans_lt hδR'
  have hHLine (p : unitInterval × NativeCircle) : H' p ∈ Ω \ S := by
    refine ⟨hBΩ (hHBall p), ?_⟩
    intro h
    have hP := (hGerm _ (hHBall p)).mp h
    change axisChartTransverseCoordinates B (x + δ • E (F (p.1.val,p.2.val)) - x) = 0 at hP
    rw [add_sub_cancel_left, map_smul, axisChartTransverseCoordinates_axisChartPlane] at hP
    have hZ : p.2.val ≠ 0 := by
      have hN := mem_sphere_zero_iff_norm.mp p.2.property
      exact norm_ne_zero_iff.1 (by rw [hN]; exact one_ne_zero)
    exact hFne p.1.val p.1.property p.2.val hZ ((smul_eq_zero.mp hP).resolve_left hδ.1.ne')
  have hSmooth : SmoothNativeAnnulus H' := by
    let G (p : ℝ × ℝ) := x + δ • E (F (p.1,(circleNativeParam p.2).val))
    have hPar : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1,(circleNativeParam p.2).val)) :=
      contDiff_fst.prodMk (contDiff_circleNativeParam_val_infty.comp contDiff_snd)
    have hG : ContDiff ℝ ∞ G := contDiff_const.add ((E.contDiff.comp (hF.comp hPar)).const_smul δ)
    exact ⟨G,hG.contDiffOn,fun _ _ => rfl⟩
  have hH₀ (z : NativeCircle) : H' (0,z) = ellipse z := by
    change x + δ • E (F (0,z.val)) = _
    rw [hF₀]
  have hH₁ (z : NativeCircle) : H' (1,z) = normal (nativeCircle_unitComplex w hw rev z) := by
    change x + δ • E (F (1,z.val)) = _
    rw [hF₁]
  have hDreg (z : NativeCircle) : dSmall z ∈ W := by
    refine ⟨⟨hDΩ ⟨y + δ • z.val, hD z, rfl⟩, ?_⟩, hDsafe z⟩
    intro h
    have hh : d (y + δ • z.val) = d y := Set.mem_singleton_iff.mp
      (hMeet ▸ (show dSmall z ∈ d '' Disk ∩ S from ⟨⟨_, hD z, rfl⟩, h⟩))
    have hP := (hd.2.1 (hD z) (ball_subset_closedBall hy) hh)
    have he : δ • z.val = 0 := add_left_cancel (hP.trans (add_zero y).symm)
    have hZ : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
    rw [(smul_eq_zero.mp he).resolve_left hδ.1.ne', norm_zero] at hZ
    norm_num at hZ
  have hEreg (z : NativeCircle) : ellipse z ∈ W := by
    refine ⟨?_, hEsafe z⟩
    rw [← hH₀]
    exact hHLine (0,z)
  have hCreg (z : NativeCircle) : normal z ∈ W := by
    have hball : normal z ∈ ball x R := by
      rw [mem_ball, dist_eq_norm]
      change ‖x + δ • E z.val - x‖ < R
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.1.le, norm_axisChartPlane,
        mem_sphere_zero_iff_norm.mp z.property, mul_one]
      exact hδR₀
    refine ⟨⟨hBΩ hball, ?_⟩, hCsafe z⟩
    intro h
    have hN := (hGerm _ hball).mp h
    change axisChartTransverseCoordinates B (x + δ • E z.val - x) = 0 at hN
    rw [add_sub_cancel_left, map_smul, axisChartTransverseCoordinates_axisChartPlane] at hN
    have hf : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
    rw [(smul_eq_zero.mp hN).resolve_left hδ.1.ne', norm_zero] at hf
    norm_num at hf
  have hSmallcont : Continuous dSmall := hd.1.continuousOn.comp_continuous (by fun_prop) hD
  have hEcont : Continuous ellipse := by dsimp [ellipse]; fun_prop
  have hCcont : Continuous normal := by dsimp [normal]; fun_prop
  obtain ⟨bS, hbS⟩ := exists_vacuum_circle_restriction a hQ hVac hSmallcont hDreg
  obtain ⟨bE, hbE⟩ := exists_vacuum_circle_restriction a hQ hVac hEcont hEreg
  obtain ⟨b, hb⟩ := exists_vacuum_circle_restriction a hQ hVac hCcont hCreg
  have hStart := nativeVacuum_homotopic_of_shrink_embedded_disk hAvoid a hΩ hS hLoc hQ hVac
    hd hDΩ hy hMeet hδ.1 hδY (fun z => ⟨fun h => (disjoint_left.mp hOuter) ⟨z.val,z.property,rfl⟩ h, hDsafe z⟩)
    b₀ bS hb₀ hbS
  have hMid := (hLocal δ ⟨hδ.1,hδ₀'⟩).2 (fun z => ⟨hDsafe z,hEsafe z⟩) bS bE hbS hbE
  let b' := b.comp (nativeCircle_unitComplex w hw rev)
  have hEnd := nativeVacuum_homotopic_of_regular_annulus hAvoid a (hΩ.sdiff hS) hLoc hQ hVac
    H' hSmooth hHLine (fun z => by rw [hH₀,hH₁]; exact ⟨hEsafe z,hCsafe _⟩) bE b'
    (fun z => (hbE z).trans (congrArg Q (hH₀ z)).symm)
    (fun z => (hb _).trans (congrArg Q (hH₁ z)).symm)
  have hHom := hStart.trans (hMid.trans hEnd)
  exact ⟨δ, ⟨hδ.1,hδσ⟩, b,hb,hCsafe,⟨w,hw,rev,hHom⟩,
    (nativeVacuumCircleCost_homotopic a hHom).trans (nativeVacuumCircleCost_comp_unitComplex a b w hw rev)⟩

end Thesis.MeasureGeometry
