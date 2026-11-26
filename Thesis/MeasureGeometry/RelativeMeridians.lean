module

public import Thesis.MeasureGeometry.MeridianTrace
public import Thesis.MeasureGeometry.MeridianCoordinates

/-! Boundary-fixed point avoidance for the meridian homotopies. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

/-- The smooth annulus is represented in actual periodic angular
coordinates, including its boundary curves. -/
def SmoothNativeAnnulus (F : C(unitInterval × NativeCircle, Point)) : Prop :=
  ∃ G : ℝ × ℝ → Point,
    ContDiffOn ℝ ∞ G (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) ∧
    ∀ (s : unitInterval) (t : ℝ), G (s.val, t) = F (s, circleNativeParam t)

/-- Standard boundary-fixed relative transversality of a smooth
two-dimensional annulus with respect to a finite set in an open
three-dimensional region. -/
def External.RelativeAnnulusPointAvoidance : Prop :=
  ∀ (U : Set Point), IsOpen U → ∀ (P : Finset Point) (F : C(unitInterval × NativeCircle, Point)),
    SmoothNativeAnnulus F → (∀ p, F p ∈ U) →
    (∀ z, F (0,z) ∉ P ∧ F (1,z) ∉ P) →
    ∃ G : C(unitInterval × NativeCircle, Point), (∀ p, G p ∈ U ∧ G p ∉ P) ∧
      ∀ z, G (0,z) = F (0,z) ∧ G (1,z) = F (1,z)

namespace MeasureGeometry

/-- A relative perturbation of the actual annulus avoids all the locally
finite point singularities while retaining its two boundary meridians. -/
theorem nativeVacuum_homotopic_of_regular_annulus
    (hAvoid : External.RelativeAnnulusPointAvoidance)
    (a : BulkCoefficients) {W Spt : Set Point} (hW : IsOpen W)
    (hLoc : LocallyFiniteIn W Spt) {Q : Point → S0}
    (hQ : ContinuousOn Q (W \ Spt)) (hVac : MapsTo Q (W \ Spt) (vacuum a))
    (F : C(unitInterval × NativeCircle, Point)) (hSmooth : SmoothNativeAnnulus F)
    (hFW : ∀ p, F p ∈ W) (hEnd : ∀ z, F (0,z) ∉ Spt ∧ F (1,z) ∉ Spt)
    (b₀ b₁ : C(NativeCircle, vacuum a))
    (hb₀ : ∀ z, (b₀ z).val = Q (F (0,z))) (hb₁ : ∀ z, (b₁ z).val = Q (F (1,z))) :
    b₀.Homotopic b₁ := by
  classical
  letI : CompactSpace NativeCircle := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let K := range F
  have hK : IsCompact K := isCompact_range F.continuous
  have hKW : K ⊆ W := by rintro _ ⟨p, rfl⟩; exact hFW p
  obtain ⟨δ, hδ, hKWδ⟩ := hK.exists_cthickening_subset_open hW hKW
  let U := thickening δ K
  let P : Set Point := Spt ∩ cthickening δ K
  have hP : P.Finite := hLoc _ hK.cthickening hKWδ
  have hU : IsOpen U := isOpen_thickening
  have hUδ : U ⊆ cthickening δ K := thickening_subset_cthickening _ _
  have hFU (p : unitInterval × NativeCircle) : F p ∈ U :=
    self_subset_thickening hδ K (mem_range_self p)
  have hFP (z : NativeCircle) : F (0,z) ∉ hP.toFinset ∧ F (1,z) ∉ hP.toFinset := by
    constructor
    · intro h; exact (hEnd z).1 (hP.mem_toFinset.mp h).1
    · intro h; exact (hEnd z).2 (hP.mem_toFinset.mp h).1
  obtain ⟨G, hGU, hGEnd⟩ := hAvoid U hU hP.toFinset F hSmooth hFU hFP
  have hGR (p : unitInterval × NativeCircle) : G p ∈ W \ Spt := by
    have hp := hUδ ((hGU p).1)
    refine ⟨hKWδ hp, ?_⟩
    intro h
    exact (hGU p).2 (hP.mem_toFinset.mpr (show G p ∈ P from ⟨h, hp⟩))
  have hGcts : Continuous (fun p => Q (G p)) := hQ.comp_continuous G.continuous hGR
  refine ⟨⟨⟨fun p => ⟨Q (G p), hVac (hGR p)⟩, hGcts.subtype_mk _⟩, ?_, ?_⟩⟩
  · intro z
    apply Subtype.ext
    change Q (G (0,z)) = (b₀ z).val
    rw [(hGEnd z).1, hb₀ z]
  · intro z
    apply Subtype.ext
    change Q (G (1,z)) = (b₁ z).val
    rw [(hGEnd z).2, hb₁ z]

private def shrinkDiskAnnulus (y : Plane) (δ : ℝ) (s : ℝ) (z : Plane) : Plane :=
  s • y + (1 - s + s * δ) • z

private theorem shrinkDiskAnnulus_in_disk {y z : Plane} {s δ : ℝ}
    (hy : ‖y‖ + δ ≤ 1) (hδ : 0 < δ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hz : ‖z‖ = 1) : shrinkDiskAnnulus y δ s z ∈ Disk := by
  apply mem_closedBall_zero_iff.mpr
  have hA : 0 ≤ 1 - s + s * δ := add_nonneg (sub_nonneg.mpr hs.2) (mul_nonneg hs.1 hδ.le)
  have h := norm_add_le (s • y) ((1 - s + s * δ) • z)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hs.1, Real.norm_of_nonneg hA, hz, mul_one] at h
  exact h.trans (by nlinarith only [mul_le_mul_of_nonneg_left hy hs.1])

private theorem shrinkDiskAnnulus_ne_intersection {y z : Plane} {s δ : ℝ}
    (hy : ‖y‖ < 1) (hδ : 0 < δ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hz : ‖z‖ = 1) : shrinkDiskAnnulus y δ s z ≠ y := by
  intro h
  have hA : 0 ≤ 1 - s + s * δ := add_nonneg (sub_nonneg.mpr hs.2) (mul_nonneg hs.1 hδ.le)
  have h' : (1 - s + s * δ) • z = (1 - s) • y := by
    dsimp only [shrinkDiskAnnulus] at h
    have hV := congrArg (fun v : Plane => v - s • y) h
    simp only [add_sub_cancel_left, sub_smul, one_smul] at hV ⊢
    exact hV
  have hn := congrArg norm h'
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hA,
    Real.norm_of_nonneg (sub_nonneg.mpr hs.2), hz, mul_one] at hn
  by_cases h₁ : s = 1
  · subst s
    norm_num at hn
    exact hδ.ne' hn
  · have hlt : 0 < 1 - s := sub_pos.mpr (lt_of_le_of_ne hs.2 h₁)
    have hsec := mul_lt_mul_of_pos_left hy hlt
    linarith only [hn, hsec, mul_nonneg hs.1 hδ.le]

/-- Away from its unique intersection with the line set, the embedded
disk gives the actual boundary-to-small-meridian free homotopy after
relative avoidance of point singularities. -/
theorem nativeVacuum_homotopic_of_shrink_embedded_disk
    (hAvoid : External.RelativeAnnulusPointAvoidance) (a : BulkCoefficients)
    {Ω S Spt : Set Point} (hΩ : IsOpen Ω) (hS : IsClosed S)
    (hLoc : LocallyFiniteIn (Ω \ S) Spt) {Q : Point → S0}
    (hQ : ContinuousOn Q ((Ω \ S) \ Spt)) (hVac : MapsTo Q ((Ω \ S) \ Spt) (vacuum a))
    {d : Plane → Point} (hd : IsSmoothDiskEmbedding d) (hDΩ : d '' Disk ⊆ Ω)
    {y : Plane} (hy : y ∈ ball (0 : Plane) 1) (hMeet : d '' Disk ∩ S = {d y})
    {δ : ℝ} (hδ : 0 < δ) (hδD : ‖y‖ + δ ≤ 1)
    (hEnd : ∀ z : NativeCircle, d z.val ∉ Spt ∧ d (y + δ • z.val) ∉ Spt)
    (b₀ b₁ : C(NativeCircle, vacuum a))
    (hb₀ : ∀ z, (b₀ z).val = Q (d z.val)) (hb₁ : ∀ z, (b₁ z).val = Q (d (y + δ • z.val))) :
    b₀.Homotopic b₁ := by
  let H (p : unitInterval × NativeCircle) := shrinkDiskAnnulus y δ p.1.val p.2.val
  have hH : Continuous H := by dsimp only [H, shrinkDiskAnnulus]; fun_prop
  have hHD (p : unitInterval × NativeCircle) : H p ∈ Disk :=
    shrinkDiskAnnulus_in_disk hδD hδ p.1.property (mem_sphere_zero_iff_norm.mp p.2.property)
  let F : C(unitInterval × NativeCircle, Point) :=
    ⟨fun p => d (H p), hd.1.continuousOn.comp_continuous hH hHD⟩
  have hF (p : unitInterval × NativeCircle) : F p ∈ Ω \ S := by
    refine ⟨hDΩ ⟨H p, hHD p, rfl⟩, ?_⟩
    intro h
    have hEq : d (H p) = d y := Set.mem_singleton_iff.mp
      (hMeet ▸ ⟨⟨H p, hHD p, rfl⟩, h⟩)
    exact shrinkDiskAnnulus_ne_intersection (mem_ball_zero_iff.mp hy) hδ p.1.property
      (mem_sphere_zero_iff_norm.mp p.2.property) (hd.2.1 (hHD p) (ball_subset_closedBall hy) hEq)
  have hSmooth : SmoothNativeAnnulus F := by
    let H' (p : ℝ × ℝ) := shrinkDiskAnnulus y δ p.1 (circleNativeParam p.2).val
    have hH' : ContDiff ℝ ∞ H' := by
      dsimp only [H', shrinkDiskAnnulus]
      have hParam : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (circleNativeParam p.2).val) :=
        contDiff_circleNativeParam_val_infty.comp contDiff_snd
      exact (contDiff_fst.smul contDiff_const).add
        (((contDiff_const.sub contDiff_fst).add (contDiff_fst.mul contDiff_const)).smul hParam)
    refine ⟨d ∘ H', hd.1.comp hH'.contDiffOn ?_, fun _ _ => rfl⟩
    intro p hp
    exact shrinkDiskAnnulus_in_disk hδD hδ hp.1 (mem_sphere_zero_iff_norm.mp (circleNativeParam p.2).property)
  have hF₀ (z : NativeCircle) : F (0,z) = d z.val := by
    change d (shrinkDiskAnnulus y δ 0 z.val) = _
    simp [shrinkDiskAnnulus]
  have hF₁ (z : NativeCircle) : F (1,z) = d (y + δ • z.val) := by
    change d (shrinkDiskAnnulus y δ 1 z.val) = _
    simp [shrinkDiskAnnulus]
  exact nativeVacuum_homotopic_of_regular_annulus hAvoid a (hΩ.sdiff hS) hLoc hQ hVac
    F hSmooth hF (fun z => by rw [hF₀, hF₁]; exact hEnd z) b₀ b₁
    (fun z => (hb₀ z).trans (congrArg Q (hF₀ z)).symm)
    (fun z => (hb₁ z).trans (congrArg Q (hF₁ z)).symm)

end MeasureGeometry
end Thesis
