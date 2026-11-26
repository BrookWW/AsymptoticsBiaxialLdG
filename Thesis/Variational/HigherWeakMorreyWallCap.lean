module

public import Thesis.Variational.HigherWeakMorreyClosure
public import Thesis.Variational.FlatWallWeakHessianCutoff
import Thesis.Variational.ClosedConvexDerivativeColumns

/-! Iterated weak regularity through a flat wall on a bounded physical cap. -/

public section

noncomputable section

open Filter Function HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal

namespace Thesis

private theorem exists_weakMorreyRepresentative_on_smaller_flat_cap {q : ℕ}
    {a : Point} {R p : ℝ} (hR : 0 < R) (hp : 3 < p)
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 (⟨upperCoordinateHalfSpace.val ∩ ball a R,
      upperCoordinateHalfSpace.property.inter isOpen_ball⟩ : OpenDomain 3) u D)
    (hLp : MemLp u (ENNReal.ofReal p) (volume.restrict (upperCoordinateHalfSpace.val ∩ ball a R)))
    (hDLp : ∀ j, MemLp (fun x => D x j) (ENNReal.ofReal p)
      (volume.restrict (upperCoordinateHalfSpace.val ∩ ball a R))) :
    ∃ v : Point → Ambient q, u =ᵐ[volume.restrict (upperCoordinateHalfSpace.val ∩ ball a (R/4))] v ∧
      ContinuousOn v (closure (upperCoordinateHalfSpace.val ∩ ball a (R/4))) := by
  let U := upperCoordinateHalfSpace
  let V := ballDomain a R
  let W := U.val ∩ ball a (R/4)
  let χ : ContDiffBump a := ⟨R/2,3*R/4,half_pos hR,by linarith only [hR]⟩
  have hχ : ContDiff ℝ ∞ (χ : Point → ℝ) := χ.contDiff
  have hχc : HasCompactSupport (χ : Point → ℝ) := χ.hasCompactSupport
  have hχs : tsupport (χ : Point → ℝ) ⊆ V.val := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (show 3*R/4 < R by linarith only [hR])
  let w (x : Point) := χ x • u x
  let G (x : Point) (j : Fin 3) := coordDeriv j χ x • u x + χ x • D x j
  have hGW : MemW12 U w G := memW12_smul_relative_cutoff (U := U) (W := V) isBounded_ball hu hχ hχc hχs
  have hC (j : Fin 3) : ContDiff ℝ ∞ (coordDeriv j χ) :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hS (j : Fin 3) : tsupport (coordDeriv j χ) ⊆ V.val :=
    (tsupport_fderiv_apply_subset ℝ (axis j)).trans hχs
  have hLpG (j : Fin 3) : MemLp (fun x => G x j) (ENNReal.ofReal p) (volume.restrict U.val) :=
    (memLp_smul_patch_cutoff (U := U) (W := V) hLp
      ((hC j).continuous.memLp_top_of_hasCompactSupport (hχc.fderiv_apply ℝ (axis j)) _)
      (hS j)).add (memLp_smul_patch_cutoff (U := U) (W := V) (hDLp j)
        (hχ.continuous.memLp_top_of_hasCompactSupport hχc _) hχs)
  have hEven := memW12_evenFlatWallWeakReflection hGW
  have hEvenLp (j : Fin 3) : MemLp (fun x => evenFlatWallWeakColumns G x j)
      (ENNReal.ofReal p) (volume : Measure Point) := by
    have hI := (memLp_indicator_iff_restrict U.property.measurableSet).2 (hLpG j)
    exact hI.add ((hI.comp_measurePreserving normalReflection.measurePreserving).const_smul (flatReflectionSign j))
  have hμ : volume.restrict V.val ≤ volume.restrict (univ : Set Point) :=
    Measure.restrict_mono_set _ (subset_univ _)
  have hRGraph : MemW12 V (evenFlatWallWeakValue w) (evenFlatWallWeakColumns G) :=
    ⟨hEven.1.mono (subset_univ _),hEven.2.1.mono_measure hμ,(fun j => (hEven.2.2 j).mono_measure hμ)⟩
  obtain ⟨v,hv,hCv,_,_,_⟩ := exists_halfBall_holder_rep_of_weakColumns hR hp hRGraph
    (fun j => (hEvenLp j).mono_measure Measure.restrict_le_self)
  have hWopen : IsOpen W := U.property.inter isOpen_ball
  have hWB : W ⊆ ball a (R/2) :=
    inter_subset_right.trans (ball_subset_ball (by linarith only [hR]))
  have hWC : closure W ⊆ ball a (R/2) :=
    (closure_minimal (inter_subset_right.trans ball_subset_closedBall) isClosed_closedBall).trans
      (closedBall_subset_ball (by linarith only [hR]))
  have hEq : u =ᵐ[volume.restrict W] evenFlatWallWeakValue w := by
    filter_upwards [ae_restrict_mem hWopen.measurableSet] with x hx
    rw [evenFlatWallWeakValue_eq_upper w hx.1]
    change u x = χ x • u x
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall (hWB hx)),one_smul]
  exact ⟨v,hEq.trans (ae_restrict_of_ae_restrict_of_subset hWB hv),hCv.mono hWC⟩

theorem flatWall_smaller_cap_nonempty {a : Point} (ha : a ∈ flatWall)
    {R : ℝ} (hR : 0 < R) : (upperCoordinateHalfSpace.val ∩ ball a (R/4)).Nonempty := by
  refine ⟨a + (R/8) • axis 2,?_⟩
  constructor
  · have ha' : a 2 = 0 := ha
    change 0 < (a+(R/8) • axis 2) 2
    simp [ha',axis]
    positivity
  · rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,
      show ‖axis 2‖ = 1 by simp [axis],mul_one,Real.norm_of_nonneg (by positivity : 0 ≤ R/8)]
    linarith only [hR]

/-- The cap has true regularity through the flat wall and through all
points in its smaller closed ball. Only the larger open half ball is used
for the displayed weak derivatives. -/
theorem exists_contDiffOn_closure_of_weakLpDerivatives_on_smaller_flat_cap {q : ℕ}
    {a : Point} (ha : a ∈ flatWall) {R p : ℝ} (hR : 0 < R) (hp : 3 < p) (k : ℕ)
    {u : Point → Ambient q}
    (hu : HasWeakLpDerivatives (upperCoordinateHalfSpace.val ∩ ball a R) univ
      (ENNReal.ofReal p) (k+1) u) :
    ∃ v : Point → Ambient q,
      u =ᵐ[volume.restrict (upperCoordinateHalfSpace.val ∩ ball a (R/4))] v ∧
      ContDiffOn ℝ (k : ℕ∞ω) v (closure (upperCoordinateHalfSpace.val ∩ ball a (R/4))) := by
  let U := upperCoordinateHalfSpace
  let V : OpenDomain 3 := ⟨U.val ∩ ball a R,U.property.inter isOpen_ball⟩
  let W : OpenDomain 3 := ⟨U.val ∩ ball a (R/4),U.property.inter isOpen_ball⟩
  have hB : Bornology.IsBounded V.val := isBounded_ball.subset inter_subset_right
  have hSub : W.val ⊆ V.val :=
    inter_subset_inter_right _ (ball_subset_ball (by linarith only [hR]))
  have hHalf : Convex ℝ U.val :=
    convex_halfSpace_gt (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).toLinearMap.isLinear 0
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal (by linarith only [hp])
  refine exists_contDiffOn_closure_of_weakLpDerivatives_on_convex_cap V W hB hSub
    (hHalf.inter (convex_ball a _)) (flatWall_smaller_cap_nonempty ha hR) hp2 ?_ k hu
  exact fun h hf hD => exists_weakMorreyRepresentative_on_smaller_flat_cap hR hp h hf hD

/-- When the weak field already has continuous values on the smaller closed
cap, those exact values have the indicated classical order. -/
theorem contDiffOn_closure_of_continuous_weakLpDerivatives_on_smaller_flat_cap {q : ℕ}
    {a : Point} (ha : a ∈ flatWall) {R p : ℝ} (hR : 0 < R) (hp : 3 < p) (k : ℕ)
    {u : Point → Ambient q}
    (hC : ContinuousOn u (closure (upperCoordinateHalfSpace.val ∩ ball a (R/4))))
    (hu : HasWeakLpDerivatives (upperCoordinateHalfSpace.val ∩ ball a R) univ
      (ENNReal.ofReal p) (k+1) u) :
    ContDiffOn ℝ (k : ℕ∞ω) u (closure (upperCoordinateHalfSpace.val ∩ ball a (R/4))) := by
  obtain ⟨v,hV,hVC⟩ :=
    exists_contDiffOn_closure_of_weakLpDerivatives_on_smaller_flat_cap ha hR hp k hu
  have hO : IsOpen (upperCoordinateHalfSpace.val ∩ ball a (R/4)) :=
    upperCoordinateHalfSpace.property.inter isOpen_ball
  have he := Measure.eqOn_open_of_ae_eq hV hO
    (hC.mono subset_closure) (hVC.continuousOn.mono subset_closure)
  exact hVC.congr (he.of_subset_closure hC hVC.continuousOn subset_closure Subset.rfl)

end Thesis
