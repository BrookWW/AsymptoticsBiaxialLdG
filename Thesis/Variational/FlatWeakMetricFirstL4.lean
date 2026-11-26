module

public import Thesis.Variational.FlatWallWeakHessianCutoff
public import Thesis.Upstream.CompactWeakGraphSobolev
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-! Fourth-integrability of the lower-order columns on the interior of a flat patch. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal

namespace Thesis

theorem hasCompactSupport_localWeakCutoffValue {q : ℕ} {χ : Point → ℝ}
    (hχ : HasCompactSupport χ) (u : Point → Ambient q) :
    HasCompactSupport (localWeakCutoffValue χ u) :=
  hχ.smul_right

theorem hasCompactSupport_localWeakCutoffColumn {q : ℕ} {χ : Point → ℝ}
    (hχ : HasCompactSupport χ) (u : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q)
    (i : Fin 3) : HasCompactSupport (fun x => localWeakCutoffColumns χ u D x i) :=
  ((hχ.fderiv_apply ℝ (axis i)).smul_right (f' := u)).add
    (hχ.smul_right (f' := fun x => D x i))

private theorem hasCompactSupport_oddFlatWallWeakCutoffValue {q : ℕ} {χ : Point → ℝ}
    (hχ : HasCompactSupport χ) (u : Point → Ambient q) :
    HasCompactSupport (oddFlatWallWeakValue (localWeakCutoffValue χ u)) := by
  have h := hasCompactSupport_localWeakCutoffValue hχ u
  exact h.sub (h.comp_homeomorph normalReflection.toHomeomorph)

private theorem hasCompactSupport_oddFlatWallWeakCutoffColumn {q : ℕ} {χ : Point → ℝ}
    (hχ : HasCompactSupport χ) (u : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q)
    (i : Fin 3) :
    HasCompactSupport (fun x => oddFlatWallWeakColumns (localWeakCutoffColumns χ u D) x i) := by
  have h := hasCompactSupport_localWeakCutoffColumn hχ u D i
  have hR := h.comp_homeomorph normalReflection.toHomeomorph
  exact h.sub (hR.smul_left (f := fun _ => flatReflectionSign i))

private theorem oddFlatWallWeakCutoff_eqOn_upper_plateau {q : ℕ}
    {W P : Set Point} (hP : IsOpen P)
    {χ : Point → ℝ} (hχS : tsupport χ ⊆ W) (hχ : EqOn χ (fun _ => 1) P)
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hZero : ∀ x ∈ W, x ∉ upperCoordinateHalfSpace.val → u x=0 ∧ D x=0) :
    EqOn (oddFlatWallWeakValue (localWeakCutoffValue χ u)) u (upperCoordinateHalfSpace.val∩P) ∧
      EqOn (oddFlatWallWeakColumns (localWeakCutoffColumns χ u D)) D
        (upperCoordinateHalfSpace.val∩P) := by
  let H : Point → Fin 3 → HarmonicMaps.Gradient 3 q := 0
  obtain ⟨hV,hD,_⟩ := localWeakCutoff_eqOn_open_plateau hP hχ u D H
  have hDχ (i : Fin 3) : tsupport (coordDeriv i χ) ⊆ W :=
    (tsupport_fderiv_apply_subset ℝ (axis i)).trans hχS
  have hLower (x : Point) (hx : x ∉ upperCoordinateHalfSpace.val) :
      localWeakCutoffValue χ u x = 0 ∧ localWeakCutoffColumns χ u D x = 0 := by
    by_cases hW : x ∈ W
    · have h := hZero x hW hx
      refine ⟨?_,funext fun i => ?_⟩
      · simp only [localWeakCutoffValue,h.1,smul_zero]
      · simp only [localWeakCutoffColumns,h.1,h.2,Pi.zero_apply,smul_zero,zero_add]
    · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hW (hχS h))
      refine ⟨?_,funext fun i => ?_⟩
      · simp only [localWeakCutoffValue,hz,zero_smul]
      · have hzD : coordDeriv i χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hW (hDχ i h))
        simp only [localWeakCutoffColumns,hz,hzD,zero_smul,zero_add,Pi.zero_apply]
  have hNeg (x : Point) (hx : x ∈ upperCoordinateHalfSpace.val) :
      normalReflection x ∉ upperCoordinateHalfSpace.val := by
    change ¬ 0 < normalReflection x 2
    have hx' : 0 < x 2 := hx
    change ¬ 0 < -(x 2)
    exact not_lt_of_ge (neg_nonpos.mpr hx'.le)
  refine ⟨fun x hx => ?_,fun x hx => ?_⟩
  · simp only [oddFlatWallWeakValue,(hLower _ (hNeg x hx.1)).1,sub_zero,hV hx.2]
  · funext i
    simp only [oddFlatWallWeakColumns,(hLower _ (hNeg x hx.1)).2,Pi.zero_apply,smul_zero,sub_zero,hD hx.2]

/-- Two weak rows of the original zero extension give the lower-order
(L^4) terms on the smaller positive half-ball, via one enclosing cutoff. -/
theorem memLp_four_firstColumns_on_flat_halfBall {R : ℝ} (hR : 0 < R)
    {u : Point → Ambient 5} {D : Point → HarmonicMaps.Gradient 3 5}
    {H : Point → Fin 3 → HarmonicMaps.Gradient 3 5}
    (hu : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D)
    (hZero : ∀ x ∈ ball (0 : Point) R, x ∉ upperCoordinateHalfSpace.val → u x=0 ∧ D x=0)
    (hUpper : ∀ i, MemW12 (⟨upperCoordinateHalfSpace.val∩ball (0 : Point) R,
      upperCoordinateHalfSpace.property.inter isOpen_ball⟩ : OpenDomain 3) (fun x => D x i) (fun x => H x i))
    (hT : ∀ i ≠ (2 : Fin 3), ∃ T : Point → HarmonicMaps.Gradient 3 5,
      MemW12 (ballDomain (0 : Point) R) (fun x => D x i) T) :
    MemLp u 4 (volume.restrict (upperCoordinateHalfSpace.val∩ball (0 : Point) (R/2))) ∧
      ∀ i, MemLp (fun x => D x i) 4
        (volume.restrict (upperCoordinateHalfSpace.val∩ball (0 : Point) (R/2))) := by
  let b : ContDiffBump (0 : Point) := ⟨R/2,3*R/4,by positivity,by linarith only [hR]⟩
  let χ : Point → ℝ := b
  have hχ : ContDiff ℝ ∞ χ := b.contDiff
  have hc : HasCompactSupport χ := b.hasCompactSupport
  have hχS : tsupport χ ⊆ ball (0 : Point) R := b.tsupport_eq.le.trans
    (closedBall_subset_ball (by change 3*R/4 < R; linarith only [hR]))
  obtain ⟨hV,hG⟩ := memW12_oddFlatWallWeakHessian_cutoff_reflection (ballDomain (0 : Point) R)
    isBounded_ball hχ hc hχS hu hZero hUpper hT
  let P := ball (0 : Point) (R/2)
  let V := upperCoordinateHalfSpace.val ∩ P
  have hVμ : MeasurableSet V := (upperCoordinateHalfSpace.property.inter isOpen_ball).measurableSet
  have hFix : EqOn χ (fun _ => 1) P := fun x hx => b.one_of_mem_closedBall (ball_subset_closedBall hx)
  obtain ⟨hEq₀,hEq₁⟩ := oddFlatWallWeakCutoff_eqOn_upper_plateau
    (P := P) isOpen_ball hχS hFix hZero
  have h₀ := memLp_four_of_compact_memW12_univ hV (hasCompactSupport_oddFlatWallWeakCutoffValue hc u)
  have h₁ (i : Fin 3) := memLp_four_of_compact_memW12_univ (hG i)
    (hasCompactSupport_oddFlatWallWeakCutoffColumn hc u D i)
  refine ⟨MemLp.ae_eq ?_ (h₀.mono_measure Measure.restrict_le_self),
    fun i => MemLp.ae_eq ?_ ((h₁ i).mono_measure Measure.restrict_le_self)⟩
  · exact (ae_restrict_mem hVμ).mono (fun x hx => hEq₀ hx)
  · exact (ae_restrict_mem hVμ).mono (fun x hx => congrFun (hEq₁ hx) i)

end Thesis
