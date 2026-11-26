module

public import Thesis.Upstream.AmbientZeroTraceExtension
public import Thesis.Variational.H10SobolevEmbedding
import Thesis.Interpolation.ConvexZeroTrace
import Thesis.Variational.WeakZeroTraceGraph
import HolderToCK.Analysis.ClassicalWeakGradient
import HarmonicMaps.Analysis.SobolevAECongruence
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Sobolev gain for an actual compactly supported whole-space graph. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal Matrix.Norms.Frobenius

namespace Thesis

private theorem weakGradient_ae_zero_off_tsupport {q : ℕ}
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (h : HasWeakGradient (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D) :
    ∀ᵐ x ∂(volume : Measure Point), x ∉ tsupport u → D x = 0 := by
  let V : OpenDomain 3 := ⟨(tsupport u)ᶜ,(isClosed_tsupport u).isOpen_compl⟩
  have h₀ : HasWeakGradient V (0 : Point → Ambient q) (0 : Point → HarmonicMaps.Gradient 3 q) := by
    change HasWeakGradient V (fun _ => (0 : Ambient q)) (fun _ _ => 0)
    have hv := HolderToCK.hasWeakGradient_of_contDiffOn_one V
      (f := fun (_ : Point) => (0 : Ambient q)) contDiffOn_const
    have he : (fun x : Point => fun i : Fin 3 =>
        fderiv ℝ (fun _ : Point => (0 : Ambient q)) x (EuclideanSpace.single i 1)) =
        fun _ _ => 0 := by
      funext x i
      exact DFunLike.congr_fun (hasFDerivAt_const (0 : Ambient q) x).fderiv _
    rwa [he] at hv
  have hu₀ : u =ᵐ[volume.restrict V.val] (0 : Point → Ambient q) := by
    filter_upwards [ae_restrict_mem (μ := volume) V.property.measurableSet] with x hx
    exact image_eq_zero_of_notMem_tsupport hx
  have hAE := (h.mono (Ω' := V) (subset_univ _)).ae_eq_of_ae_eq_map h₀ hu₀
  exact (ae_restrict_iff' V.property.measurableSet).1 hAE

/-- A compactly supported actual weak graph in dimension three belongs
to (L^6), by placing its zero-extension graph in an enclosing ball. -/
theorem memLp_six_of_compact_memW12_univ {u : Point → Ambient 5}
    {D : Point → HarmonicMaps.Gradient 3 5}
    (hu : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D) (huc : HasCompactSupport u) :
    MemLp u 6 (volume : Measure Point) := by
  obtain ⟨R,hR⟩ := huc.isCompact.isBounded.exists_norm_le
  let L := max R 0+1
  have hL : 0 < L := by dsimp only [L]; positivity
  let O := ballDomain (0 : Point) L
  have hU : tsupport u ⊆ O.val := by
    intro x hx
    exact mem_ball_zero_iff.mpr
      ((hR x hx).trans_lt ((le_max_left _ _).trans_lt (lt_add_one _)))
  have hUI : O.val.indicator u = u := indicator_eq_self.mpr ((subset_tsupport u).trans hU)
  let G := (tsupport u).indicator D
  have he : D =ᵐ[(volume : Measure Point).restrict univ] G := by
    rw [Measure.restrict_univ]
    filter_upwards [weakGradient_ae_zero_off_tsupport hu.1] with x hx
    by_cases hz : x ∈ tsupport u
    · rw [show G x = D x from indicator_of_mem hz D]
    · rw [show G x = 0 from indicator_of_notMem hz D]
      exact hx hz
  have huG := hu.congr_ae EventuallyEq.rfl he
  have hGI : O.val.indicator G = G := by
    apply indicator_eq_self.mpr
    intro x hx
    by_contra h
    exact hx (indicator_of_notMem (fun hh => h (hU hh)) D)
  have hμ : (volume : Measure Point).restrict O.val ≤ volume.restrict univ :=
    Measure.restrict_mono_set _ (subset_univ _)
  have hGraph : MemW12 O u G := ⟨huG.1.mono (subset_univ _),
    huG.2.1.mono_measure hμ,fun i => (huG.2.2 i).mono_measure hμ⟩
  have hZero : HasZeroBoundaryValues O u G := by
    refine hasZeroBoundaryValues_of_convex_zeroExtension O (convex_ball _ _)
      isBounded_ball.isCompact_closure (z := 0) (mem_ball_self hL) hGraph ?_
    rwa [hUI,hGI]
  let v (x : Point) := frobeniusCoordinateEquiv.symm (u x)
  let A (x : Point) (j : Fin 3) := frobeniusCoordinateEquiv.symm (G x j)
  have hv : frobeniusField v = u := funext fun x => frobeniusCoordinateEquiv.apply_symm_apply _
  have hA : frobeniusGradient A = G := funext fun x => funext fun i => frobeniusCoordinateEquiv.apply_symm_apply _
  have hTrace : HasZeroTrace O.val v A := by
    apply (hasZeroTrace_iff_hasZeroBoundaryValues O v A).2
    rwa [hv,hA]
  obtain ⟨w,hw,_⟩ := hTrace.exists_H10_with_ae_data O.property
  obtain ⟨_,hE⟩ := exists_h10_sobolevL6_bound
  have hv₆ : MemLp v 6 (volume.restrict O.val) :=
    MemLp.ae_eq hw (hE O.property.measurableSet w).1
  have hu₆ : MemLp u 6 (volume.restrict O.val) := by
    rw [← hv]
    exact (frobeniusCoordinateEquiv_memLp_iff _ _ _).2 hv₆
  rw [← hUI]
  exact (memLp_indicator_iff_restrict O.property.measurableSet).2 hu₆

/-- The actual whole-space graph also has fourth-integrable values. -/
theorem memLp_four_of_compact_memW12_univ {u : Point → Ambient 5}
    {D : Point → HarmonicMaps.Gradient 3 5}
    (hu : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D) (huc : HasCompactSupport u) :
    MemLp u 4 (volume : Measure Point) :=
  (memLp_six_of_compact_memW12_univ hu huc).mono_exponent_of_measure_support_ne_top
    (fun x hx => image_eq_zero_of_notMem_tsupport hx) huc.measure_lt_top.ne (by norm_num)

end Thesis
