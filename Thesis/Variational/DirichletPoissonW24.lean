module

public import Thesis.Variational.InteriorWeakPoissonFour
public import Thesis.Variational.DirichletPoissonH2
import HarmonicMaps.Analysis.SobolevAECongruence
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Global fourth-integrability of the original weak Dirichlet Hessian. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ENNReal Matrix.Norms.Frobenius

namespace Thesis

local instance dirichletPoissonW24ContinuousENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

private theorem memLp_four_restrict_union {q : ℕ} {A B : Set Point} {z : Point → Ambient q}
    (hA : MemLp z 4 (volume.restrict A)) (hB : MemLp z 4 (volume.restrict B)) :
    MemLp z 4 (volume.restrict (A ∪ B)) := by
  have hMeas := aestronglyMeasurable_union_iff.2 ⟨hA.1,hB.1⟩
  have hI : IntegrableOn (fun x => ‖z x‖^(4:ℝ)) A volume :=
    (integrable_norm_rpow_iff hA.1 (by norm_num) (by norm_num)).2 hA
  have hJ : IntegrableOn (fun x => ‖z x‖^(4:ℝ)) B volume :=
    (integrable_norm_rpow_iff hB.1 (by norm_num) (by norm_num)).2 hB
  apply (integrable_norm_rpow_iff hMeas (by norm_num) (by norm_num)).1
  rw [ENNReal.toReal_ofNat]
  exact hI.union hJ

private theorem memLp_four_restrict_finsetUnion {q : ℕ} {ι : Type*}
    (s : Finset ι) (A : ι → Set Point) {z : Point → Ambient q}
    (h : ∀ i ∈ s, MemLp z 4 (volume.restrict (A i))) :
    MemLp z 4 (volume.restrict (⋃ i ∈ s, A i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hRec =>
    have he : (⋃ j ∈ insert i s, A j) = A i ∪ ⋃ j ∈ s, A j := by
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
    rw [he]
    exact memLp_four_restrict_union (h i (Finset.mem_insert_self _ _))
      (hRec (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- For a weak Dirichlet Poisson field with fourth-integrable force, every
actual second weak column belongs to (L⁴) over the entire smooth domain. -/
theorem exists_smoothDomain_global_secondWeakColumns_four {U : Set Point} (hU : IsSmoothDomain U)
    {u f : Point → Ambient 5} {D : Point → HarmonicMaps.Gradient 3 5}
    (hData : AmbientDirichletPoissonData U u D f) (hf₄ : MemLp f 4 (volume : Measure Point)) :
    HasLocalSecondWeakColumnsLp ⟨U,hU.1.1⟩ D 4 := by
  classical
  obtain ⟨_,_,hW₂⟩ := exists_smoothDomain_global_secondWeakColumns (q := 5) hU
  obtain ⟨G,hG⟩ := hW₂ hData
  let K := closure U
  have hK : IsCompact K := hU.1.2.2.isCompact_closure
  have hLocal (x : K) :
      ∃ O : OpenDomain 3, (x : Point) ∈ O.val ∧
        ∀ j i, MemLp (fun y => G y j i) 4 (volume.restrict (O.val∩U)) := by
    have hx : (x : Point) ∈ U ∨ (x : Point) ∈ frontier U := by
      have hx₀ : (x : Point) ∈ closure U := x.property
      rwa [closure_eq_self_union_frontier,mem_union] at hx₀
    rcases hx with hx|hx
    · obtain ⟨R,hR,hInto⟩ := Metric.isOpen_iff.mp hU.1.1 x.val hx
      let A := ballDomain x.val R
      let O := ballDomain x.val (R/4)
      have hOInto : O.val ⊆ U := (ball_subset_ball (by linarith only [hR])).trans hInto
      have huA : MemW12 A u D := memW12_restrict_for_weakPoisson hData.sobolev (subset_univ _)
      have hGA (j : Fin 3) : MemW12 A (fun y => D y j) (fun y => G y j) :=
        memW12_restrict_for_weakPoisson (hG j).1 hInto
      refine ⟨O,mem_ball_self (by positivity),fun j i => ?_⟩
      rw [inter_eq_left.mpr hOInto]
      exact memLp_four_interiorWeakPoisson_secondColumns hR huA hGA
        (hData.force.mono_measure Measure.restrict_le_self) (hf₄.mono_measure Measure.restrict_le_self)
        (hData.equation.mono hInto) j i
    · obtain ⟨O,hxO,hPatch⟩ := exists_smoothDomain_boundary_secondWeakColumns_four hU hx
      let V : OpenDomain 3 := ⟨O.val∩U,O.property.inter hU.1.1⟩
      obtain ⟨J,hJ⟩ := hPatch hData hf₄
      refine ⟨O,hxO,fun j i => ?_⟩
      have hw : HasWeakGradient V (fun y => D y j) (fun y => G y j) :=
        (hG j).1.1.mono inter_subset_right
      have he := (hJ j).1.1.ae_eq hw
      exact MemLp.ae_eq (he.mono (fun y hy => congrFun hy i)) ((hJ j).2 i)
  choose O hO using hLocal
  have hCover : K ⊆ ⋃ x : K, (O x).val :=
    fun y hy => mem_iUnion.mpr ⟨⟨y,hy⟩,(hO ⟨y,hy⟩).1⟩
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover (fun x => (O x).val) (fun x => (O x).property) hCover
  let A (x : K) := (O x).val∩U
  have hU' : (⋃ x ∈ I, A x) = U := by
    ext y
    constructor
    · intro hy
      obtain ⟨x,hx⟩ := mem_iUnion.mp hy
      obtain ⟨_,hxy⟩ := mem_iUnion.mp hx
      exact hxy.2
    · intro hy
      obtain ⟨x,hx⟩ := mem_iUnion.mp (hI (subset_closure hy))
      obtain ⟨hxi,hxy⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨x,mem_iUnion.mpr ⟨hxi,hxy,hy⟩⟩
  refine ⟨G,fun j => ⟨(hG j).1,fun i => ?_⟩⟩
  change MemLp (fun x => G x j i) 4 (volume.restrict U)
  rw [← hU']
  exact memLp_four_restrict_finsetUnion I A (fun x _ => (hO x).2 j i)

/-- The actual intrinsic weak Dirichlet Poisson graph gives original tensor
Hessian columns in (L⁴) over the whole smooth domain. -/
theorem exists_H10_dirichletPoisson_secondWeakGradient_four {U : Set Point} (hU : IsSmoothDomain U)
    (w : H10 U) (g : Lp S0 2 (volume.restrict U)) (hg₄ : MemLp (fun x => g x) 4 (volume.restrict U))
    (hEq : ∀ v : H10 U, h10PrincipalPart U w v = ∫ x in U, frobeniusS0 (g x) (h10Value v x)) :
    ∃ H : Point → Fin 3 → Gradient,
      ∀ j, MemH1 U (fun x => h10Gradient w x j) (fun x => H x j) ∧
        ∀ i, MemLp (fun x => H x j i) 4 (volume.restrict U) := by
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  let O : OpenDomain 3 := ⟨U,hU.1.1⟩
  let D := frobeniusGradient (h10Gradient w)
  let D₀ := U.indicator D
  let f₀ := U.indicator (frobeniusField g)
  have hData := h10_ambientDirichletPoissonData hU.1.1 w g hEq
  have hf₄ : MemLp f₀ 4 (volume : Measure Point) :=
    (memLp_indicator_iff_restrict hU.1.1.measurableSet).2
      ((frobeniusCoordinateEquiv_memLp_iff (volume.restrict U) 4 g).2 hg₄)
  obtain ⟨G,hG⟩ := exists_smoothDomain_global_secondWeakColumns_four hU hData hf₄
  let H (x : Point) (j i : Fin 3) := frobeniusCoordinateEquiv.symm (G x j i)
  refine ⟨H,fun j => ⟨?_,fun i => ?_⟩⟩
  · apply (memH1_iff_memW12 O _ _).2
    have hw : (fun x => D₀ x j) =ᵐ[volume.restrict U] fun x => D x j := by
      filter_upwards [ae_restrict_mem hU.1.1.measurableSet] with x hx
      change U.indicator D x j = _
      rw [indicator_of_mem hx]
    have hh := (hG j).1.congr_ae hw (EventuallyEq.rfl)
    change MemW12 O (fun x => D x j) (fun x i => frobeniusCoordinateEquiv (H x j i))
    have hCols : (fun x i => frobeniusCoordinateEquiv (H x j i)) = fun x => G x j :=
      funext fun x => funext fun i => frobeniusCoordinateEquiv.apply_symm_apply (G x j i)
    rw [hCols]
    exact hh
  · exact ((hG j).2 i).continuousLinearMap_comp frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap

end Thesis
