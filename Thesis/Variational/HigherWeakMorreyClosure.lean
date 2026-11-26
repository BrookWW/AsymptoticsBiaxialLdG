module

public import Thesis.Upstream.WeakLpDerivatives
public import Thesis.Variational.ContinuousWeakColumns
import Thesis.Variational.SmoothDomainClosedJets
import Thesis.Variational.ClosedConvexDerivativeColumns
import Thesis.Upstream.LocalSobolevGradientTransport
import HolderToCK.Analysis.GradientLinearAlgebra
import HarmonicMaps.Analysis.SobolevAECongruence

/-! Integer classical regularity of the actual weak jets on a closed domain. -/

public section

noncomputable section

open Filter HarmonicMaps HolderToCK MeasureTheory Set
open scoped ContDiff ENNReal

namespace Thesis

theorem HasWeakLpDerivatives.exists_memW12_and_columns
    {n q : ℕ} (V : OpenDomain n) (hB : Bornology.IsBounded V.val)
    {p : ℝ≥0∞} (hp : 2 ≤ p) {k : ℕ} {u : Domain n → Ambient q}
    (hu : HasWeakLpDerivatives V.val univ p (k+1) u) :
    ∃ D : Domain n → HarmonicMaps.Gradient n q, MemW12 V u D ∧
      ∀ i, HasWeakLpDerivatives V.val univ p k (fun x => D x i) := by
  classical
  letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict V.val) :=
    isFiniteMeasure_restrict.mpr hB.measure_lt_top.ne
  choose d hd hReg using fun i : Fin n => hu.2 i (mem_univ i)
  let D (x : Domain n) (j : Fin n) := d j x
  exact ⟨D,memW12_of_ambient_coordinate_partials V (hu.memLp.mono_exponent hp)
    (fun j => (hReg j).memLp.mono_exponent hp) hd,hReg⟩

private theorem exists_closed_representative_of_higher_weak_derivatives
    {q : ℕ} (V W : OpenDomain 3) (hB : Bornology.IsBounded V.val) (hSub : W.val ⊆ V.val)
    {p : ℝ≥0∞} (hp : 2 ≤ p)
    (hRep : ∀ {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q},
      MemW12 V u D → MemLp u p (volume.restrict V.val) →
      (∀ i, MemLp (fun x => D x i) p (volume.restrict V.val)) →
      ∃ v : Point → Ambient q, u =ᵐ[volume.restrict W.val] v ∧ ContinuousOn v (closure W.val))
    (hLift : ∀ (k : ℕ) {v : Point → Ambient q} {G : Point → HarmonicMaps.Gradient 3 q},
      MemW12 W v G → ContinuousOn v (closure W.val) →
      (∀ i, ContDiffOn ℝ (k : ℕ∞ω) (fun x => G x i) (closure W.val)) →
        ContDiffOn ℝ (↑(k+1) : ℕ∞ω) v (closure W.val))
    (k : ℕ) {u : Point → Ambient q}
    (hu : HasWeakLpDerivatives V.val univ p (k+1) u) :
    ∃ v : Point → Ambient q, u =ᵐ[volume.restrict W.val] v ∧
      ContDiffOn ℝ (k : ℕ∞ω) v (closure W.val) := by
  classical
  induction k generalizing u with
  | zero =>
    obtain ⟨D,hGraph,hD⟩ := hu.exists_memW12_and_columns V hB hp
    obtain ⟨v,hv,hC⟩ := hRep hGraph hu.memLp (fun j => (hD j).memLp)
    exact ⟨v,hv,contDiffOn_zero.mpr hC⟩
  | succ k ih =>
    obtain ⟨D,hGraph,hD⟩ := hu.exists_memW12_and_columns V hB hp
    obtain ⟨v,hv,hC⟩ := hRep hGraph hu.memLp (fun j => (hD j).memLp)
    choose w he hw using fun j : Fin 3 => ih (hD j)
    let G (x : Point) (j : Fin 3) := w j x
    have hE : D =ᵐ[volume.restrict W.val] G := by
      filter_upwards [ae_all_iff.2 he] with x hx
      exact funext hx
    have hμ : volume.restrict W.val ≤ volume.restrict V.val := Measure.restrict_mono_set _ hSub
    have hGW : MemW12 W u D :=
      ⟨hGraph.1.mono hSub,hGraph.2.1.mono_measure hμ,fun j => (hGraph.2.2 j).mono_measure hμ⟩
    exact ⟨v,hv,hLift k (hGW.congr_ae hv hE) hC hw⟩

/-- Full weak derivatives of order (k+1) in (L^p), (p>3), have a
classical (C^k) representative on the actual smooth closure. -/
theorem IsSmoothDomain.exists_contDiffOn_closure_of_weakLpDerivatives
    {U : Set Point} (hU : IsSmoothDomain U) {q : ℕ} {p : ℝ} (hp : 3 < p)
    (k : ℕ) {u : Point → Ambient q}
    (hu : HasWeakLpDerivatives U univ (ENNReal.ofReal p) (k+1) u) :
    ∃ v : Point → Ambient q, u =ᵐ[volume.restrict U] v ∧
      ContDiffOn ℝ (k : ℕ∞ω) v (closure U) := by
  let V : OpenDomain 3 := ⟨U,hU.1.1⟩
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal (by linarith only [hp])
  refine exists_closed_representative_of_higher_weak_derivatives V V hU.1.2.2 Subset.rfl hp2
    (fun h _ hD => hU.exists_weakMorreyClosureRepresentative hp h hD) ?_ k hu
  intro m v G hv hC hG
  let L (x : Point) : Point →L[ℝ] Ambient q :=
    ∑ j : Fin 3, (PiLp.proj 2 (𝕜 := ℝ) (fun _ => ℝ) j).smulRight (G x j)
  have hL : ContDiffOn ℝ (m : ℕ∞ω) L (closure U) := by
    apply ContDiffOn.sum
    intro i _
    let A : Ambient q →L[ℝ] Point →L[ℝ] Ambient q :=
      ContinuousLinearMap.smulRightL ℝ Point (Ambient q) (PiLp.proj 2 (𝕜 := ℝ) (fun _ => ℝ) i)
    exact A.contDiff.comp_contDiffOn (hG i)
  exact hU.contDiffOn_nat_succ_of_continuous_derivative m hC hL
    (fun x hx => hasFDerivAt_of_continuous_weak_columns V hv (hC.mono subset_closure)
      (fun j => (hG j).continuousOn.mono subset_closure) hx)

/-- The continuous representative already specified on the closure is the
classical higher representative. -/
theorem IsSmoothDomain.contDiffOn_closure_of_continuous_weakLpDerivatives
    {U : Set Point} (hU : IsSmoothDomain U) {q : ℕ} {p : ℝ} (hp : 3 < p)
    (k : ℕ) {u : Point → Ambient q} (hC : ContinuousOn u (closure U))
    (hu : HasWeakLpDerivatives U univ (ENNReal.ofReal p) (k+1) u) :
    ContDiffOn ℝ (k : ℕ∞ω) u (closure U) := by
  obtain ⟨v,hv,hVC⟩ := hU.exists_contDiffOn_closure_of_weakLpDerivatives hp k hu
  exact hVC.congr ((Measure.eqOn_open_of_ae_eq hv hU.1.1
    (hC.mono subset_closure) (hVC.continuousOn.mono subset_closure)).of_subset_closure
      hC hVC.continuousOn subset_closure Subset.rfl)

/-- Higher regularity on a convex cap uses only a single local continuous
representative theorem for weak first graphs, on the same fixed cap. -/
theorem exists_contDiffOn_closure_of_weakLpDerivatives_on_convex_cap
    {q : ℕ} (V W : OpenDomain 3) (hB : Bornology.IsBounded V.val) (hSub : W.val ⊆ V.val)
    (hConv : Convex ℝ W.val) (hNe : W.val.Nonempty)
    {p : ℝ≥0∞} (hp : 2 ≤ p)
    (hRep : ∀ {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q},
      MemW12 V u D → MemLp u p (volume.restrict V.val) →
      (∀ i, MemLp (fun x => D x i) p (volume.restrict V.val)) →
      ∃ v : Point → Ambient q, u =ᵐ[volume.restrict W.val] v ∧ ContinuousOn v (closure W.val))
    (k : ℕ) {u : Point → Ambient q}
    (hu : HasWeakLpDerivatives V.val univ p (k+1) u) :
    ∃ v : Point → Ambient q, u =ᵐ[volume.restrict W.val] v ∧
      ContDiffOn ℝ (k : ℕ∞ω) v (closure W.val) := by
  refine exists_closed_representative_of_higher_weak_derivatives V W hB hSub hp hRep ?_ k hu
  intro m v G hv hC hG
  have hAt (x : Point) (hx : x ∈ W.val) :=
    hasFDerivAt_of_continuous_weak_columns W hv (hC.mono subset_closure)
      (fun j => (hG j).continuousOn.mono subset_closure) hx
  have hDiff : DifferentiableOn ℝ v W.val := fun x hx => (hAt x hx).differentiableAt.differentiableWithinAt
  have hCols (i : Fin 3) : EqOn (fun x => G x i) (coordDeriv i v) W.val := by
    intro x hx
    have hEq := DFunLike.congr_fun (hAt x hx).fderiv (axis i)
    exact ((columnLinearMap_single (G x) i).symm.trans hEq.symm)
  exact (contDiffOn_succ_of_closed_convex_derivative_columns W.property hConv hNe m hC hDiff
    (fun i x => G x i) hG hCols).1

end Thesis
