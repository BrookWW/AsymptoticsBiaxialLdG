module

public import Thesis.Upstream.AmbientWeakPartialAlgebra
import HolderToCK.Analysis.ClassicalWeakGradient

/-! Iterated actual weak derivatives in chosen Cartesian directions. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace Thesis

/-- All displayed weak derivatives are in the same (L^p) space, with
iteration restricted to the supplied coordinate directions. -/
@[expose] def HasWeakLpDerivatives {n q : ℕ} (U : Set (Domain n)) (I : Set (Fin n))
    (p : ℝ≥0∞) : ℕ → (Domain n → Ambient q) → Prop
  | 0, u => MemLp u p (volume.restrict U)
  | k+1, u => MemLp u p (volume.restrict U) ∧
      ∀ i ∈ I, ∃ D : Domain n → Ambient q, IsWeakAmbientCoordinatePartial U i u D ∧
        HasWeakLpDerivatives U I p k D

/-- An actual weak coordinate identity restricts to a smaller measurable patch. -/
theorem IsWeakAmbientCoordinatePartial.mono {n q : ℕ} {U V : Set (Domain n)}
    (hU : MeasurableSet U) (hVU : V ⊆ U) {i : Fin n} {u D : Domain n → Ambient q}
    (h : IsWeakAmbientCoordinatePartial U i u D) :
    IsWeakAmbientCoordinatePartial V i u D := by
  intro φ hφ hφc hφs
  have hDer : tsupport (coordinateDerivative φ hφ i) ⊆ V :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hφs
  have hL : (∫ x in V, coordinateDerivative φ hφ i x • u x) =
      ∫ x in U, coordinateDerivative φ hφ i x • u x := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hVU
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun he => hx.2 (hDer he)),zero_smul]
  have hR : (∫ x in V, φ x • D x) = ∫ x in U, φ x • D x := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hVU
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun he => hx.2 (hφs he)),zero_smul]
  rw [hL,hR]
  exact h φ hφ hφc (hφs.trans hVU)

namespace HasWeakLpDerivatives

variable {n q : ℕ} {U : Set (Domain n)} {I : Set (Fin n)} {p : ℝ≥0∞}
variable {u v : Domain n → Ambient q} {k : ℕ}

theorem memLp (hu : HasWeakLpDerivatives U I p k u) : MemLp u p (volume.restrict U) := by
  cases k
  · exact hu
  · exact hu.1

/-- A displayed second-order weak graph supplies the order-two predicate
with the same value and derivative columns. -/
theorem of_memW12_secondColumns (V : OpenDomain n)
    {f : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    {H : Domain n → Fin n → HarmonicMaps.Gradient n q}
    (hf : MemW12 V f D)
    (hD : ∀ j, MemW12 V (fun x => D x j) (fun x => H x j))
    (hV : MemLp f p (volume.restrict V.val))
    (hF : ∀ j, MemLp (fun x => D x j) p (volume.restrict V.val))
    (hH : ∀ j i, MemLp (fun x => H x j i) p (volume.restrict V.val)) :
    HasWeakLpDerivatives V.val I p 2 f :=
  ⟨hV,fun j _ => ⟨fun x => D x j,hf.1.2.2 j,hF j,
    fun i _ => ⟨fun x => H x j i,(hD j).1.2.2 i,hH j i⟩⟩⟩

/-- A displayed third-order weak graph supplies the order-three predicate
with each of its original columns. -/
theorem of_memW12_thirdColumns (V : OpenDomain n)
    {f : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    {H : Domain n → Fin n → HarmonicMaps.Gradient n q}
    {K : Domain n → Fin n → Fin n → HarmonicMaps.Gradient n q}
    (hf : MemW12 V f D)
    (hD : ∀ i, MemW12 V (fun x => D x i) (fun x => H x i))
    (hH : ∀ i j, MemW12 V (fun x => H x i j) (fun x => K x i j))
    (hV : MemLp f p (volume.restrict V.val))
    (hF : ∀ i, MemLp (fun x => D x i) p (volume.restrict V.val))
    (hS : ∀ i j, MemLp (fun x => H x i j) p (volume.restrict V.val))
    (hT : ∀ i j l, MemLp (fun x => K x i j l) p (volume.restrict V.val)) :
    HasWeakLpDerivatives V.val I p 3 f :=
  ⟨hV,fun i _ => ⟨fun x => D x i,hf.1.2.2 i,
    of_memW12_secondColumns V (hD i) (hH i) (hF i) (hS i) (hT i)⟩⟩

theorem mono {V : Set (Domain n)} {J : Set (Fin n)}
    (hu : HasWeakLpDerivatives U I p k u) (hU : MeasurableSet U)
    (hVU : V ⊆ U) (hJI : J ⊆ I) : HasWeakLpDerivatives V J p k u := by
  have hμ := Measure.restrict_mono_set (volume : Measure (Domain n)) hVU
  induction k generalizing u with
  | zero => exact hu.memLp.mono_measure hμ
  | succ k ih =>
    refine ⟨hu.memLp.mono_measure hμ,?_⟩
    intro i hi
    obtain ⟨D,hD,hDr⟩ := hu.2 i (hJI hi)
    exact ⟨D,hD.mono hU hVU,ih hDr⟩

theorem of_succ (hu : HasWeakLpDerivatives U I p (k+1) u) : HasWeakLpDerivatives U I p k u := by
  induction k generalizing u with
  | zero => exact hu.1
  | succ k ih =>
    refine ⟨hu.1,?_⟩
    intro i hi
    obtain ⟨D,hD,hDr⟩ := hu.2 i hi
    exact ⟨D,hD,ih hDr⟩

theorem of_le {j : ℕ} (hu : HasWeakLpDerivatives U I p k u) (h : j ≤ k) :
    HasWeakLpDerivatives U I p j u := by
  induction h with
  | refl => exact hu
  | step _ ih => exact ih hu.of_succ

theorem congr_ae (hu : HasWeakLpDerivatives U I p k u)
    (he : u =ᵐ[volume.restrict U] v) : HasWeakLpDerivatives U I p k v := by
  cases k with
  | zero => exact MemLp.ae_eq he hu.memLp
  | succ k =>
    refine ⟨MemLp.ae_eq he hu.memLp,?_⟩
    intro i hi
    obtain ⟨D,hD,hDr⟩ := hu.2 i hi
    exact ⟨D,hD.congr_ae he (EventuallyEq.rfl),hDr⟩

theorem zero : HasWeakLpDerivatives U I p k (0 : Domain n → Ambient q) := by
  induction k with
  | zero => exact MemLp.zero
  | succ k ih =>
    exact ⟨MemLp.zero,fun _ _ => ⟨0,fun _ _ _ _ => by simp,ih⟩⟩

theorem add [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U)]
    (hp : (2 : ℝ≥0∞) ≤ p) (hu : HasWeakLpDerivatives U I p k u)
    (hv : HasWeakLpDerivatives U I p k v) : HasWeakLpDerivatives U I p k (u+v) := by
  induction k generalizing u v with
  | zero => exact hu.memLp.add hv.memLp
  | succ k ih =>
    refine ⟨hu.memLp.add hv.memLp,?_⟩
    intro i hi
    obtain ⟨D,hD,hDr⟩ := hu.2 i hi
    obtain ⟨E,hE,hEr⟩ := hv.2 i hi
    refine ⟨D+E,?_,ih hDr hEr⟩
    exact hD.add hE (hu.memLp.mono_exponent hp) (hv.memLp.mono_exponent hp)
      (hDr.memLp.mono_exponent hp) (hEr.memLp.mono_exponent hp)

theorem neg (hu : HasWeakLpDerivatives U I p k u) : HasWeakLpDerivatives U I p k (-u) := by
  induction k generalizing u with
  | zero => exact hu.memLp.neg
  | succ k ih =>
    refine ⟨hu.memLp.neg,?_⟩
    intro i hi
    obtain ⟨D,hD,hDr⟩ := hu.2 i hi
    exact ⟨-D,hD.neg,ih hDr⟩

theorem sub [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U)]
    (hp : (2 : ℝ≥0∞) ≤ p) (hu : HasWeakLpDerivatives U I p k u)
    (hv : HasWeakLpDerivatives U I p k v) : HasWeakLpDerivatives U I p k (u-v) := by
  simpa only [sub_eq_add_neg] using hu.add hp hv.neg

theorem finsetSum [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U)]
    (hp : (2 : ℝ≥0∞) ≤ p) {ι : Type*} (s : Finset ι) {g : ι → Domain n → Ambient q}
    (hg : ∀ j ∈ s, HasWeakLpDerivatives U I p k (g j)) :
    HasWeakLpDerivatives U I p k (fun x => ∑ j ∈ s, g j x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change HasWeakLpDerivatives U I p k (0 : Domain n → Ambient q)
    exact zero
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hg j (Finset.mem_insert_self _ _)).add hp
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem memLp_top_of_continuousOn_closure {E : Type*} [NormedAddCommGroup E]
    (hU : MeasurableSet U) (hB : Bornology.IsBounded U)
    {a : Domain n → E} (ha : ContinuousOn a (closure U)) :
    MemLp a ⊤ (volume.restrict U) := by
  obtain ⟨C,hC⟩ := hB.isCompact_closure.exists_bound_of_continuousOn ha
  exact memLp_top_of_bound ((ha.mono subset_closure).aestronglyMeasurable hU) C
    ((ae_restrict_mem hU).mono fun x hx => hC x (subset_closure hx))

/-- Weak derivatives of all orders in the chosen directions are stable under
multiplication by a smooth coefficient on a bounded domain. -/
theorem smul_smooth (hU : MeasurableSet U) (hB : Bornology.IsBounded U)
    (hp : (2 : ℝ≥0∞) ≤ p) (hu : HasWeakLpDerivatives U I p k u)
    {a : Domain n → ℝ} (ha : ContDiff ℝ ∞ a) :
    HasWeakLpDerivatives U I p k (fun x => a x • u x) := by
  letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict U) :=
    isFiniteMeasure_restrict.mpr hB.measure_lt_top.ne
  induction k generalizing u a with
  | zero =>
    exact hu.memLp.smul (r := p) (memLp_top_of_continuousOn_closure hU hB ha.continuous.continuousOn)
  | succ k ih =>
    have hATop := memLp_top_of_continuousOn_closure hU hB ha.continuous.continuousOn
    refine ⟨hu.memLp.smul (r := p) hATop,?_⟩
    intro i hi
    obtain ⟨D,hD,hDr⟩ := hu.2 i hi
    let b := coordinateDerivative a ha i
    have hb : ContDiff ℝ ∞ b := (ha.fderiv_right (by simp)).clm_apply contDiff_const
    have hBTop := memLp_top_of_continuousOn_closure hU hB hb.continuous.continuousOn
    refine ⟨fun x => b x • u x + a x • D x,?_,?_⟩
    · exact hD.smul_smooth (hu.memLp.mono_exponent hp) (hDr.memLp.mono_exponent hp) ha hATop hBTop
    · exact (ih hu.of_succ hb).add hp (ih hDr ha)

/-- The actual within derivatives of a classical field on a bounded closed
patch give its iterated weak derivatives inside. -/
theorem of_contDiffOn_closure (V : OpenDomain n) (hB : Bornology.IsBounded V.val)
    (hUd : UniqueDiffOn ℝ (closure V.val)) {f : Domain n → Ambient q}
    (hf : ContDiffOn ℝ (k : ℕ∞ω) f (closure V.val)) :
    HasWeakLpDerivatives V.val I p k f := by
  induction k generalizing f with
  | zero =>
    letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict V.val) :=
      isFiniteMeasure_restrict.mpr hB.measure_lt_top.ne
    exact (memLp_top_of_continuousOn_closure V.property.measurableSet hB hf.continuousOn).mono_exponent le_top
  | succ k ih =>
    letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict V.val) :=
      isFiniteMeasure_restrict.mpr hB.measure_lt_top.ne
    refine ⟨(memLp_top_of_continuousOn_closure V.property.measurableSet hB hf.continuousOn).mono_exponent le_top,?_⟩
    intro i _
    let d (x : Domain n) := fderivWithin ℝ f (closure V.val) x (EuclideanSpace.single i 1)
    have hOrder : (1 : ℕ∞ω) ≤ ((k+1 : ℕ) : ℕ∞ω) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
    have hF := HolderToCK.hasWeakGradient_of_contDiffOn_one V ((hf.of_le hOrder).mono subset_closure)
    have hEq : (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) =ᵐ[volume.restrict V.val] d := by
      filter_upwards [ae_restrict_mem V.property.measurableSet] with x hx
      have hN : closure V.val ∈ 𝓝 x := mem_of_superset (V.property.mem_nhds hx) subset_closure
      change fderiv ℝ f x (EuclideanSpace.single i 1) =
        fderivWithin ℝ f (closure V.val) x (EuclideanSpace.single i 1)
      rw [fderivWithin_of_mem_nhds hN]
    have hd : ContDiffOn ℝ (k : ℕ∞ω) d (closure V.val) :=
      (hf.fderivWithin hUd (by exact_mod_cast (Nat.le_refl (k+1)))).clm_apply contDiffOn_const
    exact ⟨d,(show IsWeakAmbientCoordinatePartial V.val i f _ from hF.2.2 i).congr_ae
      (EventuallyEq.rfl) hEq,ih hd⟩

end HasWeakLpDerivatives

/-- Actual weak columns in the same coordinate are equal almost everywhere. -/
theorem IsWeakAmbientCoordinatePartial.ae_eq {n q : ℕ} {U : Set (Domain n)}
    (hU : IsOpen U) [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U)]
    {i : Fin n} {u D E : Domain n → Ambient q}
    (hD : IsWeakAmbientCoordinatePartial U i u D)
    (hE : IsWeakAmbientCoordinatePartial U i u E)
    (hDLp : MemLp D 2 (volume.restrict U)) (hELp : MemLp E 2 (volume.restrict U)) :
    D =ᵐ[volume.restrict U] E := by
  have hLocal : LocallyIntegrableOn (D-E) U volume :=
    IntegrableOn.locallyIntegrableOn ((hDLp.sub hELp).integrable (by norm_num))
  have hz : ∀ᵐ x ∂volume, x ∈ U → (D-E) x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hLocal
    intro φ hφ hφc hφs
    have hφTop := hφ.continuous.memLp_top_of_hasCompactSupport hφc (volume.restrict U)
    have hDI : Integrable (fun x => φ x • D x) (volume.restrict U) :=
      (hDLp.integrable (by norm_num)).smul_of_top_right hφTop
    have hEI : Integrable (fun x => φ x • E x) (volume.restrict U) :=
      (hELp.integrable (by norm_num)).smul_of_top_right hφTop
    have hPair : (∫ x in U, φ x • D x) = ∫ x in U, φ x • E x :=
      neg_injective ((hD φ hφ hφc hφs).symm.trans (hE φ hφ hφc hφs))
    have hZero : (∫ x in U, φ x • (D-E) x) = 0 := by
      simp_rw [Pi.sub_apply,smul_sub]
      rw [integral_sub hDI hEI,hPair,sub_self]
    rw [← hZero]
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h)),zero_smul]
  apply (ae_restrict_iff' hU.measurableSet).2
  exact hz.mono fun x hx hxU => sub_eq_zero.mp (hx hxU)

end Thesis
