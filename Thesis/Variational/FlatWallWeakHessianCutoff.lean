module

public import Thesis.Variational.FlatWallWeakHessianReflection
import StratificationTheory.Foundation.CompactSobolevCutoff
import StratificationTheory.Foundation.SobolevLocalAssembly
import HarmonicMaps.Analysis.SobolevAECongruence
import HarmonicMaps.Analysis.SobolevDifference
import HarmonicMaps.SobolevRestriction

/-! Localization of the original weak Hessian before odd wall reflection. -/

public section

noncomputable section

open Filter Function HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Topology

namespace Thesis

private abbrev weakWholeSpace : OpenDomain 3 := ⟨univ,isOpen_univ⟩

private theorem memW12_mono_patch {q : ℕ} {V U : OpenDomain 3}
    {f : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (h : MemW12 U f D) (hVU : V.val ⊆ U.val) : MemW12 V f D := by
  have hμ := Measure.restrict_mono_set (volume : Measure Point) hVU
  exact ⟨h.1.mono hVU,h.2.1.mono_measure hμ,fun j => (h.2.2 j).mono_measure hμ⟩

private theorem locallyIntegrableOn_of_patch_memLp {q : ℕ} {U : OpenDomain 3}
    {f : Point → Ambient q} (hf : MemLp f 2 (volume.restrict U.val)) : LocallyIntegrableOn f U.val volume := by
  apply (locallyIntegrableOn_iff U.property.isLocallyClosed).mpr
  intro K hKU hK
  letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact (hf.mono_measure (Measure.restrict_mono_set volume hKU)).integrable (by norm_num)

theorem memLp_smul_patch_cutoff {q : ℕ} {U W : OpenDomain 3} {p : ℝ≥0∞}
    {f : Point → Ambient q} (hf : MemLp f p (volume.restrict (U.val∩W.val)))
    {χ : Point → ℝ} (hχ : MemLp χ ∞ (volume.restrict U.val)) (hχS : tsupport χ ⊆ W.val) :
    MemLp (fun x => χ x • f x) p (volume.restrict U.val) := by
  have hμ : (volume.restrict U.val).restrict W.val = volume.restrict (U.val∩W.val) := by
    rw [Measure.restrict_restrict W.property.measurableSet,inter_comm]
  have hExt : MemLp (W.val.indicator f) p (volume.restrict U.val) :=
    (memLp_indicator_iff_restrict W.property.measurableSet).2 (hμ.symm ▸ hf)
  refine MemLp.ae_eq ?_ (hExt.smul (r := p) hχ)
  apply Eventually.of_forall
  intro x
  change χ x • W.val.indicator f x = χ x • f x
  by_cases hx : x ∈ W.val
  · simp only [indicator_of_mem hx]
  · have h₀ : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hχS h))
    simp only [indicator_of_notMem hx,h₀,zero_smul]

theorem memW12_smul_relative_cutoff {q : ℕ} {U W : OpenDomain 3}
    (hW : Bornology.IsBounded W.val) {u : Point → Ambient q}
    {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 (⟨U.val∩W.val,U.property.inter W.property⟩ : OpenDomain 3) u D)
    {χ : Point → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hS : tsupport χ ⊆ W.val) :
    MemW12 U (fun x => χ x • u x)
      (fun x j => coordDeriv j χ x • u x + χ x • D x j) := by
  let V : OpenDomain 3 := ⟨U.val∩W.val,U.property.inter W.property⟩
  let f (x : Point) := χ x • u x
  let G (x : Point) (j : Fin 3) := coordDeriv j χ x • u x + χ x • D x j
  have hχL : MemLp χ ∞ (volume.restrict U.val) := hχ.continuous.memLp_top_of_hasCompactSupport hc _
  have hχC (j : Fin 3) : ContDiff ℝ ∞ (coordDeriv j χ) :=
    (hχ.fderiv_right (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiff_const
  have hχDL (j : Fin 3) : MemLp (coordDeriv j χ) ∞ (volume.restrict U.val) :=
    (hχC j).continuous.memLp_top_of_hasCompactSupport (hc.fderiv_apply ℝ (axis j)) _
  have hDS (j : Fin 3) : tsupport (coordDeriv j χ) ⊆ tsupport χ := tsupport_fderiv_apply_subset ℝ (axis j)
  have hfL : MemLp f 2 (volume.restrict U.val) := memLp_smul_patch_cutoff hu.2.1 hχL hS
  have hGL (j : Fin 3) : MemLp (fun x => G x j) 2 (volume.restrict U.val) :=
    (memLp_smul_patch_cutoff hu.2.1 (hχDL j) ((hDS j).trans hS)).add
      (memLp_smul_patch_cutoff (hu.2.2 j) hχL hS)
  have hLocal : MemW12 V f G := by
    letI : IsFiniteMeasure (volume.restrict V.val) := isFiniteMeasure_restrict.2
      (ne_top_of_le_ne_top hW.measure_lt_top.ne (measure_mono inter_subset_right))
    have hμ : volume.restrict V.val ≤ volume.restrict U.val := Measure.restrict_mono_set _ inter_subset_left
    have hfV := hfL.mono_measure hμ
    have hGV (j : Fin 3) := (hGL j).mono_measure hμ
    refine ⟨⟨locallyIntegrableOn_of_patch_memLp hfV,fun j => locallyIntegrableOn_of_patch_memLp (hGV j),?_⟩,
      hfV,hGV⟩
    intro j φ hφ hφC hφS
    have hDpart : IsWeakAmbientCoordinatePartial V.val j u (fun x => D x j) := hu.1.2.2 j
    exact (hDpart.smul_smooth hu.2.1 (hu.2.2 j) hχ (hχL.mono_measure hμ) ((hχDL j).mono_measure hμ))
      φ hφ hφC hφS
  apply memW12_of_local_sobolev_pair hfL hGL
  intro x hx
  by_cases hxW : x ∈ W.val
  · obtain ⟨r,hr,hSub⟩ := Metric.isOpen_iff.1 V.property x ⟨hx,hxW⟩
    exact ⟨r,hr,hSub.trans inter_subset_left,memW12_mono_patch hLocal hSub⟩
  · have hxS : x ∉ tsupport χ := fun h => hxW (hS h)
    let O := U.val∩(tsupport χ)ᶜ
    have hO : IsOpen O := U.property.inter (isClosed_tsupport χ).isOpen_compl
    obtain ⟨r,hr,hSub⟩ := Metric.isOpen_iff.1 hO x ⟨hx,hxS⟩
    refine ⟨r,hr,hSub.trans inter_subset_left,?_⟩
    have hZero (y : Point) (hy : y ∈ ball x r) : f y = 0 ∧ G y = 0 := by
      have hyS : y ∉ tsupport χ := (hSub hy).2
      have hχ₀ : χ y = 0 := image_eq_zero_of_notMem_tsupport hyS
      refine ⟨by simp only [f,hχ₀,zero_smul],funext fun j => ?_⟩
      have hD₀ : coordDeriv j χ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hyS (hDS j h))
      simp only [G,hD₀,hχ₀,zero_smul,zero_add,Pi.zero_apply]
    have hAE := (ae_restrict_mem (μ := (volume : Measure Point)) measurableSet_ball).mono fun y hy => hZero y hy
    exact (MemW12.zero (ballDomain x r)).congr_ae (hAE.mono fun _ h => h.1.symm)
      (hAE.mono fun _ h => h.2.symm)

/-- Adding two finite Sobolev graphs adds their displayed weak columns. -/
theorem memW12_add_pair {q : ℕ} {U : OpenDomain 3}
    {u v : Point → Ambient q} {D G : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 U u D) (hv : MemW12 U v G) :
    MemW12 U (fun x => u x+v x) (fun x j => D x j+G x j) := by
  have h := hu.sub ((MemW12.zero U).sub hv)
  change MemW12 U (fun x => u x-(0-v x)) (fun x j => D x j-(0-G x j)) at h
  simpa only [zero_sub,sub_neg_eq_add] using h

/-- The value of the original field after multiplication by a scalar cutoff. -/
@[expose] def localWeakCutoffValue {q : ℕ} (χ : Point → ℝ) (u : Point → Ambient q) (x : Point) : Ambient q :=
  χ x • u x

/-- The exact first weak columns of the localized field. -/
@[expose] def localWeakCutoffColumns {q : ℕ} (χ : Point → ℝ) (u : Point → Ambient q)
    (D : Point → HarmonicMaps.Gradient 3 q) (x : Point) (i : Fin 3) : Ambient q :=
  coordDeriv i χ x • u x + χ x • D x i

/-- The exact Hessian rows of the localized field. -/
@[expose] def localWeakCutoffHessian {q : ℕ} (χ : Point → ℝ) (u : Point → Ambient q)
    (D : Point → HarmonicMaps.Gradient 3 q) (H : Point → Fin 3 → HarmonicMaps.Gradient 3 q)
    (x : Point) (i j : Fin 3) : Ambient q :=
  (coordDeriv j (coordDeriv i χ) x • u x + coordDeriv i χ x • D x j) +
    (coordDeriv j χ x • D x i + χ x • H x i j)

/-- The localized weak value, columns, and Hessian retain the original data
on the open plateau of the cutoff. -/
theorem localWeakCutoff_eqOn_open_plateau {q : ℕ} {O : Set Point} (hO : IsOpen O)
    {χ : Point → ℝ} (hχ : EqOn χ (fun _ => 1) O)
    (u : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q)
    (H : Point → Fin 3 → HarmonicMaps.Gradient 3 q) :
    EqOn (localWeakCutoffValue χ u) u O ∧ EqOn (localWeakCutoffColumns χ u D) D O ∧
      EqOn (localWeakCutoffHessian χ u D H) H O := by
  have hD (i : Fin 3) : EqOn (coordDeriv i χ) (fun _ => 0) O := by
    intro x hx
    have hNear : ∀ᶠ y in 𝓝 x, y ∈ O := hO.mem_nhds hx
    have he := hNear.mono fun _ hy => hχ hy
    exact DFunLike.congr_fun (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) he |>.trans
      (hasFDerivAt_const (1:ℝ) x).fderiv) (axis i)
  have hH (i j : Fin 3) : EqOn (coordDeriv j (coordDeriv i χ)) (fun _ => 0) O := by
    intro x hx
    have hNear : ∀ᶠ y in 𝓝 x, y ∈ O := hO.mem_nhds hx
    have he := hNear.mono fun _ hy => hD i hy
    exact DFunLike.congr_fun (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) he |>.trans
      (hasFDerivAt_const (0:ℝ) x).fderiv) (axis j)
  refine ⟨fun x hx => ?_,fun x hx => funext fun i => ?_,fun x hx => funext fun i => funext fun j => ?_⟩
  · simp only [localWeakCutoffValue,hχ hx,one_smul]
  · simp only [localWeakCutoffColumns,hD i hx,hχ hx,zero_smul,zero_add,one_smul]
  · simp only [localWeakCutoffHessian,hH i j hx,hD i hx,hD j hx,hχ hx,zero_smul,zero_add,one_smul]

/-- The localized rows are supported in the scalar cutoff's compact support. -/
theorem localWeakCutoffHessian_tsupport_subset {q : ℕ} (χ : Point → ℝ) (u : Point → Ambient q)
    (D : Point → HarmonicMaps.Gradient 3 q) (H : Point → Fin 3 → HarmonicMaps.Gradient 3 q)
    (i j : Fin 3) : tsupport (fun x => localWeakCutoffHessian χ u D H x i j) ⊆ tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x h
  by_contra hx
  have hχ : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hSubset (k : Fin 3) : tsupport (coordDeriv k χ) ⊆ tsupport χ :=
    tsupport_fderiv_apply_subset ℝ (axis k)
  have hD (k : Fin 3) : coordDeriv k χ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hk => hx (hSubset k hk))
  have hH : coordDeriv j (coordDeriv i χ) x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hh => hx (hSubset i (tsupport_fderiv_apply_subset ℝ (axis j) hh))
  exact h (by simp only [localWeakCutoffHessian,hχ,hD,hH,zero_smul,zero_add])

/-- An interior cutoff of the original half-patch data gives the full odd
reflected Hessian. The tangential witnesses need only exist on the whole
patch, while second rows for the normal column are given on its true half. -/
theorem memW12_oddFlatWallWeakHessian_cutoff_reflection {q : ℕ} (W : OpenDomain 3)
    (hW : Bornology.IsBounded W.val) {χ : Point → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχS : tsupport χ ⊆ W.val)
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    {H : Point → Fin 3 → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D)
    (hZero : ∀ x ∈ W.val, x ∉ upperCoordinateHalfSpace.val → u x=0 ∧ D x=0)
    (hUpper : ∀ i, MemW12 (⟨upperCoordinateHalfSpace.val∩W.val,
      upperCoordinateHalfSpace.property.inter W.property⟩ : OpenDomain 3) (fun x => D x i) (fun x => H x i))
    (hT : ∀ i ≠ (2 : Fin 3), ∃ T : Point → HarmonicMaps.Gradient 3 q, MemW12 W (fun x => D x i) T) :
    let v := localWeakCutoffValue χ u
    let G := localWeakCutoffColumns χ u D
    let J := localWeakCutoffHessian χ u D H
    MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (oddFlatWallWeakValue v) (oddFlatWallWeakColumns G) ∧
      ∀ i, MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (fun x => oddFlatWallWeakColumns G x i)
        (fun x => oddFlatWallWeakHessian J x i) := by
  intro v G J
  let S := upperCoordinateHalfSpace
  let U : OpenDomain 3 := ⟨S.val∩W.val,S.property.inter W.property⟩
  have hv : MemW12 weakWholeSpace v G := hu.to_memW12Loc.smoothCutoff_univ hχ hc (subset_univ _)
  have hχD (i : Fin 3) : ContDiff ℝ ∞ (coordDeriv i χ) :=
    (hχ.fderiv_right (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiff_const
  have hχDC (i : Fin 3) : HasCompactSupport (coordDeriv i χ) := hc.fderiv_apply ℝ (axis i)
  have hχDS (i : Fin 3) : tsupport (coordDeriv i χ) ⊆ W.val :=
    (tsupport_fderiv_apply_subset ℝ (axis i)).trans hχS
  have hG₀ (x : Point) (hx : x ∉ S.val) : G x=0 := by
    funext i
    change coordDeriv i χ x • u x + χ x • D x i = 0
    by_cases hxW : x ∈ W.val
    · rw [(hZero x hxW hx).1,(hZero x hxW hx).2,Pi.zero_apply,smul_zero,smul_zero,zero_add]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hxW (hχDS i h)),
        image_eq_zero_of_notMem_tsupport (fun h => hxW (hχS h)),zero_smul,zero_smul,zero_add]
  have huU : MemW12 U u D := memW12_mono_patch hu (subset_univ _)
  have hJ (i : Fin 3) : MemW12 S (fun x => G x i) (fun x => J x i) := by
    have hA := memW12_smul_relative_cutoff hW huU (hχD i) (hχDC i) (hχDS i)
    have hB := memW12_smul_relative_cutoff hW (hUpper i) hχ hc hχS
    exact memW12_add_pair hA hB
  have hWholeT (i : Fin 3) (hi : i ≠ 2) : ∃ T : Point → HarmonicMaps.Gradient 3 q,
      MemW12 weakWholeSpace (fun x => G x i) T := by
    obtain ⟨T,hT'⟩ := hT i hi
    have hA := hu.to_memW12Loc.smoothCutoff_univ (hχD i) (hχDC i) (subset_univ _)
    have hB := hT'.to_memW12Loc.smoothCutoff_univ hχ hc hχS
    exact ⟨_,memW12_add_pair hA hB⟩
  exact memW12_oddFlatWallWeakHessian_reflection hv hG₀ hJ hWholeT

end Thesis

end
