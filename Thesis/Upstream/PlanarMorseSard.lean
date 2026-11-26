module

public import Thesis.Variational.BoundaryBallSlices
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Euclidean.Volume.Measure
import StratificationTheory.Compactness.CofinalCompactExhaustion

/-! Morse–Sard for a real-valued C² function on the Euclidean plane. -/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal Topology

namespace Thesis

local instance planarMorseSardFirstNormed : NormedAddCommGroup (Plane →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance planarMorseSardSecondNormed : NormedAddCommGroup (Plane →L[ℝ] (Plane →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

private theorem continuousOn_fderiv_fderiv_planar {U : Set Plane} (hU : IsOpen U)
    {f : Plane → ℝ} (hf : ContDiffOn ℝ 2 f U) :
    ContinuousOn (fderiv ℝ (fderiv ℝ f)) U :=
  (hf.fderiv_of_isOpen hU (m := (1 : ℕ∞ω)) (by norm_num)).continuousOn_fderiv_of_isOpen hU le_rfl

private theorem measure_hausdorff_two_planar_lt_top {K : Set Plane} (hK : IsCompact K) :
    (Measure.hausdorffMeasure 2 : Measure Plane) K < ⊤ := by
  have hEq := congrArg (fun μ : Measure Plane => μ K) (EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2)
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hEq
  apply lt_top_iff_ne_top.2
  intro h
  have h' : (Measure.hausdorffMeasure ((2 : ℕ) : ℝ) : Measure Plane) K = ⊤ := by simpa using h
  rw [h', ENNReal.mul_top (ENNReal.coe_ne_zero.2
    (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero 2))] at hEq
  exact hK.measure_lt_top.ne hEq.symm

private theorem volume_real_eq_zero_of_hausdorff_one {S : Set ℝ}
    (hS : (Measure.hausdorffMeasure 1 : Measure ℝ) S = 0) : (volume : Measure ℝ) S = 0 := by
  have hEq : (Measure.euclideanHausdorffMeasure 1 : Measure ℝ) = volume := by
    simpa only [Module.finrank_self] using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ))
  have hS' : (Measure.hausdorffMeasure ((1 : ℕ) : ℝ) : Measure ℝ) S = 0 := by simpa using hS
  rw [← hEq, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hS', smul_zero]

private theorem critical_dist_quadratic_bound {U : Set Plane} (hU : IsOpen U)
    {f : Plane → ℝ} (hf : ContDiffOn ℝ 2 f U) {x y : Plane} {ρ ε : ℝ}
    (hε : 0 ≤ ε) (hxy : dist y x ≤ ρ) (hB : closedBall x ρ ⊆ U)
    (hZero : fderiv ℝ f x = 0)
    (hH : ∀ z ∈ closedBall x ρ, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ ε) :
    dist (f x) (f y) ≤ ε * dist x y ^ 2 := by
  let r := dist y x
  let K := closedBall x r
  have hSub : K ⊆ closedBall x ρ := closedBall_subset_closedBall hxy
  have hKU := hSub.trans hB
  have hx : x ∈ K := mem_closedBall_self dist_nonneg
  have hy : y ∈ K := mem_closedBall.2 le_rfl
  have hg := hf.fderiv_of_isOpen hU (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)
  have hGrad (z : Plane) (hz : z ∈ K) : ‖fderiv ℝ f z‖ ≤ ε * r := by
    have hDiffer (w : Plane) (hw : w ∈ K) : HasFDerivWithinAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) w) K w :=
      (((hg w (hKU hw)).contDiffAt (hU.mem_nhds (hKU hw))).differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt
    have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      hDiffer
      (fun w hw => hH w (hSub hw)) (convex_closedBall _ _) hx hz
    rw [hZero, sub_zero, ← dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_left (mem_closedBall.1 hz) hε)
  have hDiffer (w : Plane) (hw : w ∈ K) : HasFDerivWithinAt f (fderiv ℝ f w) K w :=
    (((hf w (hKU hw)).contDiffAt (hU.mem_nhds (hKU hw))).differentiableAt two_ne_zero).hasFDerivAt.hasFDerivWithinAt
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hDiffer hGrad (convex_closedBall _ _) hx hy
  rw [← dist_eq_norm, ← dist_eq_norm] at h
  rw [dist_comm (f x) (f y), dist_comm x y, pow_two, mul_assoc] at *
  exact h

private theorem exists_measurable_small_diameter_partition (δ : ℝ) (hδ : 0 < δ) :
    ∃ P : ℕ → Set Plane, Pairwise (Disjoint on P) ∧ (∀ i, MeasurableSet (P i)) ∧
      (⋃ i, P i) = univ ∧ ∀ i x, x ∈ P i → ∀ y ∈ P i, dist y x ≤ δ := by
  obtain ⟨z, hz⟩ := TopologicalSpace.exists_dense_seq Plane
  let B (i : ℕ) := ball (z i) (δ / 4)
  let P := disjointed B
  have hB : (⋃ i, B i) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := Metric.denseRange_iff.1 hz x (δ / 4) (by positivity)
    exact mem_iUnion.2 ⟨i, hi⟩
  refine ⟨P, disjoint_disjointed _, MeasurableSet.disjointed (fun _ => measurableSet_ball),
    iUnion_disjointed.trans hB, ?_⟩
  intro i x hx y hy
  have hx' : dist x (z i) < δ / 4 := disjointed_subset B i hx
  have hy' : dist y (z i) < δ / 4 := disjointed_subset B i hy
  have hd := dist_triangle_right y x (z i)
  linarith only [hd, hx', hy', hδ]

private theorem degenerate_critical_image_hausdorff_null_on_compact
    {U K : Set Plane} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : Plane → ℝ} (hf : ContDiffOn ℝ 2 f U) :
    (Measure.hausdorffMeasure 1 : Measure ℝ)
      (f '' {x ∈ K | fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0}) = 0 := by
  let A := {x ∈ K | fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0}
  let H := fderiv ℝ (fderiv ℝ f)
  have hD := (hf.continuousOn_fderiv_of_isOpen hU (by norm_num : (1 : ℕ∞ω) ≤ 2)).mono hKU
  have hHp := continuousOn_fderiv_fderiv_planar hU hf
  have hAp : A = (K ∩ (fderiv ℝ f) ⁻¹' {0}) ∩ (K ∩ H ⁻¹' {0}) := by
    ext x; simp only [A, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]; tauto
  have hAclosed : IsClosed A := hAp ▸
    ((hD.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton).inter
      ((hHp.mono hKU).preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton))
  have hAk : IsCompact A := hK.of_isClosed_subset hAclosed fun _ hx => hx.1
  let μ := (Measure.hausdorffMeasure 2 : Measure Plane)
  let ν := (Measure.hausdorffMeasure 1 : Measure ℝ)
  have hμ : μ K ≠ ⊤ := (measure_hausdorff_two_planar_lt_top hK).ne
  have hεbound (ε : ℝ≥0) (hε : 0 < ε) : ν (f '' A) ≤ (ε : ℝ≥0∞) * μ K := by
    let O := U ∩ (fun x => ‖H x‖) ⁻¹' Iio (ε : ℝ)
    have hO : IsOpen O := hHp.norm.isOpen_inter_preimage hU isOpen_Iio
    have hAO : A ⊆ O := by
      intro x hx
      refine ⟨hKU hx.1, ?_⟩
      change ‖H x‖ < (ε : ℝ)
      rw [show H x = 0 from hx.2.2, norm_zero]
      exact hε
    obtain ⟨δ, hδ, hδO⟩ := hAk.exists_cthickening_subset_open hO hAO
    obtain ⟨P, hPdis, hPm, hPc, hPsmall⟩ := exists_measurable_small_diameter_partition δ hδ
    let T (i : ℕ) := A ∩ P i
    have hTc : (⋃ i, T i) = A := by rw [show (⋃ i, T i) = A ∩ ⋃ i, P i from (inter_iUnion _ _).symm,
      hPc, inter_univ]
    have hTdis : Pairwise (Disjoint on T) := fun i j hij =>
      (hPdis hij).mono inter_subset_right inter_subset_right
    have hTmeas (i : ℕ) : MeasurableSet (T i) := hAclosed.measurableSet.inter (hPm i)
    have hHold (i : ℕ) : HolderOnWith ε 2 f (T i) := by
      intro x hx y hy
      have hxy := hPsmall i x hx.2 y hy.2
      have hBall := (closedBall_subset_cthickening hx.1 δ).trans hδO
      have hForcing (z : Plane) (hz : z ∈ closedBall x δ) : ‖H z‖ ≤ (ε : ℝ) :=
        (show ‖H z‖ < (ε : ℝ) from (hBall hz).2).le
      have hd := critical_dist_quadratic_bound hU hf ε.coe_nonneg hxy (hBall.trans inter_subset_left)
        hx.1.2.1 hForcing
      rw [edist_nndist, edist_nndist, NNReal.coe_ofNat, show (2 : ℝ) = 2 by rfl, ENNReal.rpow_two,
        ← ENNReal.coe_pow, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
      exact_mod_cast hd
    have hImg (i : ℕ) : ν (f '' T i) ≤ (ε : ℝ≥0∞) * μ (T i) := by
      simpa only [ENNReal.rpow_one, NNReal.coe_ofNat, mul_one] using
        (hHold i).hausdorffMeasure_image_le (by norm_num : (0 : ℝ≥0) < 2) (zero_le_one : (0 : ℝ) ≤ 1)
    calc
      _ = ν (⋃ i, f '' T i) := by rw [← hTc, image_iUnion]
      _ ≤ ∑' i, ν (f '' T i) := measure_iUnion_le _
      _ ≤ ∑' i, (ε : ℝ≥0∞) * μ (T i) := ENNReal.tsum_le_tsum hImg
      _ = (ε : ℝ≥0∞) * μ A := by rw [ENNReal.tsum_mul_left, ← measure_iUnion hTdis hTmeas, hTc]
      _ ≤ _ := mul_le_mul_right (measure_mono (fun _ hx => hx.1)) _
  have hLim : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * μ K) (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id :
      Tendsto ((↑) : ℝ≥0 → ℝ≥0∞) (𝓝 0) (𝓝 (↑(0 : ℝ≥0)))) (Or.inr hμ)
    simpa only [ENNReal.coe_zero, zero_mul] using h.mono_left nhdsWithin_le_nhds
  have hPos : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  exact le_antisymm (ge_of_tendsto hLim (hPos.mono hεbound)) zero_le


private theorem exists_planar_basis_image_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Plane →L[ℝ] E) (hL : L ≠ 0) :
    ∃ i : Fin 2, L (EuclideanSpace.single i 1) ≠ 0 := by
  by_contra! h
  apply hL
  ext z
  have hSum : (∑ i : Fin 2, z i • EuclideanSpace.single i (1 : ℝ)) = z := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr z
  rw [← hSum, map_sum]
  simp only [map_smul, h, smul_zero, Finset.sum_const_zero, zero_apply]

private theorem exists_implicit_zero_graph
    {g : ℝ × ℝ → ℝ} (hg : ContDiffAt ℝ 1 g (0, 0))
    (hD : fderiv ℝ g (0, 0) (0, 1) ≠ 0) :
    ∃ ψ : ℝ → ℝ, ContDiffAt ℝ 1 ψ 0 ∧
      ∀ᶠ z : ℝ × ℝ in 𝓝 (0, 0), g z = g (0, 0) → ψ z.1 = z.2 := by
  let L := fderiv ℝ g (0, 0)
  let c := L (0, 1)
  have hc : c ≠ 0 := hD
  have he : L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ) = c • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro t
    change L (0, t) = c * t
    rw [show (0, t) = t • ((0, 1) : ℝ × ℝ) by simp, map_smul, smul_eq_mul, mul_comm]
  have hInv : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible := by
    rw [he]
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext
      intro t
      change c * (c⁻¹ * t) = t
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    · apply ContinuousLinearMap.ext
      intro t
      change c⁻¹ * (c * t) = t
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  let hOne : (1 : ℕ∞ω) ≠ 0 := one_ne_zero
  exact ⟨hg.implicitFunction hOne hInv, hg.contDiffAt_implicitFunction hOne hInv,
    (hg.eventually_apply_eq_iff_implicitFunction hOne hInv).mono fun _ h => h.1⟩

private theorem planar_coordinate_affine_inverse (x y : Plane) {i j : Fin 2} (hij : i ≠ j) :
    x + ((y j - x j) • EuclideanSpace.single j (1 : ℝ) +
      (y i - x i) • EuclideanSpace.single i (1 : ℝ)) = y := by
  apply PiLp.ext
  intro k
  have hk : k = i ∨ k = j := by
    by_contra! h
    have := Fintype.card_le_of_injective (f := fun q : Fin 3 => if q = 0 then i else if q = 1 then j else k)
      (by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all)
    simp at this
  rcases hk with rfl | rfl <;>
    simp [PiLp.add_apply, PiLp.smul_apply, hij, Ne.symm hij]

private theorem nondegenerate_critical_image_locally_null {U : Set Plane} (hU : IsOpen U)
    {f : Plane → ℝ} (hf : ContDiffOn ℝ 2 f U) {x : Plane} (hx : x ∈ U)
    (hxD : fderiv ℝ f x = 0) (hxH : fderiv ℝ (fderiv ℝ f) x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      (volume : Measure ℝ)
        (f '' (({y ∈ U | fderiv ℝ f y = 0} : Set Plane) ∩ ball x r)) = 0 := by
  let H := fderiv ℝ (fderiv ℝ f) x
  obtain ⟨i, hi⟩ := exists_planar_basis_image_ne_zero H hxH
  let ei := EuclideanSpace.single i (1 : ℝ)
  obtain ⟨j, hj⟩ := exists_planar_basis_image_ne_zero (H ei) hi
  let ej := EuclideanSpace.single j (1 : ℝ)
  let h (y : Plane) := (fderiv ℝ f y) ej
  let L := ContinuousLinearMap.apply ℝ ℝ ej
  have hOne := hf.fderiv_of_isOpen hU (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)
  have hh : ContDiffAt ℝ 1 h x := L.contDiff.contDiffAt.comp x (hOne.contDiffAt (hU.mem_nhds hx))
  have hhh : HasFDerivAt h (L.comp H) x :=
    L.hasFDerivAt.comp x (((hOne.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt)
  let j' : Fin 2 := if i = 0 then 1 else 0
  have hij' : i ≠ j' := by fin_cases i <;> decide
  let e' := EuclideanSpace.single j' (1 : ℝ)
  let Z (p : ℝ × ℝ) := x + (p.1 • e' + p.2 • ei)
  let invZ (y : Plane) := (y j' - x j', y i - x i)
  have hZinverse (y : Plane) : Z (invZ y) = y := planar_coordinate_affine_inverse x y hij'
  have hZc : ContDiff ℝ 1 Z :=
    contDiff_const.add ((contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const))
  have hZ0 : Z (0, 0) = x := by simp [Z]
  have hInvZc : Continuous invZ :=
    (((PiLp.continuous_apply 2 _ j').sub continuous_const)).prodMk
      ((PiLp.continuous_apply 2 _ i).sub continuous_const)
  have hInvZ0 : invZ x = (0, 0) := by simp [invZ]
  let T : (ℝ × ℝ) →L[ℝ] Plane :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight e' + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight ei
  have hT : HasFDerivAt Z T (0, 0) := T.hasFDerivAt.const_add x
  let G := h ∘ Z
  have hGC : ContDiffAt ℝ 1 G (0, 0) :=
    (show ContDiffAt ℝ 1 h (Z (0, 0)) from hZ0.symm ▸ hh).comp _ hZc.contDiffAt
  have hGd : HasFDerivAt G ((L.comp H).comp T) (0, 0) :=
    (show HasFDerivAt h (L.comp H) (Z (0, 0)) from hZ0.symm ▸ hhh).comp _ hT
  have hGne : fderiv ℝ G (0, 0) (0, 1) ≠ 0 := by
    rw [hGd.fderiv]
    have hT1 : T (0, 1) = ei := by simp [T]
    exact (show ((L.comp H).comp T) (0, 1) = H ei ej from
      congrArg (fun z : Plane => L (H z)) hT1) ▸ hj
  obtain ⟨ψ, hψc, hψ⟩ := exists_implicit_zero_graph hGC hGne
  have hNear : ∀ᶠ y in 𝓝 x, G (invZ y) = G (0, 0) → ψ (invZ y).1 = (invZ y).2 :=
    (show Tendsto invZ (𝓝 x) (𝓝 (0, 0)) from hInvZ0 ▸ hInvZc.continuousAt.tendsto).eventually hψ
  have hψD : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ ψ t :=
    (hψc.eventually (by simp)).mono fun _ ht => ht.differentiableAt one_ne_zero
  have hNearD : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ ψ (invZ y).1 := by
    have ht : Tendsto (fun y => (invZ y).1) (𝓝 x) (𝓝 (invZ x).1) := hInvZc.fst.continuousAt.tendsto
    rw [hInvZ0] at ht
    exact ht.eventually hψD
  obtain ⟨r, hr, hro⟩ := Metric.mem_nhds_iff.1 (hNear.and hNearD)
  let Q (t : ℝ) := Z (t, ψ t)
  let S : Set ℝ := {t | Q t ∈ U ∧ fderiv ℝ f (Q t) = 0 ∧ DifferentiableAt ℝ ψ t}
  have hSzero : (volume : Measure ℝ) ((f ∘ Q) '' S) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun _ => (0 : ℝ →L[ℝ] ℝ)) _ (fun _ _ => by simp)
    intro t ht
    have hQ : DifferentiableAt ℝ Q t :=
      (hZc.differentiable one_ne_zero _).comp t (differentiableAt_id.prodMk ht.2.2)
    have hFz : HasFDerivAt f 0 (Q t) :=
      ht.2.1 ▸ (((hf.contDiffAt (hU.mem_nhds ht.1)).differentiableAt two_ne_zero).hasFDerivAt)
    simpa only [ContinuousLinearMap.zero_comp] using (hFz.comp t hQ.hasFDerivAt).hasFDerivWithinAt
  refine ⟨r, hr, le_antisymm ((measure_mono ?_).trans_eq hSzero) zero_le⟩
  rintro _ ⟨y, ⟨⟨hyU, hyD⟩, hyr⟩, rfl⟩
  let t := (invZ y).1
  have hGy : G (invZ y) = G (0, 0) := by
    change h (Z (invZ y)) = h (Z (0, 0))
    simp only [hZinverse, hZ0, h, hyD, hxD, zero_apply]
  have heq : ψ t = (invZ y).2 := (hro hyr).1 hGy
  have hQ : Q t = y := by rw [show Q t = Z (t, ψ t) from rfl, heq]; exact hZinverse y
  exact ⟨t, ⟨hQ.symm ▸ hyU, hQ.symm ▸ hyD, (hro hyr).2⟩, congrArg f hQ⟩


private theorem null_image_of_local_open_null_images {A S : Set Plane}
    (hSA : S ⊆ A) (f : Plane → ℝ)
    (hLocal : ∀ x : S, ∃ W : Set Plane, IsOpen W ∧ x.val ∈ W ∧ volume (f '' (A ∩ W)) = 0) :
    (volume : Measure ℝ) (f '' S) = 0 := by
  classical
  choose W hW hxW hImg using hLocal
  have hCover : S ⊆ ⋃ x : S, W x := fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  obtain ⟨J, hJc, hJ⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  letI := hJc.to_subtype
  have hSub : f '' S ⊆ ⋃ j : J, f '' (A ∩ W j.val) := by
    rintro _ ⟨x, hx, rfl⟩
    have hX : x ∈ ⋃ j ∈ J, W j := hJ ▸ hCover hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hX
    exact mem_iUnion.2 ⟨⟨j, hj⟩, ⟨x, ⟨hSA hx, hxj⟩, rfl⟩⟩
  exact le_antisymm ((measure_mono hSub).trans ((measure_iUnion_le _).trans_eq
    (by simp only [hImg, tsum_zero]))) zero_le

private theorem degenerate_critical_image_null {U : Set Plane} (hU : IsOpen U)
    {f : Plane → ℝ} (hf : ContDiffOn ℝ 2 f U) :
    (volume : Measure ℝ) (f '' {x ∈ U | fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0}) = 0 := by
  obtain ⟨K, hK, hKU, _, hEq, _⟩ :=
    StratificationTheory.Compactness.exists_cofinal_compact_exhaustion_openDomain ⟨U, hU⟩
  change (⋃ j, K j) = U at hEq
  let S (j : ℕ) := {x ∈ K j | fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0}
  have hS : (⋃ j, S j) = {x ∈ U | fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0} := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      exact ⟨hKU j hj.1, hj.2⟩
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hEq.symm ▸ hx.1)
      exact mem_iUnion.2 ⟨j, hj, hx.2⟩
  have hNull (j : ℕ) : volume (f '' S j) = 0 :=
    volume_real_eq_zero_of_hausdorff_one (degenerate_critical_image_hausdorff_null_on_compact hU (hK j) (hKU j) hf)
  rw [← hS, image_iUnion]
  exact le_antisymm ((measure_iUnion_le _).trans_eq (by simp only [hNull, tsum_zero])) zero_le

/-- Planar scalar Morse–Sard in the exact form used to select the
physical boundary slices. -/
theorem morseSardPlaneToReal : External.MorseSardPlaneToReal := by
  intro U f hU hf
  classical
  let A := {x ∈ U | fderiv ℝ f x = 0}
  let S := {x ∈ A | fderiv ℝ (fderiv ℝ f) x ≠ 0}
  let T := {x ∈ U | fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0}
  have hS : volume (f '' S) = 0 := by
    apply null_image_of_local_open_null_images (A := A) (fun _ hx => hx.1) f
    intro x
    obtain ⟨r, hr, hNull⟩ :=
      nondegenerate_critical_image_locally_null hU hf x.property.1.1 x.property.1.2 x.property.2
    exact ⟨ball x.val r, isOpen_ball, mem_ball_self hr, hNull⟩
  have hT : volume (f '' T) = 0 := degenerate_critical_image_null hU hf
  have hA : A = S ∪ T := by
    ext x
    constructor
    · intro hx
      by_cases he : fderiv ℝ (fderiv ℝ f) x = 0
      · exact Or.inr ⟨hx.1, hx.2, he⟩
      · exact Or.inl ⟨hx, he⟩
    · rintro (hx | hx)
      · exact hx.1
      · exact ⟨hx.1, hx.2.1⟩
  have hNull : volume (f '' A) = 0 := by
    rw [hA, image_union]
    exact measure_union_null hS hT
  have hAE : ∀ᵐ s : ℝ, s ∉ f '' A := by
    apply ae_iff.2
    have he : {s : ℝ | ¬s ∉ f '' A} = f '' A := by
      ext s
      simp only [mem_setOf_eq, not_not]
    rwa [he]
  exact hAE.mono fun s hs p hp he hZero => hs ⟨p, ⟨hp, hZero⟩, he⟩

end Thesis
