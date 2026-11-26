module

public import Thesis.Definitions
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

/-! The horizontal and normal flux of a compactly supported field on a flat half-space. -/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped ContDiff NNReal

namespace Thesis

/-- A directional derivative of a compactly supported classical test
has zero total integral in Euclidean space. -/
theorem integral_fderiv_apply_eq_zero_of_compactSupport {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ContDiff ℝ 1 g) (hK : HasCompactSupport g) (u : EuclideanSpace ℝ (Fin n)) :
    (∫ y, (fderiv ℝ g y) u) = 0 := by
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hK hg one_ne_zero
  have hI : Integrable g volume := hg.continuous.integrable_of_hasCompactSupport hK
  have hT := hL.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hK (g := fun _ => (1 : ℝ)) continuous_const u
  have hCalc (t : ℝ) : (∫ y, (t⁻¹ • (g (y + t • u) - g y)) * (1 : ℝ)) = 0 := by
    have hIt : Integrable (fun y => g (y + t • u)) :=
      (measurePreserving_add_right (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (t • u)).integrable_comp_of_integrable hI
    simp_rw [mul_one, smul_eq_mul]
    rw [integral_const_mul, integral_sub hIt hI, integral_add_right_eq_self, sub_self,mul_zero]
  have hLim : Tendsto (fun t : ℝ => ∫ y, (t⁻¹ • (g (y + t • u) - g y)) * (1 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.congr (fun t => (hCalc t).symm)
  have hEq := tendsto_nhds_unique hT hLim
  simpa only [mul_one, funext fun y =>
    (((hg.differentiable one_ne_zero y).hasFDerivAt).hasLineDerivAt u).lineDeriv] using hEq

/-- The open side of the flat wall in the ordinary product coordinates. -/
abbrev flatOpenHalf : Set (Plane × ℝ) := univ ×ˢ Ioi (0 : ℝ)

/-- The flat wall and its closed inward side. -/
abbrev flatClosedHalf : Set (Plane × ℝ) := univ ×ˢ Ici (0 : ℝ)

private theorem isOpen_flatOpenHalf : IsOpen flatOpenHalf := isOpen_univ.prod isOpen_Ioi

private theorem flatOpenHalf_subset_closed : flatOpenHalf ⊆ flatClosedHalf :=
  prod_mono subset_rfl Ioi_subset_Ici_self

private theorem uniqueDiffOn_flatClosedHalf : UniqueDiffOn ℝ flatClosedHalf := by
  apply uniqueDiffOn_convex (convex_univ.prod (convex_Ici _))
  refine ⟨((0 : Plane),(1 : ℝ)), mem_interior_iff_mem_nhds.mpr ?_⟩
  exact mem_of_superset (isOpen_flatOpenHalf.mem_nhds
    ⟨mem_univ _,mem_Ioi.mpr (by norm_num : (0 : ℝ) < 1)⟩)
    flatOpenHalf_subset_closed

/-- Applying the actual half-space derivative to a continuous vector field
is integrable for a compactly supported test. -/
theorem integrableOn_flat_derivative {G : Plane × ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G flatClosedHalf) (hCap : HasCompactSupport G)
    {u : Plane × ℝ → Plane × ℝ} (hu : Continuous u) :
    IntegrableOn (fun p => (fderiv ℝ G p) (u p)) flatOpenHalf := by
  let H := flatClosedHalf
  let S := flatOpenHalf
  let K := tsupport G ∩ H
  have hK : IsCompact K := hCap.inter_right (isClosed_univ.prod isClosed_Ici)
  let Q (p : Plane × ℝ) := (fderivWithin ℝ G H p) (u p)
  have hQC : ContinuousOn Q H :=
    (hG.continuousOn_fderivWithin uniqueDiffOn_flatClosedHalf le_rfl).clm_apply hu.continuousOn
  have hQI : IntegrableOn Q K := (hQC.mono inter_subset_right).integrableOn_compact hK
  have hRel : tsupport G ∩ S ⊆ K := inter_subset_inter_right _ flatOpenHalf_subset_closed
  have hS : MeasurableSet S := isOpen_flatOpenHalf.measurableSet
  have hT : MeasurableSet (tsupport G) := isClosed_tsupport G |>.measurableSet
  let W (p : Plane × ℝ) := (fderiv ℝ G p) (u p)
  have hQW : EqOn Q W S := by
    intro p hp
    have hN : H ∈ 𝓝 p := mem_of_superset (isOpen_flatOpenHalf.mem_nhds hp) flatOpenHalf_subset_closed
    have hDiff := ((hG _ (flatOpenHalf_subset_closed hp)).contDiffAt hN).differentiableAt one_ne_zero
    exact congrArg (fun L : Plane × ℝ →L[ℝ] ℝ => L (u p))
      (fderivWithin_eq_fderiv (uniqueDiffWithinAt_of_mem_nhds hN) hDiff)
  have hW₁ : IntegrableOn W (tsupport G ∩ S) :=
    (integrableOn_congr_fun (hQW.mono inter_subset_right) (hT.inter hS)).mp (hQI.mono_set hRel)
  have hW₀ : IntegrableOn W (S \ tsupport G) := by
    refine (integrableOn_congr_fun ?_ (hS.diff hT)).mpr (integrableOn_zero (μ := volume))
    intro p hp
    change (fderiv ℝ G p) (u p) = 0
    rw [fderiv_of_notMem_tsupport ℝ hp.2, zero_apply]
  have hUnion : (tsupport G ∩ S) ∪ (S \ tsupport G) = S := by
    rw [inter_comm, inter_union_sdiff]
  change IntegrableOn W S
  rw [← hUnion]
  exact hW₁.union hW₀

private theorem halfSpace_prod_measure :
    (volume : Measure (Plane × ℝ)).restrict flatOpenHalf =
      (volume : Measure Plane).prod ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) := by
  change ((volume : Measure Plane).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ioi (0 : ℝ)) = _
  rw [← Measure.prod_restrict, Measure.restrict_univ]

/-- A constant horizontal derivative has zero total integral on the inward
half-space. -/
theorem integral_flat_horizontal_derivative {G : Plane × ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G flatClosedHalf) (hCap : HasCompactSupport G) (u : Plane) :
    (∫ p in flatOpenHalf, (fderiv ℝ G p) (u,0)) = 0 := by
  have hI := integrableOn_flat_derivative hG hCap (u := fun _ => (u,0)) continuous_const
  rw [IntegrableOn,halfSpace_prod_measure] at hI
  rw [halfSpace_prod_measure, integral_prod_symm _ hI]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  let f (y : Plane) := G (y,t)
  have hf : ContDiff ℝ 1 f := by
    rw [← contDiffOn_univ]
    exact hG.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun y _ => ⟨mem_univ y, show t ∈ Ici 0 from (mem_Ioi.1 ht).le⟩)
  have hfCap : HasCompactSupport f := by
    have hK : IsCompact (Prod.fst '' tsupport G) := hCap.image continuous_fst
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro y hy
    exact ⟨(y,t),subset_closure hy,rfl⟩
  have hfDer (y : Plane) :
      (fderiv ℝ f y) u = (fderiv ℝ G (y,t)) (u,0) := by
    have hy : (y,t) ∈ flatOpenHalf := ⟨mem_univ _,ht⟩
    have hN : flatClosedHalf ∈ 𝓝 (y,t) :=
      mem_of_superset (isOpen_flatOpenHalf.mem_nhds hy) flatOpenHalf_subset_closed
    have hDG := ((hG _ (flatOpenHalf_subset_closed hy)).contDiffAt hN).differentiableAt one_ne_zero
    have hL : HasFDerivAt (fun y' : Plane => (y',t)) (ContinuousLinearMap.inl ℝ Plane ℝ) y := by
      let A := ContinuousLinearMap.inl ℝ Plane ℝ
      have hF : (fun y' : Plane => (y',t)) = fun y' => A y' + (0,t) := by
        funext z
        change (z,t) = (z,(0:ℝ)) + (0,t)
        simp
      rw [hF]
      exact (A.hasFDerivAt (x := y)).add_const (0,t)
    exact congrArg (fun L : Plane →L[ℝ] ℝ => L u) (hDG.hasFDerivAt.comp y hL).fderiv
  simp_rw [← hfDer]
  exact integral_fderiv_apply_eq_zero_of_compactSupport hf hfCap u

/-- A weighted normal derivative on the inward half-space gives the
negative trace integral, with the weight fixed along each normal line. -/
theorem integral_flat_vertical_derivative {G : Plane × ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G flatClosedHalf) (hCap : HasCompactSupport G)
    {w : Plane → ℝ} (hw : Continuous w) :
    (∫ p in flatOpenHalf, w p.1 * (fderiv ℝ G p) (0,1)) =
      -∫ y, w y * G (y,0) := by
  have hI := integrableOn_flat_derivative hG hCap (u := fun _ => (0,1)) continuous_const
  have hIW := integrableOn_flat_derivative hG hCap (u := fun p => (0,w p.1))
    (continuous_const.prodMk (hw.comp continuous_fst))
  have hV (p : Plane × ℝ) : (fderiv ℝ G p) (0,w p.1) = w p.1 * (fderiv ℝ G p) (0,1) := by
    rw [show ((0 : Plane),w p.1) = w p.1 • ((0 : Plane),(1 : ℝ)) by simp, map_smul, smul_eq_mul]
  simp_rw [hV] at hIW
  rw [IntegrableOn,halfSpace_prod_measure] at hI hIW
  rw [halfSpace_prod_measure,integral_prod _ hIW,← integral_neg]
  apply integral_congr_ae
  filter_upwards [hI.prod_right_ae] with y hy
  let g (t : ℝ) := G (y,t)
  have hg : ContinuousWithinAt g (Ici (0 : ℝ)) 0 :=
    (hG.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨mem_univ y,ht⟩)) 0 self_mem_Ici
  have hD (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      HasDerivAt g ((fderiv ℝ G (y,t)) (0,1)) t := by
    have hP : (y,t) ∈ flatOpenHalf := ⟨mem_univ _,ht⟩
    have hN : flatClosedHalf ∈ 𝓝 (y,t) :=
      mem_of_superset (isOpen_flatOpenHalf.mem_nhds hP) flatOpenHalf_subset_closed
    have hDG := ((hG _ (flatOpenHalf_subset_closed hP)).contDiffAt hN).differentiableAt one_ne_zero
    exact hDG.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t y).prodMk (hasDerivAt_id t))
  obtain ⟨R,hR⟩ := hCap.isBounded.exists_norm_le
  have hgT : Tendsto g atTop (𝓝 0) := tendsto_const_nhds.congr' (by
    filter_upwards [eventually_gt_atTop (max R 0)] with t ht
    symm
    change G (y,t) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hNorm := (norm_snd_le (y,t)).trans (hR (y,t) h)
    rw [Real.norm_of_nonneg ((le_max_right R 0).trans ht.le)] at hNorm
    exact (not_le_of_gt ((le_max_left R 0).trans_lt ht)) hNorm)
  have hZ := integral_Ioi_of_hasDerivAt_of_tendsto hg hD hy hgT
  rw [integral_const_mul, hZ, zero_sub, mul_neg]

end Thesis
