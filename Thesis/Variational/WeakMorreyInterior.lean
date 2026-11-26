module

public import Thesis.Variational.LocalMorreyFromLp
public import Thesis.Upstream.GlobalCompactSobolevTransport
import HarmonicMaps.Analysis.AffineBallMeasure
import StratificationTheory.Foundation.SmoothOpenDomainSobolevPullback
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Local Sobolev–Morrey regularity for actual weak columns. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory Topology
open scoped ContDiff ENNReal NNReal

namespace Thesis

/-- A smooth local chart transports (L^p) first columns on bounded patches
whenever its pushforward measure is dominated by the indicated volume. -/
theorem memLp_ambientGradientPullback_of_map_le {n q : ℕ}
    (F : Domain n → Domain n) (hF : ContDiff ℝ ∞ F)
    (V W : OpenDomain n) (hV : Bornology.IsBounded V.val)
    {c p : ℝ≥0∞} (hc : c ≠ ⊤)
    (hMap : Measure.map F (volume.restrict V.val) ≤ c • volume.restrict W.val)
    (D : Domain n → HarmonicMaps.Gradient n q)
    (hD : ∀ j, MemLp (fun x => D x j) p (volume.restrict W.val)) :
    ∀ i, MemLp (fun x => ambientGradientPullback F D x i) p (volume.restrict V.val) := by
  obtain ⟨M,hM⟩ := hV.isCompact_closure.exists_bound_of_continuousOn
    (hF.continuous_fderiv (by simp)).continuousOn
  let μ := volume.restrict V.val
  intro i
  unfold ambientGradientPullback
  apply memLp_finsetSum
  intro j _
  let a (x : Domain n) := fderiv ℝ F x (EuclideanSpace.single i 1) j
  have ha : Continuous a :=
    (EuclideanSpace.proj j).continuous.comp ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hBound : ∀ᵐ x ∂μ, ‖a x‖ ≤ M := by
    filter_upwards [ae_restrict_mem V.property.measurableSet] with x hx
    calc
      ‖a x‖ ≤ ‖(fderiv ℝ F x) (EuclideanSpace.single i 1)‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖fderiv ℝ F x‖ := by
        simpa only [PiLp.norm_single, norm_one, mul_one] using
          (fderiv ℝ F x).le_opNorm (EuclideanSpace.single i (1 : ℝ))
      _ ≤ M := hM x (subset_closure hx)
  have haTop := memLp_top_of_bound ha.aestronglyMeasurable M hBound
  have hDF : MemLp (fun x => D (F x) j) p μ := by
    have h := ((hD j).smul_measure hc).mono_measure hMap
    exact h.comp_of_map hF.continuous.measurable.aemeasurable
  exact hDF.smul (r := p) haTop

private theorem exists_half_unitBall_holder_rep {q : ℕ} {w : Point → Ambient q}
    {D : Point → HarmonicMaps.Gradient 3 q}
    (hw : MemW12 (ballDomain (0 : Point) 1) w D)
    {p : ℝ} (hp : 3 < p)
    (hD : ∀ j, MemLp (fun x => D x j) (ENNReal.ofReal p) (volume.restrict (ball (0 : Point) 1))) :
    ∃ v : ball (0 : Point) (1 / 2) → Ambient q,
        IsContinuousRepresentative (ballDomain (0 : Point) (1 / 2)) w v ∧
        ∃ H : ℝ, 0 ≤ H ∧ ∀ x y : ball (0 : Point) (1 / 2),
          ‖v x-v y‖ ≤ H*dist (x : Point) (y : Point)^(1-3/p) := by
  let β := 1-3/p
  have hp₀ : 0 < p := by linarith
  have hβ : 0 < β := sub_pos.mpr ((div_lt_iff₀ hp₀).2 (by simpa using hp))
  have hβ₁ : β < 1 := sub_lt_self _ (div_pos (by norm_num) hp₀)
  obtain ⟨C,hC,hM⟩ := exists_unitBall_holder_representative_of_lp_columns hβ hβ₁
  let g (x : Point) := ∑ j : Fin 3, ‖D x j‖
  have hg : MemLp g (ENNReal.ofReal p) (volume.restrict (ball (0 : Point) 1)) :=
    memLp_finsetSum _ (fun j _ => (hD j).norm)
  let M := (eLpNorm g (ENNReal.ofReal p) (volume.restrict (ball (0 : Point) 1))).toReal
  have hMnorm : eLpNorm g (ENNReal.ofReal p) (volume.restrict (ball (0 : Point) 1)) ≤ ENNReal.ofReal M :=
    (ENNReal.ofReal_toReal hg.eLpNorm_ne_top).ge
  have hPoint (x : Point) (j : Fin 3) : ‖D x j‖ ≤ ‖g x‖ := by
    have h₀ : 0 ≤ g x := Finset.sum_nonneg fun _ _ => norm_nonneg _
    simpa only [Real.norm_of_nonneg h₀] using
      (Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
        (f := fun i => ‖D x i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j))
  obtain ⟨v,hv,hH⟩ := hM q w D hw p M hp rfl ENNReal.toReal_nonneg g hg hMnorm (Eventually.of_forall hPoint)
  exact ⟨v,hv,C*M,mul_nonneg hC.le ENNReal.toReal_nonneg,hH⟩

/-- A weak map on an ordinary ball with (L^p) columns admits a Hölder
representative on the half ball. -/
theorem exists_halfBall_holder_rep_of_weakColumns {q : ℕ} {a : Point} {r p : ℝ}
    (hr : 0 < r) (hp : 3 < p) {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 (ballDomain a r) u D)
    (hD : ∀ j, MemLp (fun x => D x j) (ENNReal.ofReal p) (volume.restrict (ball a r))) :
    ∃ v : Point → Ambient q, u =ᵐ[volume.restrict (ball a (r/2))] v ∧
      ContinuousOn v (ball a (r/2)) ∧ ∃ K : ℝ, 0 ≤ K ∧
        ∀ x ∈ ball a (r/2), ∀ y ∈ ball a (r/2),
          ‖v x-v y‖ ≤ K*dist x y^(1-3/p) := by
  classical
  let V := ballDomain (0 : Point) 1
  let W := ballDomain a r
  let c := ENNReal.ofReal ((r ^ (3 : ℕ))⁻¹)
  let F (x : Point) := a + r • (x-0)
  have hF : ContDiff ℝ ∞ F := affineBall_contDiff a 0 r
  have hInto : MapsTo F V.val W.val := by
    intro x hx
    change x ∈ ball (0 : Point) 1 at hx
    exact (affineBall_mem_ball_iff a (0 : Point) hr r x).2 (by simpa only [div_self hr.ne'] using hx)
  have hMap : Measure.map F (volume.restrict V.val) = c • volume.restrict W.val := by
    change Measure.map (fun x : Point => a + r • (x-0)) (volume.restrict (ball (0 : Point) 1)) =
      ENNReal.ofReal ((r ^ (3 : ℕ))⁻¹) • volume.restrict (ball a r)
    simpa only [div_self hr.ne'] using affineBall_map_restrict a (0 : Point) hr r
  obtain ⟨L,hL⟩ := (isCompact_closedBall (0 : Point) 1).exists_bound_of_continuousOn
    (hF.continuous_fderiv (by simp)).continuousOn
  have hGraph : MemW12 V (u ∘ F) (ambientGradientPullback F D) :=
    memW12_smooth_open_domain_pullback hu V F hF.contDiffOn hInto L
      (fun x hx => hL x (ball_subset_closedBall hx)) c ENNReal.ofReal_ne_top hMap.le
  have hColumns := memLp_ambientGradientPullback_of_map_le F hF V W isBounded_ball
    ENNReal.ofReal_ne_top hMap.le D hD
  obtain ⟨z,hz,K,hK,hMod⟩ := exists_half_unitBall_holder_rep hGraph hp hColumns
  let I (x : Point) := (0 : Point) + r⁻¹ • (x-a)
  let U := ball a (r/2)
  have hInvRadius : (1 / 2 : ℝ) / r⁻¹ = r/2 := by field_simp
  have hInv (x : Point) : F (I x) = x := by
    dsimp only [F,I]
    rw [zero_add,sub_zero,smul_smul,mul_inv_cancel₀ hr.ne',one_smul,add_sub_cancel]
  have hI (x : Point) (hx : x ∈ U) : I x ∈ ball (0 : Point) (1/2) :=
    (affineBall_mem_ball_iff (0 : Point) a (inv_pos.mpr hr) (1/2) x).2 (hInvRadius ▸ hx)
  let A (x : U) : ball (0 : Point) (1/2) := ⟨I x,hI x x.property⟩
  have hAC : Continuous A := (affineBall_contDiff (0 : Point) a r⁻¹).continuous.comp
    continuous_subtype_val |>.subtype_mk _
  let v (x : Point) := if hx : x ∈ U then z (A ⟨x,hx⟩) else 0
  have hv (x : Point) (hx : x ∈ U) : v x = z (A ⟨x,hx⟩) := dif_pos hx
  have hCont : ContinuousOn v U := continuousOn_iff_continuous_restrict.mpr
    ((hz.1.comp hAC).congr fun x => (hv x x.property).symm)
  have hAE : u =ᵐ[volume.restrict U] v := by
    have h := ae_affineBall (0 : Point) a (inv_pos.mpr hr) (1/2) hz.2
    rw [hInvRadius] at h
    filter_upwards [h,ae_restrict_mem measurableSet_ball] with x hx hxU
    rw [hv x hxU]
    have hVal := hx (hI x hxU)
    change z (A ⟨x,hxU⟩) = u (F (I x)) at hVal
    exact ((hInv x) ▸ hVal).symm
  let β := 1-3/p
  refine ⟨v,hAE,hCont,K*(r⁻¹)^β,mul_nonneg hK (Real.rpow_nonneg (inv_nonneg.mpr hr.le) _),?_⟩
  intro x hx y hy
  have hDist : dist (I x) (I y) = r⁻¹ * dist x y := by
    rw [dist_eq_norm, dist_eq_norm]
    change ‖(0 : Point) + r⁻¹ • (x-a) - (0 + r⁻¹ • (y-a))‖ = _
    rw [zero_add,zero_add,← smul_sub,sub_sub_sub_cancel_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  rw [hv x hx,hv y hy]
  refine (hMod (A ⟨x,hx⟩) (A ⟨y,hy⟩)).trans_eq ?_
  change K*dist (I x) (I y)^β = K*(r⁻¹)^β*dist x y^β
  rw [hDist,Real.mul_rpow (inv_nonneg.mpr hr.le) dist_nonneg,mul_assoc]

end Thesis
