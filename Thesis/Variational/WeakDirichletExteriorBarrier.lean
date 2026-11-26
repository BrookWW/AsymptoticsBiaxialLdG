module

public import Thesis.Variational.BoundaryL4ExteriorBall
public import Thesis.Definitions
import Thesis.Variational.BoundaryDefect
import Thesis.Variational.ScaledDefects
import HolderToCK.Analysis.Poisson.RadialPowerDerivatives

/-! Smooth scalar superharmonic barriers at the physical Dirichlet wall. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal

namespace Thesis

private theorem inv_norm_sub_sq_contDiffAt (a x : Point) (hx : x ≠ a) :
    ContDiffAt ℝ ∞ (fun y : Point => (‖y-a‖^2)⁻¹) x := by
  simpa only [Real.rpow_neg_one] using HolderToCK.normSq_rpow_contDiffAt a (-1) x hx

private theorem laplacian_inv_norm_sub_sq (a x : Point) (hx : x ≠ a) :
    laplacian (fun y : Point => (‖y-a‖^2)⁻¹) x = 2/(‖x-a‖^4) := by
  let g (y : Point) := (‖y-a‖^2) ^ (-1 : ℝ)
  have hg : ContDiffAt ℝ ∞ g x := HolderToCK.normSq_rpow_contDiffAt a (-1) x hx
  have hEq : (fun y : Point => (‖y-a‖^2)⁻¹) = g :=
    funext fun y => (Real.rpow_neg_one (‖y-a‖^2)).symm
  rw [hEq]
  change (∑ i : Fin 3, fderiv ℝ (fun z => fderiv ℝ g z (EuclideanSpace.single i 1)) x
    (EuclideanSpace.single i 1)) = _
  rw [← HolderToCK.scalar_laplacian_coordinateSum g x hg]
  have hL := HolderToCK.normSq_rpow_laplacian a (-1) x hx
  change Laplacian.laplacian g x =
      2 * (-1 : ℝ) * ((3 : ℝ) + 2 * (-1 : ℝ) - 2) * (‖x-a‖^2) ^ ((-1 : ℝ) - 1) at hL
  rw [hL]
  rw [show 2 * (-1 : ℝ) * ((3 : ℝ) + 2 * (-1 : ℝ) - 2) = 2 by norm_num,
    show (-1 : ℝ) - 1 = -(2 : ℝ) by norm_num,Real.rpow_neg (sq_nonneg _),
    Real.rpow_two,← pow_mul,div_eq_mul_inv]

private theorem laplacian_const_exteriorBarrier (c : ℝ) (x : Point) :
    laplacian (fun _ : Point => c) x = 0 := by
  have h (i : Fin 3) : coordDeriv i (fun _ : Point => c) = fun _ => 0 :=
    funext fun y => by simp [coordDeriv]
  simp [laplacian,h,coordDeriv]

private theorem scalar_memLp_two_of_continuousOn_closed_smoothDomain
    {U : Set Point} (hU : IsSmoothDomain U) {v : Point → ℝ}
    (hv : ContinuousOn v (closure U)) : MemLp v 2 (volume.restrict U) := by
  letI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  obtain ⟨M,hM⟩ := hU.1.2.2.isCompact_closure.exists_bound_of_continuousOn hv
  exact MemLp.of_bound ((hv.mono subset_closure).aestronglyMeasurable hU.1.1.measurableSet) M
    ((ae_restrict_mem hU.1.1.measurableSet).mono fun x hx => hM x (subset_closure hx))

/-- For a fixed bound on the forcing, every wall point has a smooth
barrier vanishing there and superharmonic with the required margin.
The value and full gradient bounds are uniform over the wall. -/
theorem IsSmoothDomain.exists_exterior_tangent_scalar_barrier
    {U : Set Point} (hU : IsSmoothDomain U) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ frontier U, ∃ B : Point → ℝ,
      ContDiffOn ℝ ∞ B (closure U) ∧ B p = 0 ∧
      (∀ x ∈ closure U, 0 ≤ B x ∧ B x ≤ C ∧ ‖fderiv ℝ B x‖ ≤ C) ∧
      (∀ x ∈ U, laplacian B x ≤ -M) ∧
      MemLp B 2 (volume.restrict U) ∧
      (∀ j : Fin 3, MemLp (coordDeriv j B) 2 (volume.restrict U)) ∧
      MemLp (laplacian B) 2 (volume.restrict U) := by
  obtain ⟨S,hS,hExterior⟩ := hU.exists_uniform_exterior_tangent_balls
  let ρ := S/2
  have hρ : 0 < ρ := half_pos hS
  obtain ⟨N,hN⟩ := hU.1.2.2.isCompact_closure.exists_bound_of_continuousOn
    (continuous_id : Continuous (id : Point → Point)).continuousOn
  let L := max N 0
  have hL : 0 ≤ L := le_max_right _ _
  let R := 2*L+ρ+1
  have hR : 0 < R := by dsimp only [R]; positivity
  let K := M*R^4/2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let V : Set Point := ({(0 : Point)} : Set Point)ᶜ
  have hV : IsOpen V := isClosed_singleton.isOpen_compl
  let G (x : Point) := (‖x-(0 : Point)‖^2)⁻¹
  have hG : ContDiffOn ℝ ∞ G V :=
    fun x hx => (inv_norm_sub_sq_contDiffAt 0 x hx).contDiffWithinAt
  let A := closedBall (0 : Point) R ∩ {x : Point | ρ ≤ ‖x‖}
  have hA : IsCompact A := (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hAV : A ⊆ V := by
    intro x hx
    change x ≠ 0
    intro he
    have ht : ρ ≤ ‖x‖ := hx.2
    rw [he,norm_zero] at ht
    exact hρ.not_ge ht
  obtain ⟨D,hD⟩ := hA.exists_bound_of_continuousOn
    ((hG.continuousOn_fderiv_of_isOpen hV (by simp)).mono hAV)
  let C := max (K*(ρ^2)⁻¹) (K*(max D 0))
  have hC : 0 ≤ C := le_trans (mul_nonneg hK (inv_nonneg.mpr (sq_nonneg _))) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro p hp
  obtain ⟨ν,hν,hOut⟩ := hExterior p hp
  let a := p+ρ • ν
  obtain ⟨hLow,_⟩ := hOut ρ ⟨hρ,half_lt_self hS⟩
  have hNormρ : ‖ρ • ν‖ = ρ := by
    rw [norm_smul,Real.norm_of_nonneg hρ.le,hν,mul_one]
  have hNear : ‖p-a‖ = ρ := by
    change ‖p-(p+ρ • ν)‖ = ρ
    rw [sub_add_eq_sub_sub,sub_self,zero_sub,norm_neg,hNormρ]
  have hpL : ‖p‖ ≤ L := (hN p (frontier_subset_closure hp)).trans (le_max_left _ _)
  have hUpper (x : Point) (hx : x ∈ closure U) : ‖x-a‖ ≤ R := by
    have hxL : ‖x‖ ≤ L := (hN x hx).trans (le_max_left _ _)
    change ‖x-(p+ρ • ν)‖ ≤ R
    rw [sub_add_eq_sub_sub]
    refine (norm_sub_le _ _).trans ?_
    rw [hNormρ]
    have h := (norm_sub_le x p).trans (add_le_add hxL hpL)
    dsimp only [R]
    linarith only [h]
  let W : Set Point := ({a} : Set Point)ᶜ
  have hW : IsOpen W := isClosed_singleton.isOpen_compl
  have hInto (x : Point) (hx : x ∈ closure U) : x ∈ W := by
    change x ≠ a
    intro he
    have ht := hLow x hx
    rw [he,sub_self,norm_zero] at ht
    exact hρ.not_ge ht
  let g (x : Point) := (‖x-a‖^2)⁻¹
  have hg : ContDiffOn ℝ ∞ g W :=
    fun x hx => (inv_norm_sub_sq_contDiffAt a x hx).contDiffWithinAt
  let B (x : Point) := K • ((ρ^2)⁻¹-g x)
  have hB : ContDiffOn ℝ ∞ B W := (contDiffOn_const.sub hg).const_smul K
  have hBL (x : Point) (hx : x ∈ closure U) : ‖fderiv ℝ B x‖ ≤ C := by
    have hxA : x-a ∈ A :=
      ⟨mem_closedBall_zero_iff.mpr (hUpper x hx),hLow x hx⟩
    have hder := ((hG (x-a) (hAV hxA)).contDiffAt (hV.mem_nhds (hAV hxA))).differentiableAt (by simp)
    have hGx : HasFDerivAt g (fderiv ℝ G (x-a)) x := by
      have hd := hder.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
      have hFn : G ∘ (fun y : Point => id y-a) = g := by
        funext y
        simp only [G,g,Function.comp_apply,id_eq,sub_zero]
      rw [hFn,ContinuousLinearMap.comp_id] at hd
      exact hd
    have hDB : HasFDerivAt B (K • (0-fderiv ℝ G (x-a))) x :=
      ((hasFDerivAt_const ((ρ^2)⁻¹) x).sub hGx).const_smul K
    rw [hDB.fderiv,zero_sub,norm_smul,norm_neg,Real.norm_of_nonneg hK]
    exact (mul_le_mul_of_nonneg_left ((hD (x-a) hxA).trans (le_max_left _ _)) hK).trans
      (le_max_right _ _)
  have hBΔ (x : Point) (hx : x ∈ W) : laplacian B x = (-2*K)/(‖x-a‖^4) := by
    have hG₂ : ContDiffOn ℝ 2 g W := hg.of_le (WithTop.coe_le_coe.mpr le_top)
    change laplacian (fun y => K • ((ρ^2)⁻¹-g y)) x = _
    rw [laplacian_const_smul hW (contDiffOn_const.sub hG₂) hx,
      laplacian_sub_of_contDiffOn hW contDiffOn_const hG₂ hx,
      laplacian_const_exteriorBarrier,laplacian_inv_norm_sub_sq a x hx,zero_sub,smul_eq_mul]
    ring
  have hΔC : ContinuousOn (laplacian B) W := by
    have h := (continuous_id.sub (continuous_const (y := a))).norm.pow 4
    have h' : ContinuousOn (fun x : Point => (-2*K)/(‖x-a‖^4)) W :=
      continuousOn_const.div h.continuousOn
        (fun x hx => pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.mpr hx)))
    exact h'.congr hBΔ
  refine ⟨B,hB.mono hInto,?_,?_,?_,
    scalar_memLp_two_of_continuousOn_closed_smoothDomain hU (hB.continuousOn.mono hInto),?_,
    scalar_memLp_two_of_continuousOn_closed_smoothDomain hU (hΔC.mono hInto)⟩
  · change K • ((ρ^2)⁻¹-(‖p-a‖^2)⁻¹) = 0
    rw [hNear,sub_self,smul_zero]
  · intro x hx
    have hxPos : 0 < ‖x-a‖ := hρ.trans_le (hLow x hx)
    have hxInv : (‖x-a‖^2)⁻¹ ≤ (ρ^2)⁻¹ :=
      (inv_le_inv₀ (pow_pos hxPos _) (pow_pos hρ _)).2 (pow_le_pow_left₀ hρ.le (hLow x hx) 2)
    refine ⟨mul_nonneg hK (sub_nonneg.mpr hxInv),?_,hBL x hx⟩
    exact (mul_le_mul_of_nonneg_left (sub_le_self _ (inv_nonneg.mpr (sq_nonneg _))) hK).trans
      (le_max_left _ _)
  · intro x hx
    have hxCl := subset_closure hx
    have hxPos : 0 < ‖x-a‖ := hρ.trans_le (hLow x hxCl)
    rw [hBΔ x (hInto x hxCl)]
    apply (div_le_iff₀ (pow_pos hxPos _)).2
    have h := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ (norm_nonneg _) (hUpper x hxCl) 4) (neg_nonpos.mpr hM)
    dsimp only [K]
    linarith only [h]
  · intro j
    have hDf := hB.continuousOn_fderiv_of_isOpen hW (by simp)
    exact scalar_memLp_two_of_continuousOn_closed_smoothDomain hU
      ((hDf.clm_apply continuousOn_const).mono hInto)

end Thesis
