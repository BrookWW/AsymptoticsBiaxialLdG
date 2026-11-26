module

public import Thesis.Upstream.AmbientWeakPartialAlgebra
public import Thesis.Model
import Thesis.Variational.MorreyDomainCharts
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Tangential weak derivatives glue across a flat wall without a normal flux. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set Topology
open scoped ContDiff ENNReal

namespace Thesis

private theorem smoothTransition_normal_cutoff_column
    (L : Point →L[ℝ] ℝ) (k : Fin 3) (hL : L (axis k) = 0)
    (n : ℕ) (x : Point) :
    fderiv ℝ (fun y : Point => Real.smoothTransition (((n : ℝ)+1)*L y-1)) x (axis k) = 0 := by
  let g (y : Point) := ((n : ℝ)+1)*L y-1
  have hg : HasFDerivAt g (((n : ℝ)+1) • L) x := by
    with_unfolding_all exact ((L.hasFDerivAt (x := x)).const_smul ((n : ℝ)+1)).sub_const (1 : ℝ)
  have hT := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero (g x)).hasDerivAt
  have hComp := (hT.comp_hasFDerivAt x hg).fderiv
  change fderiv ℝ (Real.smoothTransition ∘ g) x (axis k) = 0
  rw [hComp,smul_apply,smul_apply,hL,smul_zero,smul_zero]

private theorem tendsto_smoothTransition_normal_cutoff_one {l : ℝ} (hl : 0 < l) :
    Tendsto (fun n : ℕ => Real.smoothTransition (((n : ℝ)+1)*l-1)) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  have h := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually
    (eventually_ge_atTop ((2/l) : ℝ))
  filter_upwards [h] with n hn
  symm
  apply Real.smoothTransition.one_of_one_le
  have hN := (div_le_iff₀ hl).1 (show 2/l ≤ (n : ℝ) from hn)
  nlinarith only [hN,hl]
private theorem tendsto_cutoff_setIntegral
    {q : ℕ} (L : Point →L[ℝ] ℝ) {w : Point → Ambient q}
    (hw : IntegrableOn w {x | 0 < L x}) :
    Tendsto (fun n : ℕ => ∫ x in {x | 0 < L x},
      Real.smoothTransition (((n : ℝ)+1)*L x-1) • w x) atTop
      (𝓝 (∫ x in {x | 0 < L x}, w x)) := by
  let U := {x : Point | 0 < L x}
  let χ (n : ℕ) (x : Point) := Real.smoothTransition (((n : ℝ)+1)*L x-1)
  have hU : MeasurableSet U := (isOpen_lt continuous_const L.continuous).measurableSet
  have hχ (n : ℕ) : Continuous (χ n) := by
    exact Real.smoothTransition.continuous.comp ((continuous_const.mul L.continuous).sub continuous_const)
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖w x‖)
  · exact Eventually.of_forall fun n => (hχ n).aestronglyMeasurable.smul hw.aestronglyMeasurable
  · exact Eventually.of_forall fun n => Eventually.of_forall fun x => by
      rw [norm_smul,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)
  · exact hw.norm
  · filter_upwards [ae_restrict_mem hU] with x hx
    simpa only [χ,one_smul] using (tendsto_smoothTransition_normal_cutoff_one hx).smul_const (w x)

private theorem tangential_partial_pairing_on_open_side
    {q : ℕ} (L : Point →L[ℝ] ℝ) (k : Fin 3) (hL : L (axis k) = 0)
    {v d : Point → Ambient q} (hv : MemLp v 2 volume) (hd : MemLp d 2 volume)
    (hWeak : IsWeakAmbientCoordinatePartial {x | 0 < L x} k v d)
    {φ : Point → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x in {x | 0 < L x}, coordinateDerivative φ hφ k x • v x) =
      -(∫ x in {x | 0 < L x}, φ x • d x) := by
  let U := {x : Point | 0 < L x}
  let χ (n : ℕ) (x : Point) := Real.smoothTransition (((n : ℝ)+1)*L x-1)
  let ψ (n : ℕ) (x : Point) := χ n x * φ x
  have hχ (n : ℕ) : ContDiff ℝ ∞ (χ n) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul L.contDiff).sub contDiff_const)
  have hψ (n : ℕ) : ContDiff ℝ ∞ (ψ n) := (hχ n).mul hφ
  have hψc (n : ℕ) : HasCompactSupport (ψ n) := hc.mul_left
  have hψU (n : ℕ) : tsupport (ψ n) ⊆ U := by
    have h₁ : (1 : ℝ) ≤ (n : ℝ)+1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hSet : IsClosed {x : Point | (1 : ℝ) ≤ ((n : ℝ)+1)*L x} :=
      isClosed_le continuous_const (continuous_const.mul L.continuous)
    apply (closure_minimal (t := {x : Point | (1 : ℝ) ≤ ((n : ℝ)+1)*L x}) ?_ hSet).trans
    · intro x hx
      change 0 < L x
      have hp : 0 < ((n : ℝ)+1)*L x := zero_lt_one.trans_le hx
      exact pos_of_mul_pos_right hp (zero_le_one.trans h₁)
    · intro x hx
      by_contra hn
      have hZ : χ n x = 0 := Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr (le_of_not_ge hn))
      exact (Function.mem_support.mp hx) (by simp [ψ,hZ])
  have hD (n : ℕ) (x : Point) : coordinateDerivative (ψ n) (hψ n) k x =
      χ n x * coordinateDerivative φ hφ k x := by
    have h := DFunLike.congr_fun
      ((((hχ n).differentiable (by simp) x).hasFDerivAt.mul
        ((hφ.differentiable (by simp) x).hasFDerivAt)).fderiv) (axis k)
    have hZ : fderiv ℝ (χ n) x (axis k) = 0 := smoothTransition_normal_cutoff_column L k hL n x
    change fderiv ℝ (χ n * φ) x (axis k) = χ n x * fderiv ℝ φ x (axis k)
    simpa only [add_apply,smul_apply,hZ,mul_zero,add_zero,smul_eq_mul] using h
  let w (x : Point) := coordinateDerivative φ hφ k x • v x
  let W (x : Point) := φ x • d x
  have hΦ : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hΦD : MemLp (coordinateDerivative φ hφ k) 2 volume :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single k 1))
  have hI : IntegrableOn w U := (memLp_one_iff_integrable.1 (hv.smul (r := 1) hΦD)).integrableOn
  have hJ : IntegrableOn W U := (memLp_one_iff_integrable.1 (hd.smul (r := 1) hΦ)).integrableOn
  have hP (n : ℕ) : (∫ x in U, χ n x • w x) = -(∫ x in U, χ n x • W x) := by
    have h := hWeak (ψ n) (hψ n) (hψc n) (hψU n)
    simpa only [w,W,hD,ψ,smul_smul] using h
  exact tendsto_nhds_unique (tendsto_cutoff_setIntegral L hI)
    ((tendsto_cutoff_setIntegral L hJ).neg.congr (fun n => (hP n).symm))

private theorem integral_eq_flatSideIntegrals
    {q : ℕ} {g : Point → Ambient q} (hg : Integrable g volume) :
    (∫ x, g x) = (∫ x in {x : Point | 0 < x 2}, g x) +
      ∫ x in {x : Point | x 2 < 0}, g x := by
  let P := {x : Point | 0 < x 2}
  let N := {x : Point | x 2 < 0}
  let L : Point →L[ℝ] ℝ := EuclideanSpace.proj 2
  have hP : MeasurableSet P := (isOpen_lt continuous_const L.continuous).measurableSet
  have hN : MeasurableSet N := (isOpen_lt L.continuous continuous_const).measurableSet
  have hDisj : Disjoint P N := disjoint_left.2 fun _ hx hy => (not_lt_of_ge (show (0 : ℝ) ≤ _ from hx.le)) hy
  have hNo : ∀ᵐ x : Point ∂volume, x 2 ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using normal_plane_volume_zero
  have hAE : (P ∪ N).indicator g =ᵐ[volume] g := by
    filter_upwards [hNo] with x hx
    exact indicator_of_mem (lt_or_gt_of_ne hx |>.elim Or.inr Or.inl : x ∈ P ∪ N) g
  calc
    _ = ∫ x in P ∪ N, g x := by
      rw [← integral_indicator (hP.union hN),integral_congr_ae hAE]
    _ = _ := setIntegral_union hDisj hN hg.integrableOn hg.integrableOn

/-- Tangential derivatives on the two sides of a physical flat wall give
the global tangential derivative of the same representatives. -/
theorem IsWeakAmbientCoordinatePartial.of_flat_open_sides
    {q : ℕ} {v d : Point → Ambient q}
    (hv : MemLp v 2 volume) (hd : MemLp d 2 volume) {k : Fin 3} (hk : k ≠ 2)
    (hPlus : IsWeakAmbientCoordinatePartial {x : Point | 0 < x 2} k v d)
    (hMinus : IsWeakAmbientCoordinatePartial {x : Point | x 2 < 0} k v d) :
    IsWeakAmbientCoordinatePartial univ k v d := by
  intro φ hφ hc _
  let L : Point →L[ℝ] ℝ := EuclideanSpace.proj 2
  have hL : L (axis k) = 0 := by
    change (axis k) 2 = 0
    simp [axis,Ne.symm hk]
  have hLm : (-L) (axis k) = 0 := by rw [neg_apply,hL,neg_zero]
  have hMp : IsWeakAmbientCoordinatePartial {x | 0 < (-L) x} k v d := by
    have hEq : {x : Point | 0 < (-L) x} = {x : Point | x 2 < 0} := by
      ext x
      change (0 < -x 2) ↔ x 2 < 0
      exact neg_pos
    rw [hEq]
    exact hMinus
  have hM := tangential_partial_pairing_on_open_side (-L) k hLm hv hd hMp hφ hc
  have hP :
      (∫ x in {x : Point | 0 < x 2}, coordinateDerivative φ hφ k x • v x) =
        -(∫ x in {x : Point | 0 < x 2}, φ x • d x) :=
    tangential_partial_pairing_on_open_side L k hL hv hd hPlus hφ hc
  have hM' :
      (∫ x in {x : Point | x 2 < 0}, coordinateDerivative φ hφ k x • v x) =
        -(∫ x in {x : Point | x 2 < 0}, φ x • d x) := by
    have hEq : {x : Point | 0 < (-L) x} = {x : Point | x 2 < 0} := by
      ext x
      change (0 < -x 2) ↔ x 2 < 0
      exact neg_pos
    simpa only [hEq] using hM
  have hΦ : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hΦD : MemLp (coordinateDerivative φ hφ k) 2 volume :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single k 1))
  have hI : Integrable (fun x => coordinateDerivative φ hφ k x • v x) volume :=
    memLp_one_iff_integrable.1 (hv.smul (r := 1) hΦD)
  have hJ : Integrable (fun x => φ x • d x) volume :=
    memLp_one_iff_integrable.1 (hd.smul (r := 1) hΦ)
  rw [Measure.restrict_univ,integral_eq_flatSideIntegrals hI,integral_eq_flatSideIntegrals hJ,hP,hM']
  exact (neg_add _ _).symm

end Thesis
