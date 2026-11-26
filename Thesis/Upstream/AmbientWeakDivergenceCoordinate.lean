module

public import Thesis.Upstream.AmbientMetricWeakEquation
public import Thesis.Upstream.AmbientWeakPartialAlgebra

/-! Recover the remaining coordinate derivative from the actual weak divergence. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff ENNReal RealInnerProductSpace

namespace Thesis

theorem scalar_test_identity_of_packed_divergence {n q : ℕ}
    {U : Set (Domain n)} [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U)]
    {P : Domain n → HarmonicMaps.Gradient n q} {f : Domain n → Ambient q}
    (h : HasWeakPackedDivergenceEq U (fun x => packAmbientGradient (P x)) f)
    (hP : ∀ j, MemLp (fun x => P x j) 2 (volume.restrict U))
    (hf : MemLp f 2 (volume.restrict U))
    {φ : Domain n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hU : tsupport φ ⊆ U) :
    (∑ j : Fin n, ∫ x in U, coordinateDerivative φ hφ j x • P x j) =
      -(∫ x in U, φ x • f x) := by
  apply ext_inner_left ℝ
  intro w
  let ψ (x : Domain n) := φ x • w
  have hψ : ContDiff ℝ ∞ ψ := hφ.smul contDiff_const
  have hψS : tsupport ψ ⊆ tsupport φ := tsupport_smul_subset_left φ (fun _ : Domain n => w)
  have hψC : HasCompactSupport ψ := hc.of_isClosed_subset (isClosed_tsupport ψ) hψS
  have hψU : tsupport ψ ⊆ U := hψS.trans hU
  have hDψ (x : Domain n) (j : Fin n) :
      fderiv ℝ ψ x (EuclideanSpace.single j 1) = coordinateDerivative φ hφ j x • w :=
    DFunLike.congr_fun (((hφ.differentiable (by simp) x).hasFDerivAt.smul_const w).fderiv)
      (EuclideanSpace.single j 1)
  have hL (x : Domain n) :
      inner ℝ (packAmbientGradient (P x)) (packedClassicalAmbientGradient ψ x) =
        ∑ j : Fin n, inner ℝ w (coordinateDerivative φ hφ j x • P x j) := by
    rw [packedClassicalAmbientGradient,PiLp.inner_apply]
    simp only [packAmbientGradient_apply,hDψ,real_inner_smul_right]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm (P x j) w]
  have hR (x : Domain n) : inner ℝ (f x) (ψ x) = inner ℝ w (φ x • f x) := by
    dsimp only [ψ]
    rw [real_inner_smul_right,real_inner_smul_right,real_inner_comm (f x) w]
  have hφTop : MemLp φ ∞ (volume.restrict U) := hφ.continuous.memLp_top_of_hasCompactSupport hc _
  have hDLp (j : Fin n) :
      MemLp (coordinateDerivative φ hφ j) ∞ (volume.restrict U) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single j 1)) _
  have hIntL (j : Fin n) :=
    ((hP j).integrable (by norm_num)).smul_of_top_right (hDLp j)
  have hIntR : Integrable (fun x => φ x • f x) (volume.restrict U) :=
    (hf.integrable (by norm_num)).smul_of_top_right hφTop
  have hLG :
      (∫ x in U, ∑ j : Fin n, inner ℝ w (coordinateDerivative φ hφ j x • P x j)) =
         ∫ x, ∑ j : Fin n, inner ℝ w (coordinateDerivative φ hφ j x • P x j) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply Finset.sum_eq_zero
    intro j _
    have h0 : coordinateDerivative φ hφ j x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := coordinateDerivative φ hφ j)
        (fun he => hx (hU ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1)) he)))
    rw [h0,zero_smul,inner_zero_right]
  have hRG : (∫ x in U, inner ℝ w (φ x • f x)) = ∫ x, inner ℝ w (φ x • f x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun he => hx (hU he))
    rw [h0,zero_smul,inner_zero_right]
  have he := h ψ hψ hψC hψU
  simp_rw [hL,hR] at he
  have hIntL' (j : Fin n) : Integrable
      (fun x => coordinateDerivative φ hφ j x • P x j) (volume.restrict U) := hIntL j
  rw [← hLG,← hRG,integral_finsetSum _ (fun j _ => (hIntL j).const_inner w),
    integral_inner (𝕜 := ℝ) hIntR w,← inner_neg_right] at he
  simpa only [integral_inner (𝕜 := ℝ) (hIntL' _) w,inner_sum] using he

/-- The divergence identity determines the remaining weak coordinate
derivative of the flux once the other diagonal derivatives are known. -/
theorem HasWeakPackedDivergenceEq.remaining_coordinate_partial {n q : ℕ}
    {U : Set (Domain n)} [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U)]
    {P : Domain n → HarmonicMaps.Gradient n q} {f : Domain n → Ambient q}
    (h : HasWeakPackedDivergenceEq U (fun x => packAmbientGradient (P x)) f)
    (hP : ∀ j, MemLp (fun x => P x j) 2 (volume.restrict U))
    (hf : MemLp f 2 (volume.restrict U))
    (i : Fin n) {D : Fin n → Domain n → Ambient q}
    (hD : ∀ j ≠ i, IsWeakAmbientCoordinatePartial U j (fun x => P x j) (D j))
    (hDLp : ∀ j ≠ i, MemLp (D j) 2 (volume.restrict U)) :
    IsWeakAmbientCoordinatePartial U i (fun x => P x i)
      (fun x => f x - ∑ j ∈ Finset.univ.erase i, D j x) := by
  intro φ hφ hc hU
  let J := (Finset.univ : Finset (Fin n)).erase i
  have hNe (j : Fin n) (hj : j ∈ J) : j ≠ i := (Finset.mem_erase.mp hj).1
  have hφTop : MemLp φ ∞ (volume.restrict U) := hφ.continuous.memLp_top_of_hasCompactSupport hc _
  have hFInt : Integrable (fun x => φ x • f x) (volume.restrict U) :=
    (hf.integrable (by norm_num)).smul_of_top_right hφTop
  have hDInt (j : Fin n) (hj : j ∈ J) : Integrable (fun x => φ x • D j x) (volume.restrict U) :=
    ((hDLp j (hNe j hj)).integrable (by norm_num)).smul_of_top_right hφTop
  have hEq := scalar_test_identity_of_packed_divergence h hP hf hφ hc hU
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hEq
  have hPart : (∑ j ∈ J, ∫ x in U, coordinateDerivative φ hφ j x • P x j) =
      -(∑ j ∈ J, ∫ x in U, φ x • D j x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j hj => hD j (hNe j hj) φ hφ hc hU)
  rw [hPart] at hEq
  have hSumInt : Integrable (fun x => ∑ j ∈ J, φ x • D j x) (volume.restrict U) :=
    integrable_finsetSum _ hDInt
  simp_rw [smul_sub,Finset.smul_sum]
  change (∫ x in U, coordinateDerivative φ hφ i x • P x i) =
    -(∫ x in U, φ x • f x - ∑ j ∈ J, φ x • D j x)
  rw [integral_sub hFInt hSumInt,integral_finsetSum _ hDInt]
  calc
    _ = ((∫ x in U, coordinateDerivative φ hφ i x • P x i) +
        -(∑ j ∈ J, ∫ x in U, φ x • D j x)) +
          (∑ j ∈ J, ∫ x in U, φ x • D j x) := by abel
    _ = _ := by rw [hEq]; abel

end Thesis
