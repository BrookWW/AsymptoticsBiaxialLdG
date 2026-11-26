module

public import Thesis.Variational.SecondDerivativeCalculus

/-! The actual scalar principal and drift coefficients of a pulled back Laplacian. -/

@[expose] public section

noncomputable section

open Function Set
open scoped ContDiff

namespace Thesis

def chartInverseDerivativeEntry (E : Point ≃ₜ Point) (i m : Fin 3) (z : Point) : ℝ :=
  (fderiv ℝ E.symm (E z) (axis m)) i

/-- The inverse chart derivative contracted in the physical orthonormal frame. -/
def chartPoissonPrincipal (E : Point ≃ₜ Point) (i j : Fin 3) (z : Point) : ℝ :=
  ∑ m : Fin 3, chartInverseDerivativeEntry E i m z * chartInverseDerivativeEntry E j m z

/-- The physical Laplacian of the inverse chart, in each flattened coordinate. -/
def chartPoissonDrift (E : Point ≃ₜ Point) (i : Fin 3) (z : Point) : ℝ :=
  ∑ m : Fin 3, (iteratedFDeriv ℝ 2 E.symm (E z) ![axis m,axis m]) i

private theorem sum_coordinate_smul_axis (v : Point) : (∑ i : Fin 3, v i • axis i) = v := by
  simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,axis] using
    (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v

private theorem continuousLinearMap_apply_eq_sum_coordinate
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Point →L[ℝ] F) (v : Point) :
    L v = ∑ i : Fin 3, v i • L (axis i) := by
  calc
    _ = L (∑ i : Fin 3, v i • axis i) := congrArg L (sum_coordinate_smul_axis v).symm
    _ = _ := by simp only [map_sum,map_smul]

private theorem iteratedFDeriv_two_apply_eq_coordinate_sum
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Point → F) (x v w : Point) :
    iteratedFDeriv ℝ 2 f x ![v,w] = ∑ i : Fin 3, ∑ j : Fin 3,
      (v i * w j) • iteratedFDeriv ℝ 2 f x ![axis i,axis j] := by
  let T := fderiv ℝ (fderiv ℝ f) x
  simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  change T v w = ∑ i : Fin 3, ∑ j : Fin 3, (v i * w j) • T (axis i) (axis j)
  calc
    _ = ∑ i : Fin 3, v i • T (axis i) w := by
      rw [continuousLinearMap_apply_eq_sum_coordinate T v]
      simp only [sum_apply,smul_apply]
    _ = _ := by
      simp_rw [continuousLinearMap_apply_eq_sum_coordinate (T (axis _)) w,Finset.smul_sum,smul_smul]

theorem chartPoissonPrincipal_contDiff (E : Point ≃ₜ Point) (k : ℕ)
    (hE : ContDiff ℝ (↑(k+2) : ℕ∞ω) (E : Point → Point))
    (hI : ContDiff ℝ (↑(k+2) : ℕ∞ω) (E.symm : Point → Point)) (i j : Fin 3) :
    ContDiff ℝ (k : ℕ∞ω) (chartPoissonPrincipal E i j) := by
  have hk : (k : ℕ∞ω) ≤ (↑(k+2) : ℕ∞ω) := by exact_mod_cast (show k ≤ k+2 by omega)
  have hK : (k : ℕ∞ω) + 1 ≤ (↑(k+2) : ℕ∞ω) := by exact_mod_cast (show k+1 ≤ k+2 by omega)
  have hD : ContDiff ℝ (k : ℕ∞ω) (fun z => fderiv ℝ E.symm (E z)) :=
    (hI.fderiv_right hK).comp (hE.of_le hk)
  have hEntry (r m : Fin 3) : ContDiff ℝ (k : ℕ∞ω) (chartInverseDerivativeEntry E r m) := by
    let L : Point →L[ℝ] ℝ := EuclideanSpace.proj r
    have h := L.contDiff.comp (hD.clm_apply (contDiff_const (c := axis m)))
    exact h
  exact ContDiff.sum fun m _ => (hEntry i m).mul (hEntry j m)

theorem chartPoissonDrift_contDiff (E : Point ≃ₜ Point) (k : ℕ)
    (hE : ContDiff ℝ (↑(k+2) : ℕ∞ω) (E : Point → Point))
    (hI : ContDiff ℝ (↑(k+2) : ℕ∞ω) (E.symm : Point → Point)) (i : Fin 3) :
    ContDiff ℝ (k : ℕ∞ω) (chartPoissonDrift E i) := by
  have hk : (k : ℕ∞ω) ≤ (↑(k+2) : ℕ∞ω) := by exact_mod_cast (show k ≤ k+2 by omega)
  have hK : (k : ℕ∞ω) + (2 : ℕ) ≤ (↑(k+2) : ℕ∞ω) := by exact_mod_cast (Nat.le_refl (k+2))
  have hD : ContDiff ℝ (k : ℕ∞ω) (fun z => iteratedFDeriv ℝ 2 E.symm (E z)) :=
    (hI.iteratedFDeriv_right (i := 2) hK).comp (hE.of_le hk)
  apply ContDiff.sum
  intro m _
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Point) Point ![axis m,axis m]
  exact (EuclideanSpace.proj i).contDiff.comp (L.contDiff.comp hD)

/-- Every diagonal entry of the pulled back principal matrix is strictly positive. -/
theorem chartPoissonPrincipal_diagonal_pos (E : Point ≃ₜ Point)
    (hE : Differentiable ℝ (E : Point → Point)) (hI : Differentiable ℝ (E.symm : Point → Point))
    (i : Fin 3) (z : Point) : 0 < chartPoissonPrincipal E i i z := by
  let L : Point →L[ℝ] ℝ := (EuclideanSpace.proj i).comp (fderiv ℝ E.symm (E z))
  have hInv : (fderiv ℝ E.symm (E z)).comp (fderiv ℝ E z) = ContinuousLinearMap.id ℝ Point := by
    have hC := (hI (E z)).hasFDerivAt.comp z (hE z).hasFDerivAt
    rw [show (E.symm : Point → Point) ∘ E = id from funext E.symm_apply_apply] at hC
    exact hC.fderiv.symm.trans (fderiv_id)
  obtain ⟨m,hm⟩ : ∃ m : Fin 3, L (axis m) ≠ 0 := by
    by_contra! hh
    have hZero (v : Point) : L v = 0 := by
      rw [continuousLinearMap_apply_eq_sum_coordinate]
      simp only [hh,smul_zero,Finset.sum_const_zero]
    have hC := DFunLike.congr_fun hInv (axis i)
    have hc : L (fderiv ℝ E z (axis i)) = 1 := by
      change ((fderiv ℝ E.symm (E z)) ((fderiv ℝ E z) (axis i))) i = 1
      rw [show (fderiv ℝ E.symm (E z)) ((fderiv ℝ E z) (axis i)) = axis i from hC]
      simp [axis]
    rw [hZero] at hc
    exact zero_ne_one hc
  change 0 < ∑ m : Fin 3, L (axis m) * L (axis m)
  exact (mul_self_pos.mpr hm).trans_le (Finset.single_le_sum
    (f := fun m => L (axis m) * L (axis m)) (fun _ _ => mul_self_nonneg _) (Finset.mem_univ m))

/-- The strong equation in chart coordinates is the actual pullback of the
physical Laplacian, with the literal derivative matrix and drift above. -/
theorem laplacian_flattened_eq_chartPoisson (E : Point ≃ₜ Point)
    (hE : ContDiff ℝ 2 (E : Point → Point)) (hI : ContDiff ℝ 2 (E.symm : Point → Point))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : Point → F} {z : Point} (hu : ContDiffAt ℝ 2 u (E z)) :
    let v := u ∘ E
    laplacian u (E z) =
      (∑ i : Fin 3, ∑ j : Fin 3, chartPoissonPrincipal E i j z • coordDeriv i (coordDeriv j v) z) +
        ∑ i : Fin 3, chartPoissonDrift E i z • coordDeriv i v z := by
  let v : Point → F := u ∘ E
  let x := E z
  let J := fderiv ℝ E.symm x
  let P := iteratedFDeriv ℝ 2 E.symm x
  have hInv : E.symm x = z := E.symm_apply_apply z
  have hv : ContDiffAt ℝ 2 v z := hu.comp z hE.contDiffAt
  have hv' : ContDiffAt ℝ 2 v (E.symm x) := hInv ▸ hv
  have hFun : v ∘ E.symm = u := funext fun y => congrArg u (E.apply_symm_apply y)
  have hChain (w : Point) :
      iteratedFDeriv ℝ 2 u x ![w,w] =
        iteratedFDeriv ℝ 2 v z ![J w,J w] + fderiv ℝ v z (P ![w,w]) := by
    have h := iteratedFDeriv_two_comp_apply_of_contDiffAt hv' hI.contDiffAt w w
    rwa [hFun,hInv] at h
  have hTrace := laplacian_eq_second_derivative_basis_of_contDiffAt hu (EuclideanSpace.basisFun (Fin 3) ℝ)
  simp only [EuclideanSpace.basisFun_apply] at hTrace
  change laplacian u x = ∑ m : Fin 3, iteratedFDeriv ℝ 2 u x ![axis m,axis m] at hTrace
  change laplacian u x =
    (∑ i : Fin 3, ∑ j : Fin 3, chartPoissonPrincipal E i j z • coordDeriv i (coordDeriv j v) z) +
      ∑ i : Fin 3, chartPoissonDrift E i z • coordDeriv i v z
  rw [hTrace]
  simp_rw [hChain,Finset.sum_add_distrib]
  congr 1
  · simp_rw [iteratedFDeriv_two_apply_eq_coordinate_sum v z (J _) (J _)]
    have hD (i j : Fin 3) : iteratedFDeriv ℝ 2 v z ![axis i,axis j] =
        coordDeriv i (coordDeriv j v) z :=
      (fderiv_fderiv_column_eq_iteratedFDeriv_two hv (axis i) (axis j)).symm
    simp_rw [hD]
    calc
      _ = ∑ i : Fin 3, ∑ m : Fin 3, ∑ j : Fin 3,
          ((J (axis m)) i * (J (axis m)) j) • coordDeriv i (coordDeriv j v) z := Finset.sum_comm
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ m : Fin 3,
          ((J (axis m)) i * (J (axis m)) j) • coordDeriv i (coordDeriv j v) z :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := by simp only [chartPoissonPrincipal,chartInverseDerivativeEntry,Finset.sum_smul]; rfl
  · have hD (m : Fin 3) : fderiv ℝ v z (P ![axis m,axis m]) =
        ∑ i : Fin 3, (P ![axis m,axis m]) i • coordDeriv i v z :=
      continuousLinearMap_apply_eq_sum_coordinate (fderiv ℝ v z) _
    simp_rw [hD]
    rw [Finset.sum_comm]
    simp only [chartPoissonDrift,Finset.sum_smul]
    rfl

end Thesis
