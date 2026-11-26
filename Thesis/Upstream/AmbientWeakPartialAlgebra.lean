module

public import Thesis.Upstream.WeakDifferenceQuotientLimit
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Operations on actual ambient weak coordinate derivatives. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff ENNReal

namespace Thesis

private theorem integrable_ambient_test_smul {n q : ℕ} {U : Set (Domain n)}
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U)]
    {φ : Domain n → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {u : Domain n → Ambient q} (hu : MemLp u 2 (volume.restrict U)) :
    Integrable (fun x => φ x • u x) (volume.restrict U) :=
  (hu.integrable (by norm_num)).smul_of_top_right (hφ.memLp_top_of_hasCompactSupport hc _)

theorem IsWeakAmbientCoordinatePartial.add {n q : ℕ} {U : Set (Domain n)}
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U)] {i : Fin n}
    {u v D E : Domain n → Ambient q}
    (hu : IsWeakAmbientCoordinatePartial U i u D) (hv : IsWeakAmbientCoordinatePartial U i v E)
    (huLp : MemLp u 2 (volume.restrict U)) (hvLp : MemLp v 2 (volume.restrict U))
    (hDLp : MemLp D 2 (volume.restrict U)) (hELp : MemLp E 2 (volume.restrict U)) :
    IsWeakAmbientCoordinatePartial U i (u+v) (D+E) := by
  intro φ hφ hc hS
  have hC : Continuous (coordinateDerivative φ hφ i) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hK : HasCompactSupport (coordinateDerivative φ hφ i) :=
    hc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  simp_rw [Pi.add_apply,smul_add]
  rw [integral_add (integrable_ambient_test_smul hC hK huLp) (integrable_ambient_test_smul hC hK hvLp),
    integral_add (integrable_ambient_test_smul hφ.continuous hc hDLp)
      (integrable_ambient_test_smul hφ.continuous hc hELp),
    hu φ hφ hc hS,hv φ hφ hc hS,neg_add_rev,add_comm]

theorem IsWeakAmbientCoordinatePartial.neg {n q : ℕ} {U : Set (Domain n)} {i : Fin n}
    {u D : Domain n → Ambient q} (hu : IsWeakAmbientCoordinatePartial U i u D) :
    IsWeakAmbientCoordinatePartial U i (-u) (-D) := by
  intro φ hφ hc hS
  simp_rw [Pi.neg_apply,smul_neg,integral_neg,hu φ hφ hc hS]

theorem IsWeakAmbientCoordinatePartial.sub {n q : ℕ} {U : Set (Domain n)}
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U)] {i : Fin n}
    {u v D E : Domain n → Ambient q}
    (hu : IsWeakAmbientCoordinatePartial U i u D) (hv : IsWeakAmbientCoordinatePartial U i v E)
    (huLp : MemLp u 2 (volume.restrict U)) (hvLp : MemLp v 2 (volume.restrict U))
    (hDLp : MemLp D 2 (volume.restrict U)) (hELp : MemLp E 2 (volume.restrict U)) :
    IsWeakAmbientCoordinatePartial U i (u-v) (D-E) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg huLp hvLp.neg hDLp hELp.neg

theorem IsWeakAmbientCoordinatePartial.finset_sum {n q : ℕ} {U : Set (Domain n)}
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U)] {i : Fin n} {ι : Type*}
    (s : Finset ι) {u D : ι → Domain n → Ambient q}
    (hu : ∀ j ∈ s, IsWeakAmbientCoordinatePartial U i (u j) (D j))
    (huLp : ∀ j ∈ s, MemLp (u j) 2 (volume.restrict U))
    (hDLp : ∀ j ∈ s, MemLp (D j) 2 (volume.restrict U)) :
    IsWeakAmbientCoordinatePartial U i (fun x => ∑ j ∈ s, u j x) (fun x => ∑ j ∈ s, D j x) := by
  intro φ hφ hc hS
  have hC : Continuous (coordinateDerivative φ hφ i) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hK : HasCompactSupport (coordinateDerivative φ hφ i) :=
    hc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum _ (fun j hj => integrable_ambient_test_smul hC hK (huLp j hj)),
    integral_finsetSum _ (fun j hj => integrable_ambient_test_smul hφ.continuous hc (hDLp j hj)),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun j hj => hu j hj φ hφ hc hS)

theorem IsWeakAmbientCoordinatePartial.congr_ae {n q : ℕ} {U : Set (Domain n)} {i : Fin n}
    {u v D E : Domain n → Ambient q} (h : IsWeakAmbientCoordinatePartial U i u D)
    (hu : u =ᵐ[volume.restrict U] v) (hD : D =ᵐ[volume.restrict U] E) :
    IsWeakAmbientCoordinatePartial U i v E := by
  intro φ hφ hc hS
  rw [← integral_congr_ae (hu.mono fun x hx => congrArg (fun y => coordinateDerivative φ hφ i x • y) hx),
    ← integral_congr_ae (hD.mono fun x hx => congrArg (fun y => φ x • y) hx)]
  exact h φ hφ hc hS

/-- The weak Leibniz rule for one coordinate, with the actual smooth
coefficient and the displayed derivative. -/
theorem IsWeakAmbientCoordinatePartial.smul_smooth {n q : ℕ} {U : Set (Domain n)}
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U)] {i : Fin n}
    {u D : Domain n → Ambient q}
    (hu : IsWeakAmbientCoordinatePartial U i u D)
    (huLp : MemLp u 2 (volume.restrict U)) (hDLp : MemLp D 2 (volume.restrict U))
    {a : Domain n → ℝ} (ha : ContDiff ℝ ∞ a)
    (haTop : MemLp a ∞ (volume.restrict U))
    (hdTop : MemLp (coordinateDerivative a ha i) ∞ (volume.restrict U)) :
    IsWeakAmbientCoordinatePartial U i (fun x => a x • u x)
      (fun x => coordinateDerivative a ha i x • u x + a x • D x) := by
  intro φ hφ hc hS
  let ψ (x : Domain n) := φ x*a x
  have hψ : ContDiff ℝ ∞ ψ := hφ.mul ha
  have hψC : HasCompactSupport ψ := hc.mul_right
  have hψS : tsupport ψ ⊆ U := tsupport_mul_subset_left.trans hS
  have hDer (x : Domain n) : coordinateDerivative ψ hψ i x =
      φ x*coordinateDerivative a ha i x + a x*coordinateDerivative φ hφ i x := by
    unfold coordinateDerivative
    change fderiv ℝ (fun x => φ x*a x) x (EuclideanSpace.single i 1) = _
    rw [fderiv_fun_mul (hφ.differentiable (by simp) x) (ha.differentiable (by simp) x)]
    simp only [add_apply,smul_apply,smul_eq_mul]
  have hAVal : MemLp (fun x => a x • u x) 2 (volume.restrict U) :=
    huLp.smul (r := (2 : ℝ≥0∞)) haTop
  have hDVal : MemLp (fun x => a x • D x) 2 (volume.restrict U) :=
    hDLp.smul (r := (2 : ℝ≥0∞)) haTop
  have hUVal : MemLp (fun x => coordinateDerivative a ha i x • u x) 2 (volume.restrict U) :=
    huLp.smul (r := (2 : ℝ≥0∞)) hdTop
  have hφTop : MemLp φ ∞ (volume.restrict U) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hc _
  have hφDer : MemLp (coordinateDerivative φ hφ i) ∞ (volume.restrict U) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1)) _
  have hI₀ : Integrable (fun x => φ x • (coordinateDerivative a ha i x • u x)) (volume.restrict U) :=
    (hUVal.integrable (by norm_num)).smul_of_top_right hφTop
  have hI₁ : Integrable (fun x => coordinateDerivative φ hφ i x • (a x • u x)) (volume.restrict U) :=
    (hAVal.integrable (by norm_num)).smul_of_top_right hφDer
  have hI₂ : Integrable (fun x => φ x • (a x • D x)) (volume.restrict U) :=
    (hDVal.integrable (by norm_num)).smul_of_top_right hφTop
  have he := hu ψ hψ hψC hψS
  have hTest₁ (x : Domain n) : coordinateDerivative ψ hψ i x • u x =
      φ x • (coordinateDerivative a ha i x • u x) + coordinateDerivative φ hφ i x • (a x • u x) := by
    rw [hDer,add_smul,smul_smul,smul_smul,mul_comm (coordinateDerivative φ hφ i x)]
  have hTest₂ (x : Domain n) : ψ x • D x = φ x • (a x • D x) := by
    rw [smul_smul]
  simp_rw [hTest₁,hTest₂] at he
  rw [integral_add hI₀ hI₁] at he
  simp_rw [smul_add]
  rw [integral_add hI₀ hI₂]
  calc
    _ = ((∫ x in U, φ x • (coordinateDerivative a ha i x • u x)) +
        (∫ x in U, coordinateDerivative φ hφ i x • (a x • u x))) -
          (∫ x in U, φ x • (coordinateDerivative a ha i x • u x)) := by abel
    _ = _ := by rw [he]; abel

private theorem coordinateDerivative_smooth {n : ℕ} {φ : Domain n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (i : Fin n) :
    ContDiff ℝ ∞ (coordinateDerivative φ hφ i) :=
  (hφ.fderiv_right (by simp)).clm_apply contDiff_const

private theorem mixed_scalarCoordinateDerivative_comm {n : ℕ} {φ : Domain n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (i j : Fin n) (x : Domain n) :
    coordinateDerivative (coordinateDerivative φ hφ j) (coordinateDerivative_smooth hφ j) i x =
      coordinateDerivative (coordinateDerivative φ hφ i) (coordinateDerivative_smooth hφ i) j x := by
  have hφ2 : ContDiffAt ℝ 2 φ x :=
    (hφ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hd := (hφ2.fderiv_right_succ (n := 1)).differentiableAt one_ne_zero
  have h (k : Fin n) :
      fderiv ℝ (coordinateDerivative φ hφ k) x =
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k 1)).comp (fderiv ℝ (fderiv ℝ φ) x) := by
    change fderiv ℝ ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k 1)) ∘ fderiv ℝ φ) x = _
    exact ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k 1)).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  change fderiv ℝ (coordinateDerivative φ hφ j) x (EuclideanSpace.single i 1) =
    fderiv ℝ (coordinateDerivative φ hφ i) x (EuclideanSpace.single j 1)
  rw [h i,h j]
  exact hφ2.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- Mixed weak derivatives of the original map agree as distributions. -/
theorem IsWeakAmbientCoordinatePartial.mixed {n q : ℕ} {U : OpenDomain n}
    {u E : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hu : HasWeakGradient U u D) {i j : Fin n}
    (h : IsWeakAmbientCoordinatePartial U.val i (fun x => D x j) E) :
    IsWeakAmbientCoordinatePartial U.val j (fun x => D x i) E := by
  intro φ hφ hc hS
  let ψ (k : Fin n) := coordinateDerivative φ hφ k
  have hψS (k : Fin n) : ContDiff ℝ ∞ (ψ k) := coordinateDerivative_smooth hφ k
  have hψC (k : Fin n) : HasCompactSupport (ψ k) := hc.fderiv_apply ℝ (EuclideanSpace.single k 1)
  have hψU (k : Fin n) : tsupport (ψ k) ⊆ U.val :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single k 1)).trans hS
  have h1 := hu.2.2 i (ψ j) (hψS j) (hψC j) (hψU j)
  have h2 := hu.2.2 j (ψ i) (hψS i) (hψC i) (hψU i)
  have he (x : Domain n) : coordinateDerivative (ψ j) (hψS j) i x =
      coordinateDerivative (ψ i) (hψS i) j x := mixed_scalarCoordinateDerivative_comm hφ i j x
  simp_rw [he] at h1
  exact (neg_injective (h1.symm.trans h2)).trans (h φ hφ hc hS)

end Thesis
