module

public import Thesis.Upstream.AmbientSobolevDifferenceQuotient
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The genuine finite Hilbert product of the displayed gradient columns. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory
open scoped BigOperators ENNReal RealInnerProductSpace

namespace Thesis

abbrev AmbientGradientHilbert (n q : ℕ) := PiLp 2 (fun _ : Fin n => Ambient q)

/-- Group the displayed columns in the Euclidean Hilbert product. -/
@[expose] def packAmbientGradient {n q : ℕ} (D : HarmonicMaps.Gradient n q) :
    AmbientGradientHilbert n q :=
  WithLp.toLp 2 D

@[simp] theorem packAmbientGradient_apply {n q : ℕ} (D : HarmonicMaps.Gradient n q) (i : Fin n) :
    packAmbientGradient D i = D i := rfl

theorem norm_packAmbientGradient_sq {n q : ℕ} (D : HarmonicMaps.Gradient n q) :
    ‖packAmbientGradient D‖ ^ 2 = hsNormSq D := by
  rw [PiLp.norm_sq_eq_of_L2,hsNormSq]
  simp only [packAmbientGradient_apply]

theorem packAmbientGradient_add {n q : ℕ} (D E : HarmonicMaps.Gradient n q) :
    packAmbientGradient (D + E) = packAmbientGradient D + packAmbientGradient E := rfl

theorem packAmbientGradient_sub {n q : ℕ} (D E : HarmonicMaps.Gradient n q) :
    packAmbientGradient (D - E) = packAmbientGradient D - packAmbientGradient E := rfl

theorem packAmbientGradient_smul {n q : ℕ} (c : ℝ) (D : HarmonicMaps.Gradient n q) :
    packAmbientGradient (c • D) = c • packAmbientGradient D := rfl

theorem memLp_packAmbientGradient {n q : ℕ} {μ : Measure (Domain n)}
    {D : Domain n → HarmonicMaps.Gradient n q}
    (hD : ∀ j, MemLp (fun x => D x j) 2 μ) :
    MemLp (fun x => packAmbientGradient (D x)) 2 μ := by
  have hs : AEStronglyMeasurable D μ :=
    (aemeasurable_pi_lambda _ (fun j => (hD j).1.aemeasurable)).aestronglyMeasurable
  have ht : AEStronglyMeasurable (fun x => packAmbientGradient (D x)) μ :=
    (PiLp.continuous_toLp 2 (fun _ : Fin n => Ambient q)).comp_aestronglyMeasurable hs
  exact (memLp_two_iff_integrable_sq_norm ht).mpr (by
    simp only [norm_packAmbientGradient_sq]
    exact integrable_hsNormSq_of_memLp_columns hD)

theorem memLp_of_packAmbientGradient {n q : ℕ} {μ : Measure (Domain n)}
    {D : Domain n → HarmonicMaps.Gradient n q}
    (hD : MemLp (fun x => packAmbientGradient (D x)) 2 μ) (i : Fin n) :
    MemLp (fun x => D x i) 2 μ := by
  have hMeas : AEStronglyMeasurable (fun x => D x i) μ :=
    (PiLp.continuous_apply 2 (fun _ : Fin n => Ambient q) i).comp_aestronglyMeasurable hD.1
  exact hD.of_le hMeas (Eventually.of_forall fun x => PiLp.norm_apply_le (packAmbientGradient (D x)) i)

theorem packAmbientGradient_differenceQuotient {n q : ℕ}
    (D : Domain n → HarmonicMaps.Gradient n q) (i : Fin n) (h : ℝ) (x : Domain n) :
    packAmbientGradient (fun j => ambientDifferenceQuotient i h (fun y => D y j) x) =
      ambientDifferenceQuotient i h (fun y => packAmbientGradient (D y)) x := by
  simp only [ambientDifferenceQuotient]
  exact (packAmbientGradient_smul _ _).trans
    (congrArg (fun y : AmbientGradientHilbert n q => h⁻¹ • y) (packAmbientGradient_sub _ _))

/-- The discrete product rule with the coefficient evaluated at the translated point. -/
theorem ambientDifferenceQuotient_operator_apply {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Domain n → E →L[ℝ] F) (D : Domain n → E) (i : Fin n) (h : ℝ) (x : Domain n) :
    ambientDifferenceQuotient i h (fun y => A y (D y)) x =
      A (x+h • EuclideanSpace.single i 1) (ambientDifferenceQuotient i h D x) +
        (ambientDifferenceQuotient i h A x) (D x) := by
  simp only [ambientDifferenceQuotient,map_smul,map_sub,smul_apply,sub_apply,smul_sub]
  abel

/-- The product of an actual (L^2) field and an essentially bounded
measurable operator field is (L^2). -/
theorem memLp_apply_of_ae_opNorm_le {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure X} {A : X → E →L[ℝ] F} {v : X → E}
    (hA : AEStronglyMeasurable A μ) (hv : MemLp v 2 μ) (C : ℝ)
    (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) : MemLp (fun x => A x (v x)) 2 μ := by
  have hMeas : AEStronglyMeasurable (fun x => A x (v x)) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hA.prodMk hv.1)
  apply (hv.norm.const_mul C).mono' hMeas
  filter_upwards [hC] with x hx
  exact ((A x).le_opNorm (v x)).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

end Thesis
