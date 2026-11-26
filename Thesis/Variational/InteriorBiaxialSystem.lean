module

public import Thesis.Variational.InteriorMixedEstimate

/-! The exact differentiated interior system for the tensor and the two
scaled scalar defects in the biaxial equation. -/

public section

open Filter Metric Set Topology
open scoped ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Thesis

abbrev ScalarDefectPair := Fin 2 → ℝ

@[expose] def scalarDefectPair (a : BulkCoefficients) (ε : ElasticScale) (A : S0) : ScalarDefectPair :=
  ![scaledNormDefect a ε A, scaledCubicTrace a ε A]

@[expose] def scalarDefectMass (a : BulkCoefficients) : ScalarDefectPair :=
  ![bulkRadialMass a, bulkBiaxialMass a]

@[expose] def biaxialTensorForce (a : BulkCoefficients) (z : ℝ × S0 × ScalarDefectPair) : S0 :=
  (bulkRadialCoefficient a * z.2.2 0 + a.a6 * z.1 * (z.2.2 0) ^ 2) • z.2.1 +
    (a.a6' * z.2.2 1) • traceFreeSquare z.2.1

@[expose] def biaxialGradientSource (z : S0 × Gradient) : ScalarDefectPair :=
  ![-2 * gradientNormSq z.2, -6 * ∑ j : Fin 3, ((z.2 j : Tensor) * (z.2 j : Tensor) * (z.1 : Tensor)).trace]

@[expose] def biaxialDefectCorrection (a : BulkCoefficients) (z : ℝ × ScalarDefectPair) : ScalarDefectPair :=
  ![-((2 * bulkRadialCoefficient a + 4 * a.a6 * vacuumRadius a ^ 2) * (z.2 0) ^ 2 +
      2 * a.a6 * z.1 * (z.2 0) ^ 3 + 2 * a.a6' * (z.2 1) ^ 2),
    -((3 * bulkRadialCoefficient a + 2 * a.a6' * vacuumRadius a ^ 2) * (z.2 0) * (z.2 1) +
      z.1 * (3 * a.a6 + a.a6' / 2) * (z.2 0) ^ 2 * (z.2 1))]

theorem contDiff_scalarDefectPair (a : BulkCoefficients) (ε : ElasticScale) :
    ContDiff ℝ ∞ (scalarDefectPair a ε) := by
  rw [contDiff_pi]
  intro j
  fin_cases j
  · change ContDiff ℝ ∞ (scaledNormDefect a ε)
    have hT : ContDiff ℝ ∞ (fun A : S0 => ((A : Tensor) ^ 2).trace - 2 * vacuumRadius a ^ 2) :=
      contDiff_vacuumInvariants.fst.sub contDiff_const
    exact contDiff_const.mul hT
  · change ContDiff ℝ ∞ (scaledCubicTrace a ε)
    have hEq : scaledCubicTrace a ε = fun A : S0 => (ε.val ^ 2)⁻¹ * ((A : Tensor) ^ 3).trace :=
      funext (scaledCubicTrace_eq a ε)
    rw [hEq]
    exact contDiff_const.mul contDiff_vacuumInvariants.snd

theorem contDiff_biaxialTensorForce (a : BulkCoefficients) : ContDiff ℝ ∞ (biaxialTensorForce a) := by
  have hz (j : Fin 2) : ContDiff ℝ ∞ (fun z : ℝ × S0 × ScalarDefectPair => z.2.2 j) := by
    let L : ScalarDefectPair →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) j
    have hg : ContDiff ℝ ∞ (fun z : ℝ × S0 × ScalarDefectPair => z.2.2) := contDiff_snd.snd
    exact L.contDiff.comp hg
  have hq : ContDiff ℝ ∞ (fun z : ℝ × S0 × ScalarDefectPair => z.2.1) := contDiff_snd.fst
  unfold biaxialTensorForce
  have h₀ : ContDiff ℝ ∞ (fun z : ℝ × S0 × ScalarDefectPair =>
      bulkRadialCoefficient a * z.2.2 0 + a.a6 * z.1 * (z.2.2 0) ^ 2) :=
    (contDiff_const.mul (hz 0)).add ((contDiff_const.mul contDiff_fst).mul ((hz 0).pow 2))
  exact (h₀.smul hq).add ((contDiff_const.mul (hz 1)).smul (contDiff_traceFreeSquare.comp hq))

theorem contDiff_biaxialGradientSource : ContDiff ℝ ∞ biaxialGradientSource := by
  have hp (j : Fin 3) : ContDiff ℝ ∞ (fun z : S0 × Gradient => z.2 j) := by
    let L : Gradient →L[ℝ] S0 := ContinuousLinearMap.proj (R := ℝ) j
    exact L.contDiff.comp (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : S0 × Gradient → Gradient))
  let e := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  rw [contDiff_pi]
  intro j
  fin_cases j
  · change ContDiff ℝ ∞ (fun z : S0 × Gradient => -2 * gradientNormSq z.2)
    have hNorm (z : S0 × Gradient) :
        gradientNormSq z.2 = ∑ i : Fin 3, inner ℝ (e (z.2 i)) (e (z.2 i)) := by
      rw [gradientNormSq_eq_sum_norm_sq]
      simp only [real_inner_self_eq_norm_sq, e, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map]
    simp_rw [hNorm]
    exact contDiff_const.mul (ContDiff.sum fun i _ => (e.contDiff.comp (hp i)).inner ℝ (e.contDiff.comp (hp i)))
  · change ContDiff ℝ ∞ (fun z : S0 × Gradient =>
      -6 * ∑ j : Fin 3, ((z.2 j : Tensor) * (z.2 j : Tensor) * (z.1 : Tensor)).trace)
    refine contDiff_const.mul (ContDiff.sum fun i _ => ?_)
    have hg := symmetricTraceless.subtypeL.contDiff.comp (hp i)
    have hq := symmetricTraceless.subtypeL.contDiff.comp (contDiff_fst :
      ContDiff ℝ ∞ (Prod.fst : S0 × Gradient → S0))
    exact tensorTraceCLM.contDiff.comp ((hg.mul hg).mul hq)

theorem contDiff_biaxialDefectCorrection (a : BulkCoefficients) :
    ContDiff ℝ ∞ (biaxialDefectCorrection a) := by
  have hz (j : Fin 2) : ContDiff ℝ ∞ (fun z : ℝ × ScalarDefectPair => z.2 j) := by
    let L : ScalarDefectPair →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) j
    exact L.contDiff.comp (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ScalarDefectPair → ScalarDefectPair))
  rw [contDiff_pi]
  intro j
  fin_cases j
  · change ContDiff ℝ ∞ (fun z : ℝ × ScalarDefectPair =>
      -((2 * bulkRadialCoefficient a + 4 * a.a6 * vacuumRadius a ^ 2) * (z.2 0) ^ 2 +
        2 * a.a6 * z.1 * (z.2 0) ^ 3 + 2 * a.a6' * (z.2 1) ^ 2))
    exact (((contDiff_const.mul ((hz 0).pow 2)).add ((contDiff_const.mul contDiff_fst).mul ((hz 0).pow 3)))
      |>.add (contDiff_const.mul ((hz 1).pow 2))).neg
  · change ContDiff ℝ ∞ (fun z : ℝ × ScalarDefectPair =>
      -((3 * bulkRadialCoefficient a + 2 * a.a6' * vacuumRadius a ^ 2) * z.2 0 * z.2 1 +
        z.1 * (3 * a.a6 + a.a6' / 2) * (z.2 0) ^ 2 * z.2 1))
    exact (((contDiff_const.mul (hz 0)).mul (hz 1)).add
      (((contDiff_fst.mul contDiff_const).mul ((hz 0).pow 2)).mul (hz 1))).neg

theorem scalarDefectMass_lower (a : BulkCoefficients) (j : Fin 2) :
    min (bulkRadialMass a) (bulkBiaxialMass a) ≤ scalarDefectMass a j := by
  fin_cases j
  · exact min_le_left _ _
  · exact min_le_right _ _

/-- The classical Euler equation gives both scalar screened equations with
their material masses and the same actual fields in the tensor equation. -/
theorem classical_biaxial_poisson_screened_system (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ 2 Q Ω)
    {x : Point} (hx : x ∈ Ω)
    (hEuler : (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x)) :
    let β := (ε : ℝ) ^ 2
    let w := scalarDefectPair a ε ∘ Q
    laplacian Q x = biaxialTensorForce a (β, Q x, w x) ∧
      ∀ j : Fin 2,
        -β * laplacian (fun y => w y j) x + scalarDefectMass a j * w x j =
          biaxialGradientSource (Q x, ClassicalGradient Q x) j +
            β * biaxialDefectCorrection a (β, w x) j := by
  refine ⟨?_, ?_⟩
  · apply Subtype.ext
    exact laplacian_eq_scaledDefects a ε Q x hEuler
  · intro j
    fin_cases j
    · have hEq := scaledNormDefect_equation a ε hΩ hQ hx hEuler
      let h := scaledNormDefect a ε (Q x)
      let t := scaledCubicTrace a ε (Q x)
      change -(ε : ℝ) ^ 2 * laplacian (fun y => scaledNormDefect a ε (Q y)) x +
        bulkRadialMass a * h = -2 * gradientNormSq (ClassicalGradient Q x) +
          (ε : ℝ) ^ 2 * (-((2 * bulkRadialCoefficient a + 4 * a.a6 * vacuumRadius a ^ 2) * h ^ 2 +
            2 * a.a6 * (ε : ℝ) ^ 2 * h ^ 3 + 2 * a.a6' * t ^ 2))
      linear_combination -hEq
    · have hEq := scaledCubicTrace_equation a ε hΩ hQ hx hEuler
      let h := scaledNormDefect a ε (Q x)
      let t := scaledCubicTrace a ε (Q x)
      change -(ε : ℝ) ^ 2 * laplacian (fun y => scaledCubicTrace a ε (Q y)) x +
        bulkBiaxialMass a * t = -6 * gradientTraceMul (ClassicalGradient Q) (ClassicalGradient Q) (Q x : Tensor) x +
          (ε : ℝ) ^ 2 * (-((3 * bulkRadialCoefficient a + 2 * a.a6' * vacuumRadius a ^ 2) * h * t +
            (ε : ℝ) ^ 2 * (3 * a.a6 + a.a6' / 2) * h ^ 2 * t))
      linear_combination -hEq

end Thesis

end
