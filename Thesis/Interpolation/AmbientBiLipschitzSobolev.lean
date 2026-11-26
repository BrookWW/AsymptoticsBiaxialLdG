module

public import Thesis.Interpolation.CylinderCapFill
public import Thesis.Interpolation.LipschitzSobolevPullback

/-! The native ambient Sobolev transport used by the terminal cylinder. -/

public section

noncomputable section

open HarmonicMaps MeasureTheory Set
open scoped ENNReal NNReal

namespace Thesis

/-- The three-dimensional transport uses the actual weak columns and the
volume distortion of the inverse homeomorphism. -/
theorem ambientBiLipschitzSobolevPullback3 : External.AmbientBiLipschitzSobolevPullback3 := by
  refine ⟨9600000, by norm_num, ?_⟩
  intro F hF hInv U u D hu
  let G (x : Point) (i : Fin 3) := ∑ j : Fin 3, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • D (F x) j
  refine ⟨G, memW12_lipschitz_homeomorph_preimage F hF hInv U u D hu, ?_⟩
  have hMeasure := map_lipschitzHomeomorph_preimage_volume_le F hInv U.val
  have hE := dirichletEnergy_lipschitz_pullback_le (F ⁻¹' U.val) U.val F hF hMeasure D hu.2.2
  change HarmonicMaps.dirichletEnergy G (F ⁻¹' U.val) ≤
    ENNReal.ofReal ((3 : ℝ) * ((20 : ℝ≥0) : ℝ) ^ 2) *
      ((((20 : ℝ≥0) : ℝ≥0∞) ^ 3) * HarmonicMaps.dirichletEnergy D U.val) at hE
  have hScale : ENNReal.ofReal ((3 : ℝ) * ((20 : ℝ≥0) : ℝ) ^ 2) * (((20 : ℝ≥0) : ℝ≥0∞) ^ 3) =
      ENNReal.ofReal (9600000 : ℝ) := by norm_num
  rwa [← mul_assoc, hScale] at hE

end Thesis

end
