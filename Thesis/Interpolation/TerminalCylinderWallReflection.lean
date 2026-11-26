module

public import Thesis.Interpolation.TerminalCylinderHalfChart
public import Thesis.Interpolation.CylinderLipschitzGraphTransport
import HarmonicMaps.Analysis.EuclideanHausdorffLipschitz

/-! The reversed planar wall coordinate and its actual weak graph and rim class. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Thesis.MeasureGeometry

/-- Reversal of the radial wall coordinate, with a globally Lipschitz extension. -/
def terminalWallReflection (R : ℝ) (y : Plane) : Plane :=
  min (2 * R) (max R (3 * R - ‖y‖)) • ((max R ‖y‖)⁻¹ • y)

/-- The reversed radius is literal on the original wall annulus. -/
theorem terminalWallReflection_eq {R : ℝ} {y : Plane}
    (hy : y ∈ closedPlanarRadialCollar R (2 * R)) :
    terminalWallReflection R y = (3 * R - ‖y‖) • NormedSpace.normalize y := by
  have hL : R ≤ 3 * R - ‖y‖ := by linarith only [hy.2]
  have hH : 3 * R - ‖y‖ ≤ 2 * R := by linarith only [hy.1]
  rw [terminalWallReflection, max_eq_right hy.1, max_eq_right hL, min_eq_right hH,
    NormedSpace.normalize]

theorem terminalWallReflection_lipschitz {R : ℝ} (hR : 0 < R) :
    LipschitzWith 5 (terminalWallReflection R) := by
  let a (y : Plane) := min (2 * R) (max R (3 * R - ‖y‖))
  let d (y : Plane) := max R ‖y‖
  let v (y : Plane) := (d y)⁻¹ • y
  have hd (y : Plane) : R ≤ d y := le_max_left _ _
  have hd₀ (y : Plane) : 0 < d y := hR.trans_le (hd y)
  have hdN (y : Plane) : ‖y‖ ≤ d y := le_max_right _ _
  have hA (y : Plane) : |a y| ≤ 2 * R := by
    have hPos : 0 ≤ a y := le_min (by positivity) (hR.le.trans (le_max_left _ _))
    rw [abs_of_nonneg hPos]
    exact min_le_left _ _
  have hv (y : Plane) : ‖v y‖ ≤ 1 := by
    rw [show v y = (d y)⁻¹ • y from rfl, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hd₀ y).le)]
    exact (mul_le_mul_of_nonneg_left (hdN y) (inv_nonneg.mpr (hd₀ y).le)).trans_eq
      (inv_mul_cancel₀ (hd₀ y).ne')
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hD : |d x - d y| ≤ ‖x - y‖ := by
    have h := abs_max_sub_max_le_max R ‖x‖ R ‖y‖
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg (‖x‖ - ‖y‖))] at h
    exact h.trans (abs_norm_sub_norm_le _ _)
  have hA' : |a x - a y| ≤ ‖x - y‖ := by
    have h₁ := abs_min_sub_min_le_max (2*R) (max R (3*R - ‖x‖))
      (2*R) (max R (3*R - ‖y‖))
    rw [sub_self, abs_zero,
      max_eq_right (abs_nonneg (max R (3*R - ‖x‖) - max R (3*R - ‖y‖)))] at h₁
    have h₂ := abs_max_sub_max_le_max R (3*R - ‖x‖) R (3*R - ‖y‖)
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg ((3*R - ‖x‖) - (3*R - ‖y‖))),
      sub_sub_sub_cancel_left, abs_sub_comm ‖y‖ ‖x‖] at h₂
    exact h₁.trans (h₂.trans (abs_norm_sub_norm_le _ _))
  have hV : ‖v x - v y‖ ≤ (2 / R) * ‖x-y‖ := by
    have h := norm_inverse_smul_difference_le x y (hd₀ x) (hd₀ y) (hdN y)
    have hInv : (d x)⁻¹ ≤ R⁻¹ := (inv_le_inv₀ (hd₀ x) hR).2 (hd x)
    calc
      _ ≤ (d x)⁻¹ * (‖x-y‖ + |d x-d y|) := h
      _ ≤ R⁻¹ * (‖x-y‖ + ‖x-y‖) :=
        mul_le_mul hInv (add_le_add le_rfl hD) (add_nonneg (norm_nonneg _) (abs_nonneg _)) (by positivity)
      _ = _ := by ring
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_ofNat]
  change ‖a x • v x - a y • v y‖ ≤ _
  have he : a x • v x - a y • v y = a x • (v x - v y) + (a x - a y) • v y := by
    rw [smul_sub, sub_smul, sub_add_sub_cancel]
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h := add_le_add (mul_le_mul (hA x) hV (norm_nonneg _) (by positivity))
    (mul_le_mul hA' (hv y) (norm_nonneg _) (norm_nonneg _))
  exact h.trans_eq (by field_simp; ring)

theorem terminalWallReflection_mapsTo {R : ℝ} (hR : 0 < R) :
    MapsTo (terminalWallReflection R) (terminalWallAnnulus R).val (terminalWallAnnulus R).val := by
  intro y hy
  have hyN : ‖y‖ ∈ Ioo R (2 * R) := hy
  have hy₀ : y ≠ 0 := norm_pos_iff.1 (hR.trans hyN.1)
  have hs : 0 < 3 * R - ‖y‖ := by linarith only [hR, hyN.2]
  change ‖terminalWallReflection R y‖ ∈ Ioo R (2 * R)
  rw [terminalWallReflection_eq (Ioo_subset_Icc_self hyN), norm_smul, Real.norm_of_nonneg hs.le,
    NormedSpace.norm_normalize hy₀, mul_one]
  exact ⟨by linarith only [hyN.2], by linarith only [hyN.1]⟩

theorem terminalWallReflection_involutive_on {R : ℝ} (hR : 0 < R)
    {y : Plane} (hy : y ∈ (terminalWallAnnulus R).val) :
    terminalWallReflection R (terminalWallReflection R y) = y := by
  have hy' : ‖y‖ ∈ Ioo R (2 * R) := hy
  have hy₀ : y ≠ 0 := norm_pos_iff.1 (hR.trans hy'.1)
  have hY : ‖terminalWallReflection R y‖ ∈ Ioo R (2 * R) := terminalWallReflection_mapsTo hR hy
  have hs : 0 < 3 * R - ‖y‖ := by linarith only [hR, hy'.2]
  rw [terminalWallReflection_eq (Ioo_subset_Icc_self hY), terminalWallReflection_eq (Ioo_subset_Icc_self hy'),
    norm_smul, Real.norm_of_nonneg hs.le, NormedSpace.norm_normalize hy₀, mul_one,
    sub_sub_cancel, NormedSpace.normalize_smul_of_pos hs,
    NormedSpace.normalize_eq_self_of_norm_eq_one (NormedSpace.norm_normalize hy₀),
    NormedSpace.normalize, smul_inv_smul₀ (norm_ne_zero_iff.2 hy₀)]

private theorem map_terminalWallReflection_le {R : ℝ} (hR : 0 < R) :
    Measure.map (terminalWallReflection R) (volume.restrict (terminalWallAnnulus R).val) ≤
      (25 : ℝ≥0∞) • volume.restrict (terminalWallAnnulus R).val := by
  let V := (terminalWallAnnulus R).val
  let F := terminalWallReflection R
  have hL := terminalWallReflection_lipschitz hR
  have hMeas := hL.continuous.measurable
  apply Measure.le_iff.2
  intro S hS
  rw [Measure.map_apply hMeas hS, Measure.restrict_apply (hMeas hS), Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hS]
  have hSub : F ⁻¹' S ∩ V ⊆ F '' (S ∩ V) := by
    rintro y ⟨hyS, hyV⟩
    exact ⟨F y, ⟨hyS, terminalWallReflection_mapsTo hR hyV⟩, terminalWallReflection_involutive_on hR hyV⟩
  have h := euclideanHausdorff_lipschitzOn_image_le_volume hL.lipschitzOnWith
    (subset_univ (S ∩ V))
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume, finrank_euclideanSpace_fin] at h
  norm_num at h
  exact (measure_mono hSub).trans h

/-- Reversing the radial wall changes the genuine outer rim into the inner rim. -/
theorem terminalWallReflection_trace {q : ℕ} {R : ℝ} (hR : 0 < R)
    {w : Plane → Ambient q} (T : C(Icc R (2*R), Lp (Ambient q) 2 ((volume : Measure Plane).toSphere)))
    (hT : RepresentsNativePlanarRadialTrace w T) :
    ∃ T' : C(Icc R (2*R), Lp (Ambient q) 2 ((volume : Measure Plane).toSphere)),
      RepresentsNativePlanarRadialTrace (w ∘ terminalWallReflection R) T' ∧
      T' ⟨R, le_rfl, by linarith only [hR]⟩ = T ⟨2*R, by linarith only [hR], le_rfl⟩ := by
  let I : Set ℝ := Icc R (2*R)
  have hTMap (t : I) : 3*R-t.val ∈ I := by
    change R ≤ 3*R-t.val ∧ 3*R-t.val ≤ 2*R
    exact ⟨by linarith only [t.property.2], by linarith only [t.property.1]⟩
  let θ : C(I, I) :=
    ⟨fun t => ⟨3*R-t.val, hTMap t⟩,
      (continuous_const.sub continuous_subtype_val).subtype_mk hTMap⟩
  let T' := T.comp θ
  refine ⟨T', ?_, ?_⟩
  · have hMP : Measure.QuasiMeasurePreserving (fun t : ℝ => 3*R-t) volume volume :=
      ((volume : Measure ℝ).measurePreserving_sub_left (3*R)).quasiMeasurePreserving
    unfold RepresentsNativePlanarRadialTrace at hT ⊢
    filter_upwards [hMP.ae hT] with t ht htI
    have ht' : 3*R-t ∈ Ioo R (2*R) := by constructor <;> linarith only [htI.1,htI.2]
    have hp := hR.trans htI.1
    obtain ⟨hLp, hClass⟩ := ht ht'
    have hEq (v : NativeCircle) : terminalWallReflection R (t • v.val) = (3*R-t) • v.val := by
      have hv : ‖v.val‖ = 1 := mem_sphere_zero_iff_norm.1 v.property
      have hN : ‖t • v.val‖ = t := by rw [norm_smul, Real.norm_of_nonneg hp.le, hv, mul_one]
      have hIn : (t • v.val) ∈ closedPlanarRadialCollar R (2 * R) := by
        change ‖t • v.val‖ ∈ Icc R (2*R)
        rw [hN]
        exact Ioo_subset_Icc_self htI
      rw [terminalWallReflection_eq hIn, hN, NormedSpace.normalize_smul_of_pos hp,
        NormedSpace.normalize_eq_self_of_norm_eq_one hv]
    have hAE : (fun v : NativeCircle => w ((3*R-t) • v.val)) =ᵐ[((volume : Measure Plane).toSphere)]
        (fun v => (w ∘ terminalWallReflection R) (t • v.val)) :=
      Eventually.of_forall fun v => congrArg w (hEq v).symm
    let hLp' := hLp.ae_eq hAE
    refine ⟨hLp', ?_⟩
    let a : I := ⟨t, htI.1.le, htI.2.le⟩
    let b : I := ⟨3*R-t, ht'.1.le, ht'.2.le⟩
    have hab : θ a = b := Subtype.ext rfl
    change T (θ a) = hLp'.toLp _
    rw [hab]
    exact hClass.trans (hLp.toLp_congr hLp' hAE)
  · let l : I := ⟨R, le_rfl, by linarith only [hR]⟩
    let u : I := ⟨2*R, by linarith only [hR], le_rfl⟩
    have hθ : θ l = u := by
      apply Subtype.ext
      change 3*R-R = 2*R
      ring
    change T (θ l) = T u
    rw [hθ]

/-- The reversed wall retains its original Sobolev map with a fixed
Dirichlet comparison in the very same physical parametrization. -/
theorem terminalWallReflection_memW12 {q : ℕ} {R : ℝ} (hR : 0 < R)
    {w : Plane → Ambient q} {D : Plane → HarmonicMaps.Gradient 2 q}
    (hw : MemW12 (terminalWallAnnulus R) w D) :
    ∃ G : Plane → HarmonicMaps.Gradient 2 q,
      MemW12 (terminalWallAnnulus R) (w ∘ terminalWallReflection R) G ∧
      HarmonicMaps.dirichletEnergy G (terminalWallAnnulus R).val ≤
        1250 * HarmonicMaps.dirichletEnergy D (terminalWallAnnulus R).val := by
  let V := terminalWallAnnulus R
  let F := terminalWallReflection R
  have hLip := terminalWallReflection_lipschitz hR
  have hDom := map_terminalWallReflection_le hR
  let G (x : Plane) (i : Fin 2) := ∑ j : Fin 2, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • D (F x) j
  refine ⟨G, memW12_lipschitz_domain_pullback V V F hLip (terminalWallReflection_mapsTo hR)
    (by norm_num : (25 : ℝ≥0∞) ≠ ⊤) hDom hw, ?_⟩
  have h := dirichletEnergy_lipschitz_domain_pullback_le V V F hLip hDom hw
  change HarmonicMaps.dirichletEnergy G V.val ≤
    (ENNReal.ofReal (2 * ((5 : ℝ≥0) : ℝ) ^ 2) * 25) * HarmonicMaps.dirichletEnergy D V.val at h
  have hC : ENNReal.ofReal (2 * ((5 : ℝ≥0) : ℝ) ^ 2) * 25 = 1250 := by norm_num
  rwa [hC] at h

end Thesis.MeasureGeometry

end
