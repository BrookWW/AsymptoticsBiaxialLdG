module

public import Thesis.Interpolation.CompactGlobalSobolevApproximation
import Thesis.Interpolation.LipschitzSobolevPullback
import HarmonicMaps.Analysis.L2AffineContinuity
import Mathlib.Analysis.Convex.Topology

/-! A global zero-extended graph on a bounded convex domain has zero Sobolev trace. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal NNReal Topology

namespace Thesis

private def convexTraceDilation {n : ℕ} (z : Domain n) (t : ℝ) (ht : t ≠ 0) : Domain n ≃ₜ Domain n where
  toFun x := z + t • (x - z)
  invFun x := z + t⁻¹ • (x - z)
  left_inv x := by simp [smul_smul, inv_mul_cancel₀ ht]
  right_inv x := by simp [smul_smul, mul_inv_cancel₀ ht]
  continuous_toFun := continuous_const.add ((continuous_id.sub continuous_const).const_smul t)
  continuous_invFun := continuous_const.add ((continuous_id.sub continuous_const).const_smul t⁻¹)

private theorem lipschitz_centered_scale {n : ℕ} (z : Domain n) (t : ℝ) :
    LipschitzWith ‖t‖₊ (fun x : Domain n => z + t • (x - z)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_add_left, dist_eq_norm, dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul]
  exact le_rfl

private theorem memW12_dilation_univ {n q : ℕ} {w : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hw : MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) w D) (z : Domain n) {t : ℝ} (ht : t ≠ 0) :
    MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) (fun x => w (z + t • (x - z)))
      (fun x i => t • D (z + t • (x - z)) i) := by
  let e := convexTraceDilation z t ht
  let V : OpenDomain n := ⟨e ⁻¹' univ, isOpen_univ.preimage e.continuous⟩
  have hV : V = (⟨univ, isOpen_univ⟩ : OpenDomain n) := Subtype.ext preimage_univ
  have hLip : LipschitzWith ‖t‖₊ (e : Domain n → Domain n) := lipschitz_centered_scale z t
  have hInv : LipschitzWith ‖t⁻¹‖₊ (e.symm : Domain n → Domain n) := lipschitz_centered_scale z t⁻¹
  let G (x : Domain n) (i : Fin n) := ∑ j : Fin n, (fderiv ℝ e x (EuclideanSpace.single i 1)) j • D (e x) j
  have hG : MemW12 V (w ∘ e) G := memW12_lipschitz_homeomorph_preimage e hLip hInv _ w D hw
  rw [hV] at hG
  have hDerivative (x : Domain n) : fderiv ℝ e x = t • ContinuousLinearMap.id ℝ (Domain n) := by
    have hf : HasFDerivAt (fun y : Domain n => z + t • (y - z)) (t • ContinuousLinearMap.id ℝ (Domain n)) x :=
      (((hasFDerivAt_id x).sub_const z).const_smul t).const_add z
    exact hf.fderiv
  have hColumns : G = fun x i => t • D (z + t • (x - z)) i := by
    funext x i
    dsimp only [G]
    rw [hDerivative]
    simp [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
    rfl
  exact hColumns ▸ hG

private theorem eLpNorm_sub_triangle_two {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {f g h : X → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) : eLpNorm (f - h) 2 μ ≤ eLpNorm (f - g) 2 μ + eLpNorm (g - h) 2 μ := by
  rw [show f - h = (f - g) + (g - h) by abel]
  exact eLpNorm_add_le (hf.sub hg) (hg.sub hh) (by norm_num)

private theorem tendsto_eLpNorm_of_diagonal_graph_error {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {f g : ℕ → X → E} {h : X → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) (hg : ∀ k, AEStronglyMeasurable (g k) μ)
    (hh : AEStronglyMeasurable h μ) {τ : ℕ → ℝ≥0∞} (hτ : Tendsto τ atTop (𝓝 0))
    (hErr : ∀ k, eLpNorm (f k - g k) 2 μ ≤ τ k)
    (hConv : Tendsto (fun k => eLpNorm (g k - h) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k - h) 2 μ) atTop (𝓝 0) := by
  have hUpper := hτ.add hConv
  rw [add_zero] at hUpper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper (fun _ => zero_le)
  intro k
  exact (eLpNorm_sub_triangle_two (hf k) (hg k) hh).trans (add_le_add (hErr k) le_rfl)

/-- A zero-extended global Sobolev graph belongs to the zero-trace closure on
an open convex set with compact closure. The contraction and smoothing keep
the original displayed weak columns. -/
theorem hasZeroBoundaryValues_of_convex_zeroExtension {n q : ℕ} (U : OpenDomain n)
    (hConvex : Convex ℝ U.val) (hK : IsCompact (closure U.val)) {z : Domain n} (hz : z ∈ U.val)
    {w : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q} (hw : MemW12 U w D)
    (hwZ : MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) (U.val.indicator w) (U.val.indicator D)) :
    HasZeroBoundaryValues U w D := by
  let w₀ := U.val.indicator w
  let D₀ := U.val.indicator D
  let t (k : ℕ) := 1 + 1 / ((k : ℝ) + 1)
  have ht₀ (k : ℕ) : 1 < t k := lt_add_of_pos_right 1 (by positivity : 0 < 1 / ((k : ℝ) + 1))
  have ht (k : ℕ) : 0 < t k := zero_lt_one.trans (ht₀ k)
  have htL : Tendsto t atTop (𝓝 1) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
    simpa only [t, add_zero] using h
  let e (k : ℕ) := convexTraceDilation z (t k) (ht k).ne'
  let w₁ (k : ℕ) (x : Domain n) := w₀ (e k x)
  let D₁ (k : ℕ) (x : Domain n) (i : Fin n) := t k • D₀ (e k x) i
  have hW (k : ℕ) : MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) (w₁ k) (D₁ k) :=
    memW12_dilation_univ hwZ z (ht k).ne'
  let K (k : ℕ) := (e k).symm '' closure U.val
  have hKc (k : ℕ) : IsCompact (K k) := hK.image (e k).symm.continuous
  have hKU (k : ℕ) : K k ⊆ U.val := by
    rintro _ ⟨y, hy, rfl⟩
    have hμ : (t k)⁻¹ < 1 := inv_lt_one_iff₀.mpr (Or.inr (ht₀ k))
    have hz' : z ∈ interior U.val := by rwa [U.property.interior_eq]
    have hInside := hConvex.combo_interior_closure_mem_interior hz' hy
      (sub_pos.mpr hμ) (inv_nonneg.mpr (ht k).le) (sub_add_cancel 1 (t k)⁻¹)
    rw [U.property.interior_eq] at hInside
    change z + (t k)⁻¹ • (y - z) ∈ U.val
    have hEq : z + (t k)⁻¹ • (y - z) = (1 - (t k)⁻¹) • z + (t k)⁻¹ • y := by
      rw [smul_sub, sub_smul, one_smul]
      abel
    rwa [hEq]
  have hInK (k : ℕ) (x : Domain n) (hx : e k x ∈ U.val) : x ∈ K k :=
    ⟨e k x, subset_closure hx, (e k).symm_apply_apply x⟩
  have hSup (k : ℕ) : Function.support (w₁ k) ⊆ K k := by
    intro x hx
    by_contra hn
    exact hx (indicator_of_notMem (fun h => hn (hInK k x h)) w)
  have hGrad (k : ℕ) (i : Fin n) : Function.support (fun x => D₁ k x i) ⊆ K k := by
    intro x hx
    by_contra hn
    have hn' : e k x ∉ U.val := fun h => hn (hInK k x h)
    apply hx
    dsimp only [D₁, D₀]
    rw [indicator_of_notMem hn']
    simp
  let τ (k : ℕ) := ENNReal.ofReal (1 / ((k : ℝ) + 1))
  have hτ (k : ℕ) : 0 < τ k := ENNReal.ofReal_pos.mpr (by positivity)
  have hτL : Tendsto τ atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    change Tendsto (ENNReal.ofReal ∘ fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0)
    simpa only [ENNReal.ofReal_zero] using h
  choose f hf hfK hfU hfW hfD using fun k : ℕ =>
    exists_compact_global_sobolev_approximation U (hW k) (K k) (hKc k) (hKU k) (hSup k) (hGrad k) (hτ k)
  let μ := (volume : Measure (Domain n)).restrict U.val
  have hW₀ : MemLp w₀ 2 volume := by simpa only [Measure.restrict_univ] using hwZ.2.1
  have hD₀ (i : Fin n) : MemLp (fun x => D₀ x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hwZ.2.2 i
  have hRawW : w₀ =ᵐ[μ] w := (ae_restrict_mem U.property.measurableSet).mono (fun x hx => indicator_of_mem hx w)
  have hRawD (i : Fin n) : (fun x => D₀ x i) =ᵐ[μ] (fun x => D x i) :=
    (ae_restrict_mem U.property.measurableSet).mono (fun x hx => congrFun (indicator_of_mem hx D) i)
  have hWconv : Tendsto (fun k => eLpNorm (w₁ k - w) 2 μ) atTop (𝓝 0) := by
    have h := (tendsto_eLpNorm_centeredDilation_sub hW₀ z).comp htL
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    intro k
    change eLpNorm (w₁ k - w) 2 μ ≤ eLpNorm (w₁ k - w₀) 2 volume
    rw [eLpNorm_congr_ae (EventuallyEq.rfl.sub hRawW.symm)]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hDconv (i : Fin n) : Tendsto (fun k => eLpNorm (fun x => D₁ k x i - D x i) 2 μ) atTop (𝓝 0) := by
    have h := (tendsto_eLpNorm_smul_centeredDilation_sub (hD₀ i) z).comp htL
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    intro k
    change eLpNorm (fun x => D₁ k x i - D x i) 2 μ ≤ eLpNorm (fun x => D₁ k x i - D₀ x i) 2 volume
    have hEq : (fun x => D₁ k x i - D x i) =ᵐ[μ] (fun x => D₁ k x i - D₀ x i) :=
      EventuallyEq.rfl.sub (hRawD i).symm
    rw [eLpNorm_congr_ae hEq]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  refine ⟨hw, f, hf, fun k => ⟨hfK k, hfU k⟩, ?_, ?_⟩
  · have hF (k : ℕ) : AEStronglyMeasurable (f k) μ := (hf k).continuous.aestronglyMeasurable
    have hWk (k : ℕ) : AEStronglyMeasurable (w₁ k) μ :=
      (hW k).2.1.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume (subset_univ U.val))
    exact tendsto_eLpNorm_of_diagonal_graph_error hF hWk hw.2.1.aestronglyMeasurable hτL
      (fun k => (hfW k).le) hWconv
  · intro i
    have hF (k : ℕ) : AEStronglyMeasurable (coordinateDerivative (f k) (hf k) i) μ :=
      (((hf k).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
    have hDk (k : ℕ) : AEStronglyMeasurable (fun x => D₁ k x i) μ :=
      ((hW k).2.2 i).aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume (subset_univ U.val))
    exact tendsto_eLpNorm_of_diagonal_graph_error hF hDk (hw.2.2 i).aestronglyMeasurable hτL
      (fun k => (hfD k i).le) (hDconv i)

end Thesis

end
