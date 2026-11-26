module

public import Thesis.Interpolation.VacuumSphereSobolevLift
import Thesis.Interpolation.SphericalDensitySlices
import Thesis.Interpolation.SphericalDensityProjection
import StratificationTheory.Foundation.SphereGradientData
import StratificationTheory.Foundation.RadialSobolevPullback
import StratificationTheory.Foundation.RadialL2Transfer
import HolderToCK.Analysis.ClassicalWeakGradient
import HarmonicMaps.Analysis.SobolevPostcomposition
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Strong smooth density for the native vacuum Sobolev maps on the unit two-sphere. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Frobenius

namespace Thesis

private theorem tangentialColumns_real_smul {n q : ℕ}
    (θ : UnitBoundarySphere n) (C : HarmonicMaps.Gradient n q) (r : ℝ) (i : Fin n) :
    tangentialColumns θ (r • C) i = r • tangentialColumns θ C i := by
  simp only [tangentialColumns,Pi.smul_apply,smul_sub]
  have h : (∑ j : Fin n, θ.val j • r • C j) = r • ∑ j : Fin n, θ.val j • C j := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm (θ.val j) r (C j)
  rw [h,smul_comm (θ.val i) r]

private theorem sphericalGradient_smooth_slice
    {q : ℕ} {g : Point → Ambient q} (hg : ContDiff ℝ ∞ g) (r : ℝ)
    (hv : MemSphereW12 (by decide : 2 ≤ 3) (fun θ : UnitBoundarySphere 3 => g (r • θ.val)))
    (i : Fin 3) :
    (fun θ => (sphereGradient (by decide : 2 ≤ 3) (fun θ : UnitBoundarySphere 3 => g (r • θ.val)) hv i) θ)
      =ᵐ[unitBoundarySurface 3]
      fun θ => tangentialColumns θ (fun j => r • coordinateDerivative g hg j (r • θ.val)) i := by
  let w (x : Point) := g (0+r • (‖x‖⁻¹ • x))
  let D (x : Point) (j : Fin 3) := fderiv ℝ w x (EuclideanSpace.single j 1)
  let A (θ : UnitBoundarySphere 3) (j : Fin 3) :=
    tangentialColumns θ (fun l => r • coordinateDerivative g hg l (r • θ.val)) j
  have hw : MemW12Loc ⟨({0}ᶜ : Set Point),isOpen_compl_singleton⟩ w D :=
    HolderToCK.memW12Loc_of_contDiffOn_one _ ((contDiffOn_radial_smooth_pullback hg 0 r).of_le (by simp))
  have hRay (ρ : PositiveRadius) (θ : UnitBoundarySphere 3) : w (ρ.val • θ.val) = g (r • θ.val) := by
    simpa only [w,zero_add] using radial_smooth_pullback_ray g 0 r ρ.property θ
  have hD (ρ : PositiveRadius) (θ : UnitBoundarySphere 3) (j : Fin 3) :
      D (ρ.val • θ.val) j = ρ.val⁻¹ • A θ j := by
    change fderiv ℝ w (ρ.val • θ.val) (EuclideanSpace.single j 1) = _
    rw [show w = (fun x : Point => g (0+r • (‖x‖⁻¹ • x))) from rfl,
      fderiv_radial_smooth_pullback_column hg 0 r ρ.property θ j]
    change (r/ρ.val) • tangentialColumns θ (fun l => coordinateDerivative g hg l (0+r • θ.val)) j =
      ρ.val⁻¹ • tangentialColumns θ (r • fun l => coordinateDerivative g hg l (r • θ.val)) j
    rw [tangentialColumns_real_smul,smul_smul,zero_add,div_eq_mul_inv,mul_comm r]
  exact sphericalGradient_ae_eq_of_radial_columns hv hw hRay hD i

private def smoothVacuumSlice (a : BulkCoefficients) (r : ℝ)
    (g : Point → Ambient 5) (hg : ContDiff ℝ ∞ g)
    (hT : ∀ θ : UnitBoundarySphere 3, g (r • θ.val) ∈ (vacuumCompactSmoothEmbeddedTarget a).carrierSet) :
    C(UnitBoundarySphere 3,vacuum a) := by
  let f (θ : UnitBoundarySphere 3) : S0 := frobeniusCoordinateEquiv.symm (g (r • θ.val))
  have hScaled : Continuous (fun θ : UnitBoundarySphere 3 => r • θ.val) :=
    continuous_subtype_val.const_smul r
  have hF : Continuous f := frobeniusCoordinateEquiv.symm.continuous.comp (hg.continuous.comp hScaled)
  have hVac (θ : UnitBoundarySphere 3) : f θ ∈ vacuum a :=
    mem_vacuumCompactSmoothEmbeddedTarget_iff.mp (hT θ)
  exact ⟨fun θ => ⟨f θ,hVac θ⟩,hF.subtype_mk hVac⟩

private theorem smoothVacuumSlice_coord (a : BulkCoefficients) (r : ℝ)
    (g : Point → Ambient 5) (hg : ContDiff ℝ ∞ g) (hT) (θ : UnitBoundarySphere 3) :
    frobeniusCoordinateEquiv (smoothVacuumSlice a r g hg hT θ).val = g (r • θ.val) :=
  frobeniusCoordinateEquiv.apply_symm_apply _

private theorem smoothVacuumSlice_smooth (a : BulkCoefficients) (r : ℝ)
    (g : Point → Ambient 5) (hg : ContDiff ℝ ∞ g) (hT) (base : UnitBoundarySphere 3) :
    ContDiffOn ℝ ∞ (fun x : Point => (smoothVacuumSlice a r g hg hT (sphereRadialDirection base x)).val)
      ({0}ᶜ : Set Point) := by
  have hS := frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (contDiffOn_radial_smooth_pullback hg (0 : Point) r)
  refine hS.congr fun x hx => ?_
  change frobeniusCoordinateEquiv.symm (g (r • (sphereRadialDirection base x).val)) =
    frobeniusCoordinateEquiv.symm (g (0+r • (‖x‖⁻¹ • x)))
  rw [sphereRadialDirection,dif_pos (show x ≠ 0 from hx),zero_add]
  rfl

private theorem smoothVacuumSlice_mem (a : BulkCoefficients) (r : ℝ)
    (g : Point → Ambient 5) (hg : ContDiff ℝ ∞ g) (hT) :
    MemSphereW12 (by decide : 2 ≤ 3)
      (fun θ => frobeniusCoordinateEquiv (smoothVacuumSlice a r g hg hT θ).val) := by
  simpa only [smoothVacuumSlice_coord,zero_add] using
    memSphereW12_smooth_slice (by decide : 2 ≤ 3) hg (0 : Point) r

private theorem smoothVacuumSlice_grad (a : BulkCoefficients) (r : ℝ)
    (g : Point → Ambient 5) (hg : ContDiff ℝ ∞ g) (hT) (i : Fin 3) :
    (fun θ => (sphereGradient (by decide : 2 ≤ 3)
      (fun θ => frobeniusCoordinateEquiv (smoothVacuumSlice a r g hg hT θ).val)
      (smoothVacuumSlice_mem a r g hg hT) i) θ) =ᵐ[unitBoundarySurface 3]
    fun θ => tangentialColumns θ (fun j => r • coordinateDerivative g hg j (r • θ.val)) i := by
  have he : (fun θ => frobeniusCoordinateEquiv (smoothVacuumSlice a r g hg hT θ).val) =
      (fun θ : UnitBoundarySphere 3 => g (r • θ.val)) := funext (smoothVacuumSlice_coord a r g hg hT)
  have hv : MemSphereW12 (by decide : 2 ≤ 3) (fun θ : UnitBoundarySphere 3 => g (r • θ.val)) :=
    he ▸ smoothVacuumSlice_mem a r g hg hT
  have h := sphericalGradient_smooth_slice hg r hv i
  simpa only [he] using h

private theorem tendsto_sphere_values_after_projection
    {m : ℕ → UnitBoundarySphere 3 → Ambient 5} {v : UnitBoundarySphere 3 → Ambient 5}
    (hML : Tendsto (fun k => eLpNorm (m k-v) 2 (unitBoundarySurface 3)) atTop (𝓝 0))
    {F : Ambient 5 → Ambient 5} (hF : ContDiff ℝ ∞ F)
    {L : ℝ} (hFD : ∀ x, ‖fderiv ℝ F x‖ ≤ L)
    (hFix : ∀ θ, F (v θ) = v θ) :
    Tendsto (fun k => eLpNorm (fun θ => F (m k θ)-v θ) 2 (unitBoundarySurface 3)) atTop (𝓝 0) := by
  let μ := unitBoundarySurface 3
  have hL := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal L) hML (Or.inr ENNReal.ofReal_ne_top)
  have hUpper : Tendsto (fun k => ENNReal.ofReal L * eLpNorm (m k-v) 2 μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using hL
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
  · exact fun _ => bot_le
  · intro k
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (p := 2)
    refine Eventually.of_forall fun θ => ?_
    calc
      ‖F (m k θ)-v θ‖ = ‖F (m k θ)-F (v θ)‖ := by rw [hFix]
      _ ≤ L*‖m k θ-v θ‖ := postcomposition_norm_sub_le hF hFD _ _

private theorem tendsto_native_gradient_of_angular_columns
    {q : ℕ}
    {v : UnitBoundarySphere 3 → Ambient q} (hv : MemSphereW12 (by decide : 2 ≤ 3) v)
    {u : ℕ → UnitBoundarySphere 3 → Ambient q}
    (hu : ∀ k, MemSphereW12 (by decide : 2 ≤ 3) (u k))
    {T : ℕ → UnitBoundarySphere 3 → HarmonicMaps.Gradient 3 q}
    {A : UnitBoundarySphere 3 → HarmonicMaps.Gradient 3 q}
    (hA : ∀ i, MemLp (fun θ => A θ i) 2 (unitBoundarySurface 3))
    (hT : ∀ k i, MemLp (fun θ => T k θ i) 2 (unitBoundarySurface 3))
    (hL : ∀ i, Tendsto (fun k => eLpNorm (fun θ => T k θ i-A θ i) 2
      (unitBoundarySurface 3)) atTop (𝓝 0))
    (hATan : ∀ θ, ∑ i : Fin 3, θ.val i • A θ i = 0)
    (hG : ∀ k i, (fun θ => (sphereGradient (by decide : 2 ≤ 3) (u k) (hu k) i) θ)
      =ᵐ[unitBoundarySurface 3] fun θ => tangentialColumns θ (T k θ) i)
    (hG₀ : ∀ i, (fun θ => (sphereGradient (by decide : 2 ≤ 3) v hv i) θ)
      =ᵐ[unitBoundarySurface 3] fun θ => A θ i)
    (i : Fin 3) :
    Tendsto (fun k => sphereGradient (by decide : 2 ≤ 3) (u k) (hu k) i) atTop
      (𝓝 (sphereGradient (by decide : 2 ≤ 3) v hv i)) := by
  let μ := unitBoundarySurface 3
  have hμ : unitBoundarySurface 3 = (volume : Measure Point).toSphere :=
    euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 3)
  let W (k : ℕ) (θ : UnitBoundarySphere 3) := T k θ-A θ
  have hWM (k : ℕ) (j : Fin 3) : MemLp (fun θ => W k θ j) 2 μ := (hT k j).sub (hA j)
  have hWL (j : Fin 3) : Tendsto (fun k => ∫ θ, ‖W k θ j‖^2 ∂μ) atTop (𝓝 0) :=
    tendsto_integral_normSq_zero_from_native_L2 (fun k => hWM k j) (hL j)
  have hTang : Tendsto (fun k => eLpNorm (fun θ => tangentialColumns θ (W k θ) i) 2 μ) atTop (𝓝 0) := by
    change (∀ k j, MemLp (fun θ => W k θ j) 2 (unitBoundarySurface 3)) at hWM
    change (∀ j, Tendsto (fun k => ∫ θ, ‖W k θ j‖^2 ∂unitBoundarySurface 3) atTop (𝓝 0)) at hWL
    change Tendsto (fun k => eLpNorm (fun θ => tangentialColumns θ (W k θ) i) 2
      (unitBoundarySurface 3)) atTop (𝓝 0)
    rw [hμ] at hWM hWL ⊢
    exact tendsto_eLpNorm_tangential_column_zero hWM hWL i
  have hTan (θ : UnitBoundarySphere 3) : tangentialColumns θ (A θ) i = A θ i := by
    simp only [tangentialColumns,hATan θ,smul_zero,sub_zero]
  let G (k : ℕ) := sphereGradient (by decide : 2 ≤ 3) (u k) (hu k) i
  let G₀ := sphereGradient (by decide : 2 ≤ 3) v hv i
  have hL' : Tendsto (fun k => eLpNorm (⇑(G k)-⇑G₀) 2 μ) atTop (𝓝 0) := by
    apply hTang.congr
    intro k
    apply eLpNorm_congr_ae
    filter_upwards [hG k i,hG₀ i] with θ hθ hθ₀
    change tangentialColumns θ (T k θ-A θ) i = G k θ-G₀ θ
    change G k θ = _ at hθ
    change G₀ θ = _ at hθ₀
    rw [tangentialColumns_sub,Pi.sub_apply,hTan,hθ,hθ₀]
  simpa only [Lp.toLp_coeFn] using Lp.tendsto_Lp_of_tendsto_eLpNorm _ (Lp.memLp G₀) hL'

private theorem tendsto_native_vacuumSphere_energy
    {a : BulkCoefficients} {Q : UnitBoundarySphere 3 → vacuum a}
    (hQ : MemSphereW12 (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (Q θ).val))
    {Qj : ℕ → C(UnitBoundarySphere 3,vacuum a)}
    (hj : ∀ k, MemSphereW12 (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (Qj k θ).val))
    (hGL : ∀ i : Fin 3, Tendsto (fun k =>
      sphereGradient (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (Qj k θ).val) (hj k) i) atTop
        (𝓝 (sphereGradient (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (Q θ).val) hQ i))) :
    Tendsto (fun k => vacuumSphereGradientEnergy (by decide : 2 ≤ 3) (Qj k) (hj k)) atTop
      (𝓝 (vacuumSphereGradientEnergy (by decide : 2 ≤ 3) Q hQ)) := by
  let μ := unitBoundarySurface 3
  have hSplit (F : Fin 3 → Lp (Ambient 5) 2 μ) :
      (∫ θ, ∑ i : Fin 3, ‖F i θ‖^2 ∂μ) = ∑ i : Fin 3, ∫ θ, ‖F i θ‖^2 ∂μ := by
    apply integral_finsetSum
    intro i _
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (Lp.memLp (F i)).integrable_norm_rpow (by norm_num) (by norm_num)
  let G (k : ℕ) := sphereGradient (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (Qj k θ).val) (hj k)
  let G₀ := sphereGradient (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (Q θ).val) hQ
  change Tendsto (fun k => ∫ θ, ∑ i : Fin 3, ‖G k i θ‖^2 ∂μ) atTop
    (𝓝 (∫ θ, ∑ i : Fin 3, ‖G₀ i θ‖^2 ∂μ))
  simp_rw [hSplit]
  exact tendsto_finsetSum Finset.univ (fun i _ => tendsto_integral_normSq_from_native_Lp (hGL i))

private theorem projected_sphere_slice_column
    (r : ℝ) (m : ℕ → Point → Ambient 5) (hm : ∀ k, ContDiff ℝ ∞ (m k))
    {v : UnitBoundarySphere 3 → Ambient 5}
    (hV : AEStronglyMeasurable v (unitBoundarySurface 3))
    (hM : ∀ k, AEStronglyMeasurable (fun θ : UnitBoundarySphere 3 => m k (r • θ.val)) (unitBoundarySurface 3))
    (hme : ∀ᵐ θ : UnitBoundarySphere 3 ∂unitBoundarySurface 3,
      Tendsto (fun k => m k (r • θ.val)) atTop (𝓝 (v θ)))
    {A : UnitBoundarySphere 3 → Ambient 5}
    (hA : MemLp A 2 (unitBoundarySurface 3)) (i : Fin 3)
    (hZ : ∀ k, MemLp (fun θ : UnitBoundarySphere 3 => r • coordinateDerivative (m k) (hm k) i (r • θ.val))
      2 (unitBoundarySurface 3))
    (hZL : Tendsto (fun k => eLpNorm (fun θ : UnitBoundarySphere 3 =>
      r • coordinateDerivative (m k) (hm k) i (r • θ.val)-A θ) 2 (unitBoundarySurface 3)) atTop (𝓝 0))
    {F : Ambient 5 → Ambient 5} (hF : ContDiff ℝ ∞ F)
    {L : ℝ} (hFD : ∀ x, ‖fderiv ℝ F x‖ ≤ L)
    (hFA : (fun θ => fderiv ℝ F (v θ) (A θ)) =ᵐ[unitBoundarySurface 3] A) :
    let T (k : ℕ) (θ : UnitBoundarySphere 3) :=
      r • coordinateDerivative (F ∘ m k) (hF.comp (hm k)) i (r • θ.val)
    (∀ k, MemLp (T k) 2 (unitBoundarySurface 3)) ∧
      Tendsto (fun k => eLpNorm (T k-A) 2 (unitBoundarySurface 3)) atTop (𝓝 0) := by
  let T (k : ℕ) (θ : UnitBoundarySphere 3) :=
    r • coordinateDerivative (F ∘ m k) (hF.comp (hm k)) i (r • θ.val)
  let Z (k : ℕ) (θ : UnitBoundarySphere 3) := r • coordinateDerivative (m k) (hm k) i (r • θ.val)
  have hT (k : ℕ) (θ : UnitBoundarySphere 3) : T k θ =
      fderiv ℝ F (m k (r • θ.val)) (Z k θ) := by
    change r • coordinateDerivative (F ∘ m k) (hF.comp (hm k)) i (r • θ.val) = _
    rw [coordinateDerivative_postcomposition (hm k) hF]
    exact (map_smul _ r _).symm
  change (∀ k, MemLp (T k) 2 (unitBoundarySurface 3)) ∧
    Tendsto (fun k => eLpNorm (T k-A) 2 (unitBoundarySurface 3)) atTop (𝓝 0)
  refine ⟨fun k => ?_, ?_⟩
  · have hEq := funext (hT k)
    rw [hEq]
    exact memLp_postcomposition_column (hM k) (hZ k) hF hFD
  · have hL := tendsto_sphericalProjection_column (m := fun k θ => m k (r • θ.val))
      (Z := Z) hM hV hZ hA hme hZL hF hFD
    apply hL.congr
    intro k
    apply eLpNorm_congr_ae
    filter_upwards [hFA] with θ hθ
    change fderiv ℝ F (m k (r • θ.val)) (Z k θ)-fderiv ℝ F (v θ) (A θ) = T k θ-A θ
    rw [← hT,hθ]

/-- Every native two-sphere vacuum Sobolev map is strongly approximated by
smooth maps into the same vacuum, with its original tangential energy. -/
theorem smoothVacuumSphereDensity (a : BulkCoefficients) : External.SmoothVacuumSphereDensity a := by
  intro base Q hQ
  let e := frobeniusCoordinateEquiv
  let μ := unitBoundarySurface 3
  let v (θ : UnitBoundarySphere 3) := e (Q θ).val
  obtain ⟨w,D,A,hw,hRay,hA,hD,hATan⟩ :=
    exists_sphere_radial_weak_gradient_data (by decide : 2 ≤ 3) hQ
  have hV (θ : UnitBoundarySphere 3) : v θ ∈ (vacuumCompactSmoothEmbeddedTarget a).carrierSet := by
    apply mem_vacuumCompactSmoothEmbeddedTarget_iff.mpr
    change e.symm (e (Q θ).val) ∈ vacuum a
    rw [e.symm_apply_apply]
    exact (Q θ).property
  obtain ⟨ρ,hρ,F,L,hF,hFD,hFix,hProject⟩ := exists_smooth_vacuumCoordinate_retraction a
  obtain ⟨r,_,m,hm,hTube,hMM,hML,hZM,hZL⟩ :=
    exists_sphericalVacuum_mollified_ray_data a base hw hV hRay hD hA hρ
  have hVmem : MemLp v 2 μ := hQ.1
  have hM (k : ℕ) : AEStronglyMeasurable (fun θ : UnitBoundarySphere 3 => m k (r • θ.val)) μ :=
    (hMM k).aestronglyMeasurable
  have hMeasures := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    hM hVmem.aestronglyMeasurable hML
  obtain ⟨σ,hσ,hσae⟩ := hMeasures.exists_seq_tendsto_ae
  let m' (k : ℕ) : Point → Ambient 5 := m (σ k)
  have hm' (k : ℕ) : ContDiff ℝ ∞ (m' k) := hm (σ k)
  let P (k : ℕ) : Point → Ambient 5 := F ∘ m' k
  have hP (k : ℕ) : ContDiff ℝ ∞ (P k) := hF.comp (hm' k)
  have hTarget (k : ℕ) (θ : UnitBoundarySphere 3) :
      P k (r • θ.val) ∈ (vacuumCompactSmoothEmbeddedTarget a).carrierSet :=
    hProject _ (hTube (σ k) θ)
  let Qj (k : ℕ) := smoothVacuumSlice a r (P k) (hP k) (hTarget k)
  let hj (k : ℕ) := smoothVacuumSlice_mem a r (P k) (hP k) (hTarget k)
  refine ⟨Qj,hj,fun k => smoothVacuumSlice_smooth a r (P k) (hP k) (hTarget k) base,?_,?_⟩
  · have hRaw : Tendsto (fun k => eLpNorm (fun θ : UnitBoundarySphere 3 =>
        m' k (r • θ.val)-v θ) 2 μ) atTop (𝓝 0) :=
      hML.comp hσ.tendsto_atTop
    have ht := tendsto_sphere_values_after_projection
      (m := fun k θ => m' k (r • θ.val)) (v := v) hRaw hF hFD (fun θ => hFix _ (hV θ))
    have he (k : ℕ) (θ : UnitBoundarySphere 3) :
        frobeniusCoordinateEquiv (Qj k θ).val = F (m' k (r • θ.val)) :=
      smoothVacuumSlice_coord a r (P k) (hP k) (hTarget k) θ
    simpa only [he, v, e] using ht
  · apply tendsto_native_vacuumSphere_energy hQ hj
    let T (k : ℕ) (θ : UnitBoundarySphere 3) (i : Fin 3) :=
      r • coordinateDerivative (P k) (hP k) i (r • θ.val)
    have hTA (i : Fin 3) : (∀ k, MemLp (fun θ => T k θ i) 2 μ) ∧
        Tendsto (fun k => eLpNorm (fun θ => T k θ i-A θ i) 2 μ) atTop (𝓝 0) := by
      have hAfix := sphericalProjected_weakColumn_fixed hw hRay hD F hF hFD
        (fun θ => hFix _ (hV θ)) i
      exact projected_sphere_slice_column r m' hm' hVmem.aestronglyMeasurable
        (fun k => hM (σ k)) hσae (hA i) i (fun k => hZM (σ k) i)
        ((hZL i).comp hσ.tendsto_atTop) hF hFD hAfix
    exact tendsto_native_gradient_of_angular_columns hQ hj hA (fun k i => (hTA i).1 k)
      (fun i => (hTA i).2) hATan
      (fun k i => smoothVacuumSlice_grad a r (P k) (hP k) (hTarget k) i)
      (fun i => sphericalGradient_ae_eq_of_radial_columns hQ hw hRay hD i)

end Thesis
