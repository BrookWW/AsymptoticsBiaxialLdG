module

public import StratificationTheory.Foundation.SmoothDomainSobolevPullback
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import HarmonicMaps.Analysis.SobolevAECongruence
import HarmonicMaps.Analysis.RadialIntegrability
import HarmonicMaps.EnergyLemmas
import StratificationTheory.Foundation.SobolevLocalAssembly
import HarmonicMaps.Analysis.EuclideanHausdorffLipschitz

/-! Sobolev pullback of the actual ball graph by Lipschitz Euclidean coordinates. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ContDiff ENNReal NNReal Topology

namespace Thesis

private theorem norm_coordinate_single {m : ℕ} (i : Fin m) :
    ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
  simpa only [norm_one] using PiLp.norm_single 2 (fun _ : Fin m => ℝ) i (1 : ℝ)

private theorem lipschitz_fderiv_column_memLp_top {m q : ℕ} {F : Domain m → Ambient q} {K : ℝ≥0}
    (hF : LipschitzWith K F) (i : Fin m) (μ : Measure (Domain m)) :
    MemLp (fun x => fderiv ℝ F x (EuclideanSpace.single i 1)) ∞ μ := by
  apply memLp_top_of_bound
    (measurable_fderiv_apply_const ℝ F (EuclideanSpace.single i 1)).aestronglyMeasurable (K : ℝ)
  apply ae_of_all
  intro x
  refine ((fderiv ℝ F x).le_opNorm _).trans ?_
  rw [norm_coordinate_single, mul_one]
  exact norm_fderiv_le_of_lipschitz ℝ hF (x₀ := x)

private theorem lipschitz_fderiv_coordinate_memLp_top {m n : ℕ} {F : Domain m → Domain n} {K : ℝ≥0}
    (hF : LipschitzWith K F) (i : Fin m) (j : Fin n) (μ : Measure (Domain m)) :
    MemLp (fun x => (fderiv ℝ F x (EuclideanSpace.single i 1)) j) ∞ μ := by
  have hMeas : Measurable (fun x => (fderiv ℝ F x (EuclideanSpace.single i 1)) j) :=
    (EuclideanSpace.proj j).continuous.measurable.comp
      (measurable_fderiv_apply_const ℝ F (EuclideanSpace.single i 1))
  apply memLp_top_of_bound hMeas.aestronglyMeasurable (K : ℝ)
  apply ae_of_all
  intro x
  calc
    ‖(fderiv ℝ F x (EuclideanSpace.single i 1)) j‖ ≤ ‖fderiv ℝ F x (EuclideanSpace.single i 1)‖ :=
      PiLp.norm_apply_le _ j
    _ ≤ ‖fderiv ℝ F x‖ * ‖EuclideanSpace.single i 1‖ := (fderiv ℝ F x).le_opNorm _
    _ ≤ K := by
      rw [norm_coordinate_single, mul_one]
      exact norm_fderiv_le_of_lipschitz ℝ hF (x₀ := x)

/-- The almost-everywhere Fréchet columns of a Lipschitz function are its
distributional columns on every open subset. -/
theorem hasWeakGradient_of_lipschitz {m q : ℕ} (U : OpenDomain m)
    {F : Domain m → Ambient q} {K : ℝ≥0} (hF : LipschitzWith K F) :
    HasWeakGradient U F (fun x i => fderiv ℝ F x (EuclideanSpace.single i 1)) := by
  let D := fun (x : Domain m) (i : Fin m) => fderiv ℝ F x (EuclideanSpace.single i 1)
  have hFLoc : LocallyIntegrableOn F U.val volume := hF.continuous.locallyIntegrable.locallyIntegrableOn U.val
  have hDLoc (i : Fin m) : LocallyIntegrableOn (fun x => D x i) U.val volume :=
    ((lipschitz_fderiv_column_memLp_top hF i volume).locallyIntegrable le_top).locallyIntegrableOn U.val
  refine ⟨hFLoc, hDLoc, ?_⟩
  intro i φ hφ hCompact hSupport
  let e := EuclideanSpace.single i (1 : ℝ)
  have hDerivC : Continuous (coordinateDerivative φ hφ i) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDerivSupp : tsupport (coordinateDerivative φ hφ i) ⊆ U.val :=
    (tsupport_fderiv_apply_subset ℝ e).trans hSupport
  have hInt {w : Domain m → Ambient q} (hw : LocallyIntegrableOn w U.val volume)
      {ψ : Domain m → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U.val) :
      IntegrableOn (fun x => ψ x • w x) U.val := by
    have hWI := hw.integrableOn_compact_subset hs hc
    have hψL := hψ.memLp_top_of_hasCompactSupport hc (volume.restrict (tsupport ψ))
    have hPair : IntegrableOn (fun x => ψ x • w x) (tsupport ψ) := hWI.smul_of_top_right hψL
    have hSupp : Function.support (fun x => ψ x • w x) ⊆ tsupport ψ := by
      intro x hx
      by_contra hNot
      apply hx
      change ψ x • w x = 0
      rw [image_eq_zero_of_notMem_tsupport hNot, zero_smul]
    exact ((integrableOn_iff_integrable_of_support_subset hSupp).mp hPair).integrableOn
  have hL := hInt hFLoc hDerivC (hCompact.fderiv_apply ℝ e) hDerivSupp
  have hR := hInt (hDLoc i) hφ.continuous hCompact hSupport
  obtain ⟨Kφ, hφLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hCompact hφ (by simp)
  ext j
  rw [PiLp.neg_apply, eval_integral_piLp (fun k => hL.eval_piLp k), eval_integral_piLp (fun k => hR.eval_piLp k)]
  let d : Ambient q →L[ℝ] ℝ := EuclideanSpace.proj j
  let f : Domain m → ℝ := d ∘ F
  have hFLip := d.lipschitz.comp hF
  have hDerivF : (fun x => lineDeriv ℝ f x e) =ᵐ[volume] fun x => d (D x i) := by
    filter_upwards [hF.ae_differentiableAt (μ := (volume : Measure (Domain m)))] with x hx
    exact ((d.hasFDerivAt.comp x hx.hasFDerivAt).hasLineDerivAt e).lineDeriv
  have hDerivφ (x : Domain m) : lineDeriv ℝ φ x (-e) = -coordinateDerivative φ hφ i x := by
    rw [((hφ.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt (-e)).lineDeriv, map_neg]
    rfl
  have hIBP := hFLip.integral_lineDeriv_mul_eq (μ := (volume : Measure (Domain m))) hφLip hCompact e
  have hIBP' : (∫ x, φ x * d (D x i)) = -(∫ x, coordinateDerivative φ hφ i x * f x) := by
    calc
      _ = ∫ x, lineDeriv ℝ f x e * φ x := by
        apply integral_congr_ae
        filter_upwards [hDerivF] with x hx
        rw [hx, mul_comm]
      _ = ∫ x, lineDeriv ℝ φ x (-e) * f x := hIBP
      _ = _ := by simp_rw [hDerivφ, neg_mul, integral_neg]
  change (∫ x in U.val, coordinateDerivative φ hφ i x * f x) = -(∫ x in U.val, φ x * d (D x i))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hDerivSupp h)), zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hSupport h)), zero_mul]), hIBP', neg_neg]

private theorem fderiv_coordinate_sum {m q : ℕ} {f : Domain m → Ambient q}
    (hf : ContDiff ℝ ∞ f) (x v : Domain m) :
    fderiv ℝ f x v = ∑ j : Fin m, v j • coordinateDerivative f hf j x := by
  have hv : (∑ j : Fin m, v j • EuclideanSpace.single j 1) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
  calc
    _ = fderiv ℝ f x (∑ j : Fin m, v j • EuclideanSpace.single j 1) := congrArg _ hv.symm
    _ = _ := by simp only [map_sum, map_smul, coordinateDerivative]

private theorem hasWeakGradient_lipschitz_comp_smooth_ball {m n q : ℕ} (U : OpenDomain m)
    {F : Domain m → Domain n} {K : ℝ≥0} (hF : LipschitzWith K F) {z : Domain n} {R : ℝ}
    (hR : 0 < R) (hMap : MapsTo F U.val (ball z R)) {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) :
    HasWeakGradient U (f ∘ F) (fun x i => ∑ j : Fin n,
      (fderiv ℝ F x (EuclideanSpace.single i 1)) j • coordinateDerivative f hf j (F x)) := by
  let χ : ContDiffBump z := ⟨R, R + 1, hR, by linarith⟩
  let g : Domain n → Ambient q := fun y => χ y • f y
  have hg : ContDiff ℝ ∞ g := χ.contDiff.smul hf
  have hCG : HasCompactSupport g := χ.hasCompactSupport.smul_right
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hCG hg (by simp)
  have hgf : EqOn g f (ball z R) := fun y hy => by
    change χ y • f y = f y
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_smul]
  have hValues : g ∘ F =ᵐ[volume.restrict U.val] f ∘ F := by
    filter_upwards [ae_restrict_mem U.property.measurableSet] with x hx
    exact hgf (hMap hx)
  apply (hasWeakGradient_of_lipschitz U (hLip.comp hF)).congr_ae hValues
  filter_upwards [ae_restrict_of_ae (hF.ae_differentiableAt (μ := (volume : Measure (Domain m)))),
    ae_restrict_mem U.property.measurableSet] with x hx hxU
  funext i
  have hEq : g =ᶠ[𝓝 (F x)] f := Filter.mem_of_superset (isOpen_ball.mem_nhds (hMap hxU)) hgf
  have hDg : fderiv ℝ g (F x) = fderiv ℝ f (F x) := hEq.fderiv_eq
  rw [((hg.differentiable (by simp) (F x)).hasFDerivAt.comp x hx.hasFDerivAt).fderiv,
    ContinuousLinearMap.comp_apply, hDg]
  exact fderiv_coordinate_sum hf (F x) _

/-- A globally Lipschitz map into a ball with dominated pushforward volume
pulls back the original Sobolev graph by its almost-everywhere chain rule. -/
theorem memW12_lipschitz_domain_pullback_ball {m n q : ℕ} {z : Domain n} {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain z R) u Du)
    (U : OpenDomain m) (hfinite : (volume : Measure (Domain m)) U.val ≠ ⊤)
    (F : Domain m → Domain n) {K : ℝ≥0} (hF : LipschitzWith K F) (hInto : MapsTo F U.val (ball z R))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hmap : Measure.map F (volume.restrict U.val) ≤ c • volume.restrict (ball z R)) :
    MemW12 U (u ∘ F) (fun x i => ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • Du (F x) j) := by
  let μ : Measure (Domain m) := volume.restrict U.val
  let ν : Measure (Domain n) := volume.restrict (ball z R)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hfinite
  have hFm : AEMeasurable F μ := hF.continuous.measurable.aemeasurable
  let a (i : Fin m) (j : Fin n) (x : Domain m) := (fderiv ℝ F x (EuclideanSpace.single i 1)) j
  have ha (i : Fin m) (j : Fin n) : MemLp (a i j) ∞ μ := lipschitz_fderiv_coordinate_memLp_top hF i j μ
  have hcomp {f : Domain n → Ambient q} (hf : MemLp f 2 ν) : MemLp (f ∘ F) 2 μ :=
    memLp_comp_of_map_le_smul hFm hc hmap hf
  have hcolumns {D : Domain n → Gradient n q} (hD : ∀ j, MemLp (fun y => D y j) 2 ν) (i : Fin m) :
      MemLp (fun x => ∑ j : Fin n, a i j x • D (F x) j) 2 μ := by
    have hL := memLp_finsetSum Finset.univ
      (fun j _ => (hcomp (hD j)).smul (r := (2 : ℝ≥0∞)) (ha i j))
    simpa only [Finset.sum_apply, Pi.smul_apply', Function.comp_def] using hL
  obtain ⟨f, hf, hfW, hfconv, hDfconv⟩ := hu.smoothDensity_memW12_ball hR
  let Df (k : ℕ) (x : Domain m) (i : Fin m) :=
    ∑ j : Fin n, a i j x • coordinateDerivative (f k) (hf k) j (F x)
  have hW (k : ℕ) : MemW12 U (f k ∘ F) (Df k) :=
    ⟨hasWeakGradient_lipschitz_comp_smooth_ball U hF hR hInto (hf k), hcomp (hfW k).2.1,
      fun i => hcolumns (D := fun y j => coordinateDerivative (f k) (hf k) j y) (hfW k).2.2 i⟩
  apply MemW12.of_L2_limit (Df := Df) (Du := fun x i => ∑ j : Fin n, a i j x • Du (F x) j)
    hW (hcomp hu.2.1) (hcolumns (D := Du) hu.2.2)
  · exact tendsto_eLpNorm_comp_zero_of_map_le_smul hFm hc hmap (p := 2) (f := fun k => f k - u)
      (fun k => ((hfW k).2.1.sub hu.2.1).aestronglyMeasurable) hfconv
  · intro i
    let d (k : ℕ) (j : Fin n) (x : Domain m) := coordinateDerivative (f k) (hf k) j (F x) - Du (F x) j
    have hd (k : ℕ) (j : Fin n) : MemLp (d k j) 2 μ := hcomp ((hfW k).2.2 j |>.sub (hu.2.2 j))
    have hcol (j : Fin n) : Tendsto (fun k => eLpNorm (fun x => a i j x • d k j x) 2 μ) atTop (𝓝 0) := by
      have hconv : Tendsto (fun k => eLpNorm (d k j) 2 μ) atTop (𝓝 0) :=
        tendsto_eLpNorm_comp_zero_of_map_le_smul hFm hc hmap (p := 2)
          (f := fun k y => coordinateDerivative (f k) (hf k) j y - Du y j)
          (fun k => ((hfW k).2.2 j |>.sub (hu.2.2 j)).aestronglyMeasurable) (hDfconv j)
      exact tendsto_eLpNorm_two_bounded_smul_zero (ha i j) (fun k => (hd k j).aestronglyMeasurable) hconv
    have hsum := tendsto_eLpNorm_two_finite_sum_zero
      (fun j k => ((hd k j).smul (r := (2 : ℝ≥0∞)) (ha i j)).aestronglyMeasurable) hcol
    have heq (k : ℕ) : (fun x => Df k x i - ∑ j : Fin n, a i j x • Du (F x) j) =
        fun x => ∑ j : Fin n, a i j x • d k j x := by
      funext x
      simp only [Df, d, smul_sub, Finset.sum_sub_distrib]
    simpa only [heq, Pi.smul_apply', Function.comp_def, Pi.sub_apply] using hsum

/-- The unhalved weak Dirichlet energy of the pulled-back columns is bounded
by the differential norm, source dimension and native volume distortion. -/
theorem dirichletEnergy_lipschitz_pullback_le {m n q : ℕ} (U : Set (Domain m)) (V : Set (Domain n))
    (F : Domain m → Domain n) {K : ℝ≥0} (hF : LipschitzWith K F)
    {c : ℝ≥0∞} (hmap : Measure.map F (volume.restrict U) ≤ c • volume.restrict V)
    (D : Domain n → Gradient n q) (hD : ∀ j, MemLp (fun y => D y j) 2 (volume.restrict V)) :
    let G (x : Domain m) (i : Fin m) := ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • D (F x) j
    HarmonicMaps.dirichletEnergy G U ≤ ENNReal.ofReal ((m : ℝ) * (K : ℝ) ^ 2) * (c * HarmonicMaps.dirichletEnergy D V) := by
  intro G
  have hG (x : Domain m) : hsNormSq (G x) ≤ ((m : ℝ) * (K : ℝ) ^ 2) * hsNormSq (D (F x)) := by
    have hI (i : Fin m) : ‖G x i‖ ^ 2 ≤ (K : ℝ) ^ 2 * hsNormSq (D (F x)) := by
      let v := fderiv ℝ F x (EuclideanSpace.single i 1)
      have h := norm_sq_sum_gradient_le (D (F x)) v
      have hV : ‖v‖ ≤ K := by
        apply ((fderiv ℝ F x).le_opNorm _).trans
        rw [norm_coordinate_single, mul_one]
        exact norm_fderiv_le_of_lipschitz ℝ hF (x₀ := x)
      exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hV 2) (hsNormSq_nonneg _))
    calc
      _ ≤ ∑ _ : Fin m, (K : ℝ) ^ 2 * hsNormSq (D (F x)) := Finset.sum_le_sum (fun i _ => hI i)
      _ = _ := by simp [nsmul_eq_mul, mul_assoc]
  let p (y : Domain n) := ENNReal.ofReal (hsNormSq (D y))
  have hp : AEMeasurable p (volume.restrict V) := ENNReal.measurable_ofReal.comp_aemeasurable
    (integrable_hsNormSq_of_memLp_columns hD).aestronglyMeasurable.aemeasurable
  have hpMap : AEMeasurable p (Measure.map F (volume.restrict U)) := (hp.smul_measure (c := c)).mono_measure hmap
  let B := ENNReal.ofReal ((m : ℝ) * (K : ℝ) ^ 2)
  have hB : B ≠ ⊤ := ENNReal.ofReal_ne_top
  change (∫⁻ x in U, ENNReal.ofReal (hsNormSq (G x))) ≤ B * (c * ∫⁻ y in V, p y)
  calc
    _ ≤ ∫⁻ x in U, B * p (F x) := lintegral_mono fun x => by
      have hx := ENNReal.ofReal_le_ofReal (hG x)
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (m : ℝ) * (K : ℝ) ^ 2)] at hx
      exact hx
    _ = B * (∫⁻ y, p y ∂Measure.map F (volume.restrict U)) := by
      rw [lintegral_const_mul' _ _ hB, lintegral_map' hpMap hF.continuous.measurable.aemeasurable]
    _ ≤ _ := by
      apply mul_le_mul_right
      exact (lintegral_mono' hmap le_rfl).trans_eq (lintegral_smul_measure _ _)

/-- The inverse Lipschitz constant controls actual Euclidean pushforward volume. -/
theorem map_lipschitzHomeomorph_preimage_volume_le {n : ℕ} (F : Domain n ≃ₜ Domain n) {L : ℝ≥0}
    (hL : LipschitzWith L (F.symm : Domain n → Domain n)) (V : Set (Domain n)) :
    Measure.map F (volume.restrict (F ⁻¹' V)) ≤ (L : ℝ≥0∞) ^ n • volume.restrict V := by
  have hEmb : MeasurableEmbedding F := F.isClosedEmbedding.measurableEmbedding
  have hFull : Measure.map F (volume : Measure (Domain n)) ≤ (L : ℝ≥0∞) ^ n • volume := by
    apply Measure.le_iff.2
    intro S hS
    rw [Measure.map_apply hEmb.measurable hS, ← F.image_symm]
    have h := euclideanHausdorff_lipschitzOn_image_le_volume (hL.lipschitzOnWith (s := univ)) (subset_univ S)
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume, finrank_euclideanSpace_fin] at h
    exact h
  rw [← hEmb.restrict_map, ← Measure.restrict_smul]
  exact Measure.restrict_mono_measure hFull _

private theorem memW12_lipschitz_homeomorph_preimage_ball {n q : ℕ} (F : Domain n ≃ₜ Domain n) {K L : ℝ≥0}
    (hF : LipschitzWith K (F : Domain n → Domain n)) (hL : LipschitzWith L (F.symm : Domain n → Domain n))
    {z : Domain n} {r : ℝ} (hr : 0 < r) {u : Domain n → Ambient q} {D : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain z r) u D) :
    let T : OpenDomain n := ⟨F ⁻¹' ball z r, isOpen_ball.preimage F.continuous⟩
    MemW12 T (u ∘ F) (fun x i => ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • D (F x) j) := by
  intro T
  have hSub : T.val ⊆ ball (F.symm z) ((L : ℝ) * r + 1) := by
    intro x hx
    have hDist := hL.dist_le_mul (F x) z
    rw [F.symm_apply_apply] at hDist
    have hx' : dist (F x) z < r := hx
    exact mem_ball.2 ((hDist.trans (mul_le_mul_of_nonneg_left hx'.le L.coe_nonneg)).trans_lt (lt_add_one _))
  have hVol : (volume : Measure (Domain n)) T.val ≠ ⊤ := ne_top_of_le_ne_top measure_ball_ne_top (measure_mono hSub)
  exact memW12_lipschitz_domain_pullback_ball hr hu T hVol F hF (fun _ hx => hx)
    (ENNReal.pow_ne_top ENNReal.coe_ne_top) (map_lipschitzHomeomorph_preimage_volume_le F hL (ball z r))

private theorem memW12_lipschitz_homeomorph_preimage_of_L2 {n q : ℕ}
    (F : Domain n ≃ₜ Domain n) {K L : ℝ≥0}
    (hF : LipschitzWith K (F : Domain n → Domain n)) (hL : LipschitzWith L (F.symm : Domain n → Domain n))
    {V : OpenDomain n} {u : Domain n → Ambient q} {D : Domain n → Gradient n q} (hu : MemW12 V u D) :
    let U : OpenDomain n := ⟨F ⁻¹' V.val, V.property.preimage F.continuous⟩
    let G := fun (x : Domain n) (i : Fin n) =>
      ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • D (F x) j
    MemLp (u ∘ F) 2 (volume.restrict U.val) →
    (∀ i, MemLp (fun x => G x i) 2 (volume.restrict U.val)) →
    MemW12 U (u ∘ F) G := by
  intro U G hUL hGL
  refine memW12_of_local_sobolev_pair (Ω := U) hUL hGL ?_
  intro x hx
  have hxV : F x ∈ V.val := hx
  obtain ⟨r, hr, hRV⟩ := Metric.isOpen_iff.mp V.property (F x) hxV
  let T : OpenDomain n := ⟨F ⁻¹' ball (F x) r, isOpen_ball.preimage F.continuous⟩
  have huB : MemW12 (ballDomain (F x) r) u D := ⟨hu.1.mono hRV,
    hu.2.1.mono_measure (Measure.restrict_mono_set volume hRV),
    fun i => (hu.2.2 i).mono_measure (Measure.restrict_mono_set volume hRV)⟩
  have hwT : MemW12 T (u ∘ F) G := memW12_lipschitz_homeomorph_preimage_ball F hF hL hr huB
  have hxT : x ∈ T.val := by
    change F x ∈ ball (F x) r
    exact mem_ball_self hr
  obtain ⟨s, hs, hST⟩ := Metric.isOpen_iff.mp T.property x hxT
  have hSU : ball x s ⊆ U.val := fun y hy => hRV (hST hy)
  refine ⟨s, hs, hSU, hwT.1.mono hST, hwT.2.1.mono_measure (Measure.restrict_mono_set volume hST), ?_⟩
  exact fun i => (hwT.2.2 i).mono_measure (Measure.restrict_mono_set volume hST)

/-- A bi-Lipschitz Euclidean homeomorphism pulls back the same weak graph on
every open set, with the actual chain-rule columns. -/
theorem memW12_lipschitz_homeomorph_preimage {n q : ℕ} (F : Domain n ≃ₜ Domain n) {K L : ℝ≥0}
    (hF : LipschitzWith K (F : Domain n → Domain n)) (hL : LipschitzWith L (F.symm : Domain n → Domain n))
    (V : OpenDomain n) (u : Domain n → Ambient q) (D : Domain n → Gradient n q) (hu : MemW12 V u D) :
    MemW12 ⟨F ⁻¹' V.val, V.property.preimage F.continuous⟩ (u ∘ F)
      (fun x i => ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • D (F x) j) := by
  let μ := (volume : Measure (Domain n)).restrict (F ⁻¹' V.val)
  let ν := (volume : Measure (Domain n)).restrict V.val
  let c : ℝ≥0∞ := (L : ℝ≥0∞) ^ n
  have hc : c ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hMap : Measure.map F μ ≤ c • ν := map_lipschitzHomeomorph_preimage_volume_le F hL V.val
  have hComp {f : Domain n → Ambient q} (hf : MemLp f 2 ν) : MemLp (f ∘ F) 2 μ :=
    memLp_comp_of_map_le_smul F.continuous.measurable.aemeasurable hc hMap hf
  apply memW12_lipschitz_homeomorph_preimage_of_L2 F hF hL hu (hComp hu.2.1)
  intro i
  let a (j : Fin n) (x : Domain n) := (fderiv ℝ F x (EuclideanSpace.single i 1)) j
  have hCol (j : Fin n) : MemLp (fun x => a j x • D (F x) j) 2 μ :=
    (hComp (hu.2.2 j)).smul (r := (2 : ℝ≥0∞)) (lipschitz_fderiv_coordinate_memLp_top hF i j μ)
  have hSum := memLp_finsetSum Finset.univ (fun j (_ : j ∈ Finset.univ) => hCol j)
  simpa only [a, Finset.sum_apply] using hSum

/-- Strong convergence of the original derivative columns persists under
the actual Lipschitz chain rule and dominated volume pullback. -/
theorem tendsto_eLpNorm_lipschitz_pullback_columns {m n q : ℕ}
    {μ : Measure (Domain m)} {ν : Measure (Domain n)}
    (F : Domain m → Domain n) {K : ℝ≥0} (hF : LipschitzWith K F)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hMap : Measure.map F μ ≤ c • ν)
    (D : ℕ → Domain n → Gradient n q) (J : Domain n → Gradient n q)
    (hD : ∀ k i, MemLp (fun x => D k x i) 2 ν) (hJ : ∀ i, MemLp (fun x => J x i) 2 ν)
    (hConverges : ∀ i, Tendsto (fun k => eLpNorm (fun x => D k x i - J x i) 2 ν) atTop (𝓝 0))
    (i : Fin m) :
    Tendsto (fun k => eLpNorm (fun x =>
      (∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • D k (F x) j) -
      ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • J (F x) j) 2 μ) atTop (𝓝 0) := by
  let a (j : Fin n) (x : Domain m) := (fderiv ℝ F x (EuclideanSpace.single i 1)) j
  let w (j : Fin n) (k : ℕ) (x : Domain m) := D k (F x) j - J (F x) j
  have hM : AEMeasurable F μ := hF.continuous.measurable.aemeasurable
  have ha (j : Fin n) : MemLp (a j) ⊤ μ := lipschitz_fderiv_coordinate_memLp_top hF i j μ
  have hw (j : Fin n) (k : ℕ) : MemLp (w j k) 2 μ :=
    memLp_comp_of_map_le_smul hM hc hMap ((hD k j).sub (hJ j))
  have hC (j : Fin n) : Tendsto (fun k => eLpNorm (fun x => a j x • w j k x) 2 μ) atTop (𝓝 0) := by
    have h := tendsto_eLpNorm_comp_zero_of_map_le_smul hM hc hMap (p := 2) (f := fun k x => D k x j - J x j)
      (fun k => ((hD k j).sub (hJ j)).aestronglyMeasurable) (hConverges j)
    exact tendsto_eLpNorm_two_bounded_smul_zero (ha j) (fun k => (hw j k).aestronglyMeasurable) h
  have h := tendsto_eLpNorm_two_finite_sum_zero
    (fun j k => ((hw j k).smul (r := 2) (ha j)).aestronglyMeasurable) hC
  have hDiff (k : ℕ) : (fun x => (∑ j : Fin n, a j x • D k (F x) j) - ∑ j : Fin n, a j x • J (F x) j) =
      fun x => ∑ j : Fin n, a j x • w j k x := by
    funext x
    simp only [w, smul_sub, Finset.sum_sub_distrib]
  change Tendsto (fun k => eLpNorm (fun x => (∑ j : Fin n, a j x • D k (F x) j) -
    ∑ j : Fin n, a j x • J (F x) j) 2 μ) atTop (𝓝 0)
  simpa only [hDiff, Pi.smul_apply', Finset.sum_apply] using h

/-- A smooth map on the ambient space has a compactly supported smooth
Lipschitz representative on each closed ball, with its interior columns. -/
theorem exists_smooth_lipschitz_agreeOn_closedBall {n q : ℕ} (z : Domain n) {R : ℝ} (hR : 0 < R)
    (u : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u) :
    ∃ f : Domain n → Ambient q, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ EqOn f u (closedBall z R) ∧
      ∃ K : ℝ≥0, LipschitzWith K f := by
  let χ : ContDiffBump z := ⟨R, R + 1, hR, by linarith⟩
  let f (x : Domain n) := χ x • u x
  have hf := χ.contDiff.smul hu
  have hc : HasCompactSupport f := χ.hasCompactSupport.smul_right
  refine ⟨f, hf, hc, ?_, hf.lipschitzWith_of_hasCompactSupport hc (by simp)⟩
  intro x hx
  dsimp only [f]
  rw [χ.one_of_mem_closedBall hx, one_smul]

end Thesis

end
