module

public import Thesis.Interpolation.PlanarPairContinuousExterior
import Thesis.Foundation.VacuumCoordinateRetraction
import StratificationTheory.Foundation.SphereGradientData
import StratificationTheory.Foundation.CompactSobolevCutoff
import StratificationTheory.Foundation.CylinderPostcomposition
import HarmonicMaps.Analysis.AffineBallSobolev
import HarmonicMaps.Analysis.DirichletSmoothData
import HarmonicMaps.Analysis.SobolevAECongruence

/-! The original Sobolev collars retained by smoothing the reference exterior. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff Convolution ENNReal Topology Matrix.Norms.Frobenius

namespace Thesis

private theorem finiteSobolev_add {n q : ℕ} {U : OpenDomain n}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → HarmonicMaps.Gradient n q}
    (hu : MemW12 U u Du) (hv : MemW12 U v Dv) :
    MemW12 U (u+v) (fun x i => Du x i+Dv x i) := by
  refine ⟨⟨hu.1.1.add hv.1.1,fun i => (hu.1.2.1 i).add (hv.1.2.1 i),?_⟩,
    hu.2.1.add hv.2.1,fun i => (hu.2.2 i).add (hv.2.2 i)⟩
  intro i φ hφ hc hs
  simp only [Pi.add_apply,smul_add]
  rw [integral_add (hu.1.integrable_test_derivative i hφ hc hs) (hv.1.integrable_test_derivative i hφ hc hs),
    integral_add (hu.1.integrable_test_gradient i hφ hc hs) (hv.1.integrable_test_gradient i hφ hc hs),
    hu.1.2.2 i φ hφ hc hs,hv.1.2.2 i φ hφ hc hs]
  abel

private theorem finiteSobolev_restrict {n q : ℕ} {U V : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → HarmonicMaps.Gradient n q}
    (hu : MemW12 U u Du) (h : V.val ⊆ U.val) : MemW12 V u Du :=
  ⟨hu.1.mono h,hu.2.1.mono_measure (Measure.restrict_mono_set _ h),
    fun i => (hu.2.2 i).mono_measure (Measure.restrict_mono_set _ h)⟩

private theorem bump_eq_zero_of_outside {c : Plane} (χ : ContDiffBump c) {x : Plane}
    (hx : χ.rOut ≤ dist x c) : χ x = 0 := by
  apply Function.notMem_support.mp
  rw [χ.support_eq,mem_ball]
  exact not_lt.mpr hx

private theorem exists_radial_exterior_cutoff {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    ∃ χ : Plane → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ ({0}ᶜ : Set Plane) ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, ‖x‖ ∈ Icc b c → χ x = 1) ∧
      (∀ x, ‖x‖ ≤ a ∨ d ≤ ‖x‖ → χ x = 0) := by
  let low : ContDiffBump (0 : Plane) := ⟨a,b,ha,hab⟩
  let high : ContDiffBump (0 : Plane) := ⟨c,d,(ha.trans hab).trans_le hbc,hcd⟩
  let χ (x : Plane) := (1-low x)*high x
  have hχ : ContDiff ℝ ∞ χ := (contDiff_const.sub (low.contDiff (n := ⊤))).mul high.contDiff
  have hc : HasCompactSupport χ := high.hasCompactSupport.mul_left
  have hZero (x : Plane) (hx : ‖x‖ ≤ a ∨ d ≤ ‖x‖) : χ x = 0 := by
    rcases hx with h | h
    · have hL : low x = 1 := low.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr h)
      change (1-low x)*high x = 0
      rw [hL,sub_self,zero_mul]
    · have hH : high x = 0 := bump_eq_zero_of_outside high (by rwa [dist_zero_right])
      change (1-low x)*high x = 0
      rw [hH,mul_zero]
  have hSup : tsupport χ ⊆ {x : Plane | a ≤ ‖x‖} := closure_minimal
    (fun x hx => le_of_not_gt (fun h => hx (hZero x (Or.inl h.le))))
    (isClosed_le continuous_const continuous_norm)
  have hAway : tsupport χ ⊆ ({0}ᶜ : Set Plane) := by
    intro x hx h0
    have h := hSup hx
    change a ≤ ‖x‖ at h
    rw [mem_singleton_iff.mp h0,norm_zero] at h
    exact ha.not_ge h
  refine ⟨χ,hχ,hc,hAway,?_,?_,hZero⟩
  · intro x
    have hL : 0 ≤ 1-low x := sub_nonneg.mpr low.le_one
    have hL' : 1-low x ≤ 1 := sub_le_self _ low.nonneg
    change 0 ≤ (1-low x)*high x ∧ (1-low x)*high x ≤ 1
    exact ⟨mul_nonneg hL high.nonneg,
      (mul_le_mul hL' high.le_one high.nonneg zero_le_one).trans_eq (one_mul _)⟩
  · intro x hx
    have hL : low x = 0 := bump_eq_zero_of_outside low (by rw [dist_zero_right]; exact hx.1)
    have hU : high x = 1 := high.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hx.2)
    change (1-low x)*high x = 1
    rw [hL,hU,sub_zero,one_mul]

private theorem planarPairAmbientRadial (a : BulkCoefficients) (b : C(NativeCircle,vacuum a))
    (hb : MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (b θ).val))
    (c : Plane) (χ : Plane → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hSup : tsupport χ ⊆ ({0}ᶜ : Set Plane)) :
    ∃ D : Plane → HarmonicMaps.Gradient 2 5,
      MemW12 (ballDomain (0 : Plane) 1)
        (fun x => χ (x-c) • frobeniusCoordinateEquiv
          (b (sphereRadialDirection nativeCircleLoopBase (x-c))).val) D := by
  obtain ⟨w,D,J,hW,hRay,_,_,_⟩ := exists_sphere_radial_weak_gradient_data (le_refl 2) hb
  have hInit := hW.smoothCutoff_univ hχ hc hSup
  have hTrans := (finiteSobolev_restrict hInit (show (ballDomain (-c) 1).val ⊆ univ from subset_univ _)).translate_ball 0
  refine ⟨_,hTrans.congr_ae ?_ EventuallyEq.rfl⟩
  apply Eventually.of_forall
  intro x
  have hSh : -c+(x-0) = x-c := by abel
  change χ (-c+(x-0)) • w (-c+(x-0)) =
    χ (x-c) • frobeniusCoordinateEquiv (b (sphereRadialDirection nativeCircleLoopBase (x-c))).val
  rw [hSh]
  by_cases hx : x-c = 0
  · have hχ₀ : χ (x-c) = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hSup h) hx)
    simp only [hχ₀,zero_smul]
  let z := sphereRadialDirection nativeCircleLoopBase (x-c)
  have hR : 0 < ‖x-c‖ := norm_pos_iff.mpr hx
  have hZ : ‖x-c‖ • z.val = x-c := by
    change ‖x-c‖ • (sphereRadialDirection nativeCircleLoopBase (x-c)).val = _
    rw [sphereRadialDirection,dif_pos hx]
    exact NormedSpace.norm_smul_normalize (x-c)
  have hV : w (x-c) = frobeniusCoordinateEquiv (b z).val :=
    (congrArg w hZ).symm.trans (hRay ⟨‖x-c‖,hR⟩ z)
  exact congrArg (fun u : Ambient 5 => χ (x-c) • u) hV


private theorem planarPairExterior_subset_centersCompl :
    planarPairExteriorDomain.val ⊆ planarPairCentersCompl := by
  intro x hx
  change ∀ i : Fin 2, x ≠ planarPairCoreCenter i
  intro i h
  have hd := mem_iInter.mp hx.2 i
  change 3/16 < dist x (planarPairCoreCenter i) at hd
  rw [h,dist_self] at hd
  norm_num at hd

private theorem exists_planarPairSmoothApprox
    (a : BulkCoefficients) {p : Plane → vacuum a} (hp : ContinuousOn p planarPairCentersCompl)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : Plane → Ambient 5, ContDiff ℝ ∞ u ∧
      ∀ x ∈ planarPairExteriorDomain.val, dist (u x) (frobeniusCoordinateEquiv (p x).val) ≤ δ := by
  let small (i : Fin 2) : ContDiffBump (planarPairCoreCenter i) :=
    ⟨1/16,1/8,by norm_num,by norm_num⟩
  let big : ContDiffBump (0 : Plane) := ⟨1,2,by norm_num,by norm_num⟩
  let χ (x : Plane) := big x*(1-small 0 x)*(1-small 1 x)
  let f (x : Plane) := χ x • frobeniusCoordinateEquiv (p x).val
  have hχ : Continuous χ :=
    (big.continuous.mul (continuous_const.sub (small 0).continuous)).mul
      (continuous_const.sub (small 1).continuous)
  have hχc : HasCompactSupport χ := big.hasCompactSupport.mul_right.mul_right
  have hfc : HasCompactSupport f := hχc.smul_right
  have hOpen : IsOpen planarPairCentersCompl := by
    have hSet : planarPairCentersCompl = ⋂ i : Fin 2, ({planarPairCoreCenter i} : Set Plane)ᶜ := by
      ext x
      simp [planarPairCentersCompl]
    rw [hSet]
    exact isOpen_iInter_of_finite (fun i : Fin 2 => isOpen_compl_singleton (x := planarPairCoreCenter i))
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ planarPairCentersCompl
    · have hP : ContinuousOn (fun x => frobeniusCoordinateEquiv (p x).val) planarPairCentersCompl :=
        (frobeniusCoordinateEquiv.continuous.comp
          (continuous_subtype_val : Continuous (fun p : vacuum a => p.val))).comp_continuousOn hp
      exact hχ.continuousAt.smul (hP.continuousAt (hOpen.mem_nhds hx))
    · have h : ∃ i : Fin 2, x = planarPairCoreCenter i := by
        by_contra! h
        exact hx h
      obtain ⟨i, rfl⟩ := h
      have hZero : f =ᶠ[𝓝 (planarPairCoreCenter i)] fun _ => (0 : Ambient 5) := by
        filter_upwards [ball_mem_nhds (planarPairCoreCenter i) (by norm_num : 0 < (1/16 : ℝ))] with y hy
        have hB : small i y = 1 := (small i).one_of_mem_closedBall (ball_subset_closedBall hy)
        have hI : i = 0 ∨ i = 1 := by fin_cases i <;> decide
        rcases hI with rfl | rfl
        · simp only [f,χ,hB,sub_self,mul_zero,zero_mul,zero_smul]
        · simp only [f,χ,hB,sub_self,mul_zero,zero_smul]
      exact continuousAt_const.congr_of_eventuallyEq hZero
  have hfRaw (x : Plane) (hx : x ∈ planarPairExteriorDomain.val) :
      f x = frobeniusCoordinateEquiv (p x).val := by
    have h0 : big x = 1 := big.one_of_mem_closedBall (ball_subset_closedBall hx.1)
    have hs (i : Fin 2) : small i x = 0 := by
      have hh := mem_iInter.mp hx.2 i
      exact bump_eq_zero_of_outside (small i) ((by norm_num : (1/8 : ℝ) < 3/16).le.trans (show
        3/16 < dist x (planarPairCoreCenter i) from hh).le)
    simp only [f,χ,h0,hs,sub_zero,mul_one,one_smul]
  obtain ⟨e,he,hclose⟩ := Metric.uniformContinuous_iff.mp
    (hfc.uniformContinuous_of_continuous hf) δ hδ
  let k : ContDiffBump (0 : Plane) := ⟨e/2,e,half_pos he,half_lt_self he⟩
  let L : ℝ →L[ℝ] Ambient 5 →L[ℝ] Ambient 5 := ContinuousLinearMap.lsmul ℝ ℝ
  let u := k.normed volume ⋆[L,volume] f
  have hu : ContDiff ℝ ∞ u := k.hasCompactSupport_normed.contDiff_convolution_left L
    (k.contDiff_normed (n := ⊤)) hf.locallyIntegrable
  refine ⟨u,hu,fun x hx => ?_⟩
  rw [← hfRaw x hx]
  apply ContDiffBump.dist_normed_convolution_le hf.aestronglyMeasurable
  intro y hy
  exact (hclose (mem_ball.mp hy)).le

private theorem planarPairCenters_distance :
    dist (planarPairCoreCenter 0) (planarPairCoreCenter 1) = 1 := by
  have h : planarPairCoreCenter 0-planarPairCoreCenter 1 = EuclideanSpace.single 0 (-1) := by
    apply PiLp.ext
    intro j
    fin_cases j <;> norm_num [planarPairCoreCenter,PiLp.sub_apply,PiLp.single_apply]
  rw [dist_eq_norm,h,PiLp.norm_single]
  norm_num

private theorem planarPair_normalized_ray {x : Plane} (hx : x ≠ 0) :
    ‖x‖ • (sphereRadialDirection nativeCircleLoopBase x).val = x := by
  rw [sphereRadialDirection,dif_pos hx]
  exact NormedSpace.norm_smul_normalize x

/-- For the actual vacuum target, the fixed punctured disk admits the
required Sobolev exterior with its original three collars. -/
theorem exists_planarPairExterior_of_vacuum_words
    (a : BulkCoefficients) (A : vacuum a)
    (outer : C(NativeCircle,vacuum a)) (inner : Fin 2 → C(NativeCircle,vacuum a))
    (h₀ : A = outer nativeCircleLoopBase) (hᵢ : ∀ i, A = inner i nativeCircleLoopBase)
    (hOuterSob : MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (outer θ).val))
    (hInnerSob : ∀ i, MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (inner i θ).val))
    (hWord : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop outer).cast h₀ h₀)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop (inner 0)).cast (hᵢ 0) (hᵢ 0))) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop (inner 1)).cast (hᵢ 1) (hᵢ 1)))) :
    Nonempty (PlanarPairExterior a outer inner) := by
  obtain ⟨p,hp,hInner,hOuter⟩ := exists_planarPairContinuousExterior a A outer inner h₀ hᵢ hWord
  obtain ⟨ρ,hρ,Q,C,hQ,hQD,hFix,hNear⟩ := exists_smooth_vacuumCoordinate_retraction a
  obtain ⟨m,hm,hmNear⟩ := exists_planarPairSmoothApprox a hp (half_pos hρ)
  obtain ⟨χ,hχ,hχc,hχSup,hχRange,hχOne,hχZero⟩ :=
    exists_radial_exterior_cutoff (a := 1/8) (b := 3/16) (c := 1/4) (d := 9/32)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨η,hη,hηc,hηSup,hηRange,hηOne,hηZero⟩ :=
    exists_radial_exterior_cutoff (a := 27/32) (b := 7/8) (c := 1) (d := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let E (x : Plane) := frobeniusCoordinateEquiv (p x).val
  let ci (i : Fin 2) (x : Plane) := χ (x-planarPairCoreCenter i)
  let ηi (x : Plane) := η x
  let ξ (x : Plane) := ηi x+ci 0 x+ci 1 x
  let U (i : Fin 2) (x : Plane) := ci i x • frobeniusCoordinateEquiv
    (inner i (sphereRadialDirection nativeCircleLoopBase (x-planarPairCoreCenter i))).val
  let O (x : Plane) := ηi x • frobeniusCoordinateEquiv (outer (sphereRadialDirection nativeCircleLoopBase x)).val
  let M (x : Plane) := (1-ξ x) • m x
  let V := M+U 0+U 1+O
  have hχMix : ContDiff ℝ ∞ ξ := by
    have hCi (i : Fin 2) : ContDiff ℝ ∞ (ci i) :=
      hχ.comp (contDiff_id.sub contDiff_const)
    exact (hη.add (hCi 0)).add (hCi 1)
  have hM : ContDiff ℝ ∞ M := (contDiff_const.sub hχMix).smul hm
  choose DU hU using fun i => planarPairAmbientRadial a (inner i) (hInnerSob i)
    (planarPairCoreCenter i) χ hχ hχc hχSup
  obtain ⟨DO,hO⟩ := planarPairAmbientRadial a outer hOuterSob 0 η hη hηc hηSup
  have hOS : MemW12 (ballDomain (0 : Plane) 1) O DO := by
    have hEq : O = fun x => η (x-0) • frobeniusCoordinateEquiv
        (outer (sphereRadialDirection nativeCircleLoopBase (x-0))).val := by
      funext x
      simp only [O,ηi,sub_zero]
    exact hEq ▸ hO
  let rad : PositiveRadius := ⟨1,zero_lt_one⟩
  let DM (x : Plane) (i : Fin 2) := fderiv ℝ M x (EuclideanSpace.single i 1)
  have hMS : MemW12 (ballDomain (0 : Plane) 1) M DM :=
    dirichlet_smoothData_memW12 rad univ isOpen_univ (subset_univ _) M hM.contDiffOn
  let DV (x : Plane) (i : Fin 2) := DM x i+DU 0 x i+DU 1 x i+DO x i
  have hVS : MemW12 (ballDomain (0 : Plane) 1) V DV :=
    finiteSobolev_add (finiteSobolev_add (finiteSobolev_add hMS (hU 0)) (hU 1)) hOS
  have hCI (i : Fin 2) (x : Plane) : ci i x ∈ Icc (0 : ℝ) 1 := hχRange _
  have hOI (x : Plane) : ηi x ∈ Icc (0 : ℝ) 1 := hηRange x
  have hCIpos (i : Fin 2) {x : Plane} (h : ci i x ≠ 0) : ‖x-planarPairCoreCenter i‖ < 9/32 :=
    lt_of_not_ge fun h' => h (hχZero _ (Or.inr h'))
  have hOIpos {x : Plane} (h : ηi x ≠ 0) : 27/32 < ‖x‖ :=
    lt_of_not_ge fun h' => h (hηZero _ (Or.inl h'))
  have hNoBoth (x : Plane) (hL : ci 0 x ≠ 0) (hR : ci 1 x ≠ 0) : False := by
    have h := dist_triangle (planarPairCoreCenter 0) x (planarPairCoreCenter 1)
    rw [planarPairCenters_distance,dist_comm (planarPairCoreCenter 0) x,dist_eq_norm,dist_eq_norm] at h
    linarith only [h,hCIpos 0 hL,hCIpos 1 hR]
  have hNoOuter (i : Fin 2) {x : Plane} (h : ci i x ≠ 0) : ηi x = 0 := by
    apply hηZero
    left
    have hD := norm_le_norm_sub_add x (planarPairCoreCenter i)
    rw [planarPairCoreCenter_norm] at hD
    linarith only [hD,hCIpos i h]
  have hΞ (x : Plane) : ξ x ∈ Icc (0 : ℝ) 1 := by
    refine ⟨add_nonneg (add_nonneg (hOI x).1 (hCI 0 x).1) (hCI 1 x).1,?_⟩
    by_cases hL : ci 0 x = 0
    · by_cases hR : ci 1 x = 0
      · simpa only [ξ,hL,hR,add_zero] using (hOI x).2
      · simpa only [ξ,hL,hNoOuter 1 hR,add_zero,zero_add] using (hCI 1 x).2
    · have hR : ci 1 x = 0 := by by_contra h; exact hNoBoth x hL h
      simpa only [ξ,hR,hNoOuter 0 hL,add_zero,zero_add] using (hCI 0 x).2
  have hInnerValue (i : Fin 2) {x : Plane} (hx : x ∈ planarPairExteriorDomain.val) :
      U i x = ci i x • E x := by
    change ci i x • frobeniusCoordinateEquiv
      (inner i (sphereRadialDirection nativeCircleLoopBase (x-planarPairCoreCenter i))).val =
        ci i x • frobeniusCoordinateEquiv (p x).val
    by_cases hz : ci i x = 0
    · simp only [hz,zero_smul]
    · rw [hInner i x (planarPairExterior_subset_centersCompl hx)
        (mem_closedBall.mpr (by rw [dist_eq_norm]; exact (hCIpos i hz).le))]
  have hOuterValue {x : Plane} (hx : x ∈ planarPairExteriorDomain.val) :
      O x = ηi x • E x := by
    change ηi x • frobeniusCoordinateEquiv (outer (sphereRadialDirection nativeCircleLoopBase x)).val =
      ηi x • frobeniusCoordinateEquiv (p x).val
    by_cases hz : ηi x = 0
    · simp only [hz,zero_smul]
    · have hN : x ≠ 0 := norm_ne_zero_iff.mp ((by norm_num : (0 : ℝ) < 27/32).trans
        (hOIpos hz)).ne'
      have h := congrArg p (planarPair_normalized_ray hN)
      rw [hOuter _ (hOIpos hz).le] at h
      rw [← h]
  have hV {x : Plane} (hx : x ∈ planarPairExteriorDomain.val) :
      V x = (1-ξ x) • m x+ξ x • E x := by
    change (M x+U 0 x+U 1 x)+O x = _
    rw [hInnerValue 0 hx,hInnerValue 1 hx,hOuterValue hx]
    simp only [M,ξ,add_smul]
    abel
  have hVFix {x : Plane} (hx : x ∈ planarPairExteriorDomain.val) (hξ : ξ x = 1) :
      V x = E x := by
    rw [hV hx,hξ,sub_self,zero_smul,one_smul,zero_add]
  have hXiInner (i : Fin 2) {x : Plane} (hx : x ∈ planarPairExteriorDomain.val)
      (hB : x ∈ ball (planarPairCoreCenter i) (1/4)) : ξ x = 1 := by
    have hi := mem_iInter.mp hx.2 i
    change 3/16 < dist x (planarPairCoreCenter i) at hi
    have hOne : ci i x = 1 := hχOne _ ⟨by simpa only [dist_eq_norm] using hi.le,
      by rw [← dist_eq_norm]; exact (mem_ball.mp hB).le⟩
    apply le_antisymm (hΞ x).2
    have hcases : i=0 ∨ i=1 := by fin_cases i <;> decide
    rcases hcases with rfl | rfl
    · dsimp only [ξ]
      linarith only [hOne,(hOI x).1,(hCI 1 x).1]
    · dsimp only [ξ]
      linarith only [hOne,(hOI x).1,(hCI 0 x).1]
  have hXiOuter {x : Plane} (hx : x ∈ planarPairExteriorDomain.val)
      (hR : 7/8 ≤ ‖x‖) : ξ x = 1 := by
    have hOne : ηi x = 1 := hηOne _ ⟨hR,(mem_ball_zero_iff.mp hx.1).le⟩
    apply le_antisymm (hΞ x).2
    dsimp only [ξ]
    linarith only [hOne,(hCI 0 x).1,(hCI 1 x).1]
  let N := vacuumCompactSmoothEmbeddedTarget a
  have hTargetE (x : Plane) : E x ∈ N.carrierSet :=
    mem_vacuumCompactSmoothEmbeddedTarget_iff.mpr (by
      change frobeniusCoordinateEquiv.symm (frobeniusCoordinateEquiv (p x).val) ∈ vacuum a
      rw [LinearIsometryEquiv.symm_apply_apply]
      exact (p x).property)
  have hTargetV {x : Plane} (hx : x ∈ planarPairExteriorDomain.val) :
      Metric.infDist (V x) N.carrierSet < ρ := by
    have hDist : dist (V x) (E x) ≤ ρ/2 := by
      rw [dist_eq_norm,hV hx]
      have he : (1-ξ x) • m x+ξ x • E x-E x = (1-ξ x) • (m x-E x) := by module
      rw [he,norm_smul,Real.norm_of_nonneg (sub_nonneg.mpr (hΞ x).2)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (sub_le_self _ (hΞ x).1)).trans
        (by simpa only [dist_eq_norm] using hmNear x hx)
    exact ((Metric.infDist_le_dist_of_mem (hTargetE x)).trans hDist).trans_lt (half_lt_self hρ)
  let P := planarPairExteriorDomain
  have hPV : P.val ⊆ (ballDomain (0 : Plane) 1).val := inter_subset_left
  letI : IsFiniteMeasure (volume.restrict P.val) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono hPV))
  have hProjS := StratificationTheory.MemW12.postcompose_finite (finiteSobolev_restrict hVS hPV) Q hQ C hQD
  let w (x : Plane) := if 7/8 ≤ ‖x‖ then
    frobeniusCoordinateEquiv (outer (sphereRadialDirection nativeCircleLoopBase x)).val else Q (V x)
  have hW {x : Plane} (hx : x ∈ P.val) : w x = Q (V x) := by
    by_cases hR : 7/8 ≤ ‖x‖
    · have hN : x ≠ 0 := norm_ne_zero_iff.mp (((by norm_num : (0 : ℝ) < 7/8).trans_le hR).ne')
      have h := congrArg p (planarPair_normalized_ray hN)
      rw [hOuter _ ((by norm_num : (27/32 : ℝ) ≤ 7/8).trans hR)] at h
      change (if 7/8 ≤ ‖x‖ then frobeniusCoordinateEquiv
        (outer (sphereRadialDirection nativeCircleLoopBase x)).val else Q (V x)) = Q (V x)
      rw [if_pos hR,hVFix hx (hXiOuter hx hR),hFix _ (hTargetE x)]
      exact congrArg (fun b : vacuum a => frobeniusCoordinateEquiv b.val) h
    · exact if_neg hR
  have hMem := hProjS.congr_ae ((ae_restrict_mem P.property.measurableSet).mono
    (fun x hx => (hW hx).symm)) EventuallyEq.rfl
  refine ⟨⟨w,_,hMem,?_,?_,?_⟩⟩
  · filter_upwards [ae_restrict_mem P.property.measurableSet] with x hx
    rw [hW hx]
    exact mem_vacuumCompactSmoothEmbeddedTarget_iff.mp (hNear _ (hTargetV hx))
  · intro i x hx hB
    have hInnerW := hInner i x (planarPairExterior_subset_centersCompl hx)
      (ball_subset_closedBall (ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 9/32) hB))
    rw [hW hx,hVFix hx (hXiInner i hx hB),hFix _ (hTargetE x)]
    exact congrArg (fun b : vacuum a => frobeniusCoordinateEquiv b.val) hInnerW
  · intro r hr θ
    have hr₀ : 0 < r := (by norm_num : 0 < (7/8 : ℝ)).trans_le hr
    have hn : ‖r • θ.val‖ = r := by
      rw [norm_smul,Real.norm_of_nonneg hr₀.le,mem_sphere_zero_iff_norm.mp θ.property,mul_one]
    change (if 7/8 ≤ ‖r • θ.val‖ then frobeniusCoordinateEquiv
      (outer (sphereRadialDirection nativeCircleLoopBase (r • θ.val))).val else Q (V (r • θ.val))) = _
    rw [hn,if_pos hr,sphereRadialDirection_smul nativeCircleLoopBase hr₀,sphereRadialDirection_unit]

end Thesis
