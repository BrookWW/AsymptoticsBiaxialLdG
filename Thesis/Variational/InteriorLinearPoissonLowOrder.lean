module

public import Thesis.External.InteriorCorrectionEstimates
public import Thesis.Variational.SubsolutionMeanValue
public import Thesis.Variational.InteriorDerivativeEstimate
import Thesis.Variational.EnergyEstimate
import Thesis.Upstream.PoissonGradientBound
import Thesis.Interpolation.CylinderRecoveryBand
import Mathlib.MeasureTheory.Function.L2Space

/-! Quantitative local value and gradient estimates for the linear system. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal Matrix.Norms.Frobenius RealInnerProductSpace Topology

namespace Thesis

local instance linearPoissonCoefficientNormed : NormedAddCommGroup ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance linearPoissonCoefficientSpace : NormedSpace ℝ ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance linearPoissonGradientOpNorm : Norm (Point →L[ℝ] S0) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ) (E := Point) (F := S0)

theorem norm_classicalGradient_le_sqrt_energy (v : Point → S0) (x : Point) :
    ‖ClassicalGradient v x‖ ≤ Real.sqrt (gradientNormSq (ClassicalGradient v x)) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt,gradientNormSq_eq_sum_norm_sq]
  · exact Finset.single_le_sum (fun j _ => sq_nonneg ‖ClassicalGradient v x j‖) (Finset.mem_univ i)
  · rw [gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem norm_linearPoisson_coefficient
    (B : (S0 × Gradient) →L[ℝ] S0) {M : ℝ} (hB : ‖B‖ ≤ M) (hM : 0 ≤ M)
    (v : Point → S0) (x : Point) :
    ‖B (v x,ClassicalGradient v x)‖ ≤
      M*(‖v x‖ + Real.sqrt (gradientNormSq (ClassicalGradient v x))) := by
  have hPair : ‖(v x,ClassicalGradient v x)‖ ≤
      ‖v x‖ + Real.sqrt (gradientNormSq (ClassicalGradient v x)) := by
    rw [Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      ((norm_classicalGradient_le_sqrt_energy v x).trans (le_add_of_nonneg_left (norm_nonneg _)))
  exact (B.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hB (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hPair hM))

private theorem norm_laplacian_le_of_linearPoisson
    (B : (S0 × Gradient) →L[ℝ] S0) {M D : ℝ} (hB : ‖B‖ ≤ M) (hM : 0 ≤ M)
    (v : Point → S0) (x : Point) (F : S0) (hF : ‖F‖ ≤ D)
    (hEq : laplacian v x+B (v x,ClassicalGradient v x) = F) :
    ‖laplacian v x‖ ≤ D+M*(‖v x‖+Real.sqrt (gradientNormSq (ClassicalGradient v x))) := by
  have hE : laplacian v x = F-B (v x,ClassicalGradient v x) := eq_sub_of_add_eq hEq
  rw [hE]
  exact (norm_sub_le _ _).trans (add_le_add hF (norm_linearPoisson_coefficient B hB hM v x))

private theorem laplacian_linearPoisson_square
    {U : Set Point} (hU : IsOpen U) {v : Point → S0} (hv : ContDiffOn ℝ ∞ v U)
    {x : Point} (hx : x ∈ U) (d : ℝ) :
    laplacian (fun y => ‖v y‖^2+d^2) x =
      2*(frobeniusS0 (laplacian v x) (v x)+gradientNormSq (ClassicalGradient v x)) := by
  have hEq : (fun y => ‖v y‖^2+d^2) = (fun y => frobeniusS0 (v y) (v y)+d^2) := by
    funext y
    rw [norm_sq_eq_frobeniusS0]
  rw [hEq]
  have hLap : laplacian (fun y => frobeniusS0 (v y) (v y)+d^2) x =
      laplacian (fun y => frobeniusS0 (v y) (v y)) x := by
    unfold laplacian coordDeriv
    simp only [fderiv_add_const]
  rw [hLap,laplacian_frobeniusS0_self hU hv hx,gradientNormSq_eq_sum_norm_sq]
  rfl

private theorem linearPoisson_square_subsolution
    {U : Set Point} (hU : IsOpen U) {v : Point → S0} (hv : ContDiffOn ℝ ∞ v U)
    {x : Point} (hx : x ∈ U) (B : (S0 × Gradient) →L[ℝ] S0) {M D : ℝ}
    (hM : 0 ≤ M) (hB : ‖B‖ ≤ M) (F : S0) (hF : ‖F‖ ≤ D)
    (hEq : laplacian v x+B (v x,ClassicalGradient v x) = F) :
    -laplacian (fun y => ‖v y‖^2+D^2) x ≤ (1+2*M+M^2)*(‖v x‖^2+D^2) := by
  let A := ‖v x‖
  let H := Real.sqrt (gradientNormSq (ClassicalGradient v x))
  have hA : 0 ≤ A := norm_nonneg _
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hH₂ : H^2 = gradientNormSq (ClassicalGradient v x) := by
    dsimp only [H]
    apply Real.sq_sqrt
    rw [gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hL : ‖laplacian v x‖ ≤ D+M*(A+H) :=
    norm_laplacian_le_of_linearPoisson B hB hM v x F hF hEq
  have hI : -((D+M*(A+H))*A) ≤ frobeniusS0 (laplacian v x) (v x) := by
    have h := abs_real_inner_le_norm (frobeniusCoordinateEquiv (laplacian v x))
      (frobeniusCoordinateEquiv (v x))
    rw [frobeniusCoordinateEquiv_inner,frobeniusCoordinateEquiv.norm_map,
      frobeniusCoordinateEquiv.norm_map] at h
    exact (neg_le_neg (mul_le_mul_of_nonneg_right hL hA)).trans ((neg_le_neg h).trans (neg_abs_le _))
  rw [laplacian_linearPoisson_square hU hv hx,← hH₂]
  have hY₁ := sq_nonneg (A-D)
  have hY₂ := sq_nonneg (M*A-H)
  have hT : -(2*(frobeniusS0 (laplacian v x) (v x)+H^2)) ≤ (1+2*M+M^2)*A^2+D^2 := by
    nlinarith only [hI,hY₁,hY₂,sq_nonneg H]
  have hOne : 1 ≤ 1+2*M+M^2 := by nlinarith only [hM,sq_nonneg M]
  exact hT.trans (by
    rw [mul_add]
    have h := mul_le_mul_of_nonneg_right hOne (sq_nonneg D)
    nlinarith only [h])

private theorem integral_normSq_le_of_eLpNorm_two {μ : Measure Point} {v : Point → S0}
    (hv : MemLp v 2 μ) {E : ℝ} (hE : 0 ≤ E) (h : eLpNorm v 2 μ ≤ ENNReal.ofReal E) :
    (∫ x, ‖v x‖^2 ∂μ) ≤ E^2 := by
  have hI : Integrable (fun x => ‖v x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hP : (eLpNorm v 2 μ)^2 ≤ ENNReal.ofReal (E^2) := by
    rw [ENNReal.ofReal_pow hE]
    exact pow_le_pow_left' h 2
  have hN : (eLpNorm v 2 μ)^2 = ∫⁻ x, ENNReal.ofReal (‖v x‖^2) ∂μ := by
    calc
      _ = ∫⁻ x, ‖v x‖ₑ^2 ∂μ := by
        simpa only [ENNReal.rpow_two,NNReal.coe_two,ENNReal.coe_two] using
          (eLpNorm_nnreal_pow_eq_lintegral (f := v) (μ := μ) (p := (2 : ℝ≥0)) (by norm_num))
      _ = _ := by
        apply lintegral_congr
        intro x
        rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => sq_nonneg ‖v x‖) hI.aestronglyMeasurable,← hN]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hP).trans_eq (ENNReal.toReal_ofReal (sq_nonneg E))

/-- The uniform value estimate on every fixed smaller ball for a smooth
linear Poisson system with bounded first-order coefficients. -/
theorem exists_interior_linearPoisson_value_bound (c : Point) {r s : ℝ} (_hs : 0 < s)
    (hsr : s < r) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C > (0 : ℝ), ∀ (B : Point → (S0 × Gradient) →L[ℝ] S0) (v F : Point → S0) (E D : ℝ),
      ContDiffOn ℝ ∞ v (ball c r) → 0 ≤ E → 0 ≤ D →
      MemLp v 2 (volume.restrict (ball c r)) → eLpNorm v 2 (volume.restrict (ball c r)) ≤ ENNReal.ofReal E →
      (∀ y ∈ ball c r, laplacian v y+B y (v y,ClassicalGradient v y)=F y) →
      (∀ y ∈ ball c r, ‖B y‖ ≤ M) → (∀ y ∈ ball c r, ‖F y‖ ≤ D) →
      ∀ y ∈ ball c s, ‖v y‖ ≤ C*(E+D) := by
  let A := 1+2*M+M^2
  have hA : 0 ≤ A := by positivity
  obtain ⟨L,hL,hMean⟩ := classicalScalarSubsolutionMeanValue A hA
  let ρ := min 1 ((r-s)/2)
  have hρ : 0 < ρ := lt_min zero_lt_one (half_pos (sub_pos.mpr hsr))
  have hρ₁ : ρ ≤ 1 := min_le_left _ _
  let W := volume.real (ball c r)
  let K := L*ρ⁻¹ ^ 3*(1+W)
  have hW : 0 ≤ W := ENNReal.toReal_nonneg
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨Real.sqrt K,Real.sqrt_pos.mpr hK,?_⟩
  intro B v F E D hv hE hD hV hVE hEq hB hF y hy
  have hSub : ball y ρ ⊆ ball c r := by
    intro z hz
    have hZY := mem_ball.mp hz
    have hYC := mem_ball.mp hy
    have hp := min_le_right (1 : ℝ) ((r-s)/2)
    exact mem_ball.mpr ((dist_triangle z y c).trans_lt (by linarith only [hZY,hYC,hp,hsr]))
  let w (z : Point) := ‖v z‖^2+D^2
  have hw₀ (z : Point) : 0 ≤ w z := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hwC : ContDiffOn ℝ 2 w (ball c r) := by
    have hVC : ContDiffOn ℝ 2 (frobeniusField v) (ball c r) :=
      frobeniusCoordinateEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn (hv.of_le (by decide))
    have hBase : ContDiffOn ℝ 2 (fun z => ‖frobeniusCoordinateEquiv (v z)‖^2) (ball c r) :=
      (contDiff_norm_sq ℝ).contDiffOn.comp hVC (mapsTo_univ _ _)
    have hConst : ContDiffOn ℝ 2 (fun _ : Point => D^2) (ball c r) := contDiffOn_const
    have h := hBase.add hConst
    apply h.congr
    intro z _
    change ‖v z‖^2+D^2 = ‖frobeniusCoordinateEquiv (v z)‖^2+D^2
    rw [frobeniusCoordinateEquiv.norm_map]
  have hwI : IntegrableOn w (ball c r) := by
    have hI : IntegrableOn (fun z => ‖v z‖^2) (ball c r) :=
      (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mp hV
    exact hI.add (integrableOn_const measure_ball_lt_top.ne)
  have h := hMean y ρ ⟨hρ,hρ₁⟩ w (hwC.mono hSub) (hwI.mono_set hSub) (fun z _ => hw₀ z)
    (fun z hz => linearPoisson_square_subsolution isOpen_ball hv (hSub hz) (B z)
      hM (hB z (hSub hz)) (F z) (hF z (hSub hz)) (hEq z (hSub hz)))
  have hI : (∫ z in ball y ρ, w z) ≤ E^2+W*D^2 := by
    calc
      _ ≤ ∫ z in ball c r, w z := setIntegral_mono_set hwI
        (Eventually.of_forall hw₀) (Eventually.of_forall hSub)
      _ = (∫ z in ball c r, ‖v z‖^2)+W*D^2 := by
        have hV2 : IntegrableOn (fun z => ‖v z‖^2) (ball c r) :=
          (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mp hV
        have hDI : IntegrableOn (fun _ : Point => D^2) (ball c r) :=
          integrableOn_const measure_ball_lt_top.ne
        change (∫ z in ball c r, ((fun z => ‖v z‖^2) + (fun _ : Point => D^2)) z) = _
        rw [integral_add' hV2 hDI,setIntegral_const,smul_eq_mul]
      _ ≤ _ := add_le_add (integral_normSq_le_of_eLpNorm_two hV hE hVE) le_rfl
  have hBnd : E^2+W*D^2 ≤ (1+W)*(E+D)^2 := by
    have hM := mul_le_mul_of_nonneg_left
      (show D^2 ≤ (E+D)^2 by nlinarith only [sq_nonneg E,mul_nonneg hE hD]) hW
    nlinarith only [hM,sq_nonneg D,mul_nonneg hE hD]
  have hSq : ‖v y‖^2 ≤ K*(E+D)^2 := by
    have hC : 0 ≤ L*ρ⁻¹ ^ 3 := mul_nonneg hL.le (pow_nonneg (inv_nonneg.mpr hρ.le) _)
    calc
      _ ≤ w y := le_add_of_nonneg_right (sq_nonneg D)
      _ ≤ _ := h
      _ ≤ L*ρ⁻¹ ^ 3*((1+W)*(E+D)^2) := mul_le_mul_of_nonneg_left (hI.trans hBnd) hC
      _ = _ := by dsimp only [K]; ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hE hD))).mp
  rw [mul_pow,Real.sq_sqrt hK.le]
  exact hSq

/-- The interior gradient bound for the same system, with the first-order
term absorbed across nested radii. -/
theorem exists_interior_linearPoisson_gradient_bound (c : Point) {r s : ℝ} (hs : 0 < s)
    (hsr : s < r) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C > (0 : ℝ), ∀ (B : Point → (S0 × Gradient) →L[ℝ] S0) (v F : Point → S0) (A D : ℝ),
      ContDiffOn ℝ ∞ v (ball c r) → 0 ≤ A → 0 ≤ D →
      (∀ y ∈ ball c r, ‖v y‖ ≤ A) →
      (∀ y ∈ ball c r, laplacian v y+B y (v y,ClassicalGradient v y)=F y) →
      (∀ y ∈ ball c r, ‖B y‖ ≤ M) → (∀ y ∈ ball c r, ‖F y‖ ≤ D) →
      ∀ y ∈ ball c s, Real.sqrt (gradientNormSq (ClassicalGradient v y)) ≤ C*(A+D) := by
  obtain ⟨L,hL,hGrad⟩ := interiorPoissonGradientEstimate
  let t := (s+r)/2
  have hst : s < t := by dsimp only [t]; linarith only [hsr]
  have htr : t < r := by dsimp only [t]; linarith only [hsr]
  have ht : 0 < t := hs.trans hst
  let θ := min (1/2 : ℝ) (1/(4*L*M*t+1))
  have hDen : 0 < 4*L*M*t+1 := by positivity
  have hθ : 0 < θ := lt_min (by norm_num) (one_div_pos.mpr hDen)
  have hθ₁ : θ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hθB : θ*(4*L*M*t+1) ≤ 1 := (le_div_iff₀ hDen).mp (min_le_right _ _)
  let K := L*(θ⁻¹+t*(M+1))
  let C := 2*K*(1+2/(t-s))
  have hK : 0 < K := by dsimp only [K]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro B v F A D hv hA hD hvA hEq hB hF y hy
  let g (z : Point) := Real.sqrt (gradientNormSq (ClassicalGradient v z))
  let Φ (q : ℝ) := sSup (g '' closedBall c q)
  have hg₀ (z : Point) : 0 ≤ g z := Real.sqrt_nonneg _
  have hgC : ContinuousOn g (ball c r) := by
    dsimp only [g]
    apply ContinuousOn.sqrt
    simp_rw [gradientNormSq_eq_sum_norm_sq]
    apply continuousOn_finsetSum
    intro i _
    exact ((continuousOn_coordDeriv isOpen_ball (hv.of_le (by decide)) i).norm.pow 2)
  obtain ⟨P,hP⟩ := (isCompact_closedBall c t).exists_bound_of_continuousOn
    (hgC.mono (closedBall_subset_ball htr))
  have hgP (z : Point) (hz : z ∈ closedBall c t) : g z ≤ P := by
    simpa only [Real.norm_of_nonneg (hg₀ z)] using hP z hz
  have hUpper (q : ℝ) (hq : q ≤ t) : BddAbove (g '' closedBall c q) := by
    refine ⟨P,?_⟩
    rintro b ⟨z,hz,rfl⟩
    exact hgP z (closedBall_subset_closedBall hq hz)
  have hLeΦ (q : ℝ) (hq : q ≤ t) (z : Point) (hz : z ∈ closedBall c q) : g z ≤ Φ q :=
    le_csSup (hUpper q hq) ⟨z,hz,rfl⟩
  have hΦ₀ (q : ℝ) (hq : q ∈ Icc s t) : 0 ≤ Φ q :=
    (hg₀ c).trans (hLeΦ q hq.2 c (mem_closedBall_self (hs.le.trans hq.1)))
  have hΦP (q : ℝ) (hq : q ∈ Icc s t) : Φ q ≤ P := by
    have hN : (g '' closedBall c q).Nonempty :=
      ⟨g c,mem_image_of_mem g (mem_closedBall_self (hs.le.trans hq.1))⟩
    apply csSup_le hN
    rintro b ⟨z,hz,rfl⟩
    exact hgP z (closedBall_subset_closedBall hq.2 hz)
  let C' := K*(A+D)
  have hC' : 0 ≤ C' := mul_nonneg hK.le (add_nonneg hA hD)
  have hStep (q : ℝ) (hq : q ∈ Icc s t) (q' : ℝ) (hq' : q' ∈ Icc s t) (hqq' : q < q') :
      Φ q ≤ (1/4 : ℝ)*Φ q'+C'*(1+(q'-q)⁻¹) := by
    have hN : (g '' closedBall c q).Nonempty :=
      ⟨g c,mem_image_of_mem g (mem_closedBall_self (hs.le.trans hq.1))⟩
    apply csSup_le hN
    rintro _ ⟨z,hz,rfl⟩
    let δ := q'-q
    let a := θ*δ
    have hδ : 0 < δ := sub_pos.mpr hqq'
    have ha : 0 < a := mul_pos hθ hδ
    have haδ : a ≤ δ := mul_le_of_le_one_left hδ.le hθ₁
    have hδt : δ ≤ t := by dsimp only [δ]; linarith only [hs,hq.1,hq'.2]
    have hat : a ≤ t := haδ.trans hδt
    have hAt : a ≤ θ*t := mul_le_mul_of_nonneg_left hδt hθ.le
    have hSmall : L*a*M ≤ 1/4 := by
      have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAt hL.le) hM
      nlinarith only [hm,hθB,hθ.le]
    have hBall : ball z a ⊆ closedBall c q' := by
      intro w hw
      have hwz := mem_ball.mp hw
      have hzc := mem_closedBall.mp hz
      exact mem_closedBall.mpr ((dist_triangle w z c).trans (by
        dsimp only [δ] at haδ
        linarith only [hwz,haδ,hzc]))
    have hR : ball z a ⊆ ball c r :=
      hBall.trans (closedBall_subset_ball (hq'.2.trans_lt htr))
    let E := D+M*(A+Φ q')
    have hLapl (w : Point) (hw : w ∈ ball z a) : ‖(laplacian v w : S0).val‖ ≤ E := by
      have hb := norm_laplacian_le_of_linearPoisson (B w) (hB w (hR hw)) hM v w (F w)
        (hF w (hR hw)) (hEq w (hR hw))
      exact hb.trans (add_le_add_right (mul_le_mul_of_nonneg_left
        (add_le_add (hvA w (hR hw)) (hLeΦ q' hq'.2 w (hBall hw))) hM) D)
    have hGR := hGrad z a ha v (fun w => (laplacian v w).val) A E
      ((hv.mono hR).of_le (by decide)) (fun _ _ => rfl) (fun w hw => hvA w (hR hw)) hLapl
    change a*g z ≤ L*(A+a^2*E) at hGR
    have hGz : g z ≤ L*(A/a+a*E) := by
      have h : g z ≤ L*(A+a^2*E)/a := (le_div_iff₀ ha).mpr (by rwa [mul_comm (g z) a])
      refine h.trans_eq ?_
      field_simp [ha.ne']
    have hRest : L*a*(D+M*A) ≤ K*(A+D) := by
      have hEA : D+M*A ≤ (M+1)*(A+D) := by
        nlinarith only [mul_nonneg hM hD,hA]
      have hh := mul_le_mul_of_nonneg_left hEA (mul_nonneg hL.le ha.le)
      have hMfac : 0 ≤ (M+1)*(A+D) := by positivity
      have htL := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hat hL.le) hMfac
      calc
        _ ≤ L*t*((M+1)*(A+D)) := hh.trans htL
        _ ≤ K*(A+D) := by
          dsimp only [K]
          have hExtra := mul_nonneg hL.le (mul_nonneg (inv_nonneg.mpr hθ.le) (add_nonneg hA hD))
          nlinarith only [hExtra]
    have hVol : L*(A/a) ≤ K*(A+D)*δ⁻¹ := by
      have hEq : A/a = (A*θ⁻¹)*δ⁻¹ := by dsimp only [a]; field_simp [hθ.ne',hδ.ne']
      have hA' : L*(A*θ⁻¹) ≤ K*(A+D) := by
        dsimp only [K]
        have h₁ := mul_nonneg (mul_nonneg hL.le (inv_nonneg.mpr hθ.le)) hD
        have hM₁ : 0 ≤ M+1 := by linarith only [hM]
        have h₂ := mul_nonneg (mul_nonneg hL.le (mul_nonneg ht.le hM₁))
          (add_nonneg hA hD)
        nlinarith only [h₁,h₂]
      rw [hEq,← mul_assoc]
      exact mul_le_mul_of_nonneg_right hA' (inv_nonneg.mpr hδ.le)
    have hAbs := mul_le_mul_of_nonneg_right hSmall (hΦ₀ q' hq')
    dsimp only [E] at hGz
    dsimp only [C',δ] at hVol ⊢
    nlinarith only [hGz,hRest,hVol,hAbs]
  have h := absorb_interior_radius_bounds hst hC' Φ hΦP hStep
  refine (hLeΦ s hst.le y (ball_subset_closedBall hy)).trans (h.trans_eq ?_)
  dsimp only [C',C]
  ring

/-- The native first derivative estimate in operator norm, with the same
input L² norm as the zero-order estimate. -/
theorem exists_interior_linearPoisson_first_bound (c : Point) {r s : ℝ} (hs : 0 < s)
    (hsr : s < r) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C > (0 : ℝ), ∀ (B : Point → (S0 × Gradient) →L[ℝ] S0) (v F : Point → S0) (E D : ℝ),
      ContDiffOn ℝ ∞ v (ball c r) → 0 ≤ E → 0 ≤ D →
      MemLp v 2 (volume.restrict (ball c r)) → eLpNorm v 2 (volume.restrict (ball c r)) ≤ ENNReal.ofReal E →
      (∀ y ∈ ball c r, laplacian v y+B y (v y,ClassicalGradient v y)=F y) →
      (∀ y ∈ ball c r, ‖B y‖ ≤ M) → (∀ y ∈ ball c r, ‖F y‖ ≤ D) →
      ∀ y ∈ ball c s, ‖fderiv ℝ v y‖ ≤ C*(E+D) := by
  let t := (s+r)/2
  have hst : s < t := by dsimp only [t]; linarith only [hsr]
  have htr : t < r := by dsimp only [t]; linarith only [hsr]
  obtain ⟨C₀,hC₀,hVal⟩ := exists_interior_linearPoisson_value_bound c (hs.trans hst) htr M hM
  obtain ⟨C₁,hC₁,hGrad⟩ := exists_interior_linearPoisson_gradient_bound c hs hst M hM
  refine ⟨C₁*(C₀+1),by positivity,?_⟩
  intro B v F E D hv hE hD hvLp hvE hEq hB hF y hy
  have hSub : ball c t ⊆ ball c r := ball_subset_ball htr.le
  have hA : 0 ≤ C₀*(E+D) := mul_nonneg hC₀.le (add_nonneg hE hD)
  have hG := hGrad B v F (C₀*(E+D)) D (hv.mono hSub) hA hD
    (hVal B v F E D hv hE hD hvLp hvE hEq hB hF)
    (fun z hz => hEq z (hSub hz)) (fun z hz => hB z (hSub hz)) (fun z hz => hF z (hSub hz)) y hy
  exact (MeasureGeometry.fderiv_norm_le_sqrt_gradient v y).trans (hG.trans (by
    have h := mul_nonneg hC₁.le hE
    nlinarith only [h]))

end Thesis
