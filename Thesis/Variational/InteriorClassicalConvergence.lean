module

public import Thesis.Variational.InteriorBiaxialBootstrap
public import Thesis.Variational.InteriorRegularityBounds

/-! Local classical convergence of the same strongly convergent regular
sequence. -/

public section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

noncomputable section

namespace Thesis

/-- The derivative bounds are uniform along the original sequence on
each compact regular subset. -/
theorem exists_eventual_regular_compact_derivative_bound (a : BulkCoefficients)
    (hEstimate : InteriorPoissonGradientEstimate) (hMean : External.ClassicalScalarSubsolutionMeanValue)
    {Ω K : Set Point} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (q : Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω) (hq : ContDiffOn ℝ ∞ q Ω)
    (hEuler : ∀ n x, x ∈ Ω → (ε n : ℝ) ^ 2 • (laplacian (Q n) x : S0).val = bulkGradient a (Q n x))
    (hRange : BddAbove ((fun p : ℕ × Point => ‖Q p.1 p.2‖) '' (univ ×ˢ Ω)))
    (hStrong : StrongH1Loc Ω Q (fun n => ClassicalGradient (Q n)) q (ClassicalGradient q))
    (hBulk : ConvergesScaledPotentialLoc a Ω ε Q) (j : ℕ) :
    ∃ C > (0 : ℝ), ∀ᶠ n in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ (j + 1) (Q n) x‖ ≤ C := by
  classical
  obtain ⟨r, hr, hR⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let t := 3 * r / 4
  have ht : 0 < t := by dsimp only [t]; positivity
  have htr : t < r := by dsimp only [t]; linarith
  have hrt : r / 2 < t := by dsimp only [t]; linarith
  have hLoc (c : K) : ∃ C > (0 : ℝ), ∀ᶠ n in atTop, ∀ x ∈ ball c.val (r / 2),
      ‖iteratedFDeriv ℝ (j + 1) (Q n) x‖ ≤ C := by
    have hClosed : closedBall c.val r ⊆ Ω := (closedBall_subset_cthickening c.property r).trans hR
    have hB : ball c.val r ⊆ Ω := ball_subset_closedBall.trans hClosed
    let L := (eLpNorm (fun y => Real.sqrt (gradientNormSq (ClassicalGradient q y))) ⊤
      (volume.restrict (ball c.val r))).toReal
    have hL : 0 ≤ L := ENNReal.toReal_nonneg
    obtain ⟨B, hBpos, hBase⟩ :=
      exists_eventual_interior_biaxial_orderZero_bound a hEstimate hMean r t L ht htr hL
    obtain ⟨C, hC, hCk⟩ := exists_interior_classical_biaxial_derivative_bound a hEstimate j B hBpos.le
    have hBase' := hBase c.val ε Q q hε (fun n => (hQ n).mono hB) (((contDiffOn_infty.mp hq) 2).mono hB)
      (fun n y hy => hEuler n y (hB hy)) (hRange.mono (image_mono (prod_mono subset_rfl hB)))
      (classicalGradient_le_eLpNorm_top_on_regular_ball hΩ hq hClosed)
      (fun W hW hWC => hStrong W hW ⟨hWC.1, hWC.2.trans hB⟩)
      (fun W hW hWC => hBulk W hW ⟨hWC.1, hWC.2.trans hB⟩)
    have hFactor : 0 < C * (1 + (t - r / 2)⁻¹ ^ j) := by have := sub_pos.mpr hrt; positivity
    refine ⟨C * (1 + (t - r / 2)⁻¹ ^ j), hFactor, ?_⟩
    filter_upwards [hBase'] with n hn x hx
    have hBt := (ball_subset_ball htr.le).trans hB
    have h := hCk (ε n) c.val t (r / 2) (half_pos hr) hrt (Q n) ((hQ n).mono hBt)
      (fun y hy => hEuler n y (hBt hy)) hn x hx
    linarith only [h, norm_nonneg (iteratedFDeriv ℝ j (scaledNormDefect a (ε n) ∘ Q n) x),
      norm_nonneg (iteratedFDeriv ℝ j (scaledCubicTrace a (ε n) ∘ Q n) x)]
  choose C hC hLoc' using hLoc
  let V (c : K) := ball c.val (r / 2)
  have hCov : K ⊆ ⋃ c : K, V c :=
    fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (half_pos hr)⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V (fun _ => isOpen_ball) hCov
  have hSum : 0 ≤ ∑ c ∈ I, C c := Finset.sum_nonneg fun c _ => (hC c).le
  refine ⟨1 + ∑ c ∈ I, C c, add_pos_of_pos_of_nonneg zero_lt_one hSum, ?_⟩
  have hEvt := (eventually_all_finset I).2 (fun c _ => hLoc' c)
  filter_upwards [hEvt] with n hn x hx
  obtain ⟨c, hc, hx⟩ := mem_iUnion₂.mp (hI hx)
  exact (hn c hc x hx).trans ((Finset.single_le_sum (fun c _ => (hC c).le) hc).trans
    (le_add_of_nonneg_left zero_le_one))

private theorem norm_laplacian_coordinateDerivative_le {Ω : Set Point} (hΩ : IsOpen Ω)
    {f : Point → S0} (hf : ContDiffOn ℝ ∞ f Ω) (k : ℕ) (i : Fin k → Fin 3)
    {x : Point} (hx : x ∈ Ω) :
    ‖laplacian (iteratedCoordinateDerivative k i f) x‖ ≤ 3 * ‖iteratedFDeriv ℝ (k + 2) f x‖ := by
  unfold laplacian
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _l : Fin 3, ‖iteratedFDeriv ℝ (k + 2) f x‖ := by
      apply Finset.sum_le_sum
      intro l _
      have hI : iteratedCoordinateDerivative (k + 2) (Fin.cons l (Fin.cons l i)) f =
          coordDeriv l (coordDeriv l (iteratedCoordinateDerivative k i f)) := by
        simp only [iteratedCoordinateDerivative, Fin.cons_zero, Fin.tail_cons]
      simpa only [hI] using norm_coordinateDerivative_le_norm_iteratedFDeriv hΩ hf
        (k + 2) (Fin.cons l (Fin.cons l i)) hx
    _ = _ := by simp [nsmul_eq_mul]

private theorem coordinateDerivative_locallyUniformly_converges
    {Ω : Set Point} (hΩ : IsOpen Ω) (hEstimate : InteriorPoissonGradientEstimate)
    {Q : ℕ → Point → S0} {q : Point → S0}
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω) (hq : ContDiffOn ℝ ∞ q Ω)
    (h0 : ∀ K : Set Point, IsCompact K → K ⊆ Ω → TendstoUniformlyOn Q q atTop K)
    (hBound : ∀ k (K : Set Point), IsCompact K → K ⊆ Ω → ∃ B > (0 : ℝ), ∀ᶠ n in atTop,
      ∀ x ∈ K, ‖iteratedFDeriv ℝ (k + 2) (Q n) x‖ ≤ B)
    (k : ℕ) (i : Fin k → Fin 3) (K : Set Point) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn (fun n => iteratedCoordinateDerivative k i (Q n)) (iteratedCoordinateDerivative k i q) atTop K := by
  obtain ⟨A, hA, hInt⟩ := exists_interior_tensor_gradient_interpolation hEstimate
  induction k generalizing K with
  | zero => exact h0 K hK hKΩ
  | succ k ih =>
      obtain ⟨r, hr, hrΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
      let K' := cthickening r K
      obtain ⟨B, hB, hK'⟩ := hBound k K' hK.cthickening hrΩ
      have hConn : ContinuousOn (iteratedFDeriv ℝ (k + 2) q) Ω :=
        (hq.continuousOn_iteratedFDerivWithin (WithTop.coe_le_coe.mpr le_top) hΩ.uniqueDiffOn).congr
          (fun x hx => (iteratedFDerivWithin_of_isOpen (k + 2) hΩ hx).symm)
      obtain ⟨D, hD⟩ := hK.cthickening.exists_bound_of_continuousOn (hConn.mono hrΩ)
      let L := 3 * (B + max 0 D)
      have hL : 0 ≤ L := by dsimp only [L]; positivity
      let f (n : ℕ) := iteratedCoordinateDerivative k (Fin.tail i) (Q n)
      let g := iteratedCoordinateDerivative k (Fin.tail i) q
      have hFs (n : ℕ) : ContDiffOn ℝ ∞ (f n) Ω := contDiffOn_iteratedCoordinateDerivative hΩ (hQ n) _ _
      have hGs : ContDiffOn ℝ ∞ g Ω := contDiffOn_iteratedCoordinateDerivative hΩ hq _ _
      have hQk : TendstoUniformlyOn f g atTop K' := ih (Fin.tail i) K' hK.cthickening hrΩ
      refine tendstoUniformlyOn_iff.mpr ?_
      intro δ hδ
      let F (z : ℝ) := A * (z / r + Real.sqrt (z * L))
      have hF : ContinuousAt F 0 := by dsimp only [F]; fun_prop
      have hF0 : Tendsto F (𝓝 0) (𝓝 0) := by simpa [F] using hF.tendsto
      obtain ⟨d, hd, hFd⟩ := Metric.mem_nhds_iff.mp (hF0 (Iio_mem_nhds hδ))
      let M := d / 2
      have hM : 0 < M := half_pos hd
      have hMD : F M < δ := hFd (by
        rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hM]
        exact half_lt_self hd)
      filter_upwards [hK', tendstoUniformlyOn_iff.mp hQk M hM] with n hn hN x hx
      let v (y : Point) := f n y - g y
      have hU : ball x r ⊆ K' := ball_subset_closedBall.trans (closedBall_subset_cthickening hx r)
      have hUΩ := hU.trans hrΩ
      have hV : ContDiffOn ℝ ∞ v Ω := (hFs n).sub hGs
      have hVR (y : Point) (hy : y ∈ ball x r) : ‖v y‖ ≤ M := by
        have h := hN y (hU hy)
        rw [dist_comm, dist_eq_norm] at h
        exact h.le
      have hVL (y : Point) (hy : y ∈ ball x r) : ‖laplacian v y‖ ≤ L := by
        have hy' := hU hy
        have hyΩ := hrΩ hy'
        have hb := norm_laplacian_coordinateDerivative_le hΩ (hQ n) k (Fin.tail i) hyΩ
        have hg' := norm_laplacian_coordinateDerivative_le hΩ hq k (Fin.tail i) hyΩ
        have hDup : ‖iteratedFDeriv ℝ (k + 2) q y‖ ≤ max 0 D := (hD y hy').trans (le_max_right _ _)
        change ‖laplacian (fun z => f n z - g z) y‖ ≤ _
        rw [laplacian_sub_of_contDiffOn hΩ ((contDiffOn_infty.mp (hFs n)) 2)
          ((contDiffOn_infty.mp hGs) 2) hyΩ]
        exact (norm_sub_le _ _).trans ((add_le_add
          (hb.trans (mul_le_mul_of_nonneg_left (hn y hy') (by norm_num)))
          (hg'.trans (mul_le_mul_of_nonneg_left hDup (by norm_num)))).trans_eq (by dsimp only [L]; ring))
      have hGrad := hInt x r hr v (((contDiffOn_infty.mp hV) 2).mono hUΩ)
        M L hM.le hL hVR hVL
      have hStep : ‖coordDeriv (i 0) v x‖ ≤ Real.sqrt (gradientNormSq (ClassicalGradient v x)) := by
        rw [gradientNormSq_eq_sum_norm_sq]
        exact Real.le_sqrt_of_sq_le (Finset.single_le_sum
          (fun l _ => sq_nonneg ‖ClassicalGradient v x l‖) (Finset.mem_univ (i 0)))
      have hxΩ := hKΩ hx
      have hfD := ((hFs n).differentiableOn (by simp) x hxΩ).differentiableAt (hΩ.mem_nhds hxΩ)
      have hgD := (hGs.differentiableOn (by simp) x hxΩ).differentiableAt (hΩ.mem_nhds hxΩ)
      have hEq : coordDeriv (i 0) v x = coordDeriv (i 0) (f n) x - coordDeriv (i 0) g x :=
        DFunLike.congr_fun (hfD.hasFDerivAt.sub hgD.hasFDerivAt).fderiv (axis (i 0))
      change dist (coordDeriv (i 0) g x) (coordDeriv (i 0) (f n) x) < δ
      rw [dist_comm, dist_eq_norm, ← hEq]
      exact (hStep.trans hGrad).trans_lt hMD

/-- Local uniform convergence and the higher derivative bounds determine
all classical derivatives along the same sequence. -/
theorem convergesCjLoc_of_interior_derivative_bounds {Ω : Set Point} (hΩ : IsOpen Ω)
    (hEstimate : InteriorPoissonGradientEstimate) {Q : ℕ → Point → S0} {q : Point → S0}
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω) (hq : ContDiffOn ℝ ∞ q Ω)
    (h0 : ∀ K : Set Point, IsCompact K → K ⊆ Ω → TendstoUniformlyOn Q q atTop K)
    (hBound : ∀ k (K : Set Point), IsCompact K → K ⊆ Ω → ∃ B > (0 : ℝ), ∀ᶠ n in atTop,
      ∀ x ∈ K, ‖iteratedFDeriv ℝ (k + 2) (Q n) x‖ ≤ B) :
    ∀ j : ℕ, ConvergesCjLoc j Ω Q q := by
  intro j
  refine ⟨fun n => (contDiffOn_infty.mp (hQ n)) j, (contDiffOn_infty.mp hq) j, ?_⟩
  intro k _ K hK hKΩ
  refine tendstoUniformlyOn_iff.mpr ?_
  intro d hd
  let δ := d / (2 * (3 : ℝ) ^ k)
  have hδ : 0 < δ := div_pos hd (by positivity)
  have hEach (i : Fin k → Fin 3) := tendstoUniformlyOn_iff.mp
    (coordinateDerivative_locallyUniformly_converges hΩ hEstimate hQ hq h0 hBound k i K hK hKΩ) δ hδ
  filter_upwards [eventually_all.2 hEach] with n hn x hx
  have hxΩ := hKΩ hx
  let f (y : Point) := Q n y - q y
  have hf : ContDiffOn ℝ ∞ f Ω := (hQ n).sub hq
  have hLocal (i : Fin k → Fin 3) : ‖iteratedCoordinateDerivative k i f x‖ ≤ δ := by
    have h := hn i x hx
    rw [dist_comm, dist_eq_norm] at h
    rw [show f = fun y => Q n y - q y from rfl, iteratedCoordinateDerivative_sub hΩ (hQ n) hq k i hxΩ]
    exact h.le
  have hF := norm_iteratedFDeriv_le_of_coordinateBounds hΩ hf k hxΩ hδ.le hLocal
  have hEq := fun_iteratedFDeriv_sub_apply
    (((contDiffOn_infty.mp (hQ n)) k x hxΩ).contDiffAt (hΩ.mem_nhds hxΩ))
    (((contDiffOn_infty.mp hq) k x hxΩ).contDiffAt (hΩ.mem_nhds hxΩ))
  rw [dist_comm, dist_eq_norm, ← hEq]
  refine hF.trans_lt ?_
  have hC : (3 : ℝ) ^ k * δ = d / 2 := by dsimp only [δ]; field_simp
  rw [hC]
  exact half_lt_self hd

/-- Strong local convergence of the smooth regular representatives gives
convergence in every classical order along the same sequence. -/
theorem convergesCjLoc_of_regular_penalized_solutions (a : BulkCoefficients)
    (hEstimate : InteriorPoissonGradientEstimate) (hMean : External.ClassicalScalarSubsolutionMeanValue)
    {Ω : Set Point} (hΩ : IsOpen Ω)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (q : Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω) (hq : ContDiffOn ℝ ∞ q Ω)
    (hEuler : ∀ n x, x ∈ Ω → (ε n : ℝ) ^ 2 • (laplacian (Q n) x : S0).val = bulkGradient a (Q n x))
    (hRange : BddAbove ((fun p : ℕ × Point => ‖Q p.1 p.2‖) '' (univ ×ˢ Ω)))
    (hStrong : StrongH1Loc Ω Q (fun n => ClassicalGradient (Q n)) q (ClassicalGradient q))
    (hBulk : ConvergesScaledPotentialLoc a Ω ε Q) :
    ∀ j, ConvergesCjLoc j Ω Q q := by
  obtain ⟨M, hM⟩ := hRange
  have hBound (n : ℕ) (x : Point) (hx : x ∈ Ω) : ‖Q n x‖ ≤ max 0 M :=
    (show ‖Q n x‖ ≤ M from hM ⟨(n, x), ⟨mem_univ _, hx⟩, rfl⟩).trans (le_max_right _ _)
  have hQ0 := convergesC0Loc_of_strongH1Loc_of_regular_penalized_solutions a hΩ hEstimate hMean
    ((contDiffOn_infty.mp hq) 2) ε Q hε hQ hEuler hBound hStrong hBulk
  have h0 (K : Set Point) (hK : IsCompact K) (hKΩ : K ⊆ Ω) : TendstoUniformlyOn Q q atTop K := by
    refine tendstoUniformlyOn_iff.mpr ?_
    intro δ hδ
    have hU := tendstoUniformlyOn_iff.mp (hQ0.2.2 0 le_rfl K hK hKΩ) δ hδ
    filter_upwards [hU] with n hn x hx
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      LinearIsometryEquiv.dist_map] using hn x hx
  apply convergesCjLoc_of_interior_derivative_bounds hΩ hEstimate hQ hq h0
  intro k K hK hKΩ
  exact exists_eventual_regular_compact_derivative_bound a hEstimate hMean hΩ hK hKΩ ε Q q hε
    hQ hq hEuler ⟨M, hM⟩ hStrong hBulk (k + 1)

end Thesis

end
