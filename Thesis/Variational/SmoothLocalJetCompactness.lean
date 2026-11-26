module

public import Thesis.External.InteriorCorrectionEstimates
import Thesis.Foundation.Frobenius
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.LinearAlgebra.Multilinear.Basis
import StratificationTheory.Compactness.CofinalCompactExhaustion

/-! One subsequence for all classical derivatives on compact subsets. -/

public section

noncomputable section

open Filter Metric Set
open scoped BoundedContinuousFunction ContDiff Matrix.Norms.Frobenius Topology

namespace Thesis

private abbrev Jet (j : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin j => Point) S0

local instance jetNormed (j : ℕ) :
    NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin j => Point) S0) :=
  ContinuousMultilinearMap.normedAddCommGroup

local instance jetNormedSpace (j : ℕ) :
    NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin j => Point) S0) :=
  ContinuousMultilinearMap.normedSpace'

local instance jetCLMNormed (j : ℕ) :
    NormedAddCommGroup (Point →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j => Point) S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

private theorem smooth_jet_differentiableAt {U : Set Point} (hU : IsOpen U)
    {v : Point → S0} (hv : ContDiffOn ℝ ∞ v U) (j : ℕ) {x : Point} (hx : x ∈ U) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ j v) x := by
  have hj : (1 : ℕ∞ω) + j ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    exact WithTop.coe_le_coe.mpr le_top
  exact (((hv x hx).contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right (m := 1) hj).differentiableAt one_ne_zero

private theorem jet_finiteDimensional (j : ℕ) : FiniteDimensional ℝ (Jet j) := by
  letI : FiniteDimensional ℝ S0 := Module.Finite.of_basis frobeniusBasis
  let B := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let L : Jet j →ₗ[ℝ] ((Fin j → Fin 3) → S0) :=
    { toFun := fun T i => T (fun k => B (i k))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective L ?_
  intro T S hTS
  exact ContinuousMultilinearMap.toMultilinearMap_injective
    (Module.Basis.ext_multilinear (fun _ => B) (fun i => congrFun hTS i))

private theorem all_compact_jet_bound {U K : Set Point} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {v : ℕ → Point → S0} (hv : ∀ n, ContDiffOn ℝ ∞ (v n) U) (j : ℕ)
    (hB : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ j (v n) x‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K → ‖iteratedFDeriv ℝ j (v n) x‖ ≤ C := by
  classical
  obtain ⟨C, hC, hB⟩ := hB
  obtain ⟨N, hN⟩ := eventually_atTop.1 hB
  have hL (n : ℕ) : ∃ L : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ j (v n) x‖ ≤ L :=
    hK.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv (hv n) hU (WithTop.coe_le_coe.mpr le_top)).mono hKU)
  choose L hL using hL
  let A := ∑ n ∈ Finset.range N, max (L n) 0
  have hA : 0 ≤ A := Finset.sum_nonneg fun n _ => le_max_right _ _
  refine ⟨C + A, add_nonneg hC hA, fun n x hx => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn x hx).trans (le_add_of_nonneg_right hA)
  · have hMem := Finset.mem_range.2 (lt_of_not_ge hn)
    exact (hL n x hx).trans ((le_max_left _ _).trans
      ((Finset.single_le_sum (fun i _ => le_max_right (L i) 0) hMem).trans (le_add_of_nonneg_left hC)))

private theorem jets_lipschitzOnWith_closedBall {U : Set Point} (hU : IsOpen U)
    {v : Point → S0} (hv : ContDiffOn ℝ ∞ v U) (j : ℕ)
    {x : Point} {r L : ℝ} (hL : 0 ≤ L) (hB : closedBall x r ⊆ U)
    (hNorm : ∀ z ∈ closedBall x r, ‖iteratedFDeriv ℝ (j + 1) v z‖ ≤ L) :
    LipschitzOnWith (Real.toNNReal L) (iteratedFDeriv ℝ j v) (closedBall x r) := by
  apply (convex_closedBall x r).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun z hz => smooth_jet_differentiableAt hU hv j (hB hz))
  intro z hz
  change ‖fderiv ℝ (iteratedFDeriv ℝ j v) z‖ ≤ (Real.toNNReal L : ℝ)
  rw [norm_fderiv_iteratedFDeriv, Real.coe_toNNReal _ hL]
  exact hNorm z hz

private theorem exists_compact_cthickening_in_open {E : Type*} [MetricSpace E] [LocallyCompactSpace E]
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ IsCompact (cthickening ρ K) ∧ cthickening ρ K ⊆ U := by
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_isCompact_cthickening
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  let ρ := min δ r
  exact ⟨ρ, lt_min hδ hr, hδK.of_isClosed_subset isClosed_cthickening (cthickening_mono (min_le_left _ _) K),
    (cthickening_mono (min_le_right _ _) K).trans hrU⟩

private theorem dist_le_real_mul_of_lipschitzOnWith {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {f : E → F} {K : Set E} {L : ℝ} (hL : 0 ≤ L) (hf : LipschitzOnWith (Real.toNNReal L) f K)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) : dist (f x) (f y) ≤ L * dist x y := by
  simpa only [Real.coe_toNNReal _ hL] using hf.dist_le_mul x hx y hy

private theorem exists_jets_close_dist_bound {U K : Set Point} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    {v : ℕ → Point → S0} (hv : ∀ n, ContDiffOn ℝ ∞ (v n) U)
    (hBound : ∀ T : Set Point, IsCompact T → T ⊆ U → ∀ j : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ T → ‖iteratedFDeriv ℝ j (v n) x‖ ≤ C)
    (j : ℕ) :
    ∃ L ≥ (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ n x, x ∈ K → ∀ y ∈ closedBall x ρ,
      dist (iteratedFDeriv ℝ j (v n) x) (iteratedFDeriv ℝ j (v n) y) ≤ L * dist x y := by
  obtain ⟨ρ, hρ, hT, hTU⟩ := exists_compact_cthickening_in_open hU hK hKU
  let T := cthickening ρ K
  obtain ⟨L, hL, hB⟩ := hBound T hT hTU (j + 1)
  refine ⟨L, hL, ρ, hρ, fun n x hx y hy => ?_⟩
  have hBT : closedBall x ρ ⊆ T := closedBall_subset_cthickening hx ρ
  have hLip := jets_lipschitzOnWith_closedBall hU (hv n) j hL (hBT.trans hTU)
    (fun z hz => hB n z (hBT hz))
  exact dist_le_real_mul_of_lipschitzOnWith (E := Point) (F := Jet j) hL hLip
    (mem_closedBall_self hρ.le) hy

private theorem jets_equicontinuous {U K : Set Point} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {v : ℕ → Point → S0} (hv : ∀ n, ContDiffOn ℝ ∞ (v n) U)
    (hBound : ∀ T : Set Point, IsCompact T → T ⊆ U → ∀ j : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ T → ‖iteratedFDeriv ℝ j (v n) x‖ ≤ C)
    (j : ℕ) (F : ℕ → (K →ᵇ Jet j)) (hF : ∀ n x, F n x = iteratedFDeriv ℝ j (v n) x.val) :
    Equicontinuous (fun g : Set.range F => (g.val : K → Jet j)) := by
  obtain ⟨L, hL, ρ, hρ, hDist⟩ := exists_jets_close_dist_bound hU hK hKU hv hBound j
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro η hη
  have hL' : 0 < L + 1 := by linarith only [hL]
  refine ⟨min ρ (η / (L + 1)), lt_min hρ (div_pos hη hL'), fun y hy g => ?_⟩
  obtain ⟨n, hn⟩ := g.property
  have hy' : dist y.val x.val < ρ := hy.trans_le (min_le_left _ _)
  have hyD : dist x.val y.val < η / (L + 1) := by rw [dist_comm]; exact hy.trans_le (min_le_right _ _)
  have hSub : dist (g.val x) (g.val y) = dist (F n x) (F n y) :=
    congrArg (fun w : K →ᵇ Jet j => dist (w x) (w y)) hn.symm
  have h := hDist n x.val x.property y.val (mem_closedBall.2 hy'.le)
  calc
    _ = _ := hSub
    _ = dist (iteratedFDeriv ℝ j (v n) x.val) (iteratedFDeriv ℝ j (v n) y.val) :=
      congrArg₂ dist (hF n x) (hF n y)
    _ ≤ _ := h
    _ ≤ (L + 1) * dist x.val y.val :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) dist_nonneg
    _ < η := by simpa only [mul_comm (L + 1)] using (lt_div_iff₀ hL').1 hyD

private theorem jets_ArzelaAscoli {U K : Set Point} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {v : ℕ → Point → S0} (hv : ∀ n, ContDiffOn ℝ ∞ (v n) U)
    (hBound : ∀ T : Set Point, IsCompact T → T ⊆ U → ∀ j : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ T → ‖iteratedFDeriv ℝ j (v n) x‖ ≤ C)
    (j : ℕ) [CompactSpace K]
    (F : ℕ → (K →ᵇ Jet j)) (hF : ∀ n x, F n x = iteratedFDeriv ℝ j (v n) x.val) :
    IsCompact (closure (range F)) := by
  letI : ProperSpace (Jet j) := @FiniteDimensional.proper ℝ _ (Jet j) _ _ _ (jet_finiteDimensional j)
  obtain ⟨C, _, hC⟩ := hBound K hK hKU j
  refine BoundedContinuousFunction.arzela_ascoli (closedBall (0 : Jet j) C) (isCompact_closedBall _ _) _
    ?_ (jets_equicontinuous hU hK hKU hv hBound j F hF)
  rintro _ x ⟨n, rfl⟩
  exact mem_closedBall_zero_iff.2 (by rw [hF]; exact hC n x.val x.property)


private theorem exists_locally_uniform_jet_subsequence {U : Set Point} (hU : IsOpen U)
    {v : ℕ → Point → S0} (hv : ∀ n, ContDiffOn ℝ ∞ (v n) U)
    (hBound : ∀ (K : Set Point), IsCompact K → K ⊆ U → ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ j (v n) x‖ ≤ C) :
    ∃ (κ : ℕ → ℕ) (J : ∀ j : ℕ, Point → Jet j), StrictMono κ ∧
      ∀ j, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ j (v (κ n))) (J j) atTop U := by
  classical
  obtain ⟨K, hK, hKU, _, hCover, hCofinal⟩ :=
    StratificationTheory.Compactness.exists_cofinal_compact_exhaustion_openDomain ⟨U, hU⟩
  letI : ∀ i : ℕ, CompactSpace (K i) := fun i => isCompact_iff_compactSpace.1 (hK i)
  let X (i : ℕ × ℕ) := K i.2 →ᵇ Jet i.1
  let F (n : ℕ) (i : ℕ × ℕ) : X i :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x => iteratedFDeriv ℝ i.1 (v n) x.val,
        (ContinuousOn.continuousOn_iteratedFDeriv (hv n) hU (WithTop.coe_le_coe.mpr le_top)).comp_continuous
          continuous_subtype_val (fun x => hKU i.2 x.property)⟩
  let A (i : ℕ × ℕ) : Set (X i) := closure (range fun n => F n i)
  have hA (i : ℕ × ℕ) : IsCompact (A i) :=
    jets_ArzelaAscoli hU (hK i.2) (hKU i.2) hv
      (fun K hK hKU j => all_compact_jet_bound hU hK hKU hv j (hBound K hK hKU j))
      i.1 (fun n => F n i) (fun _ _ => rfl)
  have hAF : ∀ n, F n ∈ {J : ∀ i, X i | ∀ i, J i ∈ A i} :=
    fun n i => subset_closure (mem_range_self n)
  obtain ⟨g, _, κ, hκ, hg⟩ := (isCompact_pi_infinite hA).tendsto_subseq hAF
  have hg' (i : ℕ × ℕ) : Tendsto (fun n => F (κ n) i) atTop (𝓝 (g i)) :=
    (tendsto_pi_nhds.1 hg) i
  have hIn {x : Point} (hx : x ∈ U) : ∃ i, x ∈ K i := mem_iUnion.1 (hCover.symm ▸ hx)
  let J (j : ℕ) (x : Point) : Jet j :=
    if hx : x ∈ U then g (j, (hIn hx).choose) ⟨x, (hIn hx).choose_spec⟩ else 0
  have hAt (j i : ℕ) (x : K i) : Tendsto (fun n => iteratedFDeriv ℝ j (v (κ n)) x.val)
      atTop (𝓝 (g (j, i) x)) :=
    (continuous_eval_const x).continuousAt.tendsto.comp (hg' (j, i))
  have hJ (j i : ℕ) (x : K i) : J j x.val = g (j, i) x := by
    have hxU := hKU i x.property
    rw [show J j x.val = g (j, (hIn hxU).choose) ⟨x.val, (hIn hxU).choose_spec⟩ from dif_pos hxU]
    exact tendsto_nhds_unique (hAt j (hIn hxU).choose ⟨x.val, (hIn hxU).choose_spec⟩) (hAt j i x)
  refine ⟨κ, J, hκ, fun j => (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).2 ?_⟩
  intro T hTU hT
  obtain ⟨i, hTi⟩ := hCofinal T hT hTU
  refine Metric.tendstoUniformlyOn_iff.2 fun η hη => ?_
  filter_upwards [(Metric.tendsto_nhds.1 (hg' (j, i))) η hη] with n hn y hy
  let x : K i := ⟨y, hTi hy⟩
  change dist (J j x.val) (F (κ n) (j, i) x) < η
  rw [hJ, dist_comm]
  exact (BoundedContinuousFunction.dist_coe_le_dist x).trans_lt hn

private theorem smooth_limit_of_locally_uniform_jets {U : Set Point} (hU : IsOpen U)
    {v : ℕ → Point → S0} (hv : ∀ n, ContDiffOn ℝ ∞ (v n) U)
    (J : ∀ j : ℕ, Point → Jet j)
    (hJ : ∀ j, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ j (v n)) (J j) atTop U) :
    ∃ w : Point → S0, ContDiffOn ℝ ∞ w U ∧
      ∀ j : ℕ, ConvergesCjLoc j U v w := by
  let C (j : ℕ) := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Point) S0
  have hC (j : ℕ) :
      TendstoLocallyUniformlyOn (fun n => fderiv ℝ (iteratedFDeriv ℝ j (v n)))
        (fun x => C j (J (j + 1) x)) atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    have h := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 (hJ (j + 1)) K hKU hK
    have hUnif := (C j).toContinuousLinearEquiv.toContinuousLinearMap.uniformContinuous
    simpa only [fderiv_iteratedFDeriv, C, Function.comp_def, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hUnif.comp_tendstoUniformlyOn h
  have hDerivative (j : ℕ) (x : Point) (hx : x ∈ U) :
      HasFDerivAt (J j) (C j (J (j + 1) x)) x := by
    apply hasFDerivAt_of_tendstoLocallyUniformlyOn hU (hC j) _ (fun y hy => (hJ j).tendsto_at hy) hx
    intro n y hy
    exact (smooth_jet_differentiableAt hU (hv n) j hy).hasFDerivAt
  let w (x : Point) := (J 0 x).curry0
  let p (x : Point) : FormalMultilinearSeries ℝ Point S0 := fun j => J j x
  have hp : HasFTaylorSeriesUpToOn (↑(⊤ : ℕ∞) : ℕ∞ω) w p U :=
    ⟨fun _ _ => rfl, fun j _ x hx => (hDerivative j x hx).hasFDerivWithinAt,
      fun j _ => (hJ j).continuousOn (Frequently.of_forall fun n =>
        ContinuousOn.continuousOn_iteratedFDeriv (hv n) hU (WithTop.coe_le_coe.mpr le_top))⟩
  have hw : ContDiffOn ℝ ∞ w U := hp.contDiffOn
  have hEq (j : ℕ) : EqOn (iteratedFDeriv ℝ j w) (J j) U := by
    intro x hx
    exact ((hp.eq_iteratedFDerivWithin_of_uniqueDiffOn (WithTop.coe_le_coe.mpr le_top)
      hU.uniqueDiffOn hx).trans (iteratedFDerivWithin_of_isOpen j hU hx)).symm
  refine ⟨w, hw, fun j => ⟨fun n => (hv n).of_le (WithTop.coe_le_coe.mpr le_top),
    hw.of_le (WithTop.coe_le_coe.mpr le_top), fun k _ K hK hKU => ?_⟩⟩
  exact ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 (hJ k) K hKU hK).congr_right
    (fun x hx => (hEq k (hKU hx)).symm)

/-- Mathlib's Arzelà–Ascoli and uniform derivative limits, along a
single subsequence of the countable compact exhaustion and all derivative orders. -/
theorem smoothLocalJetCompactness : External.SmoothLocalJetCompactness := by
  intro U hU v hv hB
  obtain ⟨κ, J, hκ, hJ⟩ := exists_locally_uniform_jet_subsequence hU hv hB
  obtain ⟨w, hw, hConv⟩ := smooth_limit_of_locally_uniform_jets hU (fun n => hv (κ n)) J hJ
  exact ⟨κ, w, hκ, hw, fun j _ => hConv j⟩

end Thesis
