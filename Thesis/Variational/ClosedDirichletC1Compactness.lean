module

public import Thesis.Variational.SmoothDomainClosedDerivative
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Thesis.Variational.BoundaryPoissonEstimate

/-! Compactness of the actual classical value and derivative on the
closure of a smooth domain. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open scoped BigOperators BoundedContinuousFunction ContDiff Matrix.Norms.Frobenius

namespace Thesis

local instance closedC1DerivativeNormed : NormedAddCommGroup (Point →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance closedC1DerivativeSpace : NormedSpace ℝ (Point →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance closedC1DerivativeMetric : MetricSpace (Point →L[ℝ] S0) :=
  closedC1DerivativeNormed.toMetricSpace

local instance closedC1TensorUniform : IsUniformAddGroup S0 :=
  SeminormedAddCommGroup.to_isUniformAddGroup

local instance closedC1ColumnMapNormed : NormedAddCommGroup (Gradient →L[ℝ] Point →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

private theorem exists_uniform_subsequence_of_holder
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {K : Set Point}
    (hK : IsCompact K) (v : ℕ → Point → E) (hv : ∀ n, ContinuousOn (v n) K)
    {B L α : ℝ} (_hB : 0 ≤ B) (hL : 0 ≤ L) (hα : 0 < α)
    (hNorm : ∀ n x, x ∈ K → ‖v n x‖ ≤ B)
    (hMod : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist (v n x) (v n y) ≤ L * dist x y ^ α) :
    ∃ (κ : ℕ → ℕ) (w : Point → E), StrictMono κ ∧ ContinuousOn w K ∧
      TendstoUniformlyOn (fun n => v (κ n)) w atTop K := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F (n : ℕ) : K →ᵇ E := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => v n x, continuousOn_iff_continuous_restrict.1 (hv n)⟩
  have hEqui : Equicontinuous ((↑) : range F → K → E) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    let m (t : ℝ) := L * t^α
    have hm : ContinuousAt m 0 := continuousAt_const.mul (Real.continuousAt_rpow_const 0 α (Or.inr hα.le))
    obtain ⟨δ,hδ,hUδ⟩ := Metric.continuousAt_iff.mp hm ε hε
    refine ⟨δ,hδ,?_⟩
    intro y hy g
    obtain ⟨n,hn⟩ := g.property
    have hδ' : dist x.val y.val < δ := by rw [dist_comm]; exact hy
    have hM := hUδ (x := dist x.val y.val)
      (by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg] using hδ')
    have hZero : m 0 = 0 := by simp [m,Real.zero_rpow hα.ne']
    rw [hZero,Real.dist_eq,sub_zero] at hM
    change |L * dist x.val y.val ^ α| < ε at hM
    rw [abs_of_nonneg (mul_nonneg hL (Real.rpow_nonneg dist_nonneg _))] at hM
    change dist (g.val x) (g.val y) < ε
    rw [← hn]
    exact (hMod n x.val x.property y.val y.property).trans_lt hM
  have hCompact : IsCompact (closure (range F)) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : E) B) (isCompact_closedBall _ _)
      (range F) (by
        rintro _ x ⟨n,rfl⟩
        exact mem_closedBall_zero_iff.2 (hNorm n x x.property)) hEqui
  obtain ⟨G,_,κ,hκ,hLim⟩ := hCompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  let w (x : Point) : E := if hx : x ∈ K then G ⟨x,hx⟩ else 0
  refine ⟨κ,w,hκ,?_,?_⟩
  · apply continuousOn_iff_continuous_restrict.2
    change Continuous (fun x : K => w x)
    rw [show (fun x : K => w x) = (fun x : K => G x) from funext fun x => dif_pos x.property]
    with_unfolding_all exact G.continuous
  · refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    filter_upwards [Metric.tendsto_nhds.1 hLim ε hε] with n hn x hx
    let z : K := ⟨x,hx⟩
    rw [show w x = G z from dif_pos hx,dist_comm]
    exact (BoundedContinuousFunction.dist_coe_le_dist z).trans_lt hn

private theorem gradientFromColumns_reconstruct (D : Point →L[ℝ] S0) :
    gradientFromColumns (fun j => D (axis j)) = D := by
  apply ContinuousLinearMap.ext
  intro x
  rw [gradientFromColumns_apply]
  have hx : (∑ j : Fin 3, x j • axis j) = x := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,axis] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  have h := congrArg D hx
  simp only [map_sum,map_smul] at h
  exact h

private theorem gradientFromColumns_uniformContinuous : UniformContinuous gradientFromColumns := by
  classical
  let T (i : Fin 3) : S0 →L[ℝ] Point →L[ℝ] S0 :=
    ContinuousLinearMap.smulRightL ℝ Point S0 (EuclideanSpace.proj i)
  have hT (i : Fin 3) : UniformContinuous (fun A : Gradient => T i (A i)) :=
    (T i).uniformContinuous.comp
      ((uniformContinuous_pi.1 (show UniformContinuous (id : Gradient → Gradient) from uniformContinuous_id)) i)
  have hSum (I : Finset (Fin 3)) : UniformContinuous (fun A : Gradient => ∑ i ∈ I,T i (A i)) := by
    induction I using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (uniformContinuous_const : UniformContinuous
        (fun _ : Gradient => (0 : Point →L[ℝ] S0)))
    | @insert i S hi ih =>
        simpa only [Finset.sum_insert hi] using (hT i).add ih
  have hEq : gradientFromColumns = (fun A : Gradient => ∑ i : Fin 3, T i (A i)) := by
    funext A
    unfold gradientFromColumns
    exact Finset.sum_congr rfl (fun _ _ => rfl)
  rw [hEq]
  exact hSum Finset.univ

/-- Compactness in the actual first derivative and values on the closed
domain, on one common subsequence. -/
theorem IsSmoothDomain.exists_closedC1_subsequence {U : Set Point} (hU : IsSmoothDomain U)
    {v : ℕ → Point → S0} (hv : ∀ n, ContDiffOn ℝ 2 (v n) (closure U))
    {B L α : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (hα : 0 < α)
    (hNorm : ∀ n x, x ∈ closure U → ‖((v n x, closureGradient U (v n) x) : S0 × Gradient)‖ ≤ B)
    (hMod : ∀ n x, x ∈ closure U → ∀ y, y ∈ closure U →
      dist ((v n x, closureGradient U (v n) x) : S0 × Gradient)
        (v n y, closureGradient U (v n) y) ≤ L * dist x y ^ α) :
    ∃ (κ : ℕ → ℕ) (w : Point → S0) (D : Point → Point →L[ℝ] S0), StrictMono κ ∧
      ContDiffOn ℝ 1 w (closure U) ∧
      TendstoUniformlyOn (fun n => v (κ n)) w atTop (closure U) ∧
      TendstoUniformlyOn (fun n => fderivWithin ℝ (v (κ n)) (closure U)) D atTop (closure U) ∧
      ∀ x ∈ U, HasFDerivAt w (D x) x := by
  let K := closure U
  have hK : IsCompact K := hU.1.2.2.isCompact_closure
  have hVc (n : ℕ) : ContinuousOn (v n) K := (hv n).continuousOn
  have hxNorm (n : ℕ) (x : Point) (hx : x ∈ K) : ‖v n x‖ ≤ B :=
    (le_max_left _ _).trans (hNorm n x hx)
  have hxMod (n : ℕ) (x : Point) (hx : x ∈ K) (y : Point) (hy : y ∈ K) :
      dist (v n x) (v n y) ≤ L * dist x y ^ α :=
    (le_max_left _ _).trans (hMod n x hx y hy)
  letI : FiniteDimensional ℝ S0 := Module.Finite.of_basis frobeniusBasis
  letI : ProperSpace S0 := FiniteDimensional.proper ℝ _
  obtain ⟨κ₀,w,hκ₀,hWc,hW⟩ := exists_uniform_subsequence_of_holder hK v hVc hB hL hα hxNorm hxMod
  let V (n : ℕ) := closureGradient U (v (κ₀ n))
  have hVc' (n : ℕ) : ContinuousOn (V n) K := by
    apply continuousOn_pi.2
    intro j
    exact continuousOn_closureGradient_column hU.uniqueDiffOn_closure ((hv (κ₀ n)).of_le (by norm_num)) j
  have hdNorm (n : ℕ) (x : Point) (hx : x ∈ K) : ‖V n x‖ ≤ B :=
    (le_max_right _ _).trans (hNorm (κ₀ n) x hx)
  have hdMod (n : ℕ) (x : Point) (hx : x ∈ K) (y : Point) (hy : y ∈ K) :
      dist (V n x) (V n y) ≤ L * dist x y ^ α :=
    (le_max_right _ _).trans (hMod (κ₀ n) x hx y hy)
  letI : ProperSpace Gradient := inferInstance
  obtain ⟨κ₁,C,hκ₁,hCc,hConv⟩ := exists_uniform_subsequence_of_holder hK V hVc' hB hL hα hdNorm hdMod
  let κ := κ₀ ∘ κ₁
  let D := gradientFromColumns ∘ C
  have hDc : ContinuousOn D K := gradientFromColumns_uniformContinuous.continuous.comp_continuousOn hCc
  have hDU : TendstoUniformlyOn (fun n => fderivWithin ℝ (v (κ n)) K) D atTop K := by
    have h := gradientFromColumns_uniformContinuous.comp_tendstoUniformlyOn hConv
    have hEq (n : ℕ) : gradientFromColumns ∘ V (κ₁ n) = fderivWithin ℝ (v (κ n)) K :=
      funext fun x => gradientFromColumns_reconstruct (fderivWithin ℝ (v (κ n)) K x)
    simpa only [hEq] using h
  have hWU : TendstoUniformlyOn (fun n => v (κ n)) w atTop K := by
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    exact hκ₁.tendsto_atTop.eventually (Metric.tendstoUniformlyOn_iff.1 hW _ hε)
  have hDer (x : Point) (hx : x ∈ U) : HasFDerivAt w (D x) x := by
    refine hasFDerivAt_of_tendstoUniformlyOn (f := fun n => v (κ n)) hU.1.1
      (hDU.mono subset_closure) ?_ ?_ hx
    · intro n y hy
      have hyK := Filter.mem_of_superset (hU.1.1.mem_nhds hy) subset_closure
      have hd := (((hv (κ n)) y (subset_closure hy)).contDiffAt hyK).differentiableAt two_ne_zero
      have hEq : fderivWithin ℝ (v (κ n)) K y = fderiv ℝ (v (κ n)) y :=
        fderivWithin_eq_fderiv (uniqueDiffWithinAt_of_mem_nhds hyK) hd
      exact hEq.symm ▸ hd.hasFDerivAt
    · exact fun y hy => hWU.tendsto_at (subset_closure hy)
  exact ⟨κ,w,D,hκ₀.comp hκ₁,hU.contDiffOn_one_of_continuous_derivative hWc hDc hDer,hWU,hDU,hDer⟩

end Thesis
