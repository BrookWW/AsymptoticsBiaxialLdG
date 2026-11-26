module

public import Thesis.Interpolation.CylinderNativeHeightTrace
public import Thesis.Interpolation.CylinderRadialProductTrace
public import Thesis.Interpolation.NativeBallTraceEstimate
import StratificationTheory.Foundation.RadialTraceCompatibility
import StratificationTheory.Foundation.BoundedFiberL2Trace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.ContinuousMap.Compact
import HarmonicMaps.Analysis.SobolevDifference

/-! Strong convergence of the actual axial and radial traces under Sobolev graph convergence. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ContDiff ENNReal NNReal Topology

namespace Thesis.MeasureGeometry

private theorem tendsto_of_sq_trace_bound {ι E : Type*} {l : Filter ι}
    [NormedAddCommGroup E] {H : ι → E} {A : ι → ℝ}
    (hA : Tendsto A l (𝓝 0)) (hBound : ∀ k, ‖H k‖ ^ 2 ≤ A k) :
    Tendsto H l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hS := Real.continuous_sqrt.continuousAt.tendsto.comp hA
  rw [Real.sqrt_zero] at hS
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hS
    (fun k => norm_nonneg (H k)) (fun k => Real.le_sqrt_of_sq_le (hBound k))

private theorem tendsto_sobolev_graph_budget_zero {ι : Type*} {l : Filter ι}
    {n q : ℕ} {U : Set (Domain n)}
    {f : ι → Domain n → Ambient q} {D : ι → Domain n → HarmonicMaps.Gradient n q}
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict U))
    (hD : ∀ k i, MemLp (fun x => D k x i) 2 (volume.restrict U))
    (hfv : Tendsto (fun k => eLpNorm (f k) 2 (volume.restrict U)) l (𝓝 0))
    (hDv : ∀ i, Tendsto (fun k => eLpNorm (fun x => D k x i) 2 (volume.restrict U)) l (𝓝 0))
    (A C : ℝ) :
    Tendsto (fun k => A * (∫ x in U, ‖f k x‖ ^ 2) + C * (∫ x in U, hsNormSq (D k x)))
      l (𝓝 0) := by
  have hSq {g : ι → Domain n → Ambient q}
      (hg : ∀ k, MemLp (g k) 2 (volume.restrict U))
      (hgv : Tendsto (fun k => eLpNorm (g k) 2 (volume.restrict U)) l (𝓝 0)) :
      Tendsto (fun k => ∫ x in U, ‖g k x‖ ^ 2) l (𝓝 0) := by
    have ht := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hgv).pow 2
    simpa only [Function.comp_apply, ENNReal.toReal_zero, zero_pow (by decide : 2 ≠ 0),
      ← integral_norm_sq_eq_eLpNorm_two_toReal_sq (hg _)] using ht
  have hGradEq (k : ι) : (∫ x in U, hsNormSq (D k x)) = ∑ i : Fin n, ∫ x in U, ‖D k x i‖ ^ 2 :=
    integral_finsetSum Finset.univ (fun i _ => (hD k i).integrable_norm_pow (by decide : 2 ≠ 0))
  have hGrad : Tendsto (fun k => ∫ x in U, hsNormSq (D k x)) l (𝓝 0) := by
    simp_rw [hGradEq]
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => hSq (fun k => hD k i) (hDv i))
  simpa only [mul_zero, add_zero] using ((hSq hf hfv).const_mul A).add (hGrad.const_mul C)

private theorem pair_eLpNorm_tendsto_zero_of_strong {X E : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}
    {f : ℕ → X → E} {g : X → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (fun x => f k x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => eLpNorm (fun x => f p.1 x - f p.2 x) 2 μ) atTop (𝓝 0) := by
  let F (k : ℕ) := (hf k).toLp (f k)
  have hL : Tendsto F atTop (𝓝 (hg.toLp g)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).2 hconv
  have hD := cauchySeq_iff_tendsto_dist_atTop_0.mp hL.cauchySeq
  have hE := ENNReal.tendsto_ofReal hD
  have h' : Tendsto (fun p : ℕ × ℕ => eLpNorm (f p.1 - f p.2) 2 μ) atTop (𝓝 0) := by
    simpa only [F, ← edist_dist, Lp.edist_toLp_toLp, ENNReal.ofReal_zero] using hE
  exact h'.congr fun _ => rfl

private theorem trace_unique {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {a b : ℝ} (hab : a < b) {f : X × ℝ → E}
    {H K : C(Icc a b, Lp E 2 μ)}
    (hH : ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo a b,
      ∃ h : MemLp (fun x => f (x, r)) 2 μ, H ⟨r, hr.1.le, hr.2.le⟩ = h.toLp _)
    (hK : ∀ᵐ r ∂volume, ∀ hr : r ∈ Ioo a b,
      ∃ h : MemLp (fun x => f (x, r)) 2 μ, K ⟨r, hr.1.le, hr.2.le⟩ = h.toLp _) :
    H = K :=
  continuous_Lp_representatives_eq_of_ae_slices hab H K hH hK
    (Eventually.of_forall fun _ _ => EventuallyEq.rfl)

private theorem represents_sphereTrace_sub {q : ℕ} {a b : ℝ}
    {u v : Point → Ambient q} {H K : NativeSphereRadialL2Trace q a b}
    (hH : RepresentsNativeSphereRadialTrace u H) (hK : RepresentsNativeSphereRadialTrace v K) :
    RepresentsNativeSphereRadialTrace (u - v) (H - K) := by
  filter_upwards [hH, hK] with t htH htK ht
  obtain ⟨hu, hHu⟩ := htH ht
  obtain ⟨hv, hKv⟩ := htK ht
  refine ⟨hu.sub hv, ?_⟩
  change H _ - K _ = _
  rw [hHu, hKv, ← hu.toLp_sub hv]
  rfl

/-- For a continuous map on a Euclidean closed ball, the actual radial curve
has the original boundary value at every radius. -/
theorem exists_nativeSphereTrace_of_continuousOn_closedBall {q : ℕ} {a R : ℝ}
    (ha : 0 ≤ a) (haR : a < R) {u : Point → Ambient q}
    (hu : ContinuousOn u (closedBall (0 : Point) R)) :
    ∃ T : NativeSphereRadialL2Trace q a R, RepresentsNativeSphereRadialTrace u T ∧
      ∀ t : Icc a R, (T t : UnitTensorSphere → Ambient q) =ᵐ[tensorSphereMeasure]
        fun θ => u (t.val • θ.val) := by
  let F (p : UnitTensorSphere × ℝ) := u (p.2 • p.1.val)
  have hn (θ : UnitTensorSphere) : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
  have hIn (θ : UnitTensorSphere) {t : ℝ} (ht : t ∈ Icc a R) :
      t • θ.val ∈ closedBall (0 : Point) R := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (ha.trans ht.1), hn, mul_one]
    exact ht.2
  letI : IsFiniteMeasure tensorSphereMeasure := by
    change IsFiniteMeasure (Measure.euclideanHausdorffMeasure (3 - 1) :
      Measure (sphere (0 : Domain 3) 1))
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 3)]
    infer_instance
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Point) R).exists_bound_of_continuousOn hu
  have hMeas : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a R,
      AEStronglyMeasurable (fun θ => F (θ, t)) tensorSphereMeasure := by
    refine Eventually.of_forall fun t ht => ?_
    have h := hu.comp_continuous (continuous_subtype_val.const_smul t)
      (fun θ => hIn θ (Ioo_subset_Icc_self ht))
    exact h.aestronglyMeasurable
  have hCont : ∀ᵐ θ : UnitTensorSphere ∂tensorSphereMeasure,
      ContinuousOn (fun t => F (θ, t)) (Icc a R) := by
    refine Eventually.of_forall fun θ => ?_
    have hRay : Continuous (fun t : ℝ => t • θ.val) := continuous_id.smul continuous_const
    exact hu.comp hRay.continuousOn (fun _ ht => hIn θ ht)
  have hBound : ∀ᵐ θ : UnitTensorSphere ∂tensorSphereMeasure, ∀ t ∈ Icc a R, ‖F (θ, t)‖ ≤ M :=
    Eventually.of_forall fun θ _ ht => hM _ (hIn θ ht)
  obtain ⟨T, hT, _⟩ := exists_continuous_L2_trace_of_bounded_fiber_continuity tensorSphereMeasure haR hMeas hCont hBound
  refine ⟨T, Eventually.of_forall fun t ht => hT ⟨t, ht.1.le, ht.2.le⟩, ?_⟩
  intro t
  obtain ⟨ht, hVal⟩ := hT t
  rw [hVal]
  exact ht.coeFn_toLp

/-- The original sphere-radius trace converges at each closed-interval
radius when the maps and the actual weak columns converge in the ball. -/
theorem nativeSphereTrace_tendsto_of_strong_graph {q : ℕ} {a R : ℝ}
    (ha : 0 < a) (haR : a < R)
    {u : ℕ → Point → Ambient q} {D : ℕ → Point → HarmonicMaps.Gradient 3 q}
    {v : Point → Ambient q} {J : Point → HarmonicMaps.Gradient 3 q}
    (hu : ∀ k, MemW12 (ballDomain (0 : Point) R) (u k) (D k))
    (hv : MemW12 (ballDomain (0 : Point) R) v J)
    (hMap : Tendsto (fun k => eLpNorm (u k - v) 2 (volume.restrict (ball (0 : Point) R))) atTop (𝓝 0))
    (hGrad : ∀ i, Tendsto (fun k => eLpNorm (fun x => D k x i - J x i) 2
      (volume.restrict (ball (0 : Point) R))) atTop (𝓝 0))
    {P : ℕ → NativeSphereRadialL2Trace q a R} {T : NativeSphereRadialL2Trace q a R}
    (hP : ∀ k, RepresentsNativeSphereRadialTrace (u k) (P k))
    (hT : RepresentsNativeSphereRadialTrace v T) (t : Icc a R) :
    Tendsto (fun k => P k t) atTop (𝓝 (T t)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  let A : ℝ := (2 / (R - a)) * (a ^ (3 - 1 : ℕ))⁻¹
  let C : ℝ := (2 * (R - a)) * (a ^ (3 - 1 : ℕ))⁻¹
  have hSob (k : ℕ) := (hu k).sub hv
  apply tendsto_of_sq_trace_bound
    (tendsto_sobolev_graph_budget_zero (fun k => (hSob k).2.1)
      (fun k => (hSob k).2.2) hMap hGrad A C)
  intro k
  obtain ⟨Q, hQ, hBound⟩ := exists_native_ball_radial_trace_with_estimate (by decide : 0 < 3) ha haR (hSob k)
  have hEq : P k - T = Q :=
    trace_unique (f := fun p : UnitTensorSphere × ℝ => (u k - v) (p.2 • p.1.val))
      haR (represents_sphereTrace_sub (hP k) hT) hQ
  change ‖(P k - T) t‖ ^ 2 ≤ _
  rw [hEq]
  simpa only [A, C, mul_assoc, ballDomain] using hBound t

/-- Strong convergence of the original complete graph on a cylinder
gives convergence of its horizontal native traces at every height. -/
theorem cylinderHeightTrace_tendsto_of_strong_graph {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hI : lo < hi)
    {u : ℕ → Point → Ambient q} {D : ℕ → Point → HarmonicMaps.Gradient 3 q}
    {v : Point → Ambient q} {J : Point → HarmonicMaps.Gradient 3 q}
    (hu : ∀ k, MemW12 (translatedAxisCylinderDomain B c R lo hi) (u k) (D k))
    (hv : MemW12 (translatedAxisCylinderDomain B c R lo hi) v J)
    (hMap : Tendsto (fun k => eLpNorm (u k - v) 2
      (volume.restrict (translatedAxisCylinder c (B 2) R lo hi))) atTop (𝓝 0))
    (hGrad : ∀ i, Tendsto (fun k => eLpNorm (fun x => D k x i - J x i) 2
      (volume.restrict (translatedAxisCylinder c (B 2) R lo hi))) atTop (𝓝 0))
    {P : ℕ → CylinderHeightL2Trace q R lo hi} {H : CylinderHeightL2Trace q R lo hi}
    (hP : ∀ k, RepresentsCylinderHeightL2Trace B c (u k) (P k))
    (hH : RepresentsCylinderHeightL2Trace B c v H) (t : Icc lo hi) :
    Tendsto (fun k => P k t) atTop (𝓝 (H t)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  have hSob (k : ℕ) := (hu k).sub hv
  apply tendsto_of_sq_trace_bound
    (tendsto_sobolev_graph_budget_zero (fun k => (hSob k).2.1)
      (fun k => (hSob k).2.2) hMap hGrad (2 / (hi - lo)) (2 * (hi - lo)))
  intro k
  obtain ⟨Q, hQ, hBound⟩ := exists_cylinderHeight_trace_with_estimate B c hI _ _ (hSob k)
  have hEq : P k - H = Q :=
    trace_unique (f := fun p : Plane × ℝ => (u k - v) (c + axisChart B p))
      hI ((hP k).sub hH) hQ
  change ‖(P k - H) t‖ ^ 2 ≤ _
  rw [hEq]
  exact hBound t

private theorem represents_trace_of_product_limit {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {σ : Measure X} [IsFiniteMeasure σ] {a b : ℝ}
    {f : ℕ → X × ℝ → E} {g : X × ℝ → E}
    (hf : ∀ k, MemLp (f k) 2 (σ.prod (volume.restrict (Icc a b))))
    (hg : MemLp g 2 (σ.prod (volume.restrict (Icc a b))))
    (hF : Tendsto (fun k => eLpNorm (f k - g) 2 (σ.prod (volume.restrict (Icc a b)))) atTop (𝓝 0))
    {P : ℕ → C(Icc a b, Lp E 2 σ)} {H : C(Icc a b, Lp E 2 σ)}
    (hP : ∀ k, ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ h : MemLp (fun x => f k (x, t)) 2 σ, P k ⟨t, ht.1.le, ht.2.le⟩ = h.toLp _)
    (hH : Tendsto P atTop (𝓝 H)) :
    ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ h : MemLp (fun x => g (x, t)) 2 σ, H ⟨t, ht.1.le, ht.2.le⟩ = h.toLp _ := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  have hν : ν = volume.restrict (Ioo a b) := Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  have hCon := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fun k => (hf k).aestronglyMeasurable) hg.aestronglyMeasurable hF
  obtain ⟨κ, hκ, hκAE⟩ := hCon.exists_seq_tendsto_ae
  have hSlice : ∀ᵐ t ∂ν, ∀ᵐ x ∂σ,
      Tendsto (fun k => f (κ k) (x, t)) atTop (𝓝 (g (x, t))) :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hκAE)
  have hGmem : ∀ᵐ t ∂ν, MemLp (fun x => g (x, t)) 2 σ := by
    filter_upwards [hg.aestronglyMeasurable.prodMk_right,
      (hg.integrable_norm_pow (by decide : 2 ≠ 0)).prod_left_ae] with t htM htI
    exact (memLp_two_iff_integrable_sq_norm htM).2 htI
  have hRaw : ∀ᵐ t ∂ν, ∀ k, ∀ ht : t ∈ Ioo a b,
      ∃ h : MemLp (fun x => f k (x, t)) 2 σ, P k ⟨t, ht.1.le, ht.2.le⟩ = h.toLp _ :=
    (ae_all_iff.2 hP).filter_mono (ae_mono Measure.restrict_le_self)
  have hFull : ∀ᵐ t ∂ν, ∀ ht : t ∈ Ioo a b,
      ∃ h : MemLp (fun x => g (x, t)) 2 σ, H ⟨t, ht.1.le, ht.2.le⟩ = h.toLp _ := by
    filter_upwards [hSlice, hGmem, hRaw] with t hS hgM hR ht
    let t' : Icc a b := ⟨t, ht.1.le, ht.2.le⟩
    have hC : Tendsto (fun k => P (κ k) t') atTop (𝓝 (H t')) :=
      (((continuous_eval_const t').tendsto H).comp hH).comp hκ.tendsto_atTop
    choose hM hEq using fun k : ℕ => hR (κ k) ht
    have hCoe (k : ℕ) : (P (κ k) t' : X → E) =ᵐ[σ] fun x => f (κ k) (x, t) := by
      rw [hEq k]
      exact (hM k).coeFn_toLp
    have hC' := (tendstoInMeasure_of_tendsto_Lp hC).congr_left hCoe
    have hS' := tendstoInMeasure_of_tendsto_ae (fun k => (hM k).aestronglyMeasurable) hS
    refine ⟨hgM, Lp.ext ?_⟩
    exact (tendstoInMeasure_ae_unique hC' hS').trans hgM.coeFn_toLp.symm
  rw [hν] at hFull
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hFull] with t hI ht
  exact hI ht ht

private theorem cylinderSide_trace_distance_le {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hR : 0 < R)
    {u v : Point → Ambient q} {D G : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 (translatedAxisCylinderDomain B c R lo hi) u D)
    (hv : MemW12 (translatedAxisCylinderDomain B c R lo hi) v G)
    {L M : ℝ≥0} (hL : LipschitzWith L u) (hM : LipschitzWith M v)
    {P Q : CylinderSideL2Trace q R lo hi}
    (hP : RepresentsCylinderSideL2Trace B c u P) (hQ : RepresentsCylinderSideL2Trace B c v Q) :
    let a := R / 2
    let U := translatedAxisCylinder c (B 2) R lo hi
    dist P Q ≤ Real.sqrt (((2 / (R - a)) * a⁻¹) * (∫ x in U, ‖u x - v x‖ ^ 2) +
      (2 * (R - a) * a⁻¹) * (∫ x in U, hsNormSq (fun i => D x i - G x i))) := by
  intro a U
  have hFL : LipschitzWith (L + M) (u - v) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (u x - v x) (u y - v y) ≤ _
    rw [dist_eq_norm, sub_sub_sub_comm, NNReal.coe_add, add_mul]
    exact (norm_sub_le _ _).trans (add_le_add
      (by rw [← dist_eq_norm]; exact hL.dist_le_mul x y)
      (by rw [← dist_eq_norm]; exact hM.dist_le_mul x y))
  obtain ⟨W, hW, hBound⟩ := exists_cylinderSide_trace_with_estimate_of_lipschitz B c hR
    (u - v) (fun x i => D x i - G x i) hFL (hu.sub hv)
  let f (z : (NativeCircle × ℝ) × ℝ) := (u - v) (c + axisChart B (z.2 • z.1.1.val, z.1.2))
  have hEq : P - Q = W := trace_unique (f := f) (half_lt_self hR) (hP.sub hQ) hW
  apply (ContinuousMap.dist_le (Real.sqrt_nonneg _)).2
  intro t
  rw [dist_eq_norm]
  change ‖(P - Q) t‖ ≤ _
  rw [hEq]
  apply Real.le_sqrt_of_sq_le
  simpa only [a, U, Pi.sub_apply, mul_assoc] using hBound t

private theorem cylinderSide_traces_cauchy_of_strong_graph {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hR : 0 < R)
    {u : ℕ → Point → Ambient q} {D : ℕ → Point → HarmonicMaps.Gradient 3 q}
    {v : Point → Ambient q} {J : Point → HarmonicMaps.Gradient 3 q}
    (hu : ∀ k, MemW12 (translatedAxisCylinderDomain B c R lo hi) (u k) (D k))
    (hv : MemW12 (translatedAxisCylinderDomain B c R lo hi) v J)
    (hLip : ∀ k, ∃ K : ℝ≥0, LipschitzWith K (u k))
    (hMap : Tendsto (fun k => eLpNorm (u k - v) 2
      (volume.restrict (translatedAxisCylinder c (B 2) R lo hi))) atTop (𝓝 0))
    (hGrad : ∀ i, Tendsto (fun k => eLpNorm (fun x => D k x i - J x i) 2
      (volume.restrict (translatedAxisCylinder c (B 2) R lo hi))) atTop (𝓝 0))
    (P : ℕ → CylinderSideL2Trace q R lo hi) (hP : ∀ k, RepresentsCylinderSideL2Trace B c (u k) (P k)) :
    CauchySeq P := by
  let a := R / 2
  let U := translatedAxisCylinder c (B 2) R lo hi
  let A : ℝ := (2 / (R - a)) * a⁻¹
  let C : ℝ := 2 * (R - a) * a⁻¹
  let F (p : ℕ × ℕ) := u p.1 - u p.2
  let G (p : ℕ × ℕ) (x : Point) (i : Fin 3) := D p.1 x i - D p.2 x i
  have hSob (p : ℕ × ℕ) : MemW12 (translatedAxisCylinderDomain B c R lo hi) (F p) (G p) :=
    (hu p.1).sub (hu p.2)
  let V (p : ℕ × ℕ) : ℝ :=
    A * (∫ x in U, ‖F p x‖ ^ 2) + C * (∫ x in U, hsNormSq (G p x))
  have hPairMap : Tendsto (fun p => eLpNorm (F p) 2 (volume.restrict U)) atTop (𝓝 0) :=
    pair_eLpNorm_tendsto_zero_of_strong (fun k => (hu k).2.1) hv.2.1 hMap
  have hPairGrad (i : Fin 3) : Tendsto (fun p => eLpNorm (fun x => G p x i) 2 (volume.restrict U)) atTop (𝓝 0) :=
    pair_eLpNorm_tendsto_zero_of_strong (f := fun k x => D k x i) (g := fun x => J x i)
      (fun k => (hu k).2.2 i) (hv.2.2 i) (hGrad i)
  have hV : Tendsto V atTop (𝓝 0) :=
    tendsto_sobolev_graph_budget_zero (U := U) (f := F) (D := G)
      (fun p => (hSob p).2.1) (fun p => (hSob p).2.2) hPairMap hPairGrad A C
  have hPair (p : ℕ × ℕ) : dist (P p.1) (P p.2) ≤ Real.sqrt (V p) := by
    obtain ⟨_, hL⟩ := hLip p.1
    obtain ⟨_, hM⟩ := hLip p.2
    exact cylinderSide_trace_distance_le B c hR (hu p.1) (hu p.2) hL hM (hP p.1) (hP p.2)
  have hD : Tendsto (fun p : ℕ × ℕ => dist (P p.1) (P p.2)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hV)
    (fun _ => dist_nonneg) hPair
  exact cauchySeq_iff_tendsto_dist_atTop_0.mpr hD

/-- On the original cylinder a strong Sobolev graph limit of Lipschitz maps
retains the native lateral curve. The curves converge uniformly in their L² norm. -/
theorem exists_cylinderSide_trace_of_strong_lipschitz_graph {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hR : 0 < R)
    {u : ℕ → Point → Ambient q} {D : ℕ → Point → HarmonicMaps.Gradient 3 q}
    {v : Point → Ambient q} {J : Point → HarmonicMaps.Gradient 3 q}
    (hu : ∀ k, MemW12 (translatedAxisCylinderDomain B c R lo hi) (u k) (D k))
    (hv : MemW12 (translatedAxisCylinderDomain B c R lo hi) v J)
    (hLip : ∀ k, ∃ K : ℝ≥0, LipschitzWith K (u k))
    (hMap : Tendsto (fun k => eLpNorm (u k - v) 2
      (volume.restrict (translatedAxisCylinder c (B 2) R lo hi))) atTop (𝓝 0))
    (hGrad : ∀ i, Tendsto (fun k => eLpNorm (fun x => D k x i - J x i) 2
      (volume.restrict (translatedAxisCylinder c (B 2) R lo hi))) atTop (𝓝 0))
    (P : ℕ → CylinderSideL2Trace q R lo hi) (hP : ∀ k, RepresentsCylinderSideL2Trace B c (u k) (P k)) :
    ∃ H : CylinderSideL2Trace q R lo hi, RepresentsCylinderSideL2Trace B c v H ∧
      Tendsto P atTop (𝓝 H) := by
  let a := R / 2
  have ha : 0 < a := half_pos hR
  let U := translatedAxisCylinder c (B 2) R lo hi
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete
    (cylinderSide_traces_cauchy_of_strong_graph B c hR hu hv hLip hMap hGrad P hP)
  refine ⟨H, ?_, hH⟩
  let σ := cylinderSideTraceMeasure lo hi
  let ν : Measure ℝ := volume.restrict (Icc a R)
  let E (z : (NativeCircle × ℝ) × ℝ) := c + axisChart B (z.2 • z.1.1.val, z.1.2)
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo lo hi)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  letI : IsFiniteMeasure σ := by dsimp only [σ, cylinderSideTraceMeasure]; infer_instance
  have hE : Measurable E := by
    have hA : Continuous (fun z : (NativeCircle × ℝ) × ℝ => (z.2 • z.1.1.val, z.1.2)) := by fun_prop
    exact (continuous_const.add ((continuous_axisChart B).comp hA)).measurable
  have hDom : Measure.map E (σ.prod ν) ≤ ENNReal.ofReal a⁻¹ • volume.restrict U := by
    apply (map_cylinderWallCollar_unweighted_le B c ha).trans
    have hRestrict : volume.restrict (translatedAxisCylinderWallCollar B c a R lo hi) ≤
        volume.restrict U := Measure.restrict_mono_set volume inter_subset_left
    gcongr
  have hUmem (k : ℕ) : MemLp (u k ∘ E) 2 (σ.prod ν) :=
    memLp_comp_of_map_le_smul hE.aemeasurable ENNReal.ofReal_ne_top hDom (hu k).2.1
  have hVmem : MemLp (v ∘ E) 2 (σ.prod ν) :=
    memLp_comp_of_map_le_smul hE.aemeasurable ENNReal.ofReal_ne_top hDom hv.2.1
  have hConv : Tendsto (fun k => eLpNorm ((u k ∘ E) - (v ∘ E)) 2 (σ.prod ν)) atTop (𝓝 0) := by
    have h := tendsto_eLpNorm_comp_zero_of_map_le_smul (f := fun k => u k - v)
      hE.aemeasurable ENNReal.ofReal_ne_top hDom
      (fun k => ((hu k).2.1.sub hv.2.1).aestronglyMeasurable) hMap
    exact h
  exact represents_trace_of_product_limit hUmem hVmem hConv hP hH

end Thesis.MeasureGeometry

end
