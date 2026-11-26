module

public import Thesis.Upstream.MinimizingSobolev
import Thesis.Foundation.BulkGeometry
import HarmonicMaps.Analysis.FiniteEnergyGradient
import StratificationTheory.Compactness.RellichBall
import StratificationTheory.Compactness.GradientWeakSubsequence
import StratificationTheory.Compactness.WeakGradientClosure
import StratificationTheory.Compactness.WeakLocalGradient

/-! Rellich compactness for tensor fields with actual weak gradients. -/

public section

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal Matrix.Norms.Frobenius

namespace Thesis

theorem eLpNorm_frobeniusField (u : Point → S0) (p : ENNReal) (μ : Measure Point) :
    eLpNorm (frobeniusField u) p μ = eLpNorm u p μ :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun x => frobeniusCoordinateEquiv.norm_map (u x))

private theorem frobeniusField_sub_eq (u v : Point → S0) :
    frobeniusField (u - v) = frobeniusField u - frobeniusField v :=
  funext fun x => frobeniusCoordinateEquiv.map_sub (u x) (v x)

theorem upstream_dirichletEnergy_eq_gradientNormSq (D : Point → Gradient) (U : Set Point) :
    HarmonicMaps.dirichletEnergy (frobeniusGradient D) U =
      ∫⁻ x in U, ENNReal.ofReal (gradientNormSq (D x)) := by
  simp only [HarmonicMaps.dirichletEnergy, HarmonicMaps.hsNormSq, frobeniusGradient,
    LinearIsometryEquiv.norm_map, gradientNormSq_eq_sum_norm_sq]

private theorem tendsto_integral_frobenius_of_upstream (U : Set Point)
    (d : ℕ → Point → S0) (g : Point → S0)
    (h : ∀ w : Lp (HarmonicMaps.Ambient 5) 2 (volume.restrict U),
      Tendsto (fun k => ∫ x in U, inner ℝ (frobeniusCoordinateEquiv (d k x)) (w x))
        atTop (𝓝 (∫ x in U, inner ℝ (frobeniusCoordinateEquiv (g x)) (w x))))
    (w : Lp S0 2 (volume.restrict U)) :
    Tendsto (fun k => ∫ x in U, frobeniusS0 (d k x) (w x))
      atTop (𝓝 (∫ x in U, frobeniusS0 (g x) (w x))) := by
  have hw : MemLp (frobeniusField w) 2 (volume.restrict U) :=
    (frobeniusCoordinateEquiv_memLp_iff (volume.restrict U) 2 w).2 (Lp.memLp w)
  let W := hw.toLp (frobeniusField w)
  have hW : (W : Point → HarmonicMaps.Ambient 5) =ᵐ[volume.restrict U] frobeniusField w :=
    hw.coeFn_toLp
  have hpair (v : Point → S0) :
      (∫ x in U, inner ℝ (frobeniusCoordinateEquiv (v x)) (W x)) =
        ∫ x in U, frobeniusS0 (v x) (w x) := by
    apply integral_congr_ae
    filter_upwards [hW] with x hx
    change W x = frobeniusCoordinateEquiv (w x) at hx
    rw [hx, frobeniusCoordinateEquiv_inner]
  rw [← hpair g]
  exact (h W).congr (fun k => hpair (d k))

/-- Simultaneous strong L² map and weak L² gradient extraction on a smaller
ball for arbitrary finite H¹ tensor fields. -/
theorem exists_tensor_rellich_subsequence_ball (c : Point) {r R : ℝ}
    (hR : 0 < R) (hrR : r < R)
    (u : ℕ → Point → S0) (D : ℕ → Point → Gradient)
    (hu : ∀ k, MemH1 (Metric.ball c R) (u k) (D k))
    (Cmap Cgradient : ℝ≥0)
    (hmap : ∀ k, (∫ x in Metric.ball c R, ‖u k x‖ ^ 2) ≤ Cmap)
    (hgradient : ∀ k,
      (∫⁻ x in Metric.ball c R, ENNReal.ofReal (gradientNormSq (D k x))) ≤ Cgradient) :
    ∃ (κ : ℕ → ℕ) (v : Point → S0) (G : Point → Gradient),
      StrictMono κ ∧ MemH1 (Metric.ball c r) v G ∧
      (∫⁻ x in Metric.ball c r, ENNReal.ofReal (gradientNormSq (G x))) ≤ Cgradient ∧
      Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict (Metric.ball c r)))
        atTop (𝓝 0) ∧
      ∀ (j : Fin 3) (w : Lp S0 2 (volume.restrict (Metric.ball c r))),
        Tendsto (fun k => ∫ x in Metric.ball c r, frobeniusS0 (D (κ k) x j) (w x))
          atTop (𝓝 (∫ x in Metric.ball c r, frobeniusS0 (G x j) (w x))) := by
  let U := HarmonicMaps.ballDomain c R
  let B := HarmonicMaps.ballDomain c r
  let F (k : ℕ) := frobeniusField (u k)
  let J (k : ℕ) := frobeniusGradient (D k)
  have hU (k : ℕ) : HarmonicMaps.MemW12 U (F k) (J k) := (memH1_iff_memW12 U _ _).1 (hu k)
  have hB (k : ℕ) : HarmonicMaps.MemW12 B (F k) (J k) :=
    (memH1_iff_memW12 B _ _).1 ((hu k).mono (Metric.ball_subset_ball hrR.le))
  have hF (k : ℕ) : (∫ x in Metric.ball c R, ‖F k x‖ ^ 2) ≤ Cmap := by
    simpa only [F, frobeniusField, LinearIsometryEquiv.norm_map] using hmap k
  have hJ (k : ℕ) : HarmonicMaps.dirichletEnergy (J k) (Metric.ball c R) ≤ Cgradient := by
    simpa only [J, upstream_dirichletEnergy_eq_gradientNormSq] using hgradient k
  obtain ⟨κ₀, w, hκ₀, hw, hstrong⟩ :=
    StratificationTheory.Compactness.memW12_exists_strong_L2_subsequence_ball c hR hrR
      F J hU Cmap Cgradient hF hJ
  have hJinner (k : ℕ) : HarmonicMaps.dirichletEnergy (J (κ₀ k)) (Metric.ball c r) ≤ Cgradient :=
    (lintegral_mono_set (Metric.ball_subset_ball hrR.le)).trans (hJ (κ₀ k))
  obtain ⟨κ₁, W, hκ₁, hW, hWenergy, hweak⟩ :=
    StratificationTheory.Compactness.exists_weakly_convergent_gradient_field_ball c r
      (fun k => J (κ₀ k)) (fun k => (hB (κ₀ k)).2.2) Cgradient hJinner
  let κ := κ₀ ∘ κ₁
  have hstrong' : Tendsto (fun k => eLpNorm (F (κ k) - w) 2 (volume.restrict B.val))
      atTop (𝓝 0) := hstrong.comp hκ₁.tendsto_atTop
  letI : IsFiniteMeasure (volume.restrict B.val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hSob : HarmonicMaps.MemW12 B w W :=
    StratificationTheory.Compactness.memW12_of_strong_map_weak_gradient_limit
      (fun k => hB (κ k)) hw hW hstrong' hweak
  let v (x : Point) := frobeniusCoordinateEquiv.symm (w x)
  let G (x : Point) (j : Fin 3) := frobeniusCoordinateEquiv.symm (W x j)
  have hv : frobeniusField v = w := funext fun x => frobeniusCoordinateEquiv.apply_symm_apply (w x)
  have hG : frobeniusGradient G = W := funext fun x => funext fun j =>
    frobeniusCoordinateEquiv.apply_symm_apply (W x j)
  refine ⟨κ, v, G, hκ₀.comp hκ₁,
    (memH1_iff_memW12 B v G).2 (by simpa only [hv, hG] using hSob), ?_, ?_, ?_⟩
  · rw [← upstream_dirichletEnergy_eq_gradientNormSq, hG]
    exact hWenergy
  · apply hstrong'.congr
    intro k
    change eLpNorm (frobeniusField (u (κ k)) - w) 2 _ = _
    rw [← hv, ← frobeniusField_sub_eq, eLpNorm_frobeniusField]
    rfl
  · intro j w'
    apply tendsto_integral_frobenius_of_upstream (Metric.ball c r)
    intro w''
    have hpoint (x : Point) : frobeniusCoordinateEquiv (G x j) = W x j :=
      congrFun (congrFun hG x) j
    simpa only [κ, Function.comp_apply, J, frobeniusGradient, hpoint] using hweak j w''

private theorem ambient_L2_totallyBounded_compact
    (Ω : HarmonicMaps.OpenDomain 3) (f : ℕ → Point → HarmonicMaps.Ambient 5)
    (Df : ℕ → Point → HarmonicMaps.Gradient 3 5)
    (hf : ∀ k, HarmonicMaps.MemW12Loc Ω (f k) (Df k))
    (hBounds : ∀ (c : Point) (R : ℝ), 0 < R → Metric.closedBall c R ⊆ Ω.val →
      ∃ M C : ℝ≥0, (∀ k, (∫ x in Metric.ball c R, ‖f k x‖ ^ 2) ≤ M) ∧
        ∀ k, HarmonicMaps.dirichletEnergy (Df k) (Metric.ball c R) ≤ C)
    (K : Set Point) (hK : IsCompact K) (hKU : K ⊆ Ω.val) :
    TotallyBounded (range (fun k => ((hf k).2.1 K hK hKU).toLp (f k))) := by
  classical
  obtain ⟨t, R, hR, hcover⟩ :=
    StratificationTheory.Compactness.exists_finite_interior_ball_cover Ω K hK hKU
  let I := {c : K // c ∈ t}
  letI : Fintype I := inferInstanceAs (Fintype {c : K // c ∈ t})
  let U (j : I) := Metric.ball j.val.val ((R j.val).val / 2)
  have hcoverU : K ⊆ ⋃ j : I, U j := by
    intro x hx
    obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion.mpr ⟨⟨y, hyt⟩, hy⟩
  have hW (j : I) (k : ℕ) : HarmonicMaps.MemW12
      (HarmonicMaps.ballDomain j.val.val (R j.val).val) (f k) (Df k) :=
    (hf k).memW12_ball (hR j.val)
  have hlocal (j : I) : ∃ hL : ∀ k, MemLp (f k) 2 (volume.restrict (U j)),
      TotallyBounded (range (fun k => (hL k).toLp (f k))) := by
    obtain ⟨M, C, hM, hC⟩ :=
      hBounds j.val.val (R j.val).val (R j.val).property (hR j.val)
    exact StratificationTheory.Compactness.memW12_ball_L2_totallyBounded
      j.val.val (R j.val).property (by linarith [(R j.val).property])
      f Df (hW j) M C hM hC
  choose hL hTB using hlocal
  exact StratificationTheory.Compactness.L2_totallyBounded_of_finite_cover
    volume K U hcoverU f (fun k => (hf k).2.1 K hK hKU) hL hTB

private theorem ambient_strong_local_subsequence (Ω : HarmonicMaps.OpenDomain 3)
    (f : ℕ → Point → HarmonicMaps.Ambient 5)
    (hL : ∀ k, HarmonicMaps.LocallyMemL2 Ω (f k))
    (hTB : ∀ (K : Set Point) (hK : IsCompact K) (hKU : K ⊆ Ω.val),
      TotallyBounded (range (fun k => (hL k K hK hKU).toLp (f k)))) :
    ∃ (κ : ℕ → ℕ) (w : Point → HarmonicMaps.Ambient 5),
      StrictMono κ ∧ HarmonicMaps.LocallyMemL2 Ω w ∧
      ∀ K : Set Point, IsCompact K → K ⊆ Ω.val →
        Tendsto (fun k => eLpNorm (f (κ k) - w) 2 (volume.restrict K)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hKU, hmono, _, hcofinal⟩ :=
    StratificationTheory.Compactness.exists_cofinal_compact_exhaustion_openDomain Ω
  let H (j : ℕ) : Type := Lp (HarmonicMaps.Ambient 5) 2 (volume.restrict (K j))
  have hKmem (j k : ℕ) : MemLp (f k) 2 (volume.restrict (K j)) := hL k (K j) (hK j) (hKU j)
  let F (k j : ℕ) : H j := (hKmem j k).toLp (f k)
  let S (j : ℕ) : Set (H j) := closure (range (fun k => F k j))
  have hS (j : ℕ) : IsCompact (S j) :=
    (hTB (K j) (hK j) (hKU j)).closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨κ, W, hκ, _, hconv⟩ :=
    StratificationTheory.Compactness.exists_subsequence_tendsto_countable_compacts S hS F
      (fun k j => subset_closure (mem_range_self k))
  let w (j : ℕ) : Point → HarmonicMaps.Ambient 5 := W j
  have hw (j : ℕ) : MemLp (w j) 2 (volume.restrict (K j)) := Lp.memLp (W j)
  have hmap (j : ℕ) : Tendsto (fun k => eLpNorm (f (κ k) - w j) 2 (volume.restrict (K j)))
      atTop (𝓝 0) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k => f (κ k))
      (fun k => hKmem j (κ k)) (w j) (hw j)).mp
    rw [show (hw j).toLp (w j) = W j from Lp.toLp_coeFn (W j) (hw j)]
    exact hconv j
  have hagree (j l : ℕ) (hjl : j ≤ l) : w j =ᵐ[volume.restrict (K j)] w l := by
    have hmeasure := Measure.restrict_mono_set (volume : Measure Point) (hmono hjl)
    have hwl := (hw l).mono_measure hmeasure
    have hmapl : Tendsto (fun k => eLpNorm (f (κ k) - w l) 2 (volume.restrict (K j)))
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hmap l) (fun _ => zero_le)
        (fun k => eLpNorm_mono_measure _ hmeasure)
    have hmeas (k : ℕ) := (hKmem j (κ k)).aestronglyMeasurable
    exact tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hmeas (hw j).aestronglyMeasurable (hmap j))
      (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hmeas hwl.aestronglyMeasurable hmapl)
  obtain ⟨v, hvEq⟩ := StratificationTheory.Compactness.exists_ae_glue_countable_regions
    volume K (fun j => (hK j).measurableSet) w hagree
  have hvL (j : ℕ) : MemLp v 2 (volume.restrict (K j)) := (hw j).ae_eq (hvEq j).symm
  have hvconv (j : ℕ) : Tendsto (fun k => eLpNorm (f (κ k) - v) 2 (volume.restrict (K j)))
      atTop (𝓝 0) :=
    (hmap j).congr fun k => eLpNorm_congr_ae ((EventuallyEq.refl _ _).sub (hvEq j).symm)
  refine ⟨κ, v, hκ, ?_, ?_⟩
  · intro T hT hTU
    obtain ⟨j, hj⟩ := hcofinal T hT hTU
    exact (hvL j).mono_measure (Measure.restrict_mono_set volume hj)
  · intro T hT hTU
    obtain ⟨j, hj⟩ := hcofinal T hT hTU
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hvconv j)
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hj))

/-- One subsequence converges on every compact subset of an open domain with
locally uniform L² map and gradient bounds. -/
theorem exists_tensor_rellich_subsequence_local (Ω : HarmonicMaps.OpenDomain 3)
    (u : ℕ → Point → S0) (D : ℕ → Point → Gradient) (hu : ∀ k, MemH1Loc Ω.val (u k) (D k))
    (hBounds : ∀ (c : Point) (R : ℝ), 0 < R → Metric.closedBall c R ⊆ Ω.val →
      ∃ M C : ℝ≥0, (∀ k, (∫ x in Metric.ball c R, ‖u k x‖ ^ 2) ≤ M) ∧
      ∀ k, (∫⁻ x in Metric.ball c R, ENNReal.ofReal (gradientNormSq (D k x))) ≤ C) :
    ∃ (κ : ℕ → ℕ) (v : Point → S0) (G : Point → Gradient),
      StrictMono κ ∧ MemH1Loc Ω.val v G ∧
      ∀ K : Set Point, IsCompact K → K ⊆ Ω.val →
        Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict K)) atTop (𝓝 0) ∧
        ∀ (j : Fin 3) (w : Lp S0 2 (volume.restrict K)),
          Tendsto (fun k => ∫ x in K, frobeniusS0 (D (κ k) x j) (w x)) atTop
            (𝓝 (∫ x in K, frobeniusS0 (G x j) (w x))) := by
  let F (k : ℕ) := frobeniusField (u k)
  let J (k : ℕ) := frobeniusGradient (D k)
  have hF (k : ℕ) : HarmonicMaps.MemW12Loc Ω (F k) (J k) :=
    (memH1Loc_iff_memW12Loc Ω _ _).1 (hu k)
  have hNative : ∀ (c : Point) (R : ℝ), 0 < R → Metric.closedBall c R ⊆ Ω.val →
      ∃ M C : ℝ≥0, (∀ k, (∫ x in Metric.ball c R, ‖F k x‖ ^ 2) ≤ M) ∧
      ∀ k, HarmonicMaps.dirichletEnergy (J k) (Metric.ball c R) ≤ C := by
    intro c R hr hR
    obtain ⟨M, C, hmap, hgrad⟩ := hBounds c R hr hR
    refine ⟨M, C, ?_, ?_⟩
    · intro k
      simpa only [F, frobeniusField, LinearIsometryEquiv.norm_map] using hmap k
    · intro k
      simpa only [J, upstream_dirichletEnergy_eq_gradientNormSq] using hgrad k
  obtain ⟨κ₀, w, hκ₀, hw, hstrong⟩ := ambient_strong_local_subsequence Ω F (fun k => (hF k).2.1)
    (ambient_L2_totallyBounded_compact Ω F J hF hNative)
  have hEnergy (c : Point) (R : ℝ) (hr : 0 < R) (hR : Metric.closedBall c R ⊆ Ω.val) :
      ∃ C : ℝ≥0, ∀ k, HarmonicMaps.dirichletEnergy (J (κ₀ k)) (Metric.ball c R) ≤ C := by
    obtain ⟨_, C, _, hC⟩ := hNative c R hr hR
    exact ⟨C, fun k => hC (κ₀ k)⟩
  obtain ⟨κ₁, W, hκ₁, hW, hweak⟩ :=
    StratificationTheory.Compactness.exists_weak_local_gradient_subsequence Ω (fun k => J (κ₀ k))
      (fun k j => (hF (κ₀ k)).2.2 j) hEnergy
  let κ := κ₀ ∘ κ₁
  have hstrong' (K : Set Point) (hK : IsCompact K) (hKU : K ⊆ Ω.val) :
      Tendsto (fun k => eLpNorm (F (κ k) - w) 2 (volume.restrict K)) atTop (𝓝 0) :=
    (hstrong K hK hKU).comp hκ₁.tendsto_atTop
  have hSob : HarmonicMaps.MemW12Loc Ω w W :=
    StratificationTheory.Compactness.memW12Loc_of_strong_map_weak_gradient_limit
      (fun k => hF (κ k)) hw hW hstrong' hweak
  let v (x : Point) := frobeniusCoordinateEquiv.symm (w x)
  let G (x : Point) (j : Fin 3) := frobeniusCoordinateEquiv.symm (W x j)
  have hv : frobeniusField v = w := funext fun x => frobeniusCoordinateEquiv.apply_symm_apply (w x)
  have hG : frobeniusGradient G = W := funext fun x => funext fun j =>
    frobeniusCoordinateEquiv.apply_symm_apply (W x j)
  refine ⟨κ, v, G, hκ₀.comp hκ₁,
    (memH1Loc_iff_memW12Loc Ω v G).2 (by simpa only [hv, hG] using hSob), ?_⟩
  intro K hK hKU
  constructor
  · apply (hstrong' K hK hKU).congr
    intro k
    change eLpNorm (frobeniusField (u (κ k)) - w) 2 _ = _
    rw [← hv, ← frobeniusField_sub_eq, eLpNorm_frobeniusField]
  · intro j w'
    apply tendsto_integral_frobenius_of_upstream K
    intro w''
    have hpoint (x : Point) : frobeniusCoordinateEquiv (G x j) = W x j :=
      congrFun (congrFun hG x) j
    simpa only [κ, Function.comp_apply, J, frobeniusGradient, hpoint] using hweak K hK hKU j w''

private theorem tendstoInMeasure_of_compact_exhaustion
    {E : Type*} [EDist E] (Ω : HarmonicMaps.OpenDomain 3)
    (hFinite : volume Ω.val ≠ ⊤) (K : ℕ → Set Point)
    (hK : ∀ j, IsCompact (K j)) (hmono : Monotone K) (hcover : (⋃ j, K j) = Ω.val)
    {u : ℕ → Point → E} {v : Point → E}
    (hLocal : ∀ j, TendstoInMeasure (volume.restrict (K j)) u atTop v) :
    TendstoInMeasure (volume.restrict Ω.val) u atTop v := by
  have hEmpty : (⋂ j, Ω.val \ K j) = ∅ := by rw [← sdiff_iUnion, hcover, sdiff_self]
  have hTail : Tendsto (fun j => volume (Ω.val \ K j)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := (volume : Measure Point))
      (s := fun j => Ω.val \ K j)
      (fun j => (Ω.property.measurableSet.diff (hK j).measurableSet).nullMeasurableSet)
      (fun _ _ h => sdiff_subset_sdiff_right (hmono h))
      ⟨0, ne_top_of_le_ne_top hFinite (measure_mono sdiff_subset)⟩
    rw [hEmpty, measure_empty] at h
    exact h
  intro ε hε
  apply ENNReal.tendsto_nhds_zero.mpr
  intro δ hδ
  have hhalf : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by simp)
  obtain ⟨j, hj⟩ := (ENNReal.tendsto_atTop_zero.mp hTail) (δ / 2) hhalf
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hLocal j ε hε) (δ / 2) hhalf] with n hn
  let A := {x | ε ≤ edist (u n x) (v x)}
  have hsubset : A ∩ Ω.val ⊆ (A ∩ K j) ∪ (Ω.val \ K j) := by
    intro x hx
    by_cases hxK : x ∈ K j
    · exact Or.inl ⟨hx.1, hxK⟩
    · exact Or.inr ⟨hx.2, hxK⟩
  change (volume.restrict Ω.val) A ≤ δ
  rw [Measure.restrict_apply' Ω.property.measurableSet]
  calc
    volume (A ∩ Ω.val) ≤ volume (A ∩ K j) + volume (Ω.val \ K j) :=
      (measure_mono hsubset).trans (measure_union_le _ _)
    _ ≤ δ / 2 + δ / 2 := by
      rw [← Measure.restrict_apply' (hK j).measurableSet]
      exact add_le_add hn (hj j le_rfl)
    _ = δ := ENNReal.add_halves δ

/-- A sequence of actual gradient columns with bounded total L² energy has a
common weak L² subsequence in the finite product of its column spaces. -/
theorem ambient_weak_gradient_subsequence
    (U : Set Point) (D : ℕ → Point → HarmonicMaps.Gradient 3 5)
    (hD : ∀ k (j : Fin 3), MemLp (fun x => D k x j) 2 (volume.restrict U))
    (C : ℝ≥0) (hEnergy : ∀ k, HarmonicMaps.dirichletEnergy (D k) U ≤ C) :
    ∃ (κ : ℕ → ℕ) (G : Point → HarmonicMaps.Gradient 3 5),
      StrictMono κ ∧
      (∀ j : Fin 3, MemLp (fun x => G x j) 2 (volume.restrict U)) ∧
      HarmonicMaps.dirichletEnergy G U ≤ C ∧
      ∀ (j : Fin 3) (w : Lp (HarmonicMaps.Ambient 5) 2 (volume.restrict U)),
        Tendsto (fun k => ∫ x in U, inner ℝ (D (κ k) x j) (w x))
          atTop (𝓝 (∫ x in U, inner ℝ (G x j) (w x))) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let H : Type := Lp (HarmonicMaps.Ambient 5) 2 (volume.restrict U)
  let F (k : ℕ) : PiLp 2 (fun _ : Fin 3 => H) :=
    WithLp.toLp 2 (fun j => (hD k j).toLp (fun x => D k x j))
  have hNorm (k : ℕ) : ‖F k‖ ^ 2 = (HarmonicMaps.dirichletEnergy (D k) U).toReal := by
    rw [PiLp.norm_sq_eq_of_L2]
    dsimp only [F, H, PiLp.toLp_apply]
    simp only [Lp.norm_toLp]
    exact StratificationTheory.Compactness.sum_column_L2_norm_sq_eq_dirichletEnergy (hD k)
  have hF (k : ℕ) : ‖F k‖ ≤ Real.sqrt C := by
    apply Real.le_sqrt_of_sq_le
    rw [hNorm]
    exact_mod_cast ENNReal.toReal_mono (ENNReal.coe_ne_top (r := C)) (hEnergy k)
  obtain ⟨κ, V, hκ, hV, hWeak⟩ :=
    StratificationTheory.Compactness.exists_weakly_convergent_subsequence F (Real.sqrt C) hF
  let G (x : Point) (j : Fin 3) := V j x
  have hG (j : Fin 3) : MemLp (fun x => G x j) 2 (volume.restrict U) := Lp.memLp (V j)
  refine ⟨κ, G, hκ, hG, ?_, ?_⟩
  · have hSum : (HarmonicMaps.dirichletEnergy G U).toReal = ‖V‖ ^ 2 := by
      rw [← StratificationTheory.Compactness.sum_column_L2_norm_sq_eq_dirichletEnergy hG,
        PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Lp.norm_toLp (fun x => G x j) (hG j)]
      dsimp only [G]
      rw [Lp.toLp_coeFn]
    have hSq := pow_le_pow_left₀ (norm_nonneg V) hV 2
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ (C : ℝ) from C.property)] at hSq
    apply (ENNReal.toReal_le_toReal
      (HarmonicMaps.dirichletEnergy_ne_top_of_integrable
        (HarmonicMaps.integrable_hsNormSq_of_memLp_columns hG)) ENNReal.coe_ne_top).mp
    simpa only [hSum, ENNReal.coe_toReal] using hSq
  · intro j w
    have hSingle (A : PiLp 2 (fun _ : Fin 3 => H)) :
        inner ℝ A (PiLp.single 2 j w) = inner ℝ (A j) w := by
      simp [PiLp.inner_apply, PiLp.single_apply, apply_ite]
    have hIntegral (k : ℕ) :
        inner ℝ ((hD k j).toLp (fun x => D k x j)) w =
          ∫ x in U, inner ℝ (D k x j) (w x) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hD k j).coeFn_toLp] with x hx
      rw [hx]
    have hLimit : inner ℝ (V j) w = ∫ x in U, inner ℝ (G x j) (w x) := L2.inner_def _ _
    simpa only [hSingle, F, PiLp.toLp_apply, hIntegral, hLimit] using hWeak (PiLp.single 2 j w)

private theorem memW12_of_local_of_ae_bound_of_energy
    (Ω : HarmonicMaps.OpenDomain 3) [IsFiniteMeasure (volume.restrict Ω.val)]
    {u : Point → HarmonicMaps.Ambient 5} {D : Point → HarmonicMaps.Gradient 3 5}
    (hu : HarmonicMaps.MemW12Loc Ω u D) {B : ℝ}
    (hBound : ∀ᵐ x ∂volume.restrict Ω.val, ‖u x‖ ≤ B)
    (hEnergy : HarmonicMaps.dirichletEnergy D Ω.val ≠ ⊤) :
    HarmonicMaps.MemW12 Ω u D :=
  ⟨hu.1, MemLp.of_bound hu.1.1.aestronglyMeasurable B hBound,
    hu.1.memLp_columns_of_dirichletEnergy_ne_top hEnergy⟩

/-- A finite-volume open domain admits one global H¹ weak subsequence of
locally Sobolev tensor fields under uniform essential map and energy bounds.
The maps converge strongly in L² and almost everywhere. -/
theorem exists_tensor_rellich_subsequence (Ω : HarmonicMaps.OpenDomain 3)
    (hFinite : volume Ω.val ≠ ⊤) (u : ℕ → Point → S0) (D : ℕ → Point → Gradient)
    (hu : ∀ k, MemH1Loc Ω.val (u k) (D k)) (B C : ℝ≥0)
    (hBound : ∀ k, ∀ᵐ x ∂volume.restrict Ω.val, ‖u k x‖ ≤ (B : ℝ))
    (hEnergy : ∀ k, (∫⁻ x in Ω.val, ENNReal.ofReal (gradientNormSq (D k x))) ≤ C) :
    ∃ (κ : ℕ → ℕ) (v : Point → S0) (G : Point → Gradient),
      StrictMono κ ∧ (∀ k, MemH1 Ω.val (u k) (D k)) ∧ MemH1 Ω.val v G ∧
      (∫⁻ x in Ω.val, ENNReal.ofReal (gradientNormSq (G x))) ≤ C ∧
      Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict Ω.val)) atTop (𝓝 0) ∧
      (∀ᵐ x ∂volume.restrict Ω.val, Tendsto (fun k => u (κ k) x) atTop (𝓝 (v x))) ∧
      (∀ w : Lp S0 2 (volume.restrict Ω.val),
        Tendsto (fun k => ∫ x in Ω.val, frobeniusS0 (u (κ k) x) (w x))
          atTop (𝓝 (∫ x in Ω.val, frobeniusS0 (v x) (w x)))) ∧
      ∀ (j : Fin 3) (w : Lp S0 2 (volume.restrict Ω.val)),
        Tendsto (fun k => ∫ x in Ω.val, frobeniusS0 (D (κ k) x j) (w x))
          atTop (𝓝 (∫ x in Ω.val, frobeniusS0 (G x j) (w x))) := by
  let μ := volume.restrict Ω.val
  letI : IsFiniteMeasure (volume.restrict Ω.val) := isFiniteMeasure_restrict.mpr hFinite
  let F (k : ℕ) := frobeniusField (u k)
  let J (k : ℕ) := frobeniusGradient (D k)
  have hFLocal (k : ℕ) : HarmonicMaps.MemW12Loc Ω (F k) (J k) :=
    (memH1Loc_iff_memW12Loc Ω _ _).1 (hu k)
  have hFB (k : ℕ) : ∀ᵐ x ∂μ, ‖F k x‖ ≤ (B : ℝ) := by
    simpa only [F, frobeniusField, LinearIsometryEquiv.norm_map] using hBound k
  have hJC (k : ℕ) : HarmonicMaps.dirichletEnergy (J k) Ω.val ≤ C := by
    simpa only [J, upstream_dirichletEnergy_eq_gradientNormSq] using hEnergy k
  have hF (k : ℕ) : HarmonicMaps.MemW12 Ω (F k) (J k) :=
    memW12_of_local_of_ae_bound_of_energy Ω (hFLocal k) (hFB k)
      (ne_top_of_le_ne_top ENNReal.coe_ne_top (hJC k))
  have hLocalBounds (c : Point) (R : ℝ) (_ : 0 < R)
      (hR : Metric.closedBall c R ⊆ Ω.val) :
      ∃ M C' : ℝ≥0, (∀ k, (∫ x in Metric.ball c R, ‖F k x‖ ^ 2) ≤ M) ∧
        ∀ k, HarmonicMaps.dirichletEnergy (J k) (Metric.ball c R) ≤ C' := by
    let U := Metric.ball c R
    letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
    have hU : U ⊆ Ω.val := Metric.ball_subset_closedBall.trans hR
    let M : ℝ≥0 := ⟨(B : ℝ) ^ 2 * (volume U).toReal, by positivity⟩
    refine ⟨M, C, ?_, fun k => (lintegral_mono_set hU).trans (hJC k)⟩
    intro k
    have hMem := (hF k).2.1.mono_measure (Measure.restrict_mono_set volume hU)
    have hB := ae_restrict_of_ae_restrict_of_subset hU (hFB k)
    calc
      (∫ x in U, ‖F k x‖ ^ 2) ≤ ∫ _ in U, (B : ℝ) ^ 2 :=
        integral_mono_ae (hMem.integrable_norm_pow (by decide)) (integrable_const _)
          (hB.mono fun x hx => pow_le_pow_left₀ (norm_nonneg (F k x)) hx 2)
      _ = M := by
        change (∫ _ in U, (B : ℝ) ^ 2) = (B : ℝ) ^ 2 * (volume U).toReal
        simp [integral_const, smul_eq_mul, measureReal_def, mul_comm]
  obtain ⟨κ₀, w, hκ₀, hw, hLocal⟩ :=
    ambient_strong_local_subsequence Ω F (fun k => (hFLocal k).2.1)
      (ambient_L2_totallyBounded_compact Ω F J hFLocal hLocalBounds)
  obtain ⟨K, hK, hKΩ, hKmono, hcover, _⟩ :=
    StratificationTheory.Compactness.exists_cofinal_compact_exhaustion_openDomain Ω
  have hInMeasure : TendstoInMeasure μ (fun k => F (κ₀ k)) atTop w := by
    apply tendstoInMeasure_of_compact_exhaustion Ω hFinite K hK hKmono hcover
    intro j
    exact tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
      (fun k => ((hFLocal (κ₀ k)).2.1 (K j) (hK j) (hKΩ j)).aestronglyMeasurable)
      (hw (K j) (hK j) (hKΩ j)).aestronglyMeasurable (hLocal (K j) (hK j) (hKΩ j))
  obtain ⟨κ₁, W, hκ₁, hW, hWC, hWeak⟩ :=
    ambient_weak_gradient_subsequence Ω.val (fun k => J (κ₀ k))
      (fun k => (hF (κ₀ k)).2.2) C (fun k => hJC (κ₀ k))
  obtain ⟨κ₂, hκ₂, hAE⟩ := (hInMeasure.comp hκ₁.tendsto_atTop).exists_seq_tendsto_ae
  let κ := κ₀ ∘ κ₁ ∘ κ₂
  have hAE' : ∀ᵐ x ∂μ, Tendsto (fun k => F (κ k) x) atTop (𝓝 (w x)) := hAE
  have hWB : ∀ᵐ x ∂μ, ‖w x‖ ≤ (B : ℝ) := by
    filter_upwards [hAE', ae_all_iff.mpr hFB] with x hx hB
    exact le_of_tendsto hx.norm (Eventually.of_forall fun k => hB (κ k))
  have hwMeas : AEStronglyMeasurable w μ := by
    change AEStronglyMeasurable w (volume.restrict Ω.val)
    rw [← hcover, aestronglyMeasurable_iUnion_iff]
    exact fun j => (hw (K j) (hK j) (hKΩ j)).aestronglyMeasurable
  have hwL2 : MemLp w 2 μ := MemLp.of_bound hwMeas (B : ℝ) hWB
  have hDiff (k : ℕ) : MemLp (F (κ k) - w) 2 μ := (hF (κ k)).2.1.sub hwL2
  have hStrong : Tendsto (fun k => eLpNorm (F (κ k) - w) 2 μ) atTop (𝓝 0) := by
    apply HarmonicMaps.tendsto_eLpNorm_two_zero_of_integral_norm_sq hDiff
    have hDCT := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun k x => ‖F (κ k) x - w x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun _ => (2 * (B : ℝ)) ^ 2) (fun k => (hDiff k).aestronglyMeasurable.norm.pow 2)
      (integrable_const _) ?_ ?_
    · simpa only [integral_zero, Pi.sub_apply] using hDCT
    · intro k
      filter_upwards [hFB (κ k), hWB] with x hx hy
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc
        ‖F (κ k) x - w x‖ ≤ ‖F (κ k) x‖ + ‖w x‖ := norm_sub_le _ _
        _ ≤ 2 * (B : ℝ) := by linarith
    · filter_upwards [hAE'] with x hx
      simpa only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        ((hx.sub_const (w x)).norm.pow 2)
  have hWeak' (j : Fin 3) (p : Lp (HarmonicMaps.Ambient 5) 2 μ) :
      Tendsto (fun k => ∫ x in Ω.val, inner ℝ (J (κ k) x j) (p x))
        atTop (𝓝 (∫ x in Ω.val, inner ℝ (W x j) (p x))) :=
    (hWeak j p).comp hκ₂.tendsto_atTop
  have hSob : HarmonicMaps.MemW12 Ω w W :=
    StratificationTheory.Compactness.memW12_of_strong_map_weak_gradient_limit
      (fun k => hF (κ k)) hwL2 hW hStrong hWeak'
  let v (x : Point) := frobeniusCoordinateEquiv.symm (w x)
  let G (x : Point) (j : Fin 3) := frobeniusCoordinateEquiv.symm (W x j)
  have hv : frobeniusField v = w := funext fun x => frobeniusCoordinateEquiv.apply_symm_apply (w x)
  have hG : frobeniusGradient G = W := funext fun x => funext fun j =>
    frobeniusCoordinateEquiv.apply_symm_apply (W x j)
  refine ⟨κ, v, G, hκ₀.comp (hκ₁.comp hκ₂), fun k => (memH1_iff_memW12 Ω _ _).2 (hF k),
    (memH1_iff_memW12 Ω _ _).2 (by simpa only [hv, hG] using hSob), ?_, ?_, ?_, ?_, ?_⟩
  · rwa [← upstream_dirichletEnergy_eq_gradientNormSq, hG]
  · apply hStrong.congr
    intro k
    change eLpNorm (frobeniusField (u (κ k)) - w) 2 _ = _
    rw [← hv, ← frobeniusField_sub_eq, eLpNorm_frobeniusField]
  · filter_upwards [hAE'] with x hx
    have h := frobeniusCoordinateEquiv.symm.continuous.continuousAt.tendsto.comp hx
    change Tendsto (fun k => frobeniusCoordinateEquiv.symm (frobeniusCoordinateEquiv (u (κ k) x)))
      atTop (𝓝 (v x)) at h
    simp only [LinearIsometryEquiv.symm_apply_apply] at h
    with_unfolding_all exact h
  · intro p
    apply tendsto_integral_frobenius_of_upstream Ω.val
    intro p'
    have hPair := StratificationTheory.Compactness.tendsto_integral_inner_of_L2_convergence
      (fun k => (hF (κ k)).2.1) hwL2 (Lp.memLp p') hStrong
    have hpoint (x : Point) : frobeniusCoordinateEquiv (v x) = w x := congrFun hv x
    simpa only [F, frobeniusField, hpoint] using hPair
  · intro j p
    apply tendsto_integral_frobenius_of_upstream Ω.val
    intro p'
    have hpoint (x : Point) : frobeniusCoordinateEquiv (G x j) = W x j :=
      congrFun (congrFun hG x) j
    simpa only [J, frobeniusGradient, hpoint] using hWeak' j p'

private theorem gradientNormSq_nonneg (G : Gradient) : 0 ≤ gradientNormSq G := by
  rw [gradientNormSq_eq_sum_norm_sq]
  exact Finset.sum_nonneg fun j _ => sq_nonneg ‖G j‖

/-- The unhalved squared-gradient integral is at most twice the energy. -/
theorem lintegral_gradientNormSq_le_twice_energy (a : BulkCoefficients) (ε : ElasticScale)
    (U : Set Point) (u : Point → S0) (D : Point → Gradient) :
    (∫⁻ x in U, ENNReal.ofReal (gradientNormSq (D x))) ≤
      2 * energy a ε U u D := by
  unfold energy
  rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  apply lintegral_mono
  intro x
  dsimp only
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply ENNReal.ofReal_le_ofReal
  have hb := mul_nonneg (sq_nonneg ((ε : ℝ)⁻¹)) (bulkPotential_nonneg a (u x))
  unfold energyDensity
  linarith only [hb]

/-- The integral of the unscaled bulk potential is at most the energy times
the squared elastic scale. -/
theorem lintegral_bulkPotential_le_scale_sq_energy (a : BulkCoefficients) (ε : ElasticScale)
    (U : Set Point) (u : Point → S0) (D : Point → Gradient) :
    (∫⁻ x in U, ENNReal.ofReal (bulkPotential a (u x))) ≤
      ENNReal.ofReal ((ε : ℝ) ^ 2) * energy a ε U u D := by
  unfold energy
  rw [← lintegral_const_mul' _ _ (by simp : ENNReal.ofReal ((ε : ℝ) ^ 2) ≠ ⊤)]
  apply lintegral_mono
  intro x
  dsimp only
  rw [← ENNReal.ofReal_mul (sq_nonneg (ε : ℝ))]
  apply ENNReal.ofReal_le_ofReal
  have he : (ε : ℝ) ≠ 0 := ε.property.1.ne'
  have hCancel : (ε : ℝ) ^ 2 * (ε : ℝ)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ he, one_pow]
  rw [energyDensity, mul_add, ← mul_assoc ((ε : ℝ) ^ 2) ((ε : ℝ)⁻¹ ^ 2), hCancel, one_mul]
  exact le_add_of_nonneg_left
    (mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (gradientNormSq_nonneg _)))

private theorem continuous_bulkPotential (a : BulkCoefficients) : Continuous (bulkPotential a) := by
  let trace : Tensor →L[ℝ] ℝ := (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap
  change Continuous (fun A : S0 =>
    let t := trace ((symmetricTraceless.subtypeL A) ^ 2)
    let s := trace ((symmetricTraceless.subtypeL A) ^ 3)
    let t₀ := preferredTraceSq a
    a.a2 / 2 * t₀ - a.a4 / 4 * t₀ ^ 2 - a.a6 / 6 * t₀ ^ 3
      - a.a2 / 2 * t + a.a4 / 4 * t ^ 2 + a.a6 / 6 * t ^ 3 + a.a6' / 6 * s ^ 2)
  fun_prop

/-- Fatou's lemma puts the almost everywhere limit of bounded-energy maps
into the zero set of the normalized bulk potential. -/
theorem takesVacuumValues_of_ae_tendsto_of_energy_bound
    (a : BulkCoefficients) (U : Set Point) (ε : ℕ → ElasticScale)
    (hε : Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0))
    (u : ℕ → Point → S0) (D : ℕ → Point → Gradient) (v : Point → S0)
    (hu : ∀ k, AEStronglyMeasurable (u k) (volume.restrict U))
    (hv : AEStronglyMeasurable v (volume.restrict U))
    (hAE : ∀ᵐ x ∂volume.restrict U, Tendsto (fun k => u k x) atTop (𝓝 (v x)))
    (M : ℝ)
    (hEnergy : ∀ k, energy a (ε k) U (u k) (D k) ≤ ENNReal.ofReal M) :
    TakesVacuumValues a U v := by
  let P (f : Point → S0) (x : Point) := ENNReal.ofReal (bulkPotential a (f x))
  have hP {f : Point → S0} (hf : AEStronglyMeasurable f (volume.restrict U)) :
      AEMeasurable (P f) (volume.restrict U) :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      ((continuous_bulkPotential a).comp_aestronglyMeasurable hf).aemeasurable
  have hPconv : ∀ᵐ x ∂volume.restrict U, Tendsto (fun k => P (u k) x) atTop (𝓝 (P v x)) := by
    filter_upwards [hAE] with x hx
    exact ENNReal.tendsto_ofReal ((continuous_bulkPotential a).continuousAt.tendsto.comp hx)
  have hScale : Tendsto (fun k => ENNReal.ofReal ((ε k : ℝ) ^ 2 * M)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal ((hε.pow 2).mul_const M)
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, ENNReal.ofReal_zero] using h
  have hInt : Tendsto (fun k => ∫⁻ x in U, P (u k) x) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hScale (fun _ => zero_le)
      (fun k => calc
        (∫⁻ x in U, P (u k) x) ≤
            ENNReal.ofReal ((ε k : ℝ) ^ 2) * energy a (ε k) U (u k) (D k) :=
          lintegral_bulkPotential_le_scale_sq_energy a (ε k) U (u k) (D k)
        _ ≤ ENNReal.ofReal ((ε k : ℝ) ^ 2 * M) := by
          rw [ENNReal.ofReal_mul (sq_nonneg _)]
          exact mul_le_mul_right (hEnergy k) _)
  have hZero : (∫⁻ x in U, P v x) = 0 := le_antisymm (calc
    (∫⁻ x in U, P v x) = ∫⁻ x in U, liminf (fun k => P (u k) x) atTop :=
      lintegral_congr_ae (hPconv.mono fun _ hx => hx.liminf_eq.symm)
    _ ≤ liminf (fun k => ∫⁻ x in U, P (u k) x) atTop := lintegral_liminf_le' (fun k => hP (hu k))
    _ = 0 := hInt.liminf_eq) zero_le
  have hAEzero := (lintegral_eq_zero_iff' (hP hv)).mp hZero
  exact hAEzero.mono fun x hx =>
    (bulkPotential_eq_zero_iff a (v x)).1
      (le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (bulkPotential_nonneg a (v x)))

/-- Weak H¹ compactness and the vacuum constraint for a prescribed sequence
of elastic scales tending to zero. The domain is any open set of finite
volume. -/
theorem exists_vacuum_weak_subsequence_of_bounded_energy
    (a : BulkCoefficients) {U : Set Point} (hU : IsOpen U) (hFinite : volume U ≠ ⊤)
    (ε : ℕ → ElasticScale) (hε : Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0))
    (u : ℕ → Point → S0) (D : ℕ → Point → Gradient)
    (hu : ∀ k, MemH1Loc U (u k) (D k)) (M : ℝ) (hM : 0 ≤ M)
    (hBounds : ∀ k, energy a (ε k) U (u k) (D k) ≤ ENNReal.ofReal M ∧
      eLpNorm (u k) ∞ (volume.restrict U) ≤ ENNReal.ofReal M) :
    ∃ (κ : ℕ → ℕ) (v : Point → S0) (G : Point → Gradient),
      StrictMono κ ∧ (∀ k, MemH1 U (u k) (D k)) ∧ MemH1 U v G ∧ TakesVacuumValues a U v ∧
      (∫⁻ x in U, ENNReal.ofReal (gradientNormSq (G x))) ≤ ENNReal.ofReal (2 * M) ∧
      Tendsto (fun k => eLpNorm (u (κ k) - v) 2 (volume.restrict U)) atTop (𝓝 0) ∧
      (∀ᵐ x ∂volume.restrict U, Tendsto (fun k => u (κ k) x) atTop (𝓝 (v x))) ∧
      (∀ w : Lp S0 2 (volume.restrict U),
        Tendsto (fun k => ∫ x in U, frobeniusS0 (u (κ k) x) (w x))
          atTop (𝓝 (∫ x in U, frobeniusS0 (v x) (w x)))) ∧
      ∀ (j : Fin 3) (w : Lp S0 2 (volume.restrict U)),
        Tendsto (fun k => ∫ x in U, frobeniusS0 (D (κ k) x j) (w x))
          atTop (𝓝 (∫ x in U, frobeniusS0 (G x j) (w x))) := by
  let B : ℝ≥0 := ⟨M, hM⟩
  let C : ℝ≥0 := ⟨2 * M, mul_nonneg (by norm_num) hM⟩
  have hC : (C : ℝ≥0∞) = ENNReal.ofReal (2 * M) := (ENNReal.ofReal_eq_coe_nnreal C.property).symm
  have hB (k : ℕ) : ∀ᵐ x ∂volume.restrict U, ‖u k x‖ ≤ (B : ℝ) := by
    filter_upwards [enorm_ae_le_eLpNormEssSup (u k) (volume.restrict U)] with x hx
    apply (ENNReal.ofReal_le_ofReal_iff hM).mp
    calc
      ENNReal.ofReal ‖u k x‖ = ‖u k x‖ₑ := ofReal_norm (u k x)
      _ ≤ eLpNormEssSup (u k) (volume.restrict U) := hx
      _ ≤ ENNReal.ofReal M := by simpa only [eLpNorm_exponent_top] using (hBounds k).2
  have hE (k : ℕ) : (∫⁻ x in U, ENNReal.ofReal (gradientNormSq (D k x))) ≤ C := calc
      _ ≤ 2 * energy a (ε k) U (u k) (D k) :=
        lintegral_gradientNormSq_le_twice_energy a (ε k) U (u k) (D k)
      _ ≤ 2 * ENNReal.ofReal M := mul_le_mul_right (hBounds k).1 2
      _ = C := by
        rw [hC, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  obtain ⟨κ, v, G, hκ, huH, hv, hG, hStrong, hAE, hWeakMap, hWeakGrad⟩ :=
    exists_tensor_rellich_subsequence ⟨U, hU⟩ hFinite u D hu B C hB hE
  have hVacuum := takesVacuumValues_of_ae_tendsto_of_energy_bound a U (ε ∘ κ)
    (hε.comp hκ.tendsto_atTop) (u ∘ κ) (D ∘ κ) v
    (fun k => (huH (κ k)).1.aestronglyMeasurable) hv.1.aestronglyMeasurable hAE M
    (fun k => (hBounds (κ k)).1)
  exact ⟨κ, v, G, hκ, huH, hv, hVacuum, hC ▸ hG, hStrong, hAE, hWeakMap, hWeakGrad⟩

/-- Weak compactness for the bounded-energy family in Theorem 1.4,
with a selected sequence of scales converging to zero. -/
theorem exists_vacuum_weak_limit_of_bounded_energy_family
    (a : BulkCoefficients) {U : Set Point} (hU : IsBoundedDomain U)
    (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient)
    (hLocal : ∀ ε, IsLocalEnergyMinimizer a ε U (Q ε) (D ε)) (M : ℝ) (hM : 0 < M)
    (hBounds : ∀ ε, energy a ε U (Q ε) (D ε) ≤ ENNReal.ofReal M ∧
      eLpNorm (Q ε) ∞ (volume.restrict U) ≤ ENNReal.ofReal M) :
    ∃ (ε : ℕ → ElasticScale) (v : Point → S0) (G : Point → Gradient),
      Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0) ∧
      (∀ k, MemH1 U (Q (ε k)) (D (ε k))) ∧ MemH1 U v G ∧ TakesVacuumValues a U v ∧
      (∫⁻ x in U, ENNReal.ofReal (gradientNormSq (G x))) ≤ ENNReal.ofReal (2 * M) ∧
      Tendsto (fun k => eLpNorm (Q (ε k) - v) 2 (volume.restrict U)) atTop (𝓝 0) ∧
      (∀ᵐ x ∂volume.restrict U, Tendsto (fun k => Q (ε k) x) atTop (𝓝 (v x))) ∧
      (∀ w : Lp S0 2 (volume.restrict U),
        Tendsto (fun k => ∫ x in U, frobeniusS0 (Q (ε k) x) (w x))
          atTop (𝓝 (∫ x in U, frobeniusS0 (v x) (w x)))) ∧
      ∀ (j : Fin 3) (w : Lp S0 2 (volume.restrict U)),
        Tendsto (fun k => ∫ x in U, frobeniusS0 (D (ε k) x j) (w x))
          atTop (𝓝 (∫ x in U, frobeniusS0 (G x j) (w x))) := by
  let initial (k : ℕ) : ElasticScale := ⟨1 / ((k : ℝ) + 2), by
    have hk := Nat.cast_nonneg (α := ℝ) k
    refine ⟨by positivity, (div_lt_iff₀ (by positivity)).2 ?_⟩
    linarith only [hk]⟩
  have hε : Tendsto (fun k => (initial k : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_add_atTop_iff_nat 1).2 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [initial, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h
  obtain ⟨κ, v, G, hκ, hInput, h⟩ := exists_vacuum_weak_subsequence_of_bounded_energy a hU.1
    hU.2.2.measure_lt_top.ne initial hε (Q ∘ initial) (D ∘ initial)
    (fun k => (hLocal (initial k)).1) M hM.le (fun k => hBounds (initial k))
  exact ⟨initial ∘ κ, v, G, hε.comp hκ.tendsto_atTop, fun k => hInput (κ k), h⟩

end Thesis
end
end
