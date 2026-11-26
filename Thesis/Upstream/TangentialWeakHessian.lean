module

public import Thesis.Upstream.AmbientWeakHessianFourEstimate
public import Thesis.Upstream.AmbientWeakPartialLpBounds
import Thesis.Upstream.LocalSobolevGradientTransport
import HarmonicMaps.Analysis.VariableMollificationL2

/-! Higher tangential weak derivatives of the actual flat perturbation equation. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal

namespace Thesis

private theorem compactSupport_translate {q : ℕ} {E : Type*} [Zero E]
    {f : Domain q → E} (h : HasCompactSupport f) (z : Domain q) :
    HasCompactSupport (fun x => f (x+z)) := by
  let e := (IsometryEquiv.addRight z).toHomeomorph
  change HasCompactSupport (f ∘ e)
  rw [HasCompactSupport,tsupport_comp_eq_preimage]
  exact e.isCompact_preimage.2 h

private theorem compactSupport_differenceQuotient {q : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℝ E] {f : Domain q → E}
    (hf : HasCompactSupport f) (i : Fin q) (t : ℝ) :
    HasCompactSupport (ambientDifferenceQuotient i t f) := by
  let d : Domain q → E := (fun x => f (x+t • EuclideanSpace.single i 1)) - f
  have hd : HasCompactSupport d := (compactSupport_translate hf _).sub hf
  exact hd.smul_left (f := fun _ : Domain q => t⁻¹)

/-- A tangential translation preserves the literal small coefficients. The
difference quotient of the trace equation adds just the coefficient increment
multiplied by the original Hessian. -/
theorem weakHessian_differenceQuotient_trace {q : ℕ}
    {H : Point → Fin 3 → HarmonicMaps.Gradient 3 q} {f : Point → Ambient q}
    {a : Fin 3 → Fin 3 → Point → ℝ}
    (hEq : (fun x => ∑ i : Fin 3, H x i i) =ᵐ[volume]
      fun x => f x + ∑ i : Fin 3, ∑ j : Fin 3, a i j x • H x i j)
    (k : Fin 3) (t : ℝ) :
    (fun x => ∑ i : Fin 3, ambientDifferenceQuotient k t (fun y => H y i i) x) =ᵐ[volume]
      fun x => (ambientDifferenceQuotient k t f x +
          ∑ i : Fin 3, ∑ j : Fin 3, ambientDifferenceQuotient k t (a i j) x • H x i j) +
        ∑ i : Fin 3, ∑ j : Fin 3, a i j (x+t • axis k) •
          ambientDifferenceQuotient k t (fun y => H y i j) x := by
  let z : Point := t • axis k
  have hTrans := (measurePreserving_add_right (volume : Measure Point) z).quasiMeasurePreserving.ae hEq
  filter_upwards [hEq,hTrans] with x hx hy
  change (∑ i : Fin 3, H x i i) = f x + ∑ i, ∑ j, a i j x • H x i j at hx
  change (∑ i : Fin 3, H (x+z) i i) = f (x+z) + ∑ i, ∑ j, a i j (x+z) • H (x+z) i j at hy
  simp only [ambientDifferenceQuotient,← Finset.smul_sum,Finset.sum_sub_distrib]
  change t⁻¹ • ((∑ i : Fin 3, H (x+z) i i)-(∑ i, H x i i)) = _
  rw [hy,hx,add_sub_add_comm,← Finset.sum_sub_distrib,smul_add,Finset.smul_sum,add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib,Finset.smul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [axis,z]
  module

private theorem differenceQuotient_coefficient_error_bound
    {q : ℕ} {H : Point → Fin 3 → HarmonicMaps.Gradient 3 q}
    {a : Fin 3 → Fin 3 → Point → ℝ}
    (ha : ∀ i j, AEStronglyMeasurable (a i j) volume ∧ HasCompactSupport (a i j))
    (k : Fin 3) (t : ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hA : ∀ i j x, |ambientDifferenceQuotient k t (a i j) x| ≤ L)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hH : ∀ i j, MemLp (fun x => H x i j) p (volume : Measure Point)) :
    let S (x : Point) := ∑ i : Fin 3, ∑ j : Fin 3, ambientDifferenceQuotient k t (a i j) x • H x i j
    HasCompactSupport S ∧ MemLp S p volume ∧
      lpNorm S p volume ≤ ∑ i : Fin 3, ∑ j : Fin 3, L*lpNorm (fun x => H x i j) p volume := by
  let b (i j : Fin 3) := ambientDifferenceQuotient k t (a i j)
  let z : Point := t • axis k
  let R (i j : Fin 3) (x : Point) := b i j x • H x i j
  have hbM (i j : Fin 3) : AEStronglyMeasurable (b i j) volume :=
    (((ha i j).1.comp_measurePreserving (measurePreserving_add_right volume z)).sub (ha i j).1).const_smul t⁻¹
  have hbS (i j : Fin 3) : HasCompactSupport (b i j) := compactSupport_differenceQuotient (ha i j).2 k t
  have hR (i j : Fin 3) : MemLp (R i j) p volume :=
    (hH i j).smul (r := p) (memLp_top_of_bound (hbM i j) L
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hA i j x))
  have hRN (i j : Fin 3) : lpNorm (R i j) p volume ≤ L*lpNorm (fun x => H x i j) p volume :=
    lpNorm_smul_le_of_pointwise_abs_le (hH i j) hL (hA i j)
  let S (x : Point) := ∑ i : Fin 3, ∑ j : Fin 3, R i j x
  have hS : S = ∑ i : Fin 3, ∑ j : Fin 3, R i j := by funext x; simp [S,Finset.sum_apply]
  have hScomp : HasCompactSupport S := by
    rw [hasCompactSupport_iff_eventuallyEq]
    have hOutside : ∀ᶠ x in coclosedCompact Point, ∀ i j : Fin 3, b i j x = 0 :=
      eventually_all.2 fun i => eventually_all.2 fun j => hasCompactSupport_iff_eventuallyEq.1 (hbS i j)
    filter_upwards [hOutside] with x hx
    simp only [S,R,hx,zero_smul,Finset.sum_const_zero,Pi.zero_apply]
  change HasCompactSupport S ∧ MemLp S p volume ∧
    lpNorm S p volume ≤ ∑ i : Fin 3, ∑ j : Fin 3, L*lpNorm (fun x => H x i j) p volume
  refine ⟨hScomp,?_⟩
  rw [hS]
  have hRow (i : Fin 3) : MemLp (∑ j : Fin 3, R i j) p volume :=
    memLp_finsetSum' _ (fun j _ => hR i j)
  refine ⟨memLp_finsetSum' _ (fun i _ => hRow i),(lpNorm_sum_le (fun i _ => hRow i) hp).trans ?_⟩
  exact Finset.sum_le_sum fun i _ =>
    (lpNorm_sum_le (fun j _ => hR i j) hp).trans (Finset.sum_le_sum fun j _ => hRN i j)

/-- The whole-space small-coefficient estimate applies to a coordinate
difference of a genuine weak Hessian and bounds it by the forcing difference
and the coefficient difference times the undifferentiated Hessian. -/
theorem exists_wholeSpace_weakHessian_difference_four_estimate :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ {q : ℕ} {u f : Point → Ambient q}
      {D : Point → HarmonicMaps.Gradient 3 q} {H : Point → Fin 3 → HarmonicMaps.Gradient 3 q}
      {a : Fin 3 → Fin 3 → Point → ℝ},
      MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D →
      (∀ i, MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (fun x => D x i) (fun x => H x i)) →
      HasCompactSupport f → MemLp f 2 (volume : Measure Point) → MemLp f 4 (volume : Measure Point) →
      (∀ i j, AEStronglyMeasurable (a i j) (volume : Measure Point) ∧ HasCompactSupport (a i j)) →
      (∀ i j x, |a i j x| ≤ δ) →
      ((fun x => ∑ i : Fin 3, H x i i) =ᵐ[(volume : Measure Point)]
        fun x => f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x • H x i j) →
      ∀ (k : Fin 3) (t L : ℝ), 0 ≤ L →
        (∀ i j x, |ambientDifferenceQuotient k t (a i j) x| ≤ L) →
        ∀ i j, let K := ambientDifferenceQuotient k t (fun x => H x i j)
          MemLp K 4 (volume : Measure Point) ∧
          lpNorm K 4 volume ≤ (q*C) * (lpNorm (ambientDifferenceQuotient k t f) 4 volume +
            ∑ i : Fin 3, ∑ j : Fin 3, L*lpNorm (fun x => H x i j) 4 volume) := by
  obtain ⟨δ,C,hδ,hC,hT⟩ := exists_wholeSpace_ambientWeakHessian_four_estimate
  refine ⟨δ,C,hδ,hC,?_⟩
  intro q u f D H a hu hD hc hf₂ hf₄ ha hA hEq k t L hL hDif i j
  let u' := ambientDifferenceQuotient k t u
  let D' (x : Point) (i : Fin 3) := ambientDifferenceQuotient k t (fun y => D y i) x
  let H' (x : Point) (i : Fin 3) (j : Fin 3) := ambientDifferenceQuotient k t (fun y => H y i j) x
  let S (x : Point) := ∑ i : Fin 3, ∑ j : Fin 3, ambientDifferenceQuotient k t (a i j) x • H x i j
  let G := ambientDifferenceQuotient k t f + S
  let z : Point := t • axis k
  let a' (i j : Fin 3) (x : Point) := a i j (x+z)
  have hu' : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u' D' :=
    memW12_differenceQuotient_univ hu k t
  have hD' (i : Fin 3) :
      MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (fun x => D' x i) (fun x => H' x i) :=
    memW12_differenceQuotient_univ (hD i) k t
  have hH₂ (i j : Fin 3) : MemLp (fun x => H x i j) 2 volume := by
    simpa only [Measure.restrict_univ] using (hD i).2.2 j
  have hH₄ (i j : Fin 3) : MemLp (fun x => H x i j) 4 volume :=
    (hT hu hD hc hf₂ hf₄ ha hA hEq i j).1
  obtain ⟨hSC,hS₂,_⟩ := differenceQuotient_coefficient_error_bound ha k t hL hDif (by norm_num) hH₂
  obtain ⟨_,hS₄,hSN⟩ := differenceQuotient_coefficient_error_bound ha k t hL hDif (by norm_num) hH₄
  have hG₂ : MemLp G 2 volume := (memLp_ambientDifferenceQuotient hf₂ k t).add hS₂
  have hG₄ : MemLp G 4 volume := (memLp_ambientDifferenceQuotient hf₄ k t).add hS₄
  have hGC : HasCompactSupport G := (compactSupport_differenceQuotient hc k t).add hSC
  have hGP : lpNorm G 4 volume ≤ lpNorm (ambientDifferenceQuotient k t f) 4 volume +
      ∑ i : Fin 3, ∑ j : Fin 3, L*lpNorm (fun x => H x i j) 4 volume :=
    (lpNorm_add_le (memLp_ambientDifferenceQuotient hf₄ k t) (by norm_num)).trans (add_le_add le_rfl hSN)
  have ha' (i j : Fin 3) : AEStronglyMeasurable (a' i j) volume ∧ HasCompactSupport (a' i j) :=
    ⟨(ha i j).1.comp_measurePreserving (measurePreserving_add_right volume z),
      compactSupport_translate (ha i j).2 z⟩
  have hEq' : (fun x => ∑ i : Fin 3, H' x i i) =ᵐ[volume]
      fun x => G x + ∑ i : Fin 3, ∑ j : Fin 3, a' i j x • H' x i j :=
    weakHessian_differenceQuotient_trace hEq k t
  obtain ⟨hK,hKN⟩ := hT hu' hD' hGC hG₂ hG₄ ha' (fun i j x => hA i j (x+z)) hEq' i j
  exact ⟨hK,hKN.trans (mul_le_mul_of_nonneg_left hGP (by positivity))⟩

/-- Compactly supported actual fields with uniform fourth-power bounds
on their normalized differences have a weak derivative in L² and L⁴. -/
theorem exists_weakAmbientPartial_of_compact_four_differences
    {q : ℕ} {v : Point → Ambient q} (hv : MemLp v 2 volume)
    (hvc : HasCompactSupport v) (k : Fin 3) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ t ∈ Ioo (0 : ℝ) 2,
      MemLp (ambientDifferenceQuotient k t v) 4 volume ∧
        lpNorm (ambientDifferenceQuotient k t v) 4 volume ≤ M) :
    ∃ d : Point → Ambient q, MemLp d 2 volume ∧ MemLp d 4 volume ∧
      IsWeakAmbientCoordinatePartial univ k v d ∧ lpNorm d 4 volume ≤ M := by
  obtain ⟨R,hR,hV⟩ := hvc.isBounded.subset_ball_lt 0 (0 : Point)
  let K := closedBall (0 : Point) (R+2)
  let μ := (volume : Measure Point).restrict K
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  let C := ENNReal.ofReal M * μ univ ^ ((1/4 : ℝ))
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ))
  let t (n : ℕ) := 1 / ((n : ℝ)+1)
  have hT (n : ℕ) : t n ∈ Ioo (0 : ℝ) 2 := by
    have hN : 1 ≤ (n : ℝ)+1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact ⟨by dsimp [t]; positivity, (div_le_one (zero_lt_one.trans_le hN)).2 hN |>.trans_lt (by norm_num)⟩
  have hSmall : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hMem (n : ℕ) := (hBound (t n) (hT n)).1
  have h4 (n : ℕ) : eLpNorm (ambientDifferenceQuotient k (t n) v) 4 volume ≤ ENNReal.ofReal M := by
    rw [← ofReal_lpNorm (hMem n)]
    exact ENNReal.ofReal_le_ofReal (hBound (t n) (hT n)).2
  have hSupport (n : ℕ) : (ambientDifferenceQuotient k (t n) v).support ⊆ K := by
    intro x hx
    by_contra hn
    have hOutside : R+2 < ‖x‖ := lt_of_not_ge (fun h => hn (mem_closedBall_zero_iff.2 h))
    have hDx : ‖t n • axis k‖ = t n := by
      rw [norm_smul,Real.norm_of_nonneg (hT n).1.le]
      simp [axis]
    have hShift : R < ‖x+t n • axis k‖ := by
      have h := norm_sub_le (x+t n • axis k) (t n • axis k)
      rw [add_sub_cancel_right,hDx] at h
      linarith only [h,hOutside,(hT n).2]
    have hx0 : v x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hx => (not_lt_of_ge (by linarith only [hOutside] : R ≤ ‖x‖)) (mem_ball_zero_iff.1 (hV hx)))
    have hx1 : v (x+t n • axis k) = 0 := image_eq_zero_of_notMem_tsupport
      (fun hx => (not_lt_of_ge hShift.le) (mem_ball_zero_iff.1 (hV hx)))
    apply Function.mem_support.mp hx
    change (t n)⁻¹ • (v (x+t n • axis k)-v x) = 0
    rw [hx0,hx1,sub_self,smul_zero]
  have h2 (n : ℕ) : eLpNorm (ambientDifferenceQuotient k (t n) v) 2 volume ≤ C := by
    let z := ambientDifferenceQuotient k (t n) v
    have hMem' : MemLp z 4 μ := (hMem n).mono_measure Measure.restrict_le_self
    have hNorm : eLpNorm z 4 μ ≤ ENNReal.ofReal M :=
      (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (h4 n)
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (show (2 : ℝ≥0∞) ≤ 4 by norm_num) hMem'.1
    have hExponent : 1 / ((2 : ℝ≥0∞).toReal) - 1 / ((4 : ℝ≥0∞).toReal) = (1/4 : ℝ) := by norm_num
    rw [hExponent] at h
    rw [← eLpNorm_restrict_eq_of_support_subset (hSupport n)]
    apply h.trans
    change eLpNorm z 4 μ * (μ univ)^(1/4 : ℝ) ≤ ENNReal.ofReal M* (μ univ)^(1/4 : ℝ)
    gcongr
  have hInt (n : ℕ) :
      (∫ x in univ, ‖ambientDifferenceQuotient k (t n) v x‖^2) ≤ C.toReal^2 := by
    simp only [Measure.restrict_univ]
    rw [integral_norm_sq_eq_eLpNorm_two_toReal_sq (memLp_ambientDifferenceQuotient hv k (t n))]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono hC (h2 n)) 2
  have h4' (n : ℕ) : eLpNorm (ambientDifferenceQuotient k (t n) v)
      (ENNReal.ofReal (4 : ℝ)) (volume.restrict (univ : Set Point)) ≤ ENNReal.ofReal M := by
    simpa only [Measure.restrict_univ,ENNReal.ofReal_ofNat] using h4 n
  obtain ⟨d,hd₂,_,hd,hN⟩ := exists_weakAmbientCoordinatePartial_of_differenceQuotient_bounds (U := univ)
    hv k hSmall (fun n => (hT n).1.ne') ENNReal.toReal_nonneg hInt (by norm_num : (1 : ℝ) ≤ 4) h4'
  rw [Measure.restrict_univ] at hd₂ hN
  have hE : eLpNorm d 4 volume ≤ ENNReal.ofReal M := by simpa only [ENNReal.ofReal_ofNat] using hN
  have hd₄ : MemLp d 4 volume := ⟨hd₂.1,hE.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨d,hd₂,hd₄,hd,?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff hM,ofReal_lpNorm hd₄]
  exact hE

private theorem memW12_univ_of_coordinate_partials {q : ℕ}
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemLp u 2 volume) (hD : ∀ i, MemLp (fun x => D x i) 2 volume)
    (hW : ∀ i, IsWeakAmbientCoordinatePartial univ i u (fun x => D x i)) :
    MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D := by
  refine ⟨⟨(hu.locallyIntegrable (by norm_num)).locallyIntegrableOn _,
    fun i => ((hD i).locallyIntegrable (by norm_num)).locallyIntegrableOn _,hW⟩,?_⟩
  simpa only [Measure.restrict_univ] using And.intro hu hD

/-- A tangential derivative of a compact weak graph for the flat
perturbation has an actual second weak graph in L² and L⁴, once the
forcing and coefficients have bounded tangential differences. -/
theorem exists_wholeSpace_tangential_weakHessian_four_gain :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {q : ℕ} {u f : Point → Ambient q}
      {D : Point → HarmonicMaps.Gradient 3 q} {H : Point → Fin 3 → HarmonicMaps.Gradient 3 q}
      {a : Fin 3 → Fin 3 → Point → ℝ},
      MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D →
      (∀ i, MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (fun x => D x i) (fun x => H x i)) →
      (∀ i j, HasCompactSupport (fun x => H x i j)) →
      HasCompactSupport f → MemLp f 2 (volume : Measure Point) → MemLp f 4 (volume : Measure Point) →
      (∀ i j, AEStronglyMeasurable (a i j) (volume : Measure Point) ∧ HasCompactSupport (a i j)) →
      (∀ i j x, |a i j x| ≤ δ) →
      ((fun x => ∑ i : Fin 3, H x i i) =ᵐ[(volume : Measure Point)]
        fun x => f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x • H x i j) →
      ∀ (k : Fin 3) (L N : ℝ), 0 ≤ L → 0 ≤ N →
        (∀ t ∈ Ioo (0 : ℝ) 2, ∀ i j x, |ambientDifferenceQuotient k t (a i j) x| ≤ L) →
        (∀ t ∈ Ioo (0 : ℝ) 2, lpNorm (ambientDifferenceQuotient k t f) 4 volume ≤ N) →
        MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (fun x => D x k) (fun x i => H x i k) ∧
        ∃ K : Point → Fin 3 → HarmonicMaps.Gradient 3 q,
          (∀ i, MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (fun x => H x i k) (fun x => K x i)) ∧
          (∀ i j, MemLp (fun x => K x i j) 4 (volume : Measure Point)) ∧
          ∀ i j, IsWeakAmbientCoordinatePartial univ k (fun x => H x i j) (fun x => K x i j) := by
  obtain ⟨δ,C,hδ,hC,hGain⟩ := exists_wholeSpace_weakHessian_difference_four_estimate
  refine ⟨δ,hδ,?_⟩
  intro q u f D H a hu hD hHc hc hf₂ hf₄ ha hA hEq k L N hL hN hDif hForce
  let M := q*C*(N + ∑ i : Fin 3, ∑ j : Fin 3, L*lpNorm (fun x => H x i j) 4 volume)
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (Nat.cast_nonneg q) hC.le)
    (add_nonneg hN (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg hL lpNorm_nonneg))
  have hH₂ (i j : Fin 3) : MemLp (fun x => H x i j) 2 volume := by
    simpa only [Measure.restrict_univ] using (hD i).2.2 j
  have hDiff (i j : Fin 3) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 2) :
      MemLp (ambientDifferenceQuotient k t (fun x => H x i j)) 4 volume ∧
        lpNorm (ambientDifferenceQuotient k t (fun x => H x i j)) 4 volume ≤ M := by
    obtain ⟨hT,hNorm⟩ := hGain hu hD hc hf₂ hf₄ ha hA hEq k t L hL (hDif t ht) i j
    exact ⟨hT,hNorm.trans (mul_le_mul_of_nonneg_left (add_le_add (hForce t ht) le_rfl) (by positivity))⟩
  have hDk : MemLp (fun x => D x k) 2 volume := by simpa only [Measure.restrict_univ] using hu.2.2 k
  have hFirst : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (fun x => D x k) (fun x i => H x i k) :=
    memW12_univ_of_coordinate_partials hDk (fun i => hH₂ i k)
      (fun i => IsWeakAmbientCoordinatePartial.mixed hu.1 ((hD i).1.2.2 k))
  have hExist (i j : Fin 3) :=
    exists_weakAmbientPartial_of_compact_four_differences (hH₂ i j) (hHc i j) k M hM (hDiff i j)
  choose K hK₂ hK₄ hK _hN using hExist
  let K' (x : Point) (i j : Fin 3) := K i j x
  refine ⟨hFirst,K',?_,hK₄,hK⟩
  intro i
  exact memW12_univ_of_coordinate_partials (hH₂ i k) (hK₂ i)
    (fun j => IsWeakAmbientCoordinatePartial.mixed (hD i).1 (hK i j))

end Thesis
