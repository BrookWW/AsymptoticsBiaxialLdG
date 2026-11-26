module

public import SupportingAnalysis.Euclidean
public import SupportingAnalysis.Measure.Covering

/-! A finite Calderón–Zygmund decomposition for continuous compactly supported inputs. -/

public section

open MeasureTheory Metric Set Filter
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace SupportingAnalysis

variable {d : ℕ}

private theorem ballRealVolume_scale (x : E d) {r : ℝ} (hr : 0 < r) :
    volume.real (ball x r) = r ^ d * volume.real (ball (0 : E d) 1) := by
  rw [Measure.real, Measure.addHaar_ball_of_pos volume x hr, finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  rfl

private theorem ballRealVolume_pos (x : E d) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (ball x r) :=
  ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne

private theorem exists_badBall {F : E d → ℝ} (hd : 0 < d) (hF : Continuous F)
    (hFI : Integrable F) {t : ℝ} (ht : 0 < t) :
    ∃ R : ℝ, ∀ x : E d, 2 * t ≤ |F x| → ∃ r : ℝ,
      0 < r ∧ r ≤ R ∧
      t * volume.real (ball x r) < (∫ y in ball x r, |F y|) ∧
      (∫ y in ball x (5 * r), |F y|) ≤ t * volume.real (ball x (5 * r)) := by
  let V := volume.real (ball (0 : E d) 1)
  let M := ∫ y, |F y|
  have hV : 0 < V := ballRealVolume_pos _ one_pos
  have hM : 0 ≤ M := integral_nonneg fun y => abs_nonneg (F y)
  let R := 1 + M / (t * V)
  have hR : 0 < R := by dsimp [R]; positivity
  have hRone : 1 ≤ R := le_add_of_nonneg_right (div_nonneg hM (mul_pos ht hV).le)
  have hlarge (x : E d) {r : ℝ} (hr : R ≤ r) :
      (∫ y in ball x r, |F y|) ≤ t * volume.real (ball x r) := by
    have hr0 : 0 < r := hR.trans_le hr
    have hr1 : 1 ≤ r := hRone.trans hr
    have hpow : r ≤ r ^ d := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
      rw [pow_succ, mul_comm]
      exact le_mul_of_one_le_right hr0.le (one_le_pow₀ hr1)
    rw [ballRealVolume_scale x hr0]
    calc
      _ ≤ M := setIntegral_le_integral hFI.abs (Eventually.of_forall fun y => abs_nonneg (F y))
      _ ≤ t * (r * V) := by
        have hbound : M / (t * V) ≤ r :=
          (le_add_of_nonneg_left zero_le_one : M / (t * V) ≤ R).trans hr
        have h := (div_le_iff₀ (mul_pos ht hV)).mp hbound
        linarith only [h, show r * (t * V) = t * (r * V) by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hV.le) ht.le
  refine ⟨R, fun x hx => ?_⟩
  have hNear : {y : E d | (3 / 2) * t < |F y|} ∈ 𝓝 x :=
    (isOpen_lt continuous_const hF.abs).mem_nhds (by
      change (3 / 2) * t < |F x|
      linarith only [ht, hx])
  obtain ⟨s, hs, hNear⟩ := Metric.mem_nhds_iff.mp hNear
  have hStart : t * volume.real (ball x s) < ∫ y in ball x s, |F y| := by
    calc
      _ < ((3 / 2) * t) * volume.real (ball x s) := by
        exact mul_lt_mul_of_pos_right (by linarith only [ht]) (ballRealVolume_pos x hs)
      _ = ∫ _y in ball x s, (3 / 2) * t := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ _ := by
        haveI : IsFiniteMeasure (volume.restrict (ball x s)) :=
          isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
        exact setIntegral_mono_on (integrable_const _) hFI.abs.integrableOn measurableSet_ball
          (fun y hy => (hNear hy).le)
  let P (r : ℝ) := 0 < r ∧ t * volume.real (ball x r) < ∫ y in ball x r, |F y|
  let A := {r : ℝ | P r}
  have hAne : A.Nonempty := ⟨s, hs, hStart⟩
  have hAR (r : ℝ) (hr : r ∈ A) : r ≤ R :=
    le_of_not_gt fun h => (not_lt_of_ge (hlarge x h.le)) hr.2
  have hAbdd : BddAbove A := ⟨R, hAR⟩
  have hSup : 0 < sSup A := hs.trans_le (le_csSup hAbdd ⟨hs, hStart⟩)
  obtain ⟨r, hrA, hr'⟩ := (lt_csSup_iff hAbdd hAne).mp (show sSup A / 5 < sSup A by linarith)
  refine ⟨r, hrA.1, hAR r hrA, hrA.2, le_of_not_gt fun hb => ?_⟩
  have hFive : 5 * r ∈ A := ⟨mul_pos (by norm_num) hrA.1, hb⟩
  have hFiveLe := le_csSup hAbdd hFive
  linarith only [hr', hFiveLe]

private theorem abs_indicator (A : Set (E d)) (f : E d → ℝ) (x : E d) :
    |A.indicator f x| = A.indicator (fun y => |f y|) x := by
  simpa only [Real.norm_eq_abs] using (norm_indicator_eq_indicator_norm (s := A) (f := f) (a := x))

/-- The good part is bounded at the decomposition height. Each bad part has zero integral
and is supported in the fivefold enlargement of a selected disjoint ball. -/
structure CutoffCZDecomposition (F : E d → ℝ) (t : ℝ) where
  size : ℕ
  center : Fin size → E d
  radius : Fin size → ℝ
  radius_pos : ∀ i, 0 < radius i
  good : E d → ℝ
  bad : Fin size → E d → ℝ
  good_integrable : Integrable good
  good_bound : ∀ x, |good x| ≤ (5 : ℝ) ^ d * t + 2 * t
  good_mass : (∫ x, |good x|) ≤ ∫ x, |F x|
  bad_integrable : ∀ i, Integrable (bad i)
  bad_support : ∀ i, Function.support (bad i) ⊆ ball (center i) (5 * radius i)
  bad_integral : ∀ i, (∫ x, bad i x) = 0
  bad_mass : (∑ i, ∫ x, |bad i x|) ≤ 2 * ∫ x, |F x|
  sum_eq : ∀ x, F x = good x + ∑ i, bad i x
  exceptional_mass : volume (⋃ i, ball (center i) (10 * radius i)) ≤
    ENNReal.ofReal ((10 : ℝ) ^ d * (∫ x, |F x|) / t)

private theorem exists_finite_badBall_cover (hd : 0 < d) {F : E d → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) {t : ℝ} (ht : 0 < t) :
    ∃ (n : ℕ) (z : Fin n → E d) (r : Fin n → ℝ),
      (∀ i, 0 < r i) ∧
      Pairwise (fun i j => Disjoint (ball (z i) (r i)) (ball (z j) (r j))) ∧
      {x | 2 * t ≤ |F x|} ⊆ (⋃ i, ball (z i) (5 * r i)) ∧
      (∀ i, t * volume.real (ball (z i) (r i)) ≤ ∫ x in ball (z i) (r i), |F x|) ∧
      (∀ i, (∫ x in ball (z i) (5 * r i), |F x|) ≤ t * volume.real (ball (z i) (5 * r i))) := by
  classical
  have hFI : Integrable F (volume : Measure (E d)) := hF.integrable_of_hasCompactSupport hFc
  let U := {x : E d | 2 * t ≤ |F x|}
  have hUc : IsCompact U := hFc.of_isClosed_subset (isClosed_le continuous_const hF.abs)
    (fun x hx => subset_tsupport _ <| Function.mem_support.mpr fun hz =>
      (not_le_of_gt (mul_pos two_pos ht)) (by simpa only [U, mem_setOf_eq, hz, abs_zero] using hx))
  obtain ⟨R, hR⟩ := exists_badBall hd hF hFI ht
  have hWitness (x : U) := hR x x.property
  choose r hr hbounded hlower hupper using hWitness
  obtain ⟨J, _, _, _, hdisjoint, hcover⟩ :=
    exists_fivefold_disjoint_subfamily (univ : Set U) Subtype.val r (fun i _ => hbounded i)
  have hUcover : U ⊆ ⋃ j ∈ J, ball (j : E d) (5 * r j) := by
    intro x hx
    let y : U := ⟨x, hx⟩
    exact hcover (mem_iUnion₂.mpr ⟨y, mem_univ y, mem_ball_self (hr y)⟩)
  obtain ⟨s, hs⟩ := hUc.elim_finite_subcover
    (fun j : J => ball (j.val : E d) (5 * r j.val)) (fun _ => isOpen_ball)
    (by simpa only [iUnion_subtype] using hUcover)
  let e := s.equivFin.symm
  let n := s.card
  let p (i : Fin n) : U := (e i).val.val
  let z (i : Fin n) : E d := p i
  refine ⟨n, z, fun i => r (p i), fun i => hr (p i), ?_, ?_,
    fun i => (hlower (p i)).le, fun i => hupper (p i)⟩
  · intro i j hij
    exact hdisjoint (e i).val.property (e j).val.property fun h =>
      hij (e.injective (Subtype.ext (Subtype.ext h)))
  · intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hs hx)
    refine mem_iUnion.mpr ⟨e.symm ⟨j, hj⟩, ?_⟩
    simpa only [z, p, Equiv.apply_symm_apply] using hxj

/-- A compact positive-height superlevel set needs only finitely many of the fivefold balls. -/
theorem exists_cutoffCZDecomposition (hd : 0 < d) {F : E d → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) {t : ℝ} (ht : 0 < t) :
    Nonempty (CutoffCZDecomposition F t) := by
  classical
  have hFI : Integrable F (volume : Measure (E d)) := hF.integrable_of_hasCompactSupport hFc
  obtain ⟨n, z, r, hr, hBd, hUW, hlower, hupper⟩ := exists_finite_badBall_cover hd hF hFc ht
  let B (i : Fin n) := ball (z i) (r i)
  let L (i : Fin n) := ball (z i) (5 * r i)
  let W := ⋃ i, L i
  let A := disjointed L
  have hA (i : Fin n) : A i ⊆ L i := disjointed_subset _ _
  have hAm (i : Fin n) : MeasurableSet (A i) := by
    dsimp only [A]
    rw [disjointed_eq_inter_compl]
    exact measurableSet_ball.inter (MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ : j < i => measurableSet_ball.compl)
  have hAd : Pairwise (fun i j => Disjoint (A i) (A j)) := disjoint_disjointed _
  have hAW : (⋃ i, A i) = W := iUnion_disjointed
  have hWm : MeasurableSet W := MeasurableSet.iUnion fun _ => measurableSet_ball
  have hBL (i : Fin n) : B i ⊆ L i := ball_subset_ball (by linarith only [hr i])
  let c (i : Fin n) := (∫ y in A i, F y) / volume.real (B i)
  let q (i : Fin n) := (B i).indicator (fun _ => c i)
  let b (i : Fin n) := (A i).indicator F - q i
  let a := Wᶜ.indicator F + ∑ i, q i
  have hqI (i : Fin n) : Integrable (q i) := by
    exact (integrableOn_const (C := c i) measure_ball_lt_top.ne).integrable_indicator measurableSet_ball
  have hC (i : Fin n) : |c i| * volume.real (B i) ≤ ∫ y in A i, |F y| := by
    dsimp only [c]
    rw [abs_div, abs_of_pos (ballRealVolume_pos _ (hr i)),
      div_mul_cancel₀ _ (ballRealVolume_pos _ (hr i)).ne']
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (μ := volume.restrict (A i)) F
  have hvolRatio (i : Fin n) {j : ℝ} (hj : 0 < j) :
      volume.real (ball (z i) (j * r i)) = j ^ d * volume.real (B i) := by
    dsimp only [B]
    rw [ballRealVolume_scale _ (mul_pos hj (hr i)), ballRealVolume_scale _ (hr i),
      mul_pow, mul_assoc]
  have hc (i : Fin n) : |c i| ≤ (5 : ℝ) ^ d * t := by
    apply (mul_le_mul_iff_left₀ (ballRealVolume_pos (z i) (hr i))).mp
    calc
      _ ≤ ∫ y in A i, |F y| := hC i
      _ ≤ ∫ y in L i, |F y| :=
        setIntegral_mono_set hFI.abs.integrableOn (Eventually.of_forall fun y => abs_nonneg _)
          (hA i).eventuallyLE
      _ ≤ t * volume.real (L i) := hupper i
      _ = _ := by dsimp only [L]; rw [hvolRatio i (by norm_num)]; ring
  have hqMass (i : Fin n) : (∫ x, |q i x|) ≤ ∫ y in A i, |F y| := by
    calc
      _ = |c i| * volume.real (B i) := by
        simp only [q, abs_indicator]
        rw [integral_indicator_const _ (measurableSet_ball : MeasurableSet (B i)), smul_eq_mul,
          mul_comm]
      _ ≤ _ := hC i
  have hA_mass : (∑ i, ∫ x in A i, |F x|) = ∫ x in W, |F x| := by
    rw [← hAW, integral_iUnion_fintype hAm hAd (fun _ => hFI.abs.integrableOn)]
  have hB_mass : (∑ i, ∫ x in B i, |F x|) ≤ ∫ x, |F x| := by
    rw [← integral_iUnion_fintype (fun _ => measurableSet_ball) hBd (fun _ => hFI.abs.integrableOn)]
    exact setIntegral_le_integral hFI.abs (Eventually.of_forall fun _ => abs_nonneg _)
  have hbI (i : Fin n) : Integrable (b i) := (hFI.indicator (hAm i)).sub (hqI i)
  have haI : Integrable a := by
    change Integrable (Wᶜ.indicator F + ∑ i, q i)
    have hs : (∑ i, q i) = fun x => ∑ i, q i x := by
      ext x
      simp only [Finset.sum_apply]
    rw [hs]
    exact (hFI.indicator hWm.compl).add (integrable_finsetSum Finset.univ fun i _ => hqI i)
  refine ⟨⟨n, z, fun i => r i, fun i => hr i, a, b, haI, ?_, ?_, hbI,
    ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x
    have hSum : |∑ i, q i x| ≤ (5 : ℝ) ^ d * t := by
      by_cases hx : ∃ i, x ∈ B i
      · obtain ⟨i, hi⟩ := hx
        rw [Finset.sum_eq_single i]
        · simpa only [q, indicator_of_mem hi] using hc i
        · intro j _ hj
          exact indicator_of_notMem (fun hjx => (Set.disjoint_left.mp (hBd hj) hjx hi)) _
        · simp
      · simp only [not_exists] at hx
        simp only [q, indicator_of_notMem (hx _), Finset.sum_const_zero, abs_zero]
        positivity
    have hOutside : |Wᶜ.indicator F x| ≤ 2 * t := by
      by_cases hx : x ∈ W
      · simp [indicator_of_notMem (show x ∉ Wᶜ from fun hy => hy hx), ht.le]
      · rw [indicator_of_mem (show x ∈ Wᶜ from hx)]
        exact le_of_lt (not_le.mp (fun h => hx (hUW h)))
    exact (abs_add_le _ _).trans (by simpa only [add_comm, Finset.sum_apply] using add_le_add hOutside hSum)
  · calc
      (∫ x, |a x|) ≤ (∫ x in Wᶜ, |F x|) + ∑ i, ∫ x, |q i x| := by
        have hexpr : Integrable (fun x => |Wᶜ.indicator F x| + ∑ i, |q i x|) :=
          (hFI.indicator hWm.compl).abs.add (integrable_finsetSum _ fun i _ => (hqI i).abs)
        refine (integral_mono haI.abs hexpr (fun x => (abs_add_le _ _).trans ?_)).trans_eq ?_
        · rw [Finset.sum_apply]
          exact add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
        · rw [integral_add (hFI.indicator hWm.compl).abs
            (integrable_finsetSum _ fun i _ => (hqI i).abs),
            integral_finsetSum _ fun i _ => (hqI i).abs]
          simp only [abs_indicator,
            integral_indicator hWm.compl]
      _ ≤ (∫ x in Wᶜ, |F x|) + ∫ x in W, |F x| := by
        rw [← hA_mass]
        exact add_le_add le_rfl (Finset.sum_le_sum fun i _ => hqMass i)
      _ = _ := by simpa only [compl_compl] using integral_add_compl hWm.compl hFI.abs
  · intro i x hx
    by_contra hn
    have ha0 : x ∉ A i := fun h => hn (hA i h)
    have hb0 : x ∉ B i := fun h => hn (hBL i h)
    exact Function.mem_support.mp hx (by simp [b, q, indicator_of_notMem ha0, indicator_of_notMem hb0])
  · intro i
    change (∫ x, (A i).indicator F x - q i x) = 0
    rw [integral_sub (hFI.indicator (hAm i)) (hqI i), integral_indicator (hAm i)]
    dsimp only [q, c]
    rw [integral_indicator_const _ (measurableSet_ball : MeasurableSet (B i)), smul_eq_mul,
      mul_comm (volume.real (B i)), div_mul_cancel₀ _ (ballRealVolume_pos _ (hr i)).ne',
      sub_self]
  · calc
      (∑ i, ∫ x, |b i x|) ≤ ∑ i, ((∫ x in A i, |F x|) + ∫ x, |q i x|) := by
        apply Finset.sum_le_sum
        intro i _
        refine (integral_mono (hbI i).abs
          ((hFI.indicator (hAm i)).abs.add (hqI i).abs)
          (fun x => by
            change |(A i).indicator F x - q i x| ≤ |(A i).indicator F x| + |q i x|
            simpa only [sub_eq_add_neg, abs_neg] using abs_add_le ((A i).indicator F x) (-q i x))).trans_eq ?_
        simp only [Pi.add_apply]
        rw [integral_add (hFI.indicator (hAm i)).abs (hqI i).abs]
        simp only [abs_indicator,
          integral_indicator (hAm i)]
      _ ≤ 2 * ∫ x in W, |F x| := by
        rw [← hA_mass, two_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => add_le_add le_rfl (hqMass i)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hFI.abs (Eventually.of_forall fun _ => abs_nonneg _)) zero_le_two
  · intro x
    have hFsum : (∑ i, (A i).indicator F x) = W.indicator F x := by
      rw [← hAW]
      by_cases hx : x ∈ ⋃ i, A i
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        rw [indicator_of_mem hx, Finset.sum_eq_single i, indicator_of_mem hi]
        · intro j _ hj
          exact indicator_of_notMem (fun h => Set.disjoint_left.mp (hAd hj) h hi) _
        · simp
      · have hxi (i : Fin n) : x ∉ A i := fun hi => hx (mem_iUnion.mpr ⟨i, hi⟩)
        simp only [indicator_of_notMem hx, indicator_of_notMem (hxi _), Finset.sum_const_zero]
    simp only [a, b, Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Finset.sum_sub_distrib, hFsum]
    rw [add_assoc, add_comm (∑ i, q i x), sub_add_cancel]
    by_cases hx : x ∈ W <;> simp [hx]
  · refine (measure_iUnion_le _).trans ?_
    have hfinite (i : Fin n) : volume (ball (z i) (10 * r i)) ≠ ⊤ := measure_ball_lt_top.ne
    have hterm (i : Fin n) : volume.real (ball (z i) (10 * r i)) =
        (10 : ℝ) ^ d * volume.real (B i) := hvolRatio i (by norm_num)
    have hterm' (i : Fin n) : volume (ball (z i) (10 * r i)) =
        ENNReal.ofReal ((10 : ℝ) ^ d * volume.real (B i)) := by
      rw [← hterm i, Measure.real, ENNReal.ofReal_toReal (hfinite i)]
    simp_rw [hterm', tsum_fintype]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), ← Finset.mul_sum]
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ ht).mpr
    rw [mul_assoc, mul_comm (∑ i, volume.real (B i)) t, Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (Finset.sum_le_sum fun i _ => hlower i).trans hB_mass

end SupportingAnalysis
