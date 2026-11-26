module

public import Thesis.Upstream.AmbientWeakDivergenceCoordinate
public import Thesis.Upstream.AmbientWeakPartialLpBounds

/-! Recovery of the second normal derivative in the actual elliptic equation. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff ENNReal

namespace Thesis

theorem lpNorm_finsetSum_le_card_mul {ι X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} (s : Finset ι) {f : ι → X → E}
    (hf : ∀ j ∈ s, MemLp (f j) 2 μ) {B : ℝ} (hB : ∀ j ∈ s, lpNorm (f j) 2 μ ≤ B) :
    MemLp (fun x => ∑ j ∈ s, f j x) 2 μ ∧
      lpNorm (fun x => ∑ j ∈ s, f j x) 2 μ ≤ (s.card : ℝ)*B := by
  have he : (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, f j := funext fun x => (Finset.sum_apply x s f).symm
  refine ⟨memLp_finsetSum s hf,?_⟩
  rw [he]
  exact (lpNorm_sum_le hf (by norm_num)).trans ((Finset.sum_le_sum hB).trans_eq (by
    rw [Finset.sum_const,nsmul_eq_mul]))

theorem contDiff_norm_bound_memLp_top {n : ℕ} {U : Set (Domain n)}
    (hU : MeasurableSet U) {a : Domain n → ℝ} (ha : Continuous a)
    {M : ℝ} (hM : ∀ x ∈ U, |a x| ≤ M) : MemLp a ∞ (volume.restrict U) :=
  memLp_top_of_bound ha.aestronglyMeasurable M
    ((ae_restrict_mem (μ := volume) hU).mono fun x hx => by simpa only [Real.norm_eq_abs] using hM x hx)

/-- Tangential difference bounds and the weak divergence equation give
the full second weak graph. The quantitative bound uses the fixed coefficient
and its inverse in the normal direction. -/
theorem exists_second_weakColumns_of_tangential_and_divergence {n q : ℕ} (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)] (p : Fin n)
    (A : Domain n → Fin n → Fin n → ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hNon : ∀ x ∈ U.val, A x p p ≠ 0)
    (hInv : ContDiff ℝ ∞ (fun x => (A x p p)⁻¹))
    (M : ℝ) (hM : 0 ≤ M)
    (hC : ∀ i j, ∀ x ∈ U.val, |A x i j| ≤ M)
    (hDC : ∀ i j k, ∀ x ∈ U.val, |coordinateDerivative (fun y => A y i j) (hA i j) k x| ≤ M)
    (hCInv : ∀ x ∈ U.val, |(A x p p)⁻¹| ≤ M)
    (hDCInv : ∀ x ∈ U.val, |coordinateDerivative (fun y => (A y p p)⁻¹) hInv p x| ≤ M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {u f : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q},
      MemW12 U u D → MemLp f 2 (volume.restrict U.val) →
      HasWeakPackedDivergenceEq U.val
        (fun x => packAmbientGradient (fun i => ∑ j : Fin n, A x i j • D x j)) f →
      ∀ (E : ℝ), 0 ≤ E →
      (∀ j : Fin n, lpNorm (fun x => D x j) 2 (volume.restrict U.val) ≤ E) →
      lpNorm f 2 (volume.restrict U.val) ≤ E →
      ∀ T : {i : Fin n // i ≠ p} → Domain n → HarmonicMaps.Gradient n q,
      (∀ i j, MemLp (fun x => T i x j) 2 (volume.restrict U.val) ∧
        lpNorm (fun x => T i x j) 2 (volume.restrict U.val) ≤ E ∧
        IsWeakAmbientCoordinatePartial U.val i.val (fun x => D x j) (fun x => T i x j)) →
      ∃ H : Domain n → Fin n → HarmonicMaps.Gradient n q,
        ∀ j, MemW12 U (fun x => D x j) (fun x => H x j) ∧
          ∀ i, lpNorm (fun x => H x j i) 2 (volume.restrict U.val) ≤ C*E := by
  classical
  let μ := (volume : Measure (Domain n)).restrict U.val
  let C := 1+M*(1+2*(n : ℝ)^2*M+4*(n : ℝ)*M)
  have hC1 : 1 ≤ C := le_add_of_nonneg_right (by positivity)
  refine ⟨C,hC1,?_⟩
  intro u f D hu hf hEq E hE hDValues hfE T hT
  let J := (Finset.univ : Finset (Fin n)).erase p
  have hCardJ : (J.card : ℝ) ≤ (n : ℝ) := by
    have he : J.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ J
    exact_mod_cast he
  have hNot (j : Fin n) (hj : j ∈ J) : j ≠ p := (Finset.mem_erase.mp hj).1
  let S (j i : Fin n) (x : Domain n) : Ambient q :=
    if h : i ≠ p then T ⟨i,h⟩ x j else if h : j ≠ p then T ⟨j,h⟩ x i else 0
  have hS (j i : Fin n) (h : j ≠ p ∨ i ≠ p) :
      MemLp (S j i) 2 μ ∧ lpNorm (S j i) 2 μ ≤ E ∧
        IsWeakAmbientCoordinatePartial U.val i (fun x => D x j) (S j i) := by
    by_cases hi : i ≠ p
    · simpa only [S,dif_pos hi] using hT ⟨i,hi⟩ j
    · have hj : j ≠ p := h.resolve_right hi
      have he := hT ⟨j,hj⟩ i
      refine ⟨by simpa only [S,dif_neg hi,dif_pos hj] using he.1,
        by simpa only [S,dif_neg hi,dif_pos hj] using he.2.1,?_⟩
      simpa only [S,dif_neg hi,dif_pos hj] using
        IsWeakAmbientCoordinatePartial.mixed hu.1 he.2.2
  have hATop (i j : Fin n) : MemLp (fun x => A x i j) ∞ μ :=
    contDiff_norm_bound_memLp_top U.property.measurableSet (hA i j).continuous (hC i j)
  have hDATop (i j k : Fin n) : MemLp (coordinateDerivative (fun x => A x i j) (hA i j) k) ∞ μ :=
    contDiff_norm_bound_memLp_top U.property.measurableSet
      (((hA i j).continuous_fderiv (by simp)).clm_apply continuous_const) (hDC i j k)
  let B (i j : Fin n) (x : Domain n) := A x i j • D x j
  let Q (i j k : Fin n) (x : Domain n) :=
    coordinateDerivative (fun x => A x i j) (hA i j) k x • D x j + A x i j • S j k x
  have hB (i j : Fin n) : MemLp (B i j) 2 μ ∧ lpNorm (B i j) 2 μ ≤ M*E :=
    ⟨(hu.2.2 j).smul (r := (2 : ℝ≥0∞)) (hATop i j),
      (lpNorm_smul_restrict_le U.property.measurableSet (hu.2.2 j) hM (hC i j)).trans
        (mul_le_mul_of_nonneg_left (hDValues j) hM)⟩
  have hQ (i j k : Fin n) (h : j ≠ p ∨ k ≠ p) :
      MemLp (Q i j k) 2 μ ∧ lpNorm (Q i j k) 2 μ ≤ 2*M*E ∧
        IsWeakAmbientCoordinatePartial U.val k (B i j) (Q i j k) := by
    obtain ⟨hs,hsN,hsW⟩ := hS j k h
    obtain ⟨hq,hqN⟩ := lpNorm_smoothCoefficient_derivative_le U.property.measurableSet
      (hu.2.2 j) hs (hA i j) M hM (hC i j) (hDC i j k)
    refine ⟨hq,hqN.trans ?_,hsW.smul_smooth (hu.2.2 j) hs (hA i j) (hATop i j) (hDATop i j k)⟩
    refine (mul_le_mul_of_nonneg_left (add_le_add (hDValues j) hsN) hM).trans_eq ?_
    ring
  let P (x : Domain n) (i : Fin n) := ∑ j : Fin n, B i j x
  let W (i : Fin n) (x : Domain n) := ∑ j : Fin n, Q i j i x
  have hP (i : Fin n) : MemLp (fun x => P x i) 2 μ ∧ lpNorm (fun x => P x i) 2 μ ≤ (n : ℝ)*(M*E) := by
    simpa only [P,Finset.card_univ,Fintype.card_fin] using
      lpNorm_finsetSum_le_card_mul Finset.univ (fun j _ => (hB i j).1) (fun j _ => (hB i j).2)
  have hW (i : Fin n) (hi : i ≠ p) :
      MemLp (W i) 2 μ ∧ lpNorm (W i) 2 μ ≤ (n : ℝ)*(2*M*E) ∧
        IsWeakAmbientCoordinatePartial U.val i (fun x => P x i) (W i) := by
    have hq (j : Fin n) := hQ i j i (Or.inr hi)
    have hh := lpNorm_finsetSum_le_card_mul Finset.univ (fun j _ => (hq j).1) (fun j _ => (hq j).2.1)
    refine ⟨hh.1,by simpa only [Finset.card_univ,Fintype.card_fin] using hh.2,?_⟩
    exact IsWeakAmbientCoordinatePartial.finset_sum Finset.univ (fun j _ => (hq j).2.2)
      (fun j _ => (hB i j).1) (fun j _ => (hq j).1)
  let g (x : Domain n) := f x - ∑ j ∈ J, W j x
  have hgW : IsWeakAmbientCoordinatePartial U.val p (fun x => P x p) g :=
    HasWeakPackedDivergenceEq.remaining_coordinate_partial hEq (fun i => (hP i).1) hf p
      (fun j hj => (hW j hj).2.2) (fun j hj => (hW j hj).1)
  have hgS := lpNorm_finsetSum_le_card_mul J
    (fun j hj => (hW j (hNot j hj)).1) (fun j hj => (hW j (hNot j hj)).2.1)
  have hg : MemLp g 2 μ := hf.sub hgS.1
  have hgN : lpNorm g 2 μ ≤ (1+2*(n : ℝ)^2*M)*E := by
    refine (lpNorm_sub_le hf (by norm_num)).trans ?_
    refine (add_le_add hfE (hgS.2.trans (mul_le_mul_of_nonneg_right hCardJ (by positivity)))).trans_eq ?_
    ring
  let Z (x : Domain n) := P x p - ∑ j ∈ J, B p j x
  let dZ (x : Domain n) := g x - ∑ j ∈ J, Q p j p x
  have hZSum := lpNorm_finsetSum_le_card_mul J
    (fun j _ => (hB p j).1) (fun j _ => (hB p j).2)
  have hDZSum := lpNorm_finsetSum_le_card_mul J
    (fun j hj => (hQ p j p (Or.inl (hNot j hj))).1)
    (fun j hj => (hQ p j p (Or.inl (hNot j hj))).2.1)
  have hZ : MemLp Z 2 μ := (hP p).1.sub hZSum.1
  have hDZ : MemLp dZ 2 μ := hg.sub hDZSum.1
  have hZNorm : lpNorm Z 2 μ ≤ (2*(n : ℝ)*M)*E := by
    refine (lpNorm_sub_le (hP p).1 (by norm_num)).trans ?_
    refine (add_le_add (hP p).2 (hZSum.2.trans (mul_le_mul_of_nonneg_right hCardJ (by positivity)))).trans_eq ?_
    ring
  have hDZNorm : lpNorm dZ 2 μ ≤ (1+2*(n : ℝ)^2*M+2*(n : ℝ)*M)*E := by
    refine (lpNorm_sub_le hg (by norm_num)).trans ?_
    refine (add_le_add hgN (hDZSum.2.trans (mul_le_mul_of_nonneg_right hCardJ (by positivity)))).trans_eq ?_
    ring
  have hZW : IsWeakAmbientCoordinatePartial U.val p Z dZ := by
    apply hgW.sub _ (hP p).1 hZSum.1 hg hDZSum.1
    apply IsWeakAmbientCoordinatePartial.finset_sum J
    · exact fun j hj => (hQ p j p (Or.inl (hNot j hj))).2.2
    · exact fun j _ => (hB p j).1
    · exact fun j hj => (hQ p j p (Or.inl (hNot j hj))).1
  let I (x : Domain n) := (A x p p)⁻¹
  let Epp (x : Domain n) := coordinateDerivative I hInv p x • Z x + I x • dZ x
  have hInvTop : MemLp I ∞ μ :=
    contDiff_norm_bound_memLp_top U.property.measurableSet hInv.continuous hCInv
  have hInvDTop : MemLp (coordinateDerivative I hInv p) ∞ μ :=
    contDiff_norm_bound_memLp_top U.property.measurableSet
      ((hInv.continuous_fderiv (by simp)).clm_apply continuous_const) hDCInv
  have hZE (x : Domain n) : Z x = A x p p • D x p := by
    have he := Finset.add_sum_erase (Finset.univ : Finset (Fin n)) (fun j => B p j x) (Finset.mem_univ p)
    change (∑ j : Fin n, B p j x) - ∑ j ∈ J, B p j x = B p p x
    rw [← he,add_sub_cancel_right]
  have hZI : (fun x => I x • Z x) =ᵐ[μ] fun x => D x p := by
    filter_upwards [ae_restrict_mem (μ := volume) U.property.measurableSet] with x hx
    change (A x p p)⁻¹ • Z x = _
    rw [hZE,smul_smul,inv_mul_cancel₀ (hNon x hx),one_smul]
  have hPP : IsWeakAmbientCoordinatePartial U.val p (fun x => D x p) Epp :=
    (hZW.smul_smooth hZ hDZ hInv hInvTop hInvDTop).congr_ae hZI EventuallyEq.rfl
  obtain ⟨hEpp,hEppN⟩ := lpNorm_smoothCoefficient_derivative_le U.property.measurableSet
    hZ hDZ hInv M hM hCInv hDCInv
  have hEppC : lpNorm Epp 2 μ ≤ C*E := by
    calc
      _ ≤ M*(lpNorm Z 2 μ + lpNorm dZ 2 μ) := hEppN
      _ ≤ M*((2*(n : ℝ)*M)*E + (1+2*(n : ℝ)^2*M+2*(n : ℝ)*M)*E) :=
        mul_le_mul_of_nonneg_left (add_le_add hZNorm hDZNorm) hM
      _ = (C-1)*E := by dsimp only [C]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_self _ zero_le_one) hE
  let H (x : Domain n) (j i : Fin n) := if j = p ∧ i = p then Epp x else S j i x
  have hH (j i : Fin n) :
      MemLp (fun x => H x j i) 2 μ ∧ lpNorm (fun x => H x j i) 2 μ ≤ C*E ∧
        IsWeakAmbientCoordinatePartial U.val i (fun x => D x j) (fun x => H x j i) := by
    by_cases h : j = p ∧ i = p
    · obtain ⟨rfl,rfl⟩ := h
      simpa only [H,and_self,if_true] using ⟨hEpp,hEppC,hPP⟩
    · obtain ⟨hLp,hN,hW⟩ := hS j i (not_and_or.mp h)
      have hCE : E ≤ C*E := le_mul_of_one_le_left hE hC1
      simpa only [H,h,if_false] using ⟨hLp,hN.trans hCE,hW⟩
  refine ⟨H,fun j => ⟨?_,fun i => (hH j i).2.1⟩⟩
  exact ⟨⟨IntegrableOn.locallyIntegrableOn ((hu.2.2 j).integrable (by norm_num)),
      fun i => IntegrableOn.locallyIntegrableOn ((hH j i).1.integrable (by norm_num)),
      fun i => (hH j i).2.2⟩,
    hu.2.2 j,fun i => (hH j i).1⟩

end Thesis
