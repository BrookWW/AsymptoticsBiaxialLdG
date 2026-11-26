module

public import StratificationTheory.Foundation.SobolevLocalAssembly
import HarmonicMaps.Analysis.SobolevAECongruence

/-! Exact Sobolev gluing on genuine open overlaps. -/

public section

open Filter HarmonicMaps MeasureTheory Set

namespace Thesis

private theorem ambient_memLp_two_union {n : ℕ} {E : Type*} [NormedAddCommGroup E] {u : Domain n → E}
    {A B : Set (Domain n)} (hA : MemLp u 2 (volume.restrict A)) (hB : MemLp u 2 (volume.restrict B)) :
    MemLp u 2 (volume.restrict (A ∪ B)) := by
  have hA' : IntegrableOn (fun x => ‖u x‖ ^ 2) A := hA.integrable_norm_pow (by norm_num)
  have hB' : IntegrableOn (fun x => ‖u x‖ ^ 2) B := hB.integrable_norm_pow (by norm_num)
  exact (memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_union_iff.2 ⟨hA.aestronglyMeasurable, hB.aestronglyMeasurable⟩)).2 (hA'.union hB')

/-- Two original weak graphs that agree on their open overlap give
the literal piecewise weak graph on every open subdomain they cover. -/
theorem memW12_openOverlap_piecewise {n q : ℕ} {Ω U V : OpenDomain n}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → HarmonicMaps.Gradient n q}
    [DecidablePred (· ∈ U.val)]
    (hU : MemW12 U u Du) (hV : MemW12 V v Dv) (hΩ : Ω.val ⊆ U.val ∪ V.val)
    (hAgree : EqOn u v (U.val ∩ V.val)) :
    let w (x : Domain n) := if x ∈ U.val then u x else v x
    let Dw (x : Domain n) := if x ∈ U.val then Du x else Dv x
    MemW12 Ω w Dw := by
  intro w Dw
  let A : OpenDomain n := ⟨U.val ∩ V.val, U.property.inter V.property⟩
  have hu : HasWeakGradient A u Du := hU.1.mono inter_subset_left
  have hv : HasWeakGradient A v Dv := hV.1.mono inter_subset_right
  have hD : Du =ᵐ[volume.restrict A.val] Dv :=
    hu.ae_eq_of_ae_eq_map hv ((ae_restrict_mem A.property.measurableSet).mono fun _ hx => hAgree hx)
  have hD' : ∀ᵐ x ∂volume.restrict V.val, x ∈ U.val → Du x = Dv x := by
    apply (ae_restrict_iff' U.property.measurableSet).1
    rwa [Measure.restrict_restrict U.property.measurableSet]
  have hGraphU : MemW12 U w Dw := hU.congr_ae
    ((ae_restrict_mem U.property.measurableSet).mono fun _ hx => (if_pos hx).symm)
    ((ae_restrict_mem U.property.measurableSet).mono fun _ hx => (if_pos hx).symm)
  have hwV : v =ᵐ[volume.restrict V.val] w := by
    filter_upwards [ae_restrict_mem V.property.measurableSet] with x hx
    by_cases hi : x ∈ U.val
    · exact (hAgree ⟨hi, hx⟩).symm.trans (if_pos hi).symm
    · exact (if_neg hi).symm
  have hDwV : Dv =ᵐ[volume.restrict V.val] Dw := by
    filter_upwards [hD'] with x hx
    by_cases hi : x ∈ U.val
    · exact (hx hi).symm.trans (if_pos hi).symm
    · exact (if_neg hi).symm
  have hGraphV : MemW12 V w Dw := hV.congr_ae hwV hDwV
  have hWLp := (ambient_memLp_two_union hGraphU.2.1 hGraphV.2.1).mono_measure
    (Measure.restrict_mono_set _ hΩ)
  have hDLp (i : Fin n) := (ambient_memLp_two_union (hGraphU.2.2 i) (hGraphV.2.2 i)).mono_measure
    (Measure.restrict_mono_set _ hΩ)
  let P : Bool → OpenDomain n := fun t => if t then U else V
  refine StratificationTheory.memW12_of_open_cover_sobolev_pair hWLp hDLp P ?_ ?_
  · intro x hx
    exact (hΩ hx).elim (fun h => ⟨true, h⟩) (fun h => ⟨false, h⟩)
  · intro t
    cases t
    · exact hGraphV
    · exact hGraphU

end Thesis
