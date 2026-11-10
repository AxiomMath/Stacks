module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdic
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Descending properties along a taut map with faithfully flat quotients

If `φ : A →+* B` is taut and the induced maps of discrete quotients are faithfully flat, then
the topological properties of `B` descend to `A`: a countably generated topology, weak
pre-admissibility, pre-admissibility, and weak pre-adicness.  The file ends with the extraction
of a finitely generated ideal of definition from tautness.

## References

* [Stacks Project, Tag 0GXL](https://stacks.math.columbia.edu/tag/0GXL)
* [Stacks Project, Tag 0GXM](https://stacks.math.columbia.edu/tag/0GXM)
* [Stacks Project, Tag 0GXN](https://stacks.math.columbia.edu/tag/0GXN)
* [Stacks Project, Tag 0GXP](https://stacks.math.columbia.edu/tag/0GXP)
* [Stacks Project, Tag 0GXQ](https://stacks.math.columbia.edu/tag/0GXQ)
-/

@[expose] public section

namespace TopologicalRing

section

open Filter


private theorem exists_countable_basis_open_ideals_of_isCountablyGenerated
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] (h : (nhds (0 : R)).IsCountablyGenerated) :
    ∃ I : ℕ → Ideal R, (∀ n, IsOpen (I n : Set R)) ∧
      (nhds (0 : R)).HasBasis (fun _ : ℕ => True) fun n => (I n : Set R) := by
  obtain ⟨U, hU⟩ := Filter.isCountablyGenerated_iff_exists_antitone_basis.mp h
  choose I hI using fun n =>
    (IsLinearTopology.hasBasis_open_ideal (R := R)).mem_iff.mp (hU.mem n)
  refine ⟨I, fun n => (hI n).1, ?_⟩
  refine Filter.hasBasis_iff.mpr (fun t => ⟨?_, ?_⟩)
  · rintro ht
    obtain ⟨n, hn⟩ := hU.mem_iff.mp ht
    exact ⟨n, trivial, (hI n).2.trans hn⟩
  · rintro ⟨n, -, hn⟩
    exact (IsLinearTopology.hasBasis_open_ideal (R := R)).mem_iff.mpr
      ⟨I n, (hI n).1, hn⟩

/-- If `I` is open and the induced map on quotients by `I` and the closure of `I.map φ` is
faithfully flat, then `φ a ∈ closure (I.map φ)` implies `a ∈ I`. -/
private theorem mem_of_map_mem_closure_map_of_faithfullyFlat
    {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    {φ : A →+* B} {I : Ideal A}
    (hff : (Ideal.quotientMap (Ideal.closure (I.map φ)) φ
      (Ideal.map_le_iff_le_comap.mp (fun _ hx ↦ subset_closure hx))).FaithfullyFlat)
    {a : A} (ha : φ a ∈ Ideal.closure (I.map φ)) : a ∈ I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hff.injective
  simpa only [Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem] using ha

universe u v

/-- A countable fundamental system of open ideals descends along a continuous taut map
whose induced maps on quotients by open ideals are faithfully flat. -/
@[stacks 0GXL]
public theorem isCountablyGenerated_nhds_zero_of_isTaut_of_faithfullyFlat_quotient
    {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] (φ : A →+* B)
    (hφ_taut : RingHom.IsTaut φ)
    (hφ_quotient : ∀ (I : Ideal A), IsOpen (I : Set A) →
      (Ideal.quotientMap (Ideal.closure (I.map φ)) φ
        (Ideal.map_le_iff_le_comap.mp (fun _ hx ↦ subset_closure hx))).FaithfullyFlat)
    (hB : (nhds (0 : B)).IsCountablyGenerated) :
    (nhds (0 : A)).IsCountablyGenerated := by
  obtain ⟨J, hJopen, hJbasis⟩ := exists_countable_basis_open_ideals_of_isCountablyGenerated hB
  choose I hI using fun n => hφ_taut.2.mem_iff.mp
    (hJbasis.mem_iff.mpr ⟨n, trivial, subset_rfl⟩)
  have hA_basis : (nhds (0 : A)).HasBasis (fun _ : ℕ => True)
      (fun n => (I n : Set A)) := by
    refine Filter.hasBasis_iff.mpr (fun U => ⟨?_, ?_⟩)
    · intro hU
      obtain ⟨K, hKopen, hKU⟩ := (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp hU
      let L : Ideal B := Ideal.closure (K.map φ)
      obtain ⟨n, -, hn⟩ := hJbasis.mem_iff.mp ((hφ_taut.1 K hKopen).mem_nhds L.zero_mem)
      refine ⟨n, trivial, ?_⟩
      intro a ha
      exact hKU (mem_of_map_mem_closure_map_of_faithfullyFlat (hφ_quotient K hKopen)
        (show φ a ∈ L from hn ((hI n).2 (subset_closure (Ideal.mem_map_of_mem φ ha)))))
    · rintro ⟨n, -, hsub⟩
      exact (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mpr
        ⟨I n, (hI n).1, hsub⟩
  exact hA_basis.isCountablyGenerated

end

section

open Filter

universe u v

/-- Weak pre-admissibility descends along a taut map when the induced
maps on quotients by open ideals and their closed extensions are faithfully flat. -/
@[stacks 0GXM]
public theorem isWeaklyPreAdmissible_of_isTaut_of_faithfullyFlat_quotient
    {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : A →+* B)
    (hφ_taut : RingHom.IsTaut φ)
    (hφ_quotient : ∀ I : Ideal A, IsOpen (I : Set A) →
      (Ideal.quotientMap (I := I) (Ideal.closure (I.map φ)) φ (by
        exact Ideal.map_le_iff_le_comap.mp
          (show I.map φ ≤ Ideal.closure (I.map φ) from
            fun _ hx ↦ subset_closure hx))).FaithfullyFlat)
    (hB : TopologicalRing.IsWeaklyPreAdmissible B) :
    TopologicalRing.IsWeaklyPreAdmissible A := by
  rcases hB with ⟨J, hJopen, hJnil⟩
  obtain ⟨I, hIopen, hIle⟩ := hφ_taut.2.mem_iff.mp (hJopen.mem_nhds J.zero_mem)
  refine ⟨I, hIopen, ?_⟩
  intro x hx
  simp only [IsTopologicallyNilpotent,
    atTop_basis.tendsto_iff IsLinearTopology.hasBasis_open_ideal, true_and]
  intro K hK
  let K' : Ideal B := Ideal.closure (K.map φ)
  obtain ⟨n, hn⟩ := (hJnil (φ x) (hIle (subset_closure
    (Ideal.mem_map_of_mem φ hx)))).exists_pow_mem_of_mem_nhds
      ((hφ_taut.1 K hK).mem_nhds K'.zero_mem)
  exact ⟨n, fun m hm ↦ K.pow_mem_of_pow_mem
    (mem_of_map_mem_closure_map_of_faithfullyFlat (hφ_quotient K hK)
      (by rw [map_pow]; exact hn)) hm⟩

end

section

universe u v

/-- Pre-admissibility descends along a continuous taut homomorphism when all of the induced maps
on quotients by open ideals and their closed extensions are faithfully flat. -/
@[stacks 0GXN]
public theorem isPreAdmissible_of_isTaut_of_faithfullyFlat_quotient
    {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] (φ : A →+* B) (hφ_taut : RingHom.IsTaut φ)
    (hφ_quotient : ∀ (I : Ideal A), IsOpen (I : Set A) →
      (Ideal.quotientMap (Ideal.closure (I.map φ)) φ
        (Ideal.map_le_iff_le_comap.mp (fun _ hx ↦ subset_closure hx))).FaithfullyFlat)
    (hB : TopologicalRing.IsPreAdmissible B) :
    TopologicalRing.IsPreAdmissible A := by
  obtain ⟨J, hJopen, hJpowers⟩ := hB
  obtain ⟨I, hIopen, hIle⟩ := hφ_taut.2.mem_iff.mp (hJopen.mem_nhds (J.zero_mem))
  refine ⟨I, hIopen, fun U hU ↦ ?_⟩
  obtain ⟨I', hI'open, hI'U⟩ := (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp hU
  obtain ⟨n, hn⟩ := hJpowers _ ((hφ_taut.1 I' hI'open).mem_nhds (Ideal.closure (I'.map φ)).zero_mem)
  refine ⟨n, fun x hx ↦ hI'U ?_⟩
  exact mem_of_map_mem_closure_map_of_faithfullyFlat (hφ_quotient I' hI'open)
    (show φ x ∈ Ideal.closure (I'.map φ) from hn ((pow_le_pow_left₀ bot_le
      ((show I.map φ ≤ Ideal.closure (I.map φ) from fun _ hy ↦ subset_closure hy).trans hIle) n)
      (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem φ hx)))

end

section

universe u v


open Filter
open scoped Topology


/-- An element lying in `J ⊔ L` for every open ideal `L` lies in the closure of `J`. -/
private theorem mem_closure_of_forall_mem_sup {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] {J : Ideal R} {x : R}
    (h : ∀ L : Ideal R, IsOpen (L : Set R) → x ∈ J ⊔ L) : x ∈ closure (J : Set R) := by
  refine mem_closure_iff_nhds.mpr fun t ht ↦ ?_
  obtain ⟨L, hL, hLt⟩ := (IsLinearTopology.hasBasis_open_ideal.nhds_of_zero' x).mem_iff.mp ht
  obtain ⟨j, hj, l, hl, hsum⟩ := Submodule.mem_sup.mp (h L hL)
  refine ⟨j, hLt ⟨-l, L.neg_mem hl, ?_⟩, hj⟩
  simpa only [vadd_eq_add, sub_eq_add_neg] using (show x + -l = j by rw [← hsum]; abel)

private theorem open_closure_pow_of_open {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [TopologicalRing.IsWeaklyPreAdic R] (J : Ideal R) (hJ : IsOpen (J : Set R))
    (n : ℕ) : IsOpen ((J ^ n).closure : Set R) := by
  obtain ⟨K, hKopen, hKbasis⟩ := TopologicalRing.IsWeaklyPreAdic.exists_ideal (A := R)
  have hJn : (J : Set R) ∈ 𝓝 (0 : R) := hJ.mem_nhds J.zero_mem
  obtain ⟨m, _, hm⟩ := hKbasis.mem_iff.mp hJn
  have hm' : K ^ m ≤ J := by
    intro x hx; exact hm (by simpa only [Submodule.topologicalClosure_coe] using
      (show x ∈ closure ((K ^ m : Ideal R) : Set R) from subset_closure hx))
  have hpow : K ^ (m * n) ≤ J ^ n := by
    rw [pow_mul]; exact pow_le_pow_left' hm' n
  exact Ideal.isOpen_of_isOpen_subideal (Submodule.topologicalClosure_mono hpow)
    (hKopen (m * n))

private theorem closure_comap_map {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : A →+* B) (hφ : Continuous φ) (hφ_taut : RingHom.IsTaut φ)
    (hquot : ∀ L : Ideal A, IsOpen (L : Set A) →
      (Ideal.quotientMap (I := L) (Ideal.closure (L.map φ)) φ
        (Ideal.map_le_iff_le_comap.mp
          (show L.map φ ≤ Ideal.closure (L.map φ) from
            fun _ hx ↦ subset_closure hx))).FaithfullyFlat)
    (J : Ideal A) :
    J.closure = (Ideal.closure (J.map φ)).comap φ := by
  apply le_antisymm
  · intro x hx
    change φ x ∈ closure (J.map φ : Set B)
    exact map_mem_closure hφ hx (fun _ hy ↦ Ideal.mem_map_of_mem φ hy)
  · intro x hx
    change φ x ∈ closure (J.map φ : Set B) at hx
    have hsup (L : Ideal A) (hL : IsOpen (L : Set A)) : x ∈ J ⊔ L := by
      let M : Ideal B := Ideal.closure (L.map φ)
      let qA : A →+* A ⧸ L := Ideal.Quotient.mk L
      let qB : B →+* B ⧸ M := Ideal.Quotient.mk M
      let ψ : A ⧸ L →+* B ⧸ M := Ideal.quotientMap M φ
        (Ideal.map_le_iff_le_comap.mp
          (show L.map φ ≤ Ideal.closure (L.map φ) from
            fun _ hy ↦ subset_closure hy))
      have hM : IsOpen (M : Set B) := hφ_taut.1 L hL
      have hxy : φ x ∈ J.map φ ⊔ M :=
        closure_minimal (show (J.map φ : Set B) ⊆ (J.map φ ⊔ M : Ideal B) from
          show J.map φ ≤ J.map φ ⊔ M from le_sup_left)
          ((J.map φ ⊔ M).toAddSubgroup.isClosed_of_isOpen
            (Ideal.isOpen_of_isOpen_subideal le_sup_right hM)) hx
      have hmq : qB (φ x) ∈ (J.map φ).map qB := by
        have hm := Ideal.mem_map_of_mem qB hxy
        change qB (φ x) ∈ (J.map φ ⊔ M).map qB at hm
        rw [Ideal.map_sup, show M.map qB = ⊥ from Ideal.map_quotient_self M,
          sup_bot_eq] at hm
        exact hm
      have hmap : (J.map qA).map ψ = (J.map φ).map qB := by
        rw [Ideal.map_map, Ideal.map_map, Ideal.quotientMap_comp_mk]
      have hq : qA x ∈ J.map qA := by
        rw [← faithfullyFlat_comap_map_eq ψ (hquot L hL) (J.map qA)]
        change ψ (qA x) ∈ (J.map qA).map ψ
        rw [hmap, Ideal.quotientMap_mk]; exact hmq
      exact Ideal.mem_quotient_iff_mem_sup.mp hq
    exact mem_closure_of_forall_mem_sup hsup

/-- Weak pre-adicness descends along a continuous taut homomorphism when all maps on the
corresponding quotients by open ideals are faithfully flat. -/
@[stacks 0GXP]
public theorem isWeaklyPreAdic_of_isTaut_of_faithfullyFlat_quotient
    {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] (φ : A →+* B) (hφ : Continuous φ) (hφ_taut : RingHom.IsTaut φ)
    (hquot : ∀ I : Ideal A, IsOpen (I : Set A) →
      (Ideal.quotientMap (I := I) (Ideal.closure (I.map φ)) φ (by
        exact Ideal.map_le_iff_le_comap.mp
          (show I.map φ ≤ Ideal.closure (I.map φ) from
            fun _ hx ↦ subset_closure hx))).FaithfullyFlat)
    (hB : TopologicalRing.IsWeaklyPreAdic B) : TopologicalRing.IsWeaklyPreAdic A := by
  let _ := hB
  obtain ⟨K, hKopen, hKbasis⟩ := TopologicalRing.IsWeaklyPreAdic.exists_ideal (A := B)
  obtain ⟨I, hI, hIK⟩ := hφ_taut.2.mem_iff.mp
    ((by simpa using hKopen 1 : IsOpen (K.closure : Set B)).mem_nhds
      K.closure.zero_mem)
  have hIB : IsOpen (Ideal.closure (I.map φ) : Set B) := hφ_taut.1 I hI
  have hIopen (n : ℕ) : IsOpen ((I ^ n).closure : Set A) := by
    have hBopen : IsOpen (Ideal.closure ((I ^ n).map φ) : Set B) := by
      exact Ideal.isOpen_of_isOpen_subideal
        ((Submodule.topologicalClosure_mono
          (by simpa only [Ideal.map_pow] using (closure_pow_le_closure_pow (I.map φ) n))).trans_eq
          (Ideal.closure_eq_of_isClosed _ isClosed_closure))
        (open_closure_pow_of_open (Ideal.closure (I.map φ)) hIB n)
    rw [closure_comap_map φ hφ hφ_taut hquot (I ^ n)]
    exact hBopen.preimage hφ
  refine ⟨⟨I, hIopen, ?_⟩⟩
  apply Filter.hasBasis_iff.mpr; intro U; constructor
  · intro hU
    obtain ⟨L, hL, hLU⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp hU
    have hLB : (Ideal.closure (L.map φ) : Set B) ∈ 𝓝 (0 : B) :=
      (hφ_taut.1 L hL).mem_nhds (Ideal.closure (L.map φ)).zero_mem
    obtain ⟨m, _, hm⟩ := hKbasis.mem_iff.mp hLB
    have hIK' : Ideal.closure (I.map φ) ≤ K.closure := hIK
    have hpowIK : (Ideal.closure (I.map φ)) ^ m ≤ (K ^ m).closure := by
      exact (pow_le_pow_left' hIK' m).trans (closure_pow_le_closure_pow K m)
    have hmapIL : Ideal.closure ((I ^ m).map φ) ≤ Ideal.closure (L.map φ) := by
      have h1 : Ideal.closure ((I ^ m).map φ) ≤
          ((Ideal.closure (I.map φ)) ^ m).closure := by
        apply Submodule.topologicalClosure_mono
        simpa only [Ideal.map_pow] using
          (pow_le_pow_left' (show I.map φ ≤ Ideal.closure (I.map φ) from
            fun _ hx ↦ subset_closure hx) m)
      exact ((h1.trans ((Submodule.topologicalClosure_mono hpowIK).trans_eq
        (Ideal.closure_eq_of_isClosed _ isClosed_closure)))).trans hm
    refine ⟨m, trivial, ?_⟩
    have hLclosed : L.closure = L :=
      Ideal.closure_eq_of_isClosed L (L.toAddSubgroup.isClosed_of_isOpen hL)
    have hIL : (I ^ m).closure ≤ L := by
      rw [closure_comap_map φ hφ hφ_taut hquot (I ^ m), ← hLclosed,
        closure_comap_map φ hφ hφ_taut hquot L]
      exact Ideal.comap_mono hmapIL
    exact fun _ hx ↦ hLU (hIL hx)
  · rintro ⟨n, _, hn⟩
    exact Filter.mem_of_superset ((hIopen n).mem_nhds (I ^ n).closure.zero_mem) hn

end

section

open Filter
open scoped Topology


universe u

private lemma exists_ideal_of_definition_of_weaklyPreAdic
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyPreAdic A) :
    ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧
      ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).topologicalClosure : Set A) := by
  have hchar :=
    (TopologicalRing.weaklyPreAdic_tfae.{u, u} A).out 1 3
  rcases hchar.mp hA with ⟨_, I, hI, hopen⟩
  exact ⟨I, hI, hopen⟩

private lemma pow_le_fg_add_closure_pow_of_faithfully_flat
    {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : A →+* B) (I I' : Ideal A) (n k : ℕ)
    (hquot : ∀ L : Ideal A, IsOpen (L : Set A) →
      (Ideal.quotientMap (Ideal.closure (L.map φ)) φ
        (Ideal.le_comap_of_map_le
          (show L.map φ ≤ Ideal.closure (L.map φ) from subset_closure))).FaithfullyFlat)
    (hKopen : IsOpen (((I ^ (n + k)).topologicalClosure : Ideal A) : Set A))
    (hJ : Ideal.map φ (I ^ n) ≤ Ideal.map φ I') :
    I ^ n ≤ I' + (I ^ (n + k)).topologicalClosure := by
  let K : Ideal A := (I ^ (n + k)).topologicalClosure
  let M : Ideal B := Ideal.closure (K.map φ)
  let qA : A →+* A ⧸ K := Ideal.Quotient.mk K
  let qB : B →+* B ⧸ M := Ideal.Quotient.mk M
  let ψ : A ⧸ K →+* B ⧸ M := Ideal.quotientMap M φ
    (Ideal.le_comap_of_map_le
      (show K.map φ ≤ M from fun _ hx ↦ subset_closure hx))
  have hff : ψ.FaithfullyFlat := hquot K hKopen
  have htarget : Ideal.map ψ (Ideal.map qA (I ^ n)) ≤
      Ideal.map ψ (Ideal.map qA I') := by
    calc
      Ideal.map ψ (Ideal.map qA (I ^ n)) = Ideal.map qB (Ideal.map φ (I ^ n)) := by
        rw [Ideal.map_map, Ideal.map_map, Ideal.quotientMap_comp_mk]
      _ ≤ Ideal.map qB (Ideal.map φ I') := Ideal.map_mono hJ
      _ = Ideal.map ψ (Ideal.map qA I') := by
        rw [Ideal.map_map, Ideal.map_map, Ideal.quotientMap_comp_mk]
  have hcontract₁ := faithfullyFlat_comap_map_eq ψ hff (Ideal.map qA (I ^ n))
  have hcontract₂ := faithfullyFlat_comap_map_eq ψ hff (Ideal.map qA I')
  have hmap : Ideal.map qA (I ^ n) ≤ Ideal.map qA I' := by
    calc
      Ideal.map qA (I ^ n) = Ideal.comap ψ (Ideal.map ψ (Ideal.map qA (I ^ n))) := hcontract₁.symm
      _ ≤ Ideal.comap ψ (Ideal.map ψ (Ideal.map qA I')) := Ideal.comap_mono htarget
      _ = Ideal.map qA I' := hcontract₂
  intro x hx
  have hqx : qA x ∈ Ideal.map qA I' := hmap (Ideal.mem_map_of_mem qA hx)
  have hx' : x ∈ I' ⊔ K := (Ideal.mem_quotient_iff_mem_sup).mp hqx
  simpa [Ideal.add_eq_sup, K] using hx'

private lemma exists_fg_subideal_whose_extension_contains
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (I : Ideal A) (J : Ideal B) (hJfg : J.FG) (hJ : J ≤ I.map φ) :
    ∃ I' : Ideal A, I'.FG ∧ I' ≤ I ∧ J ≤ I'.map φ := by
  classical
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp hJfg
  have hspan (x : {x : B // x ∈ s}) :
      ∃ t : Finset B, (t : Set B) ⊆ φ '' (I : Set A) ∧
        x.1 ∈ Submodule.span B (t : Set B) := by
    apply Submodule.mem_span_finite_of_mem_span
    change x.1 ∈ Ideal.map φ I
    apply hJ
    rw [← hs]
    exact Submodule.subset_span x.2
  let t : B → Finset B := fun x =>
    if hx : x ∈ s then Classical.choose (hspan ⟨x, hx⟩) else ∅
  have ht_subset (x : B) (hx : x ∈ s) : (t x : Set B) ⊆ φ '' (I : Set A) := by
    dsimp [t]
    rw [dite_eq_left hx]
    exact (Classical.choose_spec (hspan ⟨x, hx⟩)).1
  have ht_span (x : B) (hx : x ∈ s) :
      x ∈ Submodule.span B (t x : Set B) := by
    dsimp [t]
    rw [dite_eq_left hx]
    exact (Classical.choose_spec (hspan ⟨x, hx⟩)).2
  let U : Finset B := hsfin.toFinset.biUnion t
  have hpre (b : {b : B // b ∈ U}) : ∃ a : A, a ∈ I ∧ φ a = b.1 := by
    obtain ⟨x, hx, hb⟩ := Finset.mem_biUnion.mp b.2
    rcases (Set.mem_image φ (I : Set A) _).mp
        (ht_subset x (hsfin.mem_toFinset.mp hx) hb) with ⟨a, ha, hφa⟩
    exact ⟨a, ha, hφa⟩
  let f : {b : B // b ∈ U} → A := fun b => Classical.choose (hpre b)
  let I' : Ideal A := Ideal.span (Set.range f)
  have hfg : I'.FG := by
    dsimp [I']
    exact Submodule.fg_span (Set.finite_range f)
  have hI'le : I' ≤ I := by
    apply Ideal.span_le.2
    rintro a ⟨b, rfl⟩
    exact (Classical.choose_spec (hpre b)).1
  have ht_map (x : B) (hx : x ∈ s) : (t x : Set B) ⊆ Ideal.map φ I' := by
    intro b hb
    have hbU : b ∈ U := Finset.mem_biUnion.mpr ⟨x, hsfin.mem_toFinset.mpr hx, hb⟩
    let bc : {b : B // b ∈ U} := ⟨b, hbU⟩
    have hfI : f bc ∈ I' := Submodule.subset_span ⟨bc, rfl⟩
    have hmap := Ideal.mem_map_of_mem φ hfI
    rw [(Classical.choose_spec (hpre bc)).2] at hmap
    exact hmap
  have hJle : J ≤ Ideal.map φ I' := by
    rw [← hs]
    apply Submodule.span_le.2
    intro x hx
    exact (Submodule.span_le.2 (ht_map x hx)) (ht_span x hx)
  exact ⟨I', hfg, hI'le, hJle⟩

private lemma continuous_id_from_closure_cofinal {A : Type*} [CommRing A]
    [τ : TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (J : Ideal A)
    (hcofinal : ∀ U ∈ @nhds A τ 0, ∃ n : ℕ,
      ((J ^ n).topologicalClosure : Set A) ⊆ U) :
    @Continuous A A J.adicTopology τ (RingHom.id A) := by
  refine @continuous_of_tendsto_nhds_zero A J.adicTopology
    (inferInstance) (by let _ := J.adicTopology; infer_instance)
    A (A →+* A) (inferInstance) τ (inferInstance) (inferInstance) (inferInstance)
    (RingHom.id A) ?_
  intro U hU
  obtain ⟨n, hn⟩ := hcofinal U hU
  apply J.hasBasis_nhds_zero_adic.mem_iff.mpr
  refine ⟨n, trivial, ?_⟩
  exact Set.Subset.trans (Submodule.le_topologicalClosure _) hn

private lemma taut_id_from_closure_cofinal {A : Type*} [CommRing A]
    [τ : TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (J : Ideal A)
    (hopen : ∀ n : ℕ, 1 ≤ n →
      IsOpen ((J ^ n).topologicalClosure : Set A))
    (hcofinal : ∀ U ∈ @nhds A τ 0, ∃ n : ℕ,
      ((J ^ n).topologicalClosure : Set A) ⊆ U) :
    @RingHom.IsTaut A A (inferInstance) J.adicTopology (inferInstance) τ
      (inferInstance) (RingHom.id A) := by
  have hfirst : ∀ L : Ideal A, @IsOpen A J.adicTopology (L : Set A) →
      IsOpen (Ideal.closure (L.map (RingHom.id A)) : Set A) := by
    intro L hL
    obtain ⟨n, hn⟩ := source_open_contains_power J L hL
    have hle : (J ^ n).topologicalClosure ≤ Ideal.closure (L.map (RingHom.id A)) := by
      simpa only [Ideal.map_id, ideal_closure_eq_submodule_closure] using
        (Submodule.topologicalClosure_mono hn)
    apply Ideal.isOpen_of_isOpen_subideal hle
    cases n with
    | zero => simp
    | succ n => exact hopen (n + 1) (by omega)
  constructor
  · exact hfirst
  · refine ⟨fun U => ?_⟩
    constructor
    · intro hU
      obtain ⟨n, hn⟩ := hcofinal U hU
      refine ⟨J ^ n, source_power_open J n, ?_⟩
      simpa only [Ideal.map_id, ideal_closure_eq_submodule_closure] using hn
    · rintro ⟨L, hL, hLU⟩
      have hopenL : IsOpen (Ideal.closure (L.map (RingHom.id A)) : Set A) := hfirst L hL
      exact Filter.mem_of_superset
        (hopenL.mem_nhds (Ideal.closure (L.map (RingHom.id A))).zero_mem) hLU

/-- Adicness with a finitely generated ideal of definition descends along a continuous taut
homomorphism when all the induced maps modulo open ideals are faithfully flat. -/
@[stacks 0GXQ]
public theorem exists_fg_ideal_of_definition_of_taut
    {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)] [T2Space A]
    [@CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B)] [T2Space B]
    (φ : A →+* B) (_hφ : Continuous φ) (_htaut : RingHom.IsTaut φ)
    (_hquot : ∀ I : Ideal A, IsOpen (I : Set A) →
      (Ideal.quotientMap (Ideal.closure (I.map φ)) φ
        (Ideal.le_comap_of_map_le
          (show I.map φ ≤ Ideal.closure (I.map φ) from subset_closure))).FaithfullyFlat)
    (_hB : ∃ J : Ideal B, _root_.IsAdic J ∧ J.FG) :
    ∃ I : Ideal A, _root_.IsAdic I ∧ I.FG := by
  classical
  have hBpre : TopologicalRing.IsWeaklyPreAdic B := by
    obtain ⟨J, hJ, _⟩ := _hB
    refine ⟨J, ?_⟩
    have hclosure (n : ℕ) : (J ^ n).topologicalClosure = J ^ n := by
      apply le_antisymm
      · exact Submodule.topologicalClosure_minimal _ le_rfl
          ((J ^ n).toAddSubgroup.isClosed_of_isOpen ((isAdic_iff.mp hJ).1 n))
      · exact Submodule.le_topologicalClosure _
    constructor
    · intro n
      rw [hclosure n]
      exact (isAdic_iff.mp hJ).1 n
    · simpa only [hclosure] using (hJ ▸ J.hasBasis_nhds_zero_adic)
  have hApre : TopologicalRing.IsWeaklyPreAdic A :=
    TopologicalRing.isWeaklyPreAdic_of_isTaut_of_faithfullyFlat_quotient
      φ _hφ _htaut _hquot hBpre
  let : TopologicalRing.IsWeaklyAdic A := {
    toIsWeaklyPreAdic := hApre
    toT2Space := inferInstance
    completeSpace := inferInstance
  }
  obtain ⟨I, hIdef, hIclosure⟩ := exists_ideal_of_definition_of_weaklyPreAdic hApre
  obtain ⟨J₀, hJadic, hJfg⟩ := _hB
  have hIBopen : IsOpen (Ideal.closure (I.map φ) : Set B) := _htaut.1 I hIdef.1
  have hIBnhds : (Ideal.closure (I.map φ) : Set B) ∈ 𝓝 (0 : B) :=
    hIBopen.mem_nhds (Ideal.closure (I.map φ)).zero_mem
  obtain ⟨n, hn⟩ := (isAdic_iff.mp hJadic).2 (Ideal.closure (I.map φ) : Set B) hIBnhds
  let m := max n 1
  have hmpos : 0 < m := by dsimp [m]; omega
  have hmle : J₀ ^ m ≤ Ideal.closure (I.map φ) := by
    exact SetLike.coe_subset_coe.mp (Set.Subset.trans
      (show ((J₀ ^ m : Ideal B) : Set B) ⊆ (J₀ ^ n : Ideal B) from
        Ideal.pow_le_pow_right (Nat.le_max_left n 1)) hn)
  let J : Ideal B := J₀ ^ m
  have hJadic' : _root_.IsAdic J := is_ideal_adic_pow hJadic hmpos
  have hJfg' : J.FG := hJfg.pow
  have hJopen : IsOpen (J : Set B) := by simpa [J] using (isAdic_iff.mp hJadic').1 1
  have hJjac : J ≤ (⊥ : Ideal B).jacobson := by
    let : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
    let : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
    let : IsAdicComplete J B := hJadic'.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩
    exact IsAdicComplete.le_jacobson_bot J
  have hJ2open : IsOpen ((J ^ 2 : Ideal B) : Set B) := (isAdic_iff.mp hJadic').1 2
  have hJle : J ≤ I.map φ + J ^ 2 := by
    have hcl : Ideal.closure (I.map φ) ≤ I.map φ + J ^ 2 := by
      apply closure_minimal
      · intro x hx
        exact (show I.map φ ≤ I.map φ + J ^ 2 from le_sup_left) hx
      · exact (I.map φ + J ^ 2).toAddSubgroup.isClosed_of_isOpen
          (Ideal.isOpen_of_isOpen_subideal le_sup_right hJ2open)
    exact le_trans hmle hcl
  have hJrel : J ≤ I.map φ ⊔ (J : Submodule B B) • J := by
    simpa only [Ideal.add_eq_sup, Ideal.smul_eq_mul, pow_two] using hJle
  have hJIB : J ≤ I.map φ :=
    Submodule.le_of_le_smul_of_le_jacobson_bot hJfg' hJjac hJrel
  obtain ⟨I', hI'fg, hI'I, hJI'⟩ :=
    exists_fg_subideal_whose_extension_contains φ I J hJfg' hJIB
  have hpreopen : IsOpen ((J.comap φ : Ideal A) : Set A) :=
    _hφ.isOpen_preimage (J : Set B) hJopen
  obtain ⟨n₀, hn₀⟩ := hIdef.2 _ (hpreopen.mem_nhds (J.comap φ).zero_mem)
  let n := max n₀ 1
  have hnpos : 1 ≤ n := le_max_right _ _
  have hpowcomap : I ^ n ≤ J.comap φ := by
    exact (Ideal.pow_le_pow_right (le_max_left n₀ 1)).trans
      (SetLike.coe_subset_coe.mp hn₀)
  have hpowmap : Ideal.map φ (I ^ n) ≤ J :=
    (Ideal.map_le_iff_le_comap).2 hpowcomap
  have hpowmap' : Ideal.map φ (I ^ n) ≤ Ideal.map φ I' := hpowmap.trans hJI'
  have hcontain (k : ℕ) (hk : 1 ≤ k) :
      I ^ n ≤ I' + (I ^ (n + k)).topologicalClosure := by
    apply pow_le_fg_add_closure_pow_of_faithfully_flat φ I I' n k _
      (hIclosure (n + k) (by have hn := hnpos; omega)) hpowmap'
    exact _hquot
  have hpower_remainder (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
      I ^ (n * m) ≤ (I' ^ m) + (I ^ (n * m + k)).topologicalClosure := by
    let K : Ideal A := (I ^ (n * m + k)).topologicalClosure
    let q : A →+* A ⧸ K := Ideal.Quotient.mk K
    have hbase : I ^ n ≤ I' + K := by
      have hnm : n ≤ n * m := Nat.le_mul_of_pos_right n (by omega : 0 < m)
      have := hcontain (n * m + k - n) (by have hn := hnpos; have hm' := hm; have hk' := hk; omega)
      have hnm' : n ≤ n * m + k := le_trans hnm (Nat.le_add_right _ _)
      have hexp : n + (n * m + k - n) = n * m + k := Nat.add_sub_of_le hnm'
      simpa [K, hexp] using this
    have hmapBase : Ideal.map q (I ^ n) ≤ Ideal.map q I' := by
      have hmap := Ideal.map_mono (f := q) hbase
      rw [Ideal.add_eq_sup, Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq] at hmap
      exact hmap
    have hmapPow : Ideal.map q (I ^ (n * m)) ≤ Ideal.map q (I' ^ m) := by
      calc
        Ideal.map q (I ^ (n * m)) = (Ideal.map q (I ^ n)) ^ m := by
          rw [pow_mul, Ideal.map_pow]
        _ ≤ (Ideal.map q I') ^ m := pow_le_pow_left' hmapBase m
        _ = Ideal.map q (I' ^ m) := (Ideal.map_pow q I' m).symm
    intro x hx
    have hqx : q x ∈ Ideal.map q (I' ^ m) := hmapPow (Ideal.mem_map_of_mem q hx)
    have hx' : x ∈ I' ^ m ⊔ K := (Ideal.mem_quotient_iff_mem_sup).mp hqx
    simpa [Ideal.add_eq_sup, K] using hx'
  have hclosure_power (m : ℕ) (hm : 1 ≤ m) :
      I ^ (n * m) ≤ (I' ^ m).topologicalClosure := by
    intro x hx
    refine mem_closure_of_forall_mem_sup fun L hLopen ↦ ?_
    obtain ⟨r, hr⟩ := hIdef.2 (L : Set A) (hLopen.mem_nhds L.zero_mem)
    let k := max 1 r
    have hk : 1 ≤ k := le_max_left _ _
    have hkexp : r ≤ n * m + k := by
      dsimp [k]
      have hn : 1 ≤ n := hnpos
      have hm' : 1 ≤ m := hm
      omega
    have hKle : (I ^ (n * m + k)).topologicalClosure ≤ L := by
      apply Submodule.topologicalClosure_minimal
      · exact (Ideal.pow_le_pow_right hkexp).trans (SetLike.coe_subset_coe.mp hr)
      · exact L.toAddSubgroup.isClosed_of_isOpen hLopen
    exact sup_le_sup_left hKle _ (hpower_remainder m k hm hk hx)
  have hIprimeOpen (m : ℕ) (hm : 1 ≤ m) :
      IsOpen ((I' ^ m).topologicalClosure : Set A) := by
    have hle : (I ^ (n * m)).topologicalClosure ≤ (I' ^ m).topologicalClosure :=
      Submodule.topologicalClosure_minimal _ (hclosure_power m hm)
        (Submodule.isClosed_topologicalClosure _)
    apply Ideal.isOpen_of_isOpen_subideal hle
    exact hIclosure (n * m) (by
      have hprod : 0 < n * m := Nat.mul_pos (by omega) (by omega)
      omega)
  have hcofinal : ∀ U ∈ 𝓝 (0 : A), ∃ m : ℕ,
      ((I' ^ m).topologicalClosure : Set A) ⊆ U := by
    intro U hU
    obtain ⟨L, hLopen, hLU⟩ :=
      (IsLinearTopology.hasBasis_open_ideal.nhds_of_zero' (0 : A)).mem_iff.mp hU
    obtain ⟨r, hr⟩ := hIdef.2 (L : Set A) (hLopen.mem_nhds L.zero_mem)
    let m := max r 1
    have hm : 1 ≤ m := le_max_right _ _
    have hI'close : (I' ^ m).topologicalClosure ≤ L := by
      apply Submodule.topologicalClosure_minimal
      · exact (pow_le_pow_left' hI'I m).trans
          ((Ideal.pow_le_pow_right (Nat.le_max_left r 1)).trans (SetLike.coe_subset_coe.mp hr))
      · exact L.toAddSubgroup.isClosed_of_isOpen hLopen
    exact ⟨m, Set.Subset.trans (SetLike.coe_subset_coe.mpr hI'close) (by simpa using hLU)⟩
  obtain ⟨K, hKfg, hKadic⟩ := @RingHom.exists_fg_ideal_isAdic_of_isTaut
    A A (inferInstance) I'.adicTopology (adic_topological_ring I')
    (Ideal.isLinearTopology I') (inferInstance) (inferInstance)
    (inferInstance) (inferInstance) (RingHom.id A)
    (taut_id_from_closure_cofinal I' hIprimeOpen hcofinal)
    ⟨I', hI'fg, rfl⟩ (inferInstance) (inferInstance)
  exact ⟨K, hKadic, hKfg⟩

end

end TopologicalRing

end
