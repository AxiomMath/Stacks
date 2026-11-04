module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension

/-!
# Affine neighborhoods of generic points of irreducible components

In a quasi-separated scheme, the generic points of any finite family of distinct irreducible
components admit pairwise disjoint affine open neighborhoods. Their union is affine, and hence
the generic points also lie in one affine open; adding any further point of the scheme, the
resulting finite set still lies in a single affine open.

## Main results

* `AlgebraicGeometry.exists_pairwise_disjoint_affine_opens_of_generic_points` constructs the
  disjoint affine neighborhoods and records that their union is affine.
* `AlgebraicGeometry.exists_affine_open_containing_generic_points` gives one affine open
  containing all the generic points.
* `AlgebraicGeometry.exists_affineOpen_mem_of_genericPoints_irreducibleComponents` adds an
  arbitrary point of the scheme to that affine open.

## Implementation notes

The finite list in the source is represented by an arbitrary finite index type, respectively by
a function from `Fin n`. Pairwise distinctness of the indexed irreducible components is expressed
by injectivity of the family, and generic points are recorded using `IsGenericPoint` without
making a choice of them. The union of the neighborhoods is their supremum in the lattice of open
subsets.

## References

* [Stacks Project, Tag 01ZV](https://stacks.math.columbia.edu/tag/01ZV)
* [Stacks Project, Tag 01ZX](https://stacks.math.columbia.edu/tag/01ZX)
-/

public section

open Function Topology TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- The prime of an affine open corresponding to the generic point of an irreducible component
is a minimal prime of the ring of sections. -/
private lemma primeIdealOf_mem_minimalPrimes {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffineOpen U) (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (η : X) (hη : IsGenericPoint η Z) (hηU : η ∈ U) :
    (hU.primeIdealOf ⟨η, hηU⟩).asIdeal ∈ minimalPrimes Γ(X, U) := by
  let p : Spec Γ(X, U) := hU.primeIdealOf ⟨η, hηU⟩
  have hpη : hU.fromSpec p = η := hU.fromSpec_primeIdealOf ⟨η, hηU⟩
  have hpgen : IsGenericPoint p (hU.fromSpec ⁻¹' Z) := by
    rw [isGenericPoint_iff_specializes]
    intro q
    rw [← hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff, hpη,
      hη.specializes_iff_mem]
    rfl
  change p.asIdeal ∈ minimalPrimes Γ(X, U)
  rw [← PrimeSpectrum.vanishingIdeal_singleton p,
    PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
  change closure ({p} : Set (Spec Γ(X, U))) ∈ irreducibleComponents (Spec Γ(X, U))
  rw [hpgen.def]
  exact preimage_mem_irreducibleComponents hZ hU.fromSpec.isOpenEmbedding ⟨η, hη.mem, p, hpη⟩

/-- Inside an affine open containing the generic point of an irreducible component, there is a
smaller affine open neighbourhood disjoint from a given compact open avoiding that point. -/
private lemma exists_affineOpen_le_disjoint {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (W U : X.Opens) (hW : IsCompact (W : Set X)) (hU : IsAffineOpen U)
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (η : X) (hη : IsGenericPoint η Z) (hηU : η ∈ U) (hηW : η ∉ W) :
    ∃ V : X.Opens, IsAffineOpen V ∧ η ∈ V ∧ V ≤ U ∧ Disjoint V W := by
  let T : TopologicalSpace.Opens (PrimeSpectrum Γ(X, U)) := hU.fromSpec ⁻¹ᵁ (U ⊓ W)
  have hTcompact : IsCompact (T : Set (PrimeSpectrum Γ(X, U))) :=
    hU.fromSpec.isOpenEmbedding.isInducing.isCompact_preimage'
      (QuasiSeparatedSpace.inter_isCompact (U : Set X) (W : Set X)
        U.isOpen hU.isCompact W.isOpen hW) (hU.range_fromSpec ▸ fun y hy => hy.1)
  have hpT : hU.primeIdealOf ⟨η, hηU⟩ ∉ T := by
    intro hp
    change hU.fromSpec (hU.primeIdealOf ⟨η, hηU⟩) ∈ U ⊓ W at hp
    rw [hU.fromSpec_primeIdealOf] at hp
    exact hηW hp.2
  obtain ⟨f, hfp, hfdisj⟩ := PrimeSpectrum.exists_disjoint_basicOpen_of_mem_minimalPrimes
    (primeIdealOf_mem_minimalPrimes U hU Z hZ η hη hηU) hTcompact hpT
  refine ⟨X.basicOpen f, hU.basicOpen f, ?_, X.basicOpen_le f, ?_⟩
  · rw [← hU.fromSpec_image_basicOpen]
    exact ⟨_, (PrimeSpectrum.mem_basicOpen f _).2 hfp, hU.fromSpec_primeIdealOf ⟨η, hηU⟩⟩
  · rw [← TopologicalSpace.Opens.coe_disjoint]
    apply Set.disjoint_left.2
    intro y hyV hyW
    have hyU : y ∈ U := X.basicOpen_le f hyV
    have hybasic : hU.primeIdealOf ⟨y, hyU⟩ ∈ PrimeSpectrum.basicOpen f := by
      obtain ⟨q, hq, hqy⟩ : y ∈ hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f := by
        rwa [hU.fromSpec_image_basicOpen]
      exact hU.fromSpec.isOpenEmbedding.injective
        (hqy.trans (hU.fromSpec_primeIdealOf ⟨y, hyU⟩).symm) ▸ hq
    have hyT : hU.primeIdealOf ⟨y, hyU⟩ ∈ T := by
      change hU.fromSpec (hU.primeIdealOf ⟨y, hyU⟩) ∈ U ⊓ W
      simpa [hU.fromSpec_primeIdealOf] using ⟨hyU, hyW⟩
    exact Set.disjoint_left.mp hfdisj hybasic hyT

section PairwiseDisjoint

variable {X : AlgebraicGeometry.Scheme.{u}} {ι : Type v} [Finite ι]

/-- **Stacks Project, Tag 01ZV.** A finite family of distinct irreducible components
of a quasi-separated scheme has pairwise disjoint affine open neighborhoods of its
generic points; the union of these neighborhoods is affine. -/
@[stacks 01ZV "pairwise disjoint neighborhoods"]
theorem exists_pairwise_disjoint_affine_opens_of_generic_points
    [QuasiSeparatedSpace X] (Z : ι → Set X)
    (hZ : ∀ i, Z i ∈ irreducibleComponents X) (hZ_injective : Injective Z)
    (η : ι → X) (hη : ∀ i, IsGenericPoint (η i) (Z i)) :
    ∃ U : ι → X.Opens,
      (∀ i, AlgebraicGeometry.IsAffineOpen (U i)) ∧
      (∀ i, η i ∈ U i) ∧
      Pairwise (Disjoint on U) ∧
      AlgebraicGeometry.IsAffineOpen (iSup U) := by
  classical
  let C : ι → Set X := fun i => ⋃ j : {j // j ≠ i}, Z j
  have hC_closed (i : ι) : IsClosed (C i) :=
    isClosed_iUnion_of_finite fun j => isClosed_of_mem_irreducibleComponents _ (hZ j)
  have hηC (i : ι) : η i ∉ C i := by
    intro hi
    obtain ⟨j, hij⟩ := Set.mem_iUnion.mp hi
    have hsub : Z i ⊆ Z j := by
      rw [← hη i]
      exact closure_minimal (Set.singleton_subset_iff.mpr hij)
        (isClosed_of_mem_irreducibleComponents _ (hZ j))
    exact j.property (hZ_injective (Set.Subset.antisymm hsub ((hZ i).2 (hZ j).1 hsub)).symm)
  choose S hS_aff hηS hSC using fun i =>
    X.isBasis_affineOpens.exists_subset_of_mem_open (hηC i)
      (hC_closed i).isOpen_compl
  choose V hV_eq using hS_aff
  have hV_aff (i : ι) : AlgebraicGeometry.IsAffineOpen (V i) := (hV_eq i).1
  have hηV (i : ι) : η i ∈ V i := by
    change η i ∈ (V i : Set X)
    simpa only [(hV_eq i).2] using hηS i
  have hVC (i : ι) : (V i : Set X) ⊆ (C i)ᶜ := (hV_eq i).2 ▸ hSC i
  have hηW (i : ι) : η i ∉ (⨆ j : {j // j ≠ i}, V j) := by
    intro hi
    obtain ⟨j, hij⟩ := TopologicalSpace.Opens.mem_iSup.mp hi
    have : η i ∈ C j := by
      simp only [C, Set.mem_iUnion]
      exact ⟨⟨i, Ne.symm j.property⟩, (hη i).mem⟩
    exact hVC j hij this
  choose U hU_aff hηU hUV hUW using fun i =>
    exists_affineOpen_le_disjoint (⨆ j : {j // j ≠ i}, V j) (V i)
      (by
        rw [TopologicalSpace.Opens.coe_iSup]
        exact isCompact_iUnion fun j => (hV_aff j).isCompact)
      (hV_aff i) (Z i) (hZ i) (η i) (hη i) (hηV i) (hηW i)
  have hU_disj : Pairwise (Disjoint on U) := fun i j hij =>
    (hUW i).mono_right <| (hUV j).trans <|
      le_iSup (fun k : {k // k ≠ i} => V k) ⟨j, Ne.symm hij⟩
  exact ⟨U, hU_aff, hηU, hU_disj, IsAffineOpen.iSup_of_disjoint hU_aff hU_disj⟩

/-- **Stacks Project, Tag 01ZV.** The generic points of a finite family of distinct
irreducible components of a quasi-separated scheme lie in a single affine open. -/
@[stacks 01ZV "common affine neighborhood"]
theorem exists_affine_open_containing_generic_points
    [QuasiSeparatedSpace X] (Z : ι → Set X)
    (hZ : ∀ i, Z i ∈ irreducibleComponents X) (hZ_injective : Injective Z)
    (η : ι → X) (hη : ∀ i, IsGenericPoint (η i) (Z i)) :
    ∃ U : X.Opens, AlgebraicGeometry.IsAffineOpen U ∧ ∀ i, η i ∈ U := by
  obtain ⟨U, -, hηU, -, hsup⟩ :=
    exists_pairwise_disjoint_affine_opens_of_generic_points Z hZ hZ_injective η hη
  exact ⟨iSup U, hsup, fun i => le_iSup U i (hηU i)⟩

end PairwiseDisjoint

/-- **Stacks Project, Tag 01ZX.** In a quasi-separated scheme, any point and
the generic points of finitely many pairwise distinct irreducible components
are contained in a common affine open. -/
@[stacks 01ZX]
theorem exists_affineOpen_mem_of_genericPoints_irreducibleComponents
    (X : Scheme.{u}) [QuasiSeparatedSpace X] {n : ℕ}
    (Z : Fin n → Set X) (hZ : ∀ i, Z i ∈ irreducibleComponents X)
    (hZ_injective : Function.Injective Z)
    (η : Fin n → X) (hη : ∀ i, IsGenericPoint (η i) (Z i)) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ i, η i ∈ U := by
  classical
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let S := {i : Fin n | η i ∉ W}
  obtain ⟨U, hUaff, hηU, hUdisj, -⟩ :=
    exists_pairwise_disjoint_affine_opens_of_generic_points
      (fun i : S ↦ Z i) (fun i ↦ hZ i) (hZ_injective.comp Subtype.val_injective)
      (fun i : S ↦ η i) (fun i ↦ hη i)
  choose V hVaff hηV hVU hVW using fun i : S ↦
    exists_affineOpen_le_disjoint W (U i) hW.isCompact (hUaff i) (Z i) (hZ i)
      (η i) (hη i) (hηU i) i.2
  let V' : X.Opens := ⨆ i : S, V i
  have hV'aff : IsAffineOpen V' := IsAffineOpen.iSup_of_disjoint hVaff fun i j hij ↦
    Disjoint.mono (hVU i) (hVU j) (hUdisj hij)
  have hWV' : Disjoint W V' := (iSup_disjoint_iff.mpr hVW).symm
  refine ⟨W ⊔ V', hW.sup_of_disjoint hV'aff hWV', (le_sup_left : W ≤ W ⊔ V') hxW, ?_⟩
  intro i
  by_cases hi : η i ∈ W
  · exact (le_sup_left : W ≤ W ⊔ V') hi
  · exact (le_sup_right : V' ≤ W ⊔ V')
      (le_iSup (fun j : S ↦ V j) ⟨i, hi⟩ (hηV ⟨i, hi⟩))

end AlgebraicGeometry

end
