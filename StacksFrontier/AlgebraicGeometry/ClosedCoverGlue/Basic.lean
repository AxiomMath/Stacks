module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Sections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.Topology.DiscreteSubset
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeTFAE
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.Topology.Irreducible.DisjointComponentLocus
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Glueing.AlgebraicStructure
public import StacksFrontier.Topology.Sheaves.Glueing.Sheaf
public import StacksFrontier.Topology.Sheaves.Modules.Invertible
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Glueing an invertible module from a finite closed cover with discrete overlaps

Let `X` be a reduced scheme covered set-theoretically by finitely many closed subschemes
`f i : Z i ⟶ X`, and suppose two distinct members meet in a *discrete* space. [Stacks,
Tag 09NE] asserts that invertible modules `L i` on the `Z i` glue to an invertible module on
`X` restricting to each `L i`. This file proves that existence assertion.

## The construction

Write `T` for the *overlap locus* `⋃_{i ≠ j} f i '' Z i ∩ f j '' Z j` — the complement of
`Stacks.Topology.Irreducible.disjointLocus` of the ranges, recorded as
`StacksTag09NE.overlapLocus_eq_compl_disjointLocus`. The cover is closed, so `T` is closed, and
the pairwise discreteness hypothesis makes `T` itself discrete: a finite union of closed
discrete sets is discrete.

The glueing then goes through [Stacks, Tag 0C0T], in the form
`Stacks.PicFinite.exists_isInvertible_modulePullback_iso`, applied to the single morphism
`g = Sigma.desc f : ∐ Z ⟶ X` out of the coproduct, with the open `U = Tᶜ`:

* `g` is finite, because each `f i` is a closed immersion and the index type is finite;
* `g ∣_ U` is an isomorphism (`isIso_sigmaDesc_morphismRestrict_complement_overlap`). Over `U`
  the members of the cover are pairwise disjoint, hence — being finitely many closed sets
  covering `U` — each is *open* in `U`, so each closed immersion is an open immersion onto a
  clopen piece and the coproduct map is an iso by
  `isIso_of_isClosedImmersion_of_surjective`, `X` being reduced;
* `Uᶜ = T` is discrete.

The module fed to 0C0T is `moduleOnSchemeSigma`, the coproduct of the extensions by zero of the
`L i` along the summand immersions; `pullback_moduleOnSchemeSigma` identifies its restriction to
the `i`-th summand with `L i`, the other summands contributing zero because the summands are
pairwise disjoint opens. It is invertible because it is finite locally free of rank one, which
is checked pointwise through `localGeneratorsDataOfTrivializations` and then converted by
[Stacks, Tag 0B8M].

## Main results

* `StacksTag09NE.exists_invertible_of_closed_cover_discrete_intersections`: **Tag 09NE**,
  existence of the invertible module.

## References

* [Stacks Project, Tag 09NE](https://stacks.math.columbia.edu/tag/09NE)
* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u v

namespace StacksTag09NE

open Stacks.FiniteLocallyFree.ModuleTFAE
  (localGeneratorsDataOfTrivializations localGeneratorsDataOfTrivializations_isLocallyFreeData)

/-- The `Stacks` spelling of invertibility, available from the `AlgebraicGeometry` one on a
scheme. Tag 01CS's class exists under both names; the two are equivalent by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`, and 09NE's statement is written in
the `AlgebraicGeometry` spelling (forced by Tag 0C0T) while the Tag 01CY and Tag 0B8M results it
consumes are stated in the `Stacks` one. Supplying the crossing as an instance is what keeps
that from appearing at every call site. -/
public instance isInvertible_stacks_of_isInvertible (Y : Scheme.{u}) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L
        :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property L).2
      ‹_›

/-! ### Free sheaves on an open subscheme -/

/-- The free sheaf on an open `U` of a scheme, read through the equivalence between sheaves of
modules over the restricted structure sheaf and sheaves of modules on `U` as a scheme. -/
public noncomputable def freeOverEquivIso {X : Scheme.{u}} (U : X.Opens) (I : Type u) :
    SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
      (Scheme.Modules.overEquiv U).functor.obj
        (SheafOfModules.free (R := X.ringCatSheaf.over U) I) := by
  let F := (Scheme.Modules.overEquiv U).functor
  haveI : PreservesColimitsOfShape.{u, u} (Discrete I) F :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} F
  exact @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I this (Iso.refl _)

/-! ### The overlap locus -/

/-- The overlap locus of a family of morphisms into `X`: the union of the pairwise intersections
`range (f i) ∩ range (f j)` over distinct indices `i ≠ j`. -/
public def overlapLocus {ι : Type v} (X : Scheme.{u}) (Z : ι → Scheme.{u})
    (f : ∀ i, Z i ⟶ X) : Set X :=
  ⋃ p ∈ {p : ι × ι | p.1 ≠ p.2}, Set.range (f p.1) ∩ Set.range (f p.2)

/-- A finite union of the pairwise intersections in a closed cover is still discrete. -/
public theorem overlapLocus_discrete {ι : Type v} [Finite ι] (X : Scheme.{u})
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (hdiscrete : ∀ i j, i ≠ j → DiscreteTopology
      (↥(Set.range (f i) ∩ Set.range (f j) : Set X))) :
    DiscreteTopology (overlapLocus X Z f) := by
  rw [← isDiscrete_iff_discreteTopology]
  apply IsDiscrete.biUnion (I := {p : ι × ι | p.1 ≠ p.2})
  · exact Set.toFinite _
  · rintro ⟨i, j⟩ hp
    exact isDiscrete_iff_discreteTopology.mpr (hdiscrete i j hp)
  · rintro ⟨i, j⟩ hp
    exact (f i).isClosedEmbedding.isClosed_range.inter (f j).isClosedEmbedding.isClosed_range

/-- The overlap locus is the complement of the disjointness locus of the ranges: this is one
notion, not two, and every statement below may be read through
`Stacks.Topology.Irreducible.disjointLocus`. -/
public theorem overlapLocus_eq_compl_disjointLocus {ι : Type v} (X : Scheme.{u})
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) :
    overlapLocus X Z f =
      (Stacks.Topology.Irreducible.disjointLocus fun i => Set.range (f i))ᶜ := by
  ext x
  simp only [overlapLocus, Set.mem_iUnion, Set.mem_compl_iff,
    Stacks.Topology.Irreducible.mem_disjointLocus, not_forall, not_not,
    Set.mem_ofPred_eq, exists_prop]
  exact ⟨fun ⟨p, hp, hx⟩ => ⟨p.1, p.2, hp, hx⟩, fun ⟨i, j, hij, hx⟩ => ⟨(i, j), hij, hx⟩⟩

/-- The pairwise intersection locus is closed, so its complement is an open neighborhood of
every point lying on exactly one member of the cover. This is
`Stacks.Topology.Irreducible.isOpen_disjointLocus` read through
`overlapLocus_eq_compl_disjointLocus`. -/
public theorem overlapLocus_closed {ι : Type v} [Finite ι] (X : Scheme.{u})
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)] :
    IsClosed (overlapLocus X Z f) := by
  rw [overlapLocus_eq_compl_disjointLocus, isClosed_compl_iff]
  exact Stacks.Topology.Irreducible.isOpen_disjointLocus fun i =>
    (f i).isClosedEmbedding.isClosed_range

/-- The discrete complement hypothesis in `0C0T` holds after removing the overlap locus. -/
public theorem overlapComplement_discrete {ι : Type v} [Finite ι] (X : Scheme.{u})
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (hdiscrete : ∀ i j, i ≠ j → DiscreteTopology
      (↥(Set.range (f i) ∩ Set.range (f j) : Set X))) :
    let U : X.Opens := ⟨(overlapLocus X Z f)ᶜ, (overlapLocus_closed X Z f).isOpen_compl⟩
    DiscreteTopology (Uᶜ : Set X) := by
  dsimp only
  let U : X.Opens := ⟨(overlapLocus X Z f)ᶜ, (overlapLocus_closed X Z f).isOpen_compl⟩
  have hU : (Uᶜ : Set X) = overlapLocus X Z f := by
    ext x
    simp [U]
  rw [hU]
  exact overlapLocus_discrete X Z f hdiscrete

/-- A point of a closed discrete subset has an open neighborhood meeting that subset only in
that point. -/
public theorem exists_open_meeting_closedDiscrete_only_at {α : Type u} [TopologicalSpace α]
    (T : Set α) (hT : IsClosed T) [DiscreteTopology T] {x : α} (hx : x ∈ T) :
    ∃ U : Opens (TopCat.of α), x ∈ U ∧ (U : Set α) ∩ T = {x} := by
  let A : Set (↥T) := {y | (y : α) ≠ x}
  have hA : IsClosed A := by
    simp [A]
  obtain ⟨B, hB, hBA⟩ := (isClosed_induced_iff (s := A) (f := fun y : ↥T => (y : α))).mp hA
  let C : Set α := B ∩ T
  have hC : IsClosed C := hB.inter hT
  have hCT : C = T \ {x} := by
    ext y
    simp only [C, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hyB, hyT⟩
      have : (⟨y, hyT⟩ : ↥T) ∈ A := by
        rw [← hBA]
        exact hyB
      exact ⟨hyT, by simpa [A] using this⟩
    · rintro ⟨hyT, hyx⟩
      have hyA : (⟨y, hyT⟩ : ↥T) ∈ A := by simpa [A] using hyx
      rw [← hBA] at hyA
      exact ⟨hyA, hyT⟩
  refine ⟨⟨Cᶜ, hC.isOpen_compl⟩, ?_, ?_⟩
  · show x ∈ Cᶜ
    rw [hCT]
    simp
  · show Cᶜ ∩ T = {x}
    ext y
    by_cases hy : y = x <;> simp [hCT, hy, hx]

/-- Every point of the overlap locus has a neighborhood that contains no other overlap point. -/
public theorem exists_open_meeting_overlap_only_at {ι : Type v} [Finite ι]
    (X : Scheme.{u}) (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (hdiscrete : ∀ i j, i ≠ j → DiscreteTopology
      (↥(Set.range (f i) ∩ Set.range (f j) : Set X)))
    {x : X} (hx : x ∈ overlapLocus X Z f) :
    ∃ U : X.Opens, x ∈ U ∧ (U : Set X) ∩ overlapLocus X Z f = {x} := by
  let : DiscreteTopology (overlapLocus X Z f) :=
    overlapLocus_discrete X Z f hdiscrete
  exact exists_open_meeting_closedDiscrete_only_at (overlapLocus X Z f)
    (overlapLocus_closed X Z f) hx

/-- The first stage of the open cover used for gluing: the complement of the overlap locus,
together with one isolating neighborhood for every overlap point. -/
public noncomputable def overlapPatchCoverOpen {ι : Type v} [Finite ι]
    (X : Scheme.{u}) (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (hdiscrete : ∀ i j, i ≠ j → DiscreteTopology
      (↥(Set.range (f i) ∩ Set.range (f j) : Set X))) :
    Option (↥(overlapLocus X Z f)) → X.Opens
  | none => ⟨(overlapLocus X Z f)ᶜ, (overlapLocus_closed X Z f).isOpen_compl⟩
  | some x => Classical.choose
      (exists_open_meeting_overlap_only_at X Z f hdiscrete (x := x.1) x.2)

/-- The complement and isolated neighborhoods in `overlapPatchCoverOpen` cover `X`. -/
public theorem overlapPatchCoverOpen_covers {ι : Type v} [Finite ι]
    (X : Scheme.{u}) (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (hdiscrete : ∀ i j, i ≠ j → DiscreteTopology
      (↥(Set.range (f i) ∩ Set.range (f j) : Set X))) :
    ∀ x : X, ∃ i, x ∈ overlapPatchCoverOpen X Z f hdiscrete i := by
  intro x
  by_cases hx : x ∈ overlapLocus X Z f
  · let t : ↥(overlapLocus X Z f) := ⟨x, hx⟩
    refine ⟨some t, ?_⟩
    exact (Classical.choose_spec
      (exists_open_meeting_overlap_only_at X Z f hdiscrete (x := t.1) t.2)).1
  · refine ⟨none, ?_⟩
    simpa [overlapPatchCoverOpen] using hx

/-- An invertible module on a scheme is trivial on some open neighborhood of each point. -/
public theorem exists_open_trivialization_of_invertible (Y : Scheme.{u}) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] (x : Y) :
    ∃ U : Y.Opens, x ∈ U ∧ Nonempty
      (L.over U ≅ SheafOfModules.unit (Y.ringCatSheaf.over U)) := by
  obtain ⟨q, hq, hrank⟩ :=
    (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible
      Y L).exists_isFiniteLocallyFreeOfRankData
  have hxcover : x ∈ ⨆ i, q.X i := by
    rw [(Opens.coversTop_iff Y q.X).mp q.coversTop]
    simp
  rw [TopologicalSpace.Opens.mem_iSup] at hxcover
  obtain ⟨i, hxi⟩ := hxcover
  let : IsIso (q.generators i).π := hq.isIso i
  let eIndex : (q.generators i).I ≃ PUnit.{u + 1} :=
    (hrank i).some.trans (Equiv.equivPUnit _)
  let eFree := (SheafOfModules.freeFunctor
    (R := Y.ringCatSheaf.over (q.X i))).mapIso eIndex.toIso
  let eUnit := Limits.coproductUniqueIso
    (fun _ : PUnit.{u + 1} => SheafOfModules.unit (Y.ringCatSheaf.over (q.X i)))
  let e : L.over (q.X i) ≅ SheafOfModules.unit (Y.ringCatSheaf.over (q.X i)) :=
    (asIso (q.generators i).π).symm ≪≫ eFree ≪≫ eUnit
  exact ⟨q.X i, hxi, ⟨e⟩⟩

/-- Outside the pairwise intersection locus, a point in a closed cover belongs to a unique
member. -/
public theorem existsUnique_mem_range_of_not_overlap {ι : Type v} (X : Scheme.{u})
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (hcover : ∀ x : X, ∃ i z, f i z = x) {x : X}
    (hx : x ∉ overlapLocus X Z f) : ∃! i, x ∈ Set.range (f i) := by
  obtain ⟨i, z, rfl⟩ := hcover x
  refine ⟨i, ⟨z, rfl⟩, ?_⟩
  intro j hj
  by_contra hij
  have hij' : i ≠ j := fun h => hij h.symm
  obtain ⟨z', hz'⟩ := hj
  apply hx
  simp only [overlapLocus, Set.mem_iUnion]
  exact ⟨(i, j), hij', ⟨z, rfl⟩, ⟨z', hz'⟩⟩

/-- A closed immersion has a unique point over every point in its image. -/
public theorem existsUnique_preimage_of_mem_range {Y X : Scheme.{u}} (f : Y ⟶ X)
    [IsClosedImmersion f] {x : X} (hx : x ∈ Set.range f) : ∃! y : Y, f y = x := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, rfl, fun _ hz ↦ f.isClosedEmbedding.injective hz⟩

/-- An open neighborhood in a closed subscheme is induced by an open neighborhood in the
ambient scheme. -/
public theorem exists_open_in_ambient_of_open_in_closed {Y X : Scheme.{u}} (f : Y ⟶ X)
    [IsClosedImmersion f] (V : Y.Opens) {y : Y} (hy : y ∈ V) :
    ∃ W : X.Opens, f y ∈ W ∧ f ⁻¹ᵁ W = V := by
  have hind := f.isClosedEmbedding.isEmbedding.isInducing
  obtain ⟨W, hW, hpre⟩ := hind.isOpen_iff.mp V.2
  refine ⟨⟨W, hW⟩, ?_, ?_⟩
  · show f y ∈ W
    show y ∈ f ⁻¹' W
    rw [hpre]
    exact hy
  · ext z
    show f z ∈ W ↔ z ∈ V
    show z ∈ f ⁻¹' W ↔ z ∈ V
    rw [hpre]
    rfl

/-- Finitely many local neighborhoods on the closed pieces can be imposed by one ambient open
neighborhood. -/
public theorem exists_open_shrinking_component_preimages {ι : Type v} [Finite ι]
    (X : Scheme.{u}) (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)] {x : X} (V : ∀ i, (Z i).Opens)
    (hV : ∀ i (z : Z i), f i z = x → z ∈ V i) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ i, f i ⁻¹ᵁ U ≤ V i := by
  classical
  let W : ∀ i, X.Opens := fun i => if hxi : ∃ z, f i z = x then
      Classical.choose (exists_open_in_ambient_of_open_in_closed (f i) (V i)
        (hV i (Classical.choose hxi) (Classical.choose_spec hxi)))
    else ⟨(Set.range (f i))ᶜ, (f i).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let U : X.Opens := ⨅ i, W i
  refine ⟨U, ?_, ?_⟩
  · show x ∈ (U : Set X)
    simp only [U, Opens.coe_iInf, Set.mem_iInter]
    intro i
    by_cases hxi : ∃ z, f i z = x
    · have hxEq : (f i) (Classical.choose hxi) = x := Classical.choose_spec hxi
      have hxW := (Classical.choose_spec (exists_open_in_ambient_of_open_in_closed
        (f i) (V i) (hV i (Classical.choose hxi) hxEq))).1
      simpa [W, hxi, hxEq] using hxW
    · simp [W, hxi]
  · intro i z hz
    change (f i) z ∈ (U : Set X) at hz
    simp only [U, Opens.coe_iInf, Set.mem_iInter] at hz
    have hzW : (f i) z ∈ W i := hz i
    by_cases hxi : ∃ z, f i z = x
    · let z₀ : Z i := Classical.choose hxi
      have hz₀ : f i z₀ = x := Classical.choose_spec hxi
      have hpre := (Classical.choose_spec (exists_open_in_ambient_of_open_in_closed
        (f i) (V i) (hV i z₀ hz₀))).2
      have hzW' : (f i) z ∈ Classical.choose (exists_open_in_ambient_of_open_in_closed
          (f i) (V i) (hV i z₀ hz₀)) := by
        simpa [W, hxi] using hzW
      have hzpre : z ∈ (f i) ⁻¹ᵁ Classical.choose (exists_open_in_ambient_of_open_in_closed
          (f i) (V i) (hV i z₀ hz₀)) := hzW'
      rw [hpre] at hzpre
      exact hzpre
    · have hzrange : (f i) z ∈ Set.range (f i) := ⟨z, rfl⟩
      have hnot : (f i) z ∈ (Set.range (f i))ᶜ := by
        simp only [W, hxi, dite_eq_right, not_false_eq_true] at hzW
        exact hzW
      exact (hnot hzrange).elim

/-- A prescribed section on a member of the cover is nonvanishing at every point of that
member which lies in the overlap locus. -/
public theorem nonvanishing_of_mem_overlap {ι : Type v} (X : Scheme.{u})
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    (L : ∀ i, (Z i).Modules) (s : ∀ i, (L i).sections)
    (hs : ∀ i j, i ≠ j → ∀ z : Z i,
      (f i) z ∈ Set.range (f j) →
        z ∈ Stacks.SheafOfModules.nonvanishingLocus (X := (Z i).toRingedSpace) (L i) (s i))
    {i : ι} {z : Z i} (hz : (f i) z ∈ overlapLocus X Z f) :
    z ∈ Stacks.SheafOfModules.nonvanishingLocus (X := (Z i).toRingedSpace) (L i) (s i) := by
  change (f i) z ∈ ⋃ p ∈ {p : ι × ι | p.1 ≠ p.2},
    Set.range (f p.1) ∩ Set.range (f p.2) at hz
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hp, hleft, hright⟩ := Set.mem_iUnion.mp hp
  rcases hleft with ⟨z₁, hz₁⟩
  rcases hright with ⟨z₂, hz₂⟩
  rcases p with ⟨j, k⟩
  change j ≠ k at hp
  by_cases hi₁ : i = j
  · subst j
    exact hs i k hp z ⟨z₂, hz₂⟩
  · by_cases hi₂ : i = k
    · subst k
      exact hs i j hp.symm z ⟨z₁, hz₁⟩
    · exact hs i j hi₁ z ⟨z₁, hz₁⟩

/-- Away from the overlap locus, a closed cover is locally just one of its members: after
shrinking around such a point, the unique member maps isomorphically to the neighborhood. -/
public theorem exists_open_neighborhood_isIso_component_of_not_overlap
    {ι : Type v} [Finite ι] (X : Scheme.{u}) [IsReduced X] (Z : ι → Scheme.{u})
    (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (hcover : ∀ x : X, ∃ i z, f i z = x) {x : X}
    (hx : x ∉ overlapLocus X Z f) :
    ∃ (i : ι) (U : X.Opens), x ∈ U ∧ IsIso ((f i) ∣_ U) ∧
      ∀ j, j ≠ i → f j ⁻¹ᵁ U = ⊥ := by
  classical
  obtain ⟨i, hi, huniq⟩ := existsUnique_mem_range_of_not_overlap X Z f hcover hx
  let V : ∀ j, (Z j).Opens := fun j => if j = i then ⊤ else ⊥
  have hV : ∀ j (z : Z j), f j z = x → z ∈ V j := by
    intro j z hz
    by_cases hji : j = i
    · simp [V, hji]
    · exact (hji (huniq j ⟨z, hz⟩)).elim
  obtain ⟨U, hxU, hpre⟩ := exists_open_shrinking_component_preimages X Z f V hV
  refine ⟨i, U, hxU, ?_, ?_⟩
  · have hsurj : Surjective ((f i) ∣_ U) := by
      constructor
      intro y
      obtain ⟨j, z, hz⟩ := hcover y.1
      by_cases hji : j = i
      · subst j
        have hzU : z ∈ f i ⁻¹ᵁ U := by
          show f i z ∈ U
          rw [hz]
          exact y.2
        exact ⟨⟨z, hzU⟩, U.ι.isOpenEmbedding.injective
          ((morphismRestrict_base_coe (f i) U ⟨z, hzU⟩).trans hz)⟩
      · have hzU : z ∈ f j ⁻¹ᵁ U := by
          show f j z ∈ U
          rw [hz]
          exact y.2
        have hzero : f j ⁻¹ᵁ U ≤ (⊥ : (Z j).Opens) := by
          simpa [V, hji] using hpre j
        have hbot : z ∈ (⊥ : (Z j).Opens) := hzero hzU
        simp at hbot
    let : IsClosedImmersion ((f i) ∣_ U) := inferInstance
    let : IsReduced U.toScheme := inferInstance
    exact isIso_of_isClosedImmersion_of_surjective ((f i) ∣_ U)
  · intro j hji
    exact le_antisymm (by simpa [V, hji] using hpre j) bot_le

/-- The coproduct descent of `f` sends the `i`-th summand inclusion of a point to `f i`. -/
private theorem sigmaDesc_sigmaι_apply {ι : Type v} [Small.{u} ι] {X : Scheme.{u}}
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X) (i : ι) (z : Z i) :
    Limits.Sigma.desc f (Limits.Sigma.ι Z i z) = f i z := by
  change (Limits.Sigma.ι Z i ≫ Limits.Sigma.desc f) z = _
  rw [Limits.Sigma.ι_desc]

/-- A disjoint open cover of schemes with common target presents that target as their
coproduct. -/
public theorem isIso_sigmaDesc_of_disjointOpenCover {ι : Type v} [Small.{u} ι]
    {X : Scheme.{u}} (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsOpenImmersion (f i)]
    (hdisjoint : Pairwise (Function.onFun Disjoint (fun i => Set.range ⇑(f i))))
    (hcover : ∀ x : X, ∃ i z, f i z = x) : IsIso (Limits.Sigma.desc f) := by
  have hopen : IsOpenImmersion (Limits.Sigma.desc f) := isOpenImmersion_sigmaDesc Z f hdisjoint
  have hsurjective : Surjective (Limits.Sigma.desc f) := by
    constructor
    intro x
    obtain ⟨i, z, rfl⟩ := hcover x
    exact ⟨Limits.Sigma.ι Z i z, sigmaDesc_sigmaι_apply Z f i z⟩
  exact (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hopen, hsurjective⟩

/-- A closed immersion into a reduced scheme is an open immersion when its image is open. -/
public theorem isOpenImmersion_of_closedImmersion_of_open_range {Y Z : Scheme.{u}}
    (g : Y ⟶ Z) [IsClosedImmersion g] [IsReduced Z]
    (hopen : IsOpen (Set.range ⇑g)) : IsOpenImmersion g := by
  let U : Z.Opens := ⟨Set.range ⇑g, hopen⟩
  have hsub : Set.range ⇑g ⊆ Set.range ⇑U.ι := by simp [U]
  let q : Y ⟶ U.toScheme := IsOpenImmersion.lift U.ι g hsub
  have hfac : q ≫ U.ι = g := IsOpenImmersion.lift_fac U.ι g hsub
  have hqcomp : IsClosedImmersion (q ≫ U.ι) := hfac ▸ inferInstance
  have hqclosed : IsClosedImmersion q := IsClosedImmersion.of_comp q U.ι
  have hqsurjective : Surjective q := ⟨fun ⟨z, hz⟩ ↦ by
    change z ∈ Set.range ⇑g at hz
    obtain ⟨y, hy⟩ := hz
    refine ⟨y, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    have hqg : U.ι (q y) = g y := by
      simpa only [← Scheme.Hom.comp_apply] using congr($hfac y)
    rw [hqg, hy]
    rfl⟩
  let : IsClosedImmersion q := hqclosed
  let : Surjective q := hqsurjective
  let : IsReduced U.toScheme := inferInstance
  have : IsIso q := isIso_of_isClosedImmersion_of_surjective q
  rw [← hfac]
  infer_instance

/-- Every member of a finite disjoint closed cover is open. -/
public theorem isOpen_of_finite_disjoint_closed_cover_piece {ι : Type v} [Finite ι]
    {α : Type u} [TopologicalSpace α] (S : ι → Set α)
    (hclosed : ∀ i, IsClosed (S i))
    (hdisjoint : Pairwise (Function.onFun Disjoint S))
    (hcover : (⋃ i, S i) = Set.univ) (i : ι) : IsOpen (S i) := by
  have hcompl : (S i)ᶜ = ⋃ j : {j : ι // j ≠ i}, S j.1 := by
    ext x
    constructor
    · intro hx
      have hxcover : x ∈ ⋃ j, S j := by rw [hcover]; trivial
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxcover
      have hji : j ≠ i := fun h ↦ hx (h ▸ hj)
      exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
    · intro hx hxsi
      obtain ⟨⟨j, hji⟩, hxj⟩ := Set.mem_iUnion.mp hx
      exact (Set.disjoint_right.mp (hdisjoint hji)) hxsi hxj
  have hclosedCompl : IsClosed ((S i)ᶜ) := by
    rw [hcompl]
    convert (Set.toFinite (Set.univ : Set {j : ι // j ≠ i})).isClosed_biUnion
      (fun j hj => hclosed j.1) using 1
    simp
  simpa using hclosedCompl.isOpen_compl

/-- A finite family of closed immersions with disjoint images that cover a scheme is a
coproduct presentation. -/
public theorem isIso_sigmaDesc_of_disjointClosedCover {ι : Type v} [Finite ι]
    {X : Scheme.{u}} [IsReduced X] (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (hdisjoint : Pairwise (Function.onFun Disjoint (fun i => Set.range ⇑(f i))))
    (hcover : ∀ x : X, ∃ i z, f i z = x) : IsIso (Limits.Sigma.desc f) := by
  have hclosed : ∀ i, IsClosed (Set.range ⇑(f i)) := fun i =>
    (f i).isClosedEmbedding.isClosed_range
  have hcover' : (⋃ i, Set.range ⇑(f i)) = Set.univ := Set.iUnion_eq_univ_iff.mpr hcover
  have hopen : ∀ i, IsOpen (Set.range ⇑(f i)) := fun i =>
    isOpen_of_finite_disjoint_closed_cover_piece (fun i => Set.range ⇑(f i))
      hclosed hdisjoint hcover' i
  let (i : ι) : IsOpenImmersion (f i) :=
    isOpenImmersion_of_closedImmersion_of_open_range (f i) (hopen i)
  exact isIso_sigmaDesc_of_disjointOpenCover Z f hdisjoint hcover

/-- Away from the overlap locus, the restrictions of the closed cover pieces are a disjoint
closed cover, hence form a scheme coproduct. -/
public theorem isIso_sigmaDesc_restrict_complement_overlap {ι : Type v} [Finite ι]
    {X : Scheme.{u}} [IsReduced X] (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)] (hcover : ∀ x : X, ∃ i z, f i z = x) :
    let U : X.Opens := ⟨(overlapLocus X Z f)ᶜ, (overlapLocus_closed X Z f).isOpen_compl⟩
    IsIso (Limits.Sigma.desc (fun i => f i ∣_ U)) := by
  let U : X.Opens := ⟨(overlapLocus X Z f)ᶜ, (overlapLocus_closed X Z f).isOpen_compl⟩
  have hdisjoint : Pairwise
      (Function.onFun Disjoint (fun i => Set.range ⇑(f i ∣_ U))) := by
    intro i j hij
    show Disjoint (Set.range ⇑(f i ∣_ U)) (Set.range ⇑(f j ∣_ U))
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨yi, hyi⟩ := hxi
    obtain ⟨yj, hyj⟩ := hxj
    have hxi_val : (f i) yi.1 = x.1 := by
      have h := congrArg Subtype.val hyi
      simpa only [morphismRestrict_base_coe] using h
    have hval : (f i) yi.1 = (f j) yj.1 := by
      have h := congrArg Subtype.val (hyi.trans hyj.symm)
      simpa only [morphismRestrict_base_coe] using h
    have hpair : (f i) yi.1 ∈
        ⋃ p ∈ {p : ι × ι | p.1 ≠ p.2}, Set.range (f p.1) ∩ Set.range (f p.2) := by
      simp only [Set.mem_iUnion]
      exact ⟨(i, j), hij, ⟨yi.1, rfl⟩, ⟨yj.1, hval.symm⟩⟩
    have hxoverlap : (x.1 : X) ∈ overlapLocus X Z f := hxi_val ▸ hpair
    exact (show (x.1 : X) ∉ overlapLocus X Z f from x.2) hxoverlap
  have hcoverU : ∀ x : U, ∃ i z, (f i ∣_ U) z = x := by
    intro x
    obtain ⟨i, z, hz⟩ := hcover x.1
    have hzU : (f i) z ∈ U := by
      rw [hz]
      exact x.2
    exact ⟨i, ⟨z, hzU⟩, Subtype.ext ((morphismRestrict_base_coe (f i) U ⟨z, hzU⟩).trans hz)⟩
  let : IsReduced U.toScheme := inferInstance
  exact isIso_sigmaDesc_of_disjointClosedCover
    (fun i => (f i ⁻¹ᵁ U).toScheme) (fun i => f i ∣_ U) hdisjoint hcoverU

/-- Every point of a scheme coproduct lies in one of its summands. -/
public theorem exists_component_point_of_sigma {ι : Type v} [Finite ι] [Small.{u} ι]
    (Z : ι → Scheme.{u}) (x : ↥(∐ Z)) : ∃ i z, Limits.Sigma.ι Z i z = x := by
  classical
  let e : ι ≃ Shrink.{u} ι := equivShrink.{u} ι
  let Z' : Shrink.{u} ι → Scheme.{u} := fun i => Z (e.symm i)
  let E : (∐ Z') ≅ ∐ Z := Limits.Sigma.reindex e.symm Z
  have hι (i : Shrink.{u} ι) :
      Limits.Sigma.ι Z' i ≫ E.hom = Limits.Sigma.ι Z (e.symm i) := by
    show Limits.Sigma.ι (Z ∘ e.symm) i ≫ (Limits.Sigma.reindex e.symm Z).hom = _
    exact Limits.Sigma.ι_reindex_hom e.symm Z i
  obtain ⟨p, hp⟩ := (sigmaMk Z').surjective (E.inv x)
  rcases p with ⟨i, z⟩
  refine ⟨e.symm i, z, ?_⟩
  rw [← hι i]
  simpa [sigmaMk_mk] using congrArg E.hom hp

/-- Restriction commutes with the finite coproduct presentation over the complement of the
overlap locus. -/
public theorem isIso_sigmaDesc_morphismRestrict_complement_overlap {ι : Type v} [Finite ι]
    {X : Scheme.{u}} [IsReduced X] (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)] (hcover : ∀ x : X, ∃ i z, f i z = x) :
    let g := Limits.Sigma.desc f
    let U : X.Opens := ⟨(overlapLocus X Z f)ᶜ, (overlapLocus_closed X Z f).isOpen_compl⟩
    IsIso (g ∣_ U) := by
  classical
  dsimp only
  let g : (∐ Z) ⟶ X := Limits.Sigma.desc f
  let U : X.Opens := ⟨(overlapLocus X Z f)ᶜ, (overlapLocus_closed X Z f).isOpen_compl⟩
  let W : (∐ Z).Opens := g ⁻¹ᵁ U
  have hsub (i : ι) :
      Set.range ⇑((f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i) ⊆ Set.range ⇑W.ι := by
    intro x hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨⟨Limits.Sigma.ι Z i ((f i ⁻¹ᵁ U).ι z), ?_⟩, rfl⟩
    show Limits.Sigma.desc f (Limits.Sigma.ι Z i ((f i ⁻¹ᵁ U).ι z)) ∈ U
    rw [sigmaDesc_sigmaι_apply]
    exact z.2
  let kf : ∀ i, (f i ⁻¹ᵁ U).toScheme ⟶ W.toScheme := fun i =>
    IsOpenImmersion.lift W.ι ((f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i) (hsub i)
  have hfac (i : ι) : kf i ≫ W.ι = (f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i :=
    IsOpenImmersion.lift_fac W.ι _ (hsub i)
  have hdisjoint : Pairwise
      (Function.onFun Disjoint (fun i => Set.range ⇑(kf i))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨yi, hyi⟩ := hxi
    obtain ⟨yj, hyj⟩ := hxj
    have hEq : Limits.Sigma.ι Z i ((f i ⁻¹ᵁ U).ι yi) =
        Limits.Sigma.ι Z j ((f j ⁻¹ᵁ U).ι yj) := by
      have hi := congrArg (fun q => q.base yi) (hfac i)
      have hj := congrArg (fun q => q.base yj) (hfac j)
      calc
        Limits.Sigma.ι Z i ((f i ⁻¹ᵁ U).ι yi) = W.ι (kf i yi) := by simpa using hi.symm
        _ = W.ι (kf j yj) := congrArg W.ι (hyi.trans hyj.symm)
        _ = Limits.Sigma.ι Z j ((f j ⁻¹ᵁ U).ι yj) := by simpa using hj
    have hidx := (sigmaι_eq_iff Z i j ((f i ⁻¹ᵁ U).ι yi) ((f j ⁻¹ᵁ U).ι yj)).mp hEq
    exact hij (congrArg Sigma.fst hidx)
  have hcoverW : ∀ x : W.toScheme, ∃ i z, kf i z = x := by
    intro x
    obtain ⟨i, z, hpoint⟩ := exists_component_point_of_sigma Z (W.ι x)
    have hzU : z ∈ f i ⁻¹ᵁ U := by
      show f i z ∈ U
      have hval : f i z = g (W.ι x) := by
        rw [← hpoint]
        exact (sigmaDesc_sigmaι_apply Z f i z).symm
      exact hval ▸ x.2
    refine ⟨i, ⟨z, hzU⟩, ?_⟩
    apply W.ι.isOpenEmbedding.injective
    calc
      W.ι (kf i ⟨z, hzU⟩) = (kf i ≫ W.ι) ⟨z, hzU⟩ := rfl
      _ = ((f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i) ⟨z, hzU⟩ :=
        congrArg (fun q => q ⟨z, hzU⟩) (hfac i)
      _ = Limits.Sigma.ι Z i z := by
        show Limits.Sigma.ι Z i (((f i ⁻¹ᵁ U).ι ⟨z, hzU⟩)) = _
        simp
      _ = W.ι x := hpoint
  have hopenComp (i : ι) : IsOpenImmersion
      ((f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i) := inferInstance
  let (i : ι) : IsOpenImmersion (kf i) := inferInstance
  have hk : IsIso (Limits.Sigma.desc kf) :=
    isIso_sigmaDesc_of_disjointOpenCover (fun i => (f i ⁻¹ᵁ U).toScheme) kf
      hdisjoint hcoverW
  have hh : IsIso (Limits.Sigma.desc (fun i => f i ∣_ U)) :=
    isIso_sigmaDesc_restrict_complement_overlap Z f hcover
  have hcomponent (i : ι) : kf i ≫ g ∣_ U = f i ∣_ U := by
    apply (cancel_mono U.ι).1
    calc
      (kf i ≫ g ∣_ U) ≫ U.ι = kf i ≫ (g ∣_ U ≫ U.ι) := by rw [Category.assoc]
      _ = kf i ≫ (W.ι ≫ g) := by rw [morphismRestrict_ι]
      _ = (kf i ≫ W.ι) ≫ g := by rw [Category.assoc]
      _ = ((f i ⁻¹ᵁ U).ι ≫ Limits.Sigma.ι Z i) ≫ g := by rw [hfac]
      _ = (f i ⁻¹ᵁ U).ι ≫ (Limits.Sigma.ι Z i ≫ g) := by rw [Category.assoc]
      _ = (f i ⁻¹ᵁ U).ι ≫ f i := by
        show (f i ⁻¹ᵁ U).ι ≫ (Limits.Sigma.ι Z i ≫ Limits.Sigma.desc f) = _
        rw [Limits.Sigma.ι_desc]
      _ = (f i ∣_ U) ≫ U.ι := (morphismRestrict_ι (f i) U).symm
  have hcomp : Limits.Sigma.desc kf ≫ g ∣_ U =
      Limits.Sigma.desc (fun i => f i ∣_ U) := by
    apply Limits.Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
    exact hcomponent i
  have hresult : g ∣_ U = inv (Limits.Sigma.desc kf) ≫
      Limits.Sigma.desc (fun i => f i ∣_ U) := by
    rw [← hcomp]
    simp
  let : IsIso (g ∣_ U) := hresult ▸ (inferInstance : IsIso
    (inv (Limits.Sigma.desc kf) ≫ Limits.Sigma.desc (fun i => f i ∣_ U)))
  infer_instance

/-- Along an open immersion `f`, the pullback of the pushforward of a module `M` is `M` again:
the restriction along `f` composed with the counit of the restriction-pushforward adjunction. -/
public noncomputable def pullback_pushforward_self {Y X : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M : Y.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj M) ≅ M := by
  exact ((Scheme.Modules.restrictFunctorIsoPullback f).app
      ((Scheme.Modules.pushforward f).obj M)).symm ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso f).app M

/-- A module over the zero ring is a subsingleton. -/
public theorem subsingleton_module_of_subsingleton_ring {R M : Type u} [Ring R]
    [AddCommGroup M] [Module R M] [Subsingleton R] : Subsingleton M :=
  Module.subsingleton R M

/-- Restricting along an open immersion `f` a module pushed forward along an open immersion `g`
with range disjoint from that of `f` gives the zero module. -/
public theorem restrict_pushforward_isZero_of_disjoint {Y Z X : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (hdisjoint : Disjoint (Set.range ⇑f) (Set.range ⇑g)) (M : Z.Modules) :
    Limits.IsZero
      ((Scheme.Modules.restrictFunctor f).obj ((Scheme.Modules.pushforward g).obj M)) := by
  let Q := (Scheme.Modules.restrictFunctor f).obj ((Scheme.Modules.pushforward g).obj M)
  have hpre (V : Y.Opens) : g ⁻¹ᵁ (f ''ᵁ V) = ⊥ := by
    refine le_antisymm (fun z hz ↦ ?_) bot_le
    change g z ∈ f ''ᵁ V at hz
    obtain ⟨y, hyV, hy⟩ := hz
    exact (Set.disjoint_left.mp hdisjoint ⟨y, rfl⟩ ⟨z, hy.symm⟩).elim
  have hsections (V : Y.Opens) : Subsingleton (Γ(Q, V)) := by
    rw [Scheme.Modules.restrict_obj, Scheme.Modules.pushforward_obj_obj, hpre]
    let : Subsingleton Γ(Z, (⊥ : Z.Opens)) := inferInstance
    exact @subsingleton_module_of_subsingleton_ring
      (Γ(Z, (⊥ : Z.Opens))) (Γ(M, (⊥ : Z.Opens))) _ _ _ inferInstance
  let Q' := (Scheme.Modules.toPresheafOfModules Y).obj Q
  have hQ' : Limits.IsZero Q' := by
    refine ⟨?_, ?_⟩
    · intro N
      refine ⟨⟨⟨(0 : Q' ⟶ N)⟩, ?_⟩⟩
      intro φ
      apply PresheafOfModules.hom_ext
      intro V
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hx : x = 0 := hsections V.unop |>.elim x 0
      simp [hx]
    · intro N
      refine ⟨⟨⟨(0 : N ⟶ Q')⟩, ?_⟩⟩
      intro φ
      apply PresheafOfModules.hom_ext
      intro V
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact hsections V.unop |>.elim _ _
  exact Limits.IsZero.of_full_of_faithful_of_isZero
    (Scheme.Modules.toPresheafOfModules Y) Q hQ'

/-- The module on the coproduct `∐ Z` assembled from modules `L i` on the summands: the
coproduct of their pushforwards along the summand inclusions. -/
public noncomputable def moduleOnSchemeSigma {ι : Type v} [Finite ι] [Small.{u} ι]
    (Z : ι → Scheme.{u}) (L : ∀ i, (Z i).Modules) : (∐ Z).Modules :=
  ∐ fun i => (Scheme.Modules.pushforward (Limits.Sigma.ι Z i)).obj (L i)

/-- The pullback of `moduleOnSchemeSigma Z L` to the `i`-th summand is `L i`. -/
public noncomputable def pullback_moduleOnSchemeSigma {ι : Type v} [Finite ι]
    [Small.{u} ι] (Z : ι → Scheme.{u}) (L : ∀ i, (Z i).Modules) (i : ι) :
    (Scheme.Modules.pullback (Limits.Sigma.ι Z i)).obj (moduleOnSchemeSigma Z L) ≅ L i := by
  classical
  let A : ι → (∐ Z).Modules := fun j =>
    (Scheme.Modules.pushforward (Limits.Sigma.ι Z j)).obj (L j)
  let F := Scheme.Modules.pullback (Limits.Sigma.ι Z i)
  let B : ι → (Z i).Modules := fun j => F.obj (A j)
  have hdisjoint (j k : ι) (hjk : j ≠ k) :
      Disjoint (Set.range ⇑(Limits.Sigma.ι Z j)) (Set.range ⇑(Limits.Sigma.ι Z k)) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨yj, rfl⟩ ⟨yk, hyk⟩
    exact hjk (congrArg Sigma.fst ((sigmaι_eq_iff Z j k yj yk).mp hyk.symm))
  have hzero (j : ι) (hji : j ≠ i) : Limits.IsZero (B j) := by
    let hR := restrict_pushforward_isZero_of_disjoint (Limits.Sigma.ι Z i)
      (Limits.Sigma.ι Z j) (hdisjoint i j (Ne.symm hji)) (L j)
    exact Limits.IsZero.of_iso hR
      ((Scheme.Modules.restrictFunctorIsoPullback (Limits.Sigma.ι Z i)).app (A j)).symm
  let eSelf : B i ≅ L i := pullback_pushforward_self (Limits.Sigma.ι Z i) (L i)
  let inj : ∀ j, B j ⟶ L i := fun j => if hji : j = i then
    eqToHom (by subst j; rfl) ≫ eSelf.hom else (hzero j hji).to_ (L i)
  let hpres := preservesColimitIso F (Discrete.functor A)
  let D := Discrete.functor A ⋙ F
  let c' : Cocone D := Cocone.mk (L i) (Discrete.natTrans fun j => inj j.as)
  have hc' : IsColimit c' := by
    refine IsColimit.mk (fun s => eSelf.inv ≫ s.ι.app ⟨i⟩) ?_ ?_
    · intro s j
      by_cases hji : j.as = i
      · have hj : j = ⟨i⟩ := Discrete.ext hji
        subst j
        simp [c', inj, eSelf]
      · exact (hzero j.as hji).eq_of_src _ _
    · intro s m hm
      have hmi : eSelf.hom ≫ m = s.ι.app ⟨i⟩ := by
        simpa [c', inj, eSelf] using hm ⟨i⟩
      simp [← hmi]
  let hstd := colimit.isColimit D
  let eCofan := IsColimit.coconePointUniqueUpToIso hc' hstd
  exact hpres ≪≫ eCofan.symm

/-- If every `L i` is invertible, then `moduleOnSchemeSigma Z L` is free of rank one on a
neighbourhood of each point of `∐ Z`. -/
public theorem moduleOnSchemeSigma_exists_local_free
    {ι : Type v} [Finite ι] [Small.{u} ι]
    (Z : ι → Scheme.{u}) (L : ∀ i, (Z i).Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible (Z i).presheaf (Z i).ringCatSheaf.2 (L i)]
    (x : ↥(∐ Z)) :
    ∃ (U : (∐ Z).Opens) (_ : x ∈ U) (I : Type u),
      Nonempty ((moduleOnSchemeSigma Z L).restrict U.ι ≅ SheafOfModules.free I) ∧
      Nonempty (I ≃ Fin 1) := by
  classical
  obtain ⟨i, y, hy⟩ := exists_component_point_of_sigma Z x
  let Yi := Z i
  let Mi := L i
  obtain ⟨q, hq, hrank⟩ :=
    (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible
      Yi Mi).exists_isFiniteLocallyFreeOfRankData
  have hycover : y ∈ ⨆ j, q.X j := by
    rw [(Opens.coversTop_iff Yi q.X).mp q.coversTop]
    simp
  rw [TopologicalSpace.Opens.mem_iSup] at hycover
  obtain ⟨j, hyV⟩ := hycover
  let V : (Z i).Opens := q.X j
  let : IsIso (q.generators j).π := hq.isIso j
  let G := (Scheme.Modules.overEquiv V).functor
  let eFree := freeOverEquivIso V (q.generators j).I
  let eV : Mi.restrict V.ι ≅ SheafOfModules.free (q.generators j).I :=
    (eFree ≪≫ G.mapIso (asIso (q.generators j).π) ≪≫
      (Scheme.Modules.overFunctorEquiv V).app Mi).symm
  let eI : (q.generators j).I ≃ Fin 1 := (hrank j).some
  let f := Limits.Sigma.ι Z i
  let U : (∐ Z).Opens := f ''ᵁ V
  let eImg := f.isoImage V
  let N := (moduleOnSchemeSigma Z L).restrict U.ι
  let GF := Scheme.Modules.restrictFunctor eImg.hom
  let GG := Scheme.Modules.restrictFunctor eImg.inv
  let eCompFiber : (Scheme.Modules.restrictFunctor f).obj
      (moduleOnSchemeSigma Z L) ≅ Mi :=
    (Scheme.Modules.restrictFunctorIsoPullback f).app (moduleOnSchemeSigma Z L) ≪≫
      pullback_moduleOnSchemeSigma Z L i
  let eComp : (Scheme.Modules.restrictFunctor (V.ι ≫ f)).obj
      (moduleOnSchemeSigma Z L) ≅ Mi.restrict V.ι :=
    (Scheme.Modules.restrictFunctorComp V.ι f).app (moduleOnSchemeSigma Z L) ≪≫
      (Scheme.Modules.restrictFunctor V.ι).mapIso eCompFiber
  have hEq : eImg.hom ≫ U.ι = V.ι ≫ f := Scheme.Hom.isoImage_hom_ι f V
  let eToComp : GF.obj N ≅ Mi.restrict V.ι :=
    ((Scheme.Modules.restrictFunctorComp eImg.hom U.ι).app (moduleOnSchemeSigma Z L)).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hEq).app (moduleOnSchemeSigma Z L) ≪≫
      eComp
  let eFiber : GF.obj N ≅ SheafOfModules.free (q.generators j).I := eToComp ≪≫ eV
  let eRound : N ≅ GG.obj (GF.obj N) :=
    ((Scheme.Modules.restrictFunctorId (X := U.toScheme)).app N).symm ≪≫
      ((Scheme.Modules.restrictFunctorCongr eImg.inv_hom_id).app N).symm ≪≫
      (Scheme.Modules.restrictFunctorComp eImg.inv eImg.hom).app N
  have : PreservesColimitsOfShape (Discrete (q.generators j).I) GG :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint GG
  let eFreeInv := @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ GG
    (q.generators j).I ‹PreservesColimitsOfShape (Discrete (q.generators j).I) GG›
    (Scheme.Modules.restrictUnitIso eImg.inv).symm
  let eU : N ≅ SheafOfModules.free (q.generators j).I :=
    eRound ≪≫ GG.mapIso eFiber ≪≫ eFreeInv.symm
  exact ⟨U, by
    show x ∈ f '' V
    exact ⟨y, hyV, hy⟩,
    (q.generators j).I, ⟨eU⟩, ⟨eI⟩⟩

/-- Invertible sheaves on a finite closed cover of a reduced scheme extend when
pairwise intersections are discrete. -/
@[stacks 09NE "existence of an invertible sheaf"]
public theorem exists_invertible_of_closed_cover_discrete_intersections
    {ι : Type v} [Finite ι] (X : Scheme.{u}) [IsReduced X]
    (Z : ι → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (hcover : ∀ x : X, ∃ i z, f i z = x)
    (hdiscrete : ∀ i j, i ≠ j → DiscreteTopology
      (↥(Set.range (f i) ∩ Set.range (f j) : Set X)))
    (L : ∀ i, (Z i).Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible (Z i).presheaf (Z i).ringCatSheaf.2 (L i)] :
    ∃ (M : X.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M),
      ∀ i, Nonempty ((modulePullback (f i).toLRSHom.toShHom).obj M ≅ L i) := by
  classical
  let g : (∐ Z) ⟶ X := Limits.Sigma.desc f
  let U : X.Opens :=
    ⟨(overlapLocus X Z f)ᶜ, (overlapLocus_closed X Z f).isOpen_compl⟩
  let S : Scheme.{u} := ∐ Z
  let Lcop : (∐ Z).Modules := moduleOnSchemeSigma Z L
  have hLcop : AlgebraicGeometry.SheafOfModules.IsInvertible
      (∐ Z).presheaf (∐ Z).ringCatSheaf.2 Lcop := by
    have hLoc (x : ↥S) :=
      moduleOnSchemeSigma_exists_local_free Z L (show ↥(∐ Z) from x)
    choose U hU I e eI using hLoc
    let q := localGeneratorsDataOfTrivializations Lcop U hU I e
    have hq := localGeneratorsDataOfTrivializations_isLocallyFreeData Lcop U hU I e
    have hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
        (C := TopologicalSpace.Opens S)
        (J := Opens.grothendieckTopology S) Lcop 1 :=
      @AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.mk.{u, u, u}
        (TopologicalSpace.Opens S) _
        (Opens.grothendieckTopology S) S.ringCatSheaf _ _ Lcop 1
        ⟨q, hq, eI⟩
    exact (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry
        S.toRingedSpace.presheaf
        (structureSheafRing S.toRingedSpace).property
          Lcop).1
      (Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one
        (h := hflf) S.toRingedSpace Lcop)
  have : IsFinite g := inferInstance
  have : IsIso (g ∣_ U) := isIso_sigmaDesc_morphismRestrict_complement_overlap Z f hcover
  have : DiscreteTopology (Uᶜ : Set X) := overlapComplement_discrete X Z f hdiscrete
  obtain ⟨M, hM, hMpull⟩ :=
    Stacks.PicFinite.exists_isInvertible_modulePullback_iso g U Lcop hLcop
  obtain ⟨eM⟩ := hMpull
  refine ⟨M, hM, fun i ↦ ?_⟩
  have hdesc : Limits.Sigma.ι Z i ≫ g = f i := by
    dsimp [g]
    rw [Limits.Sigma.ι_desc]
  let eEq : (Scheme.Modules.pullback (Limits.Sigma.ι Z i ≫ g)).obj M ≅
      (Scheme.Modules.pullback (f i)).obj M :=
    eqToIso (congrArg (fun q => (Scheme.Modules.pullback q).obj M) hdesc)
  let eComp := (Scheme.Modules.pullbackComp (Limits.Sigma.ι Z i) g).app M
  have eFiber : (Scheme.Modules.pullback (Limits.Sigma.ι Z i)).obj Lcop ≅ L i :=
    pullback_moduleOnSchemeSigma Z L i
  refine ⟨eEq.symm.trans (eComp.symm.trans ?_)⟩
  exact ((Scheme.Modules.pullback (Limits.Sigma.ι Z i)).mapIso eM).trans eFiber

end StacksTag09NE

end
