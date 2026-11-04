module

import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsAtAnOpenFromTheCover
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.OpenSubspaceRestrictionBridge
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.FullnessOfExtensionByZeroDerived

/-!
# The vanishing clause of Tag 0D68 for a collection covering only an open

Let `(X, 𝒪_X)` be a ringed space, let `S` be a system of locally given derived objects on it
(Situation [Stacks, Tag 0D67]) and let `𝒟` be a subcollection of its displayed opens.  Let `O` be
an open that `𝒟` covers and let `K`, `L` be objects given *only over* `O` whose displayed
restrictions to the members of `𝒟` below `O` admit no morphisms of negative degree.  This file
proves that the same vanishing holds over every open `P ≤ O` that `𝒟` covers: [Stacks, Tag 0D66]
part (1) with the collection covering only `O` rather than the whole of `X`.  As a consequence
`Stacks.DerivedGlueing.HasGlobalNegativeExtVanishing S O`, and with it
`Stacks.DerivedGlueing.HasGluingForHomsAt S O`, `Stacks.DerivedGlueing.HasGluingForHomsOver S` and
`Stacks.DerivedGlueing.HasUniqueSolutionOverIso S`, hold at every open the collection covers.

## Main definitions

* `Stacks.DerivedGlueing.restrictedOpen` and `Stacks.DerivedGlueing.restrictedCollection` — an
  open of `X` below `O`, and a collection of them, read inside the open subspace `X|O`.
* `Stacks.DerivedGlueing.subspaceCompare` — the comparison of `(X|O)|W'` with `X|W`.
* `Stacks.DerivedGlueing.restrictionIsoSubspaceSlice` — the displayed restriction of an object
  over `O` to a smaller open, read inside `X|O`.

## Main results

* `Stacks.DerivedGlueing.subsingleton_shiftedHom_restrict_on_subcollection` — [Stacks, Tag 0D66]
  part (1) with the collection covering only `O`.
* `Stacks.DerivedGlueing.subsingleton_shiftedHom_of_subcollection` — the same read at the open
  `⊤` of `X|O`.
* `Stacks.DerivedGlueing.hasGlobalNegativeExtVanishing_of_sSup_covered` —
  `Stacks.DerivedGlueing.HasGlobalNegativeExtVanishing S O` at every open `O` the collection
  covers.
* `Stacks.DerivedGlueing.hasGluingForHomsAt_of_covers`,
  `Stacks.DerivedGlueing.hasGluingForHomsOver_of_covers` and
  `Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_covers` — the sheaf condition of
  [Stacks, Tag 0D66] part (2) in the vocabulary of Situation 0D67, and the uniqueness clause of
  [Stacks, Tag 0D68] relativized to every open the collection covers.
* `Stacks.DerivedGlueing.exists_unique_overlapIso_of_covers` and
  `Stacks.DerivedGlueing.restrictOverlapHom_cocycle_of_covers` — the comparison isomorphism over
  an overlap and the cocycle condition of [Stacks, Tag 0D69], under the hypotheses (1) and (2) of
  [Stacks, Tag 0D68].

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D69](https://stacks.math.columbia.edu/tag/0D69)
* [Stacks Project, Tag 0D5Q](https://stacks.math.columbia.edu/tag/0D5Q)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction
open AlgebraicGeometry.RingedSpace.CorrespondingOpens (ofBase)

namespace Stacks.DerivedGlueing

universe u

variable {X : RingedSpace.{u, u}}

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-! ### A collection of opens below `O`, read inside the open subspace `X|O` -/

/-- **An open of `X` contained in `O`, read as an open of the subspace `X|O`**: the inverse image
of the open along the inclusion of `O`, which is what
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.ofBase` attaches to it. -/
abbrev restrictedOpen (O W : Opens X.carrier) :
    Opens (X.restrict O.isOpenEmbedding).carrier :=
  (Opens.map O.inclusion').obj W

/-- The open of the subspace attached by
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.ofBase` is
`Stacks.DerivedGlueing.restrictedOpen`. -/
theorem ofBase_sub_eq {O W : Opens X.carrier} (hWO : W ≤ O) :
    (ofBase hWO).sub = restrictedOpen O W := rfl

/-- Reading an open of `X` inside the subspace `X|O` is monotone. -/
theorem restrictedOpen_mono {O W W' : Opens X.carrier} (h : W ≤ W') :
    restrictedOpen O W ≤ restrictedOpen O W' := fun _ hp ↦ h hp

/-- **A collection of opens of `X`, read inside the open subspace `X|O`**: the opens of `X|O`
attached to the members of the collection that are contained in `O`. -/
def restrictedCollection (O : Opens X.carrier) (𝒟 : Set (Opens X.carrier)) :
    Set (Opens (X.restrict O.isOpenEmbedding).carrier) :=
  {V | ∃ W, W ∈ 𝒟 ∧ W ≤ O ∧ restrictedOpen O W = V}

/-- A member of the collection contained in `O` is seen by the restricted collection. -/
theorem restrictedOpen_mem_restrictedCollection {O W : Opens X.carrier}
    {𝒟 : Set (Opens X.carrier)} (hW : W ∈ 𝒟) (hWO : W ≤ O) :
    restrictedOpen O W ∈ restrictedCollection O 𝒟 := ⟨W, hW, hWO, rfl⟩

/-- **The restricted collection covers the open subspace.**  If `O` is the union of the members of
`𝒟` contained in it, the restricted collection covers all of `X|O`. -/
theorem sSup_restrictedCollection {O : Opens X.carrier} {𝒟 : Set (Opens X.carrier)}
    (hO : O = sSup {W | W ∈ 𝒟 ∧ W ≤ O}) : sSup (restrictedCollection O 𝒟) = ⊤ := by
  refine top_le_iff.mp fun (p : ↥O) _ ↦ ?_
  obtain ⟨W, hW, hpW⟩ := Opens.mem_sSup.mp (hO.le p.2)
  exact Opens.mem_sSup.mpr ⟨restrictedOpen O W,
    restrictedOpen_mem_restrictedCollection hW.1 hW.2, hpW⟩

/-- **The pairwise intersections of the restricted collection are unions of its members**, when
those of `𝒟` are. -/
theorem inf_eq_sSup_restrictedCollection {O : Opens X.carrier} {𝒟 : Set (Opens X.carrier)}
    (hinter : ∀ U ∈ 𝒟, ∀ V ∈ 𝒟, U ⊓ V = sSup {W | W ∈ 𝒟 ∧ W ≤ U ⊓ V}) :
    ∀ A ∈ restrictedCollection O 𝒟, ∀ B ∈ restrictedCollection O 𝒟,
      A ⊓ B = sSup {V | V ∈ restrictedCollection O 𝒟 ∧ V ≤ A ⊓ B} := by
  rintro A ⟨U, hU, hUO, rfl⟩ B ⟨V, hV, -, rfl⟩
  refine le_antisymm (fun (p : ↥O) hp ↦ ?_) (sSup_le fun _ h ↦ h.2)
  have hpUV : (p : X.carrier) ∈ U ⊓ V := ⟨hp.1, hp.2⟩
  rw [hinter U hU V hV] at hpUV
  obtain ⟨R, hR, hpR⟩ := Opens.mem_sSup.mp hpUV
  exact Opens.mem_sSup.mpr ⟨restrictedOpen O R,
    ⟨restrictedOpen_mem_restrictedCollection hR.1 (hR.2.trans (inf_le_left.trans hUO)),
      le_inf (restrictedOpen_mono (hR.2.trans inf_le_left))
        (restrictedOpen_mono (hR.2.trans inf_le_right))⟩, hpR⟩

/-- **An open below `O` that the collection covers is, inside `X|O`, the union of the members of
the restricted collection contained in it.** -/
theorem sSup_covered_restrictedCollection {O P : Opens X.carrier} {𝒟 : Set (Opens X.carrier)}
    (hPO : P ≤ O) (hP : P = sSup {W | W ∈ 𝒟 ∧ W ≤ P}) :
    restrictedOpen O P =
      sSup {V | V ∈ restrictedCollection O 𝒟 ∧ V ≤ restrictedOpen O P} := by
  refine le_antisymm (fun (p : ↥O) hp ↦ ?_) (sSup_le fun _ h ↦ h.2)
  obtain ⟨W, hW, hpW⟩ := Opens.mem_sSup.mp (hP.le hp)
  exact Opens.mem_sSup.mpr ⟨restrictedOpen O W,
    ⟨restrictedOpen_mem_restrictedCollection hW.1 (hW.2.trans hPO),
      restrictedOpen_mono hW.2⟩, hpW⟩

/-- **The open subspace is itself the union of the members of the restricted collection.** -/
theorem top_eq_sSup_restrictedCollection {O : Opens X.carrier} {𝒟 : Set (Opens X.carrier)}
    (hO : O = sSup {W | W ∈ 𝒟 ∧ W ≤ O}) :
    (⊤ : Opens (X.restrict O.isOpenEmbedding).carrier) =
      sSup {V | V ∈ restrictedCollection O 𝒟 ∧ V ≤ ⊤} := by
  have hset : {V | V ∈ restrictedCollection O 𝒟 ∧
      V ≤ (⊤ : Opens (X.restrict O.isOpenEmbedding).carrier)} = restrictedCollection O 𝒟 :=
    Set.ext fun _ ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, le_top⟩⟩
  rw [hset, sSup_restrictedCollection hO]

/-! ### The comparison of `(X|O)|W'` with `X|W`, in the spelling of Situation 0D67 -/

section Compare

variable {O W : Opens X.carrier}

/-- **The comparison of the doubly restricted space `(X|O)|W'` with the singly restricted space
`X|W`, with its source category of modules named through
`structureSheafRing (X|O)`.**  It is `AlgebraicGeometry.RingedSpace.CorrespondingOpens.compare`
with the structure sheaves of rings named differently. -/
def subspaceCompare (hWO : W ≤ O) :
    SheafOfModules.{u} (resRing (ofBase hWO).sub
        (structureSheafRing (X.restrict O.isOpenEmbedding))) ⥤
      SheafOfModules.{u} (restrictedRingSheaf X W) :=
  (ofBase hWO).compare

/-- **The comparison, as an equivalence**, in the same spelling. -/
def subspaceCompareEquiv (hWO : W ≤ O) :
    SheafOfModules.{u} (resRing (ofBase hWO).sub
        (structureSheafRing (X.restrict O.isOpenEmbedding))) ≌
      SheafOfModules.{u} (restrictedRingSheaf X W) :=
  (ofBase hWO).compareEquiv

/-- The comparison is the functor of the comparison equivalence. -/
theorem subspaceCompareEquiv_functor (hWO : W ≤ O) :
    (subspaceCompareEquiv hWO).functor = subspaceCompare hWO := rfl

/-- The comparison is additive. -/
instance subspaceCompare_additive (hWO : W ≤ O) : (subspaceCompare hWO).Additive :=
  inferInstanceAs ((ofBase hWO).compare).Additive

/-- The comparison preserves finite limits. -/
instance subspaceCompare_preservesFiniteLimits (hWO : W ≤ O) :
    PreservesFiniteLimits (subspaceCompare hWO) :=
  inferInstanceAs (PreservesFiniteLimits ((ofBase hWO).compare))

/-- The comparison preserves finite colimits. -/
instance subspaceCompare_preservesFiniteColimits (hWO : W ≤ O) :
    PreservesFiniteColimits (subspaceCompare hWO) :=
  inferInstanceAs (PreservesFiniteColimits ((ofBase hWO).compare))

/-- The functor of the comparison equivalence is additive. -/
instance subspaceCompareEquiv_functor_additive (hWO : W ≤ O) :
    (subspaceCompareEquiv hWO).functor.Additive :=
  inferInstanceAs ((ofBase hWO).compare).Additive

/-- The inverse of the comparison equivalence is additive. -/
instance subspaceCompareEquiv_inverse_additive (hWO : W ≤ O) :
    (subspaceCompareEquiv hWO).inverse.Additive :=
  Equivalence.inverse_additive _

/-- **The comparison is fully faithful on unbounded derived categories.** -/
def subspaceCompareDerivedFullyFaithful (hWO : W ≤ O) :
    (subspaceCompare hWO).mapDerivedCategory.FullyFaithful :=
  letI := faithful_mapDerivedCategory_of_comp (subspaceCompare hWO)
    (subspaceCompareEquiv hWO).inverse (subspaceCompareEquiv hWO).unitIso.symm
  letI := full_mapDerivedCategory_of_equivalence (subspaceCompare hWO)
    (subspaceCompareEquiv hWO).inverse (subspaceCompareEquiv hWO).unitIso
    (subspaceCompareEquiv hWO).counitIso
  Functor.FullyFaithful.ofFullyFaithful _

/-- **Restriction inside `X|O` to the open attached to `W`, followed by the comparison with
`X|W`**, with its source category of modules named as Situation 0D67 names it. -/
def subspaceRestrictCompare (hWO : W ≤ O) :
    SheafOfModules.{u} (restrictedRingSheaf X O) ⥤
      SheafOfModules.{u} (restrictedRingSheaf X W) :=
  jStar (ofBase hWO).sub (structureSheafRing (X.restrict O.isOpenEmbedding)) ⋙
    subspaceCompare hWO

/-- The composite is additive. -/
instance subspaceRestrictCompare_additive (hWO : W ≤ O) :
    (subspaceRestrictCompare hWO).Additive :=
  inferInstanceAs (jStar (ofBase hWO).sub
    (structureSheafRing (X.restrict O.isOpenEmbedding)) ⋙ subspaceCompare hWO).Additive

/-- The composite preserves finite limits. -/
instance subspaceRestrictCompare_preservesFiniteLimits (hWO : W ≤ O) :
    PreservesFiniteLimits (subspaceRestrictCompare hWO) :=
  inferInstanceAs (PreservesFiniteLimits (jStar (ofBase hWO).sub
    (structureSheafRing (X.restrict O.isOpenEmbedding)) ⋙ subspaceCompare hWO))

/-- The composite preserves finite colimits. -/
instance subspaceRestrictCompare_preservesFiniteColimits (hWO : W ≤ O) :
    PreservesFiniteColimits (subspaceRestrictCompare hWO) :=
  inferInstanceAs (PreservesFiniteColimits (jStar (ofBase hWO).sub
    (structureSheafRing (X.restrict O.isOpenEmbedding)) ⋙ subspaceCompare hWO))

/-- **Restriction inside `X|O` to the open attached to `W`, followed by the comparison with
`X|W`, is the restriction `Stacks.DerivedGlueing.openModuleRestriction` from `O` to `W`.** -/
def subspaceRestrictCompareIso (hWO : W ≤ O) :
    subspaceRestrictCompare hWO ≅ openModuleRestriction X W O hWO :=
  (openModuleRestrictionIsoJStarCompare hWO).symm

end Compare

/-! ### The displayed restriction, read inside the open subspace -/

section Bridge

/-- **The displayed restriction of an object given over `O` to a smaller open `W`, read inside the
ringed space `X|O`.**  It is the restriction of the object to the opens of `X|O` below the open
attached to `W`, read in the open-subspace model and carried along the comparison of `(X|O)|W'`
with `X|W`. -/
def restrictionIsoSubspaceSlice (S : LocallyGiven X) {O W : Opens X.carrier} (hWO : W ≤ O)
    (K : OpenDerivedCategory X O) :
    (S.restriction W O hWO).obj K ≅
      (subspaceCompare hWO).mapDerivedCategory.obj
        ((sliceToSubspace (structureSheafRing (X.restrict O.isOpenEmbedding))
            (ofBase hWO).sub).mapDerivedCategory.obj
          ((SheafOfModules.overFunctor.{u}
            (structureSheafRing (X.restrict O.isOpenEmbedding))
            (ofBase hWO).sub).mapDerivedCategory.obj K)) :=
  ((restrictionIsoMapDerivedCategory S W O hWO).app K) ≪≫
    ((mapDerivedCategoryCongr (subspaceRestrictCompareIso hWO)).app K).symm ≪≫
    ((mapDerivedCategoryCompIso
      (jStar (ofBase hWO).sub (structureSheafRing (X.restrict O.isOpenEmbedding)))
      (subspaceCompare hWO)).app K).symm ≪≫
    (subspaceCompare hWO).mapDerivedCategory.mapIso
      ((Stacks.Homology.mapDerivedCategoryCompIso
        (SheafOfModules.overFunctor.{u} (structureSheafRing (X.restrict O.isOpenEmbedding))
          (ofBase hWO).sub)
        (sliceToSubspace (structureSheafRing (X.restrict O.isOpenEmbedding)) (ofBase hWO).sub)
        (jStar (ofBase hWO).sub (structureSheafRing (X.restrict O.isOpenEmbedding)))
        (eqToIso (overFunctor_comp_sliceToSubspace
          (structureSheafRing (X.restrict O.isOpenEmbedding)) (ofBase hWO).sub))).app K).symm

/-- **The negative-`Ext` hypothesis of Situation 0D67 at an open below `O`, read inside `X|O`.**
If the displayed restrictions of `K` and `L` to `W` admit no morphisms of degree `i`, neither do
their restrictions inside `X|O` to the open attached to `W`. -/
theorem subsingleton_shiftedHom_restrictedOpen_of_restriction (S : LocallyGiven X)
    {O W : Opens X.carrier} (hWO : W ≤ O) (K L : OpenDerivedCategory X O) (i : ℤ)
    (h : Subsingleton (ShiftedHom ((S.restriction W O hWO).obj K)
      ((S.restriction W O hWO).obj L) i)) :
    Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (structureSheafRing (X.restrict O.isOpenEmbedding))
        (ofBase hWO).sub).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} (structureSheafRing (X.restrict O.isOpenEmbedding))
        (ofBase hWO).sub).mapDerivedCategory.obj L) i) := by
  let := (subspaceCompareDerivedFullyFaithful hWO).faithful
  let := faithful_sliceToSubspace_mapDerivedCategory
    (structureSheafRing (X.restrict O.isOpenEmbedding)) (ofBase hWO).sub
  refine subsingleton_shiftedHom_of_faithful
    (sliceToSubspace (structureSheafRing (X.restrict O.isOpenEmbedding))
      (ofBase hWO).sub).mapDerivedCategory _ _ i ?_
  refine subsingleton_shiftedHom_of_faithful (subspaceCompare hWO).mapDerivedCategory _ _ i ?_
  exact subsingleton_shiftedHom_of_iso (restrictionIsoSubspaceSlice S hWO K).symm
    (restrictionIsoSubspaceSlice S hWO L).symm i h

/-- **The converse reading: the vanishing inside `X|O` gives the vanishing of the displayed
restriction.** -/
theorem subsingleton_shiftedHom_restriction_of_restrictedOpen (S : LocallyGiven X)
    {O W : Opens X.carrier} (hWO : W ≤ O) (K L : OpenDerivedCategory X O) (i : ℤ)
    (h : Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (structureSheafRing (X.restrict O.isOpenEmbedding))
        (ofBase hWO).sub).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} (structureSheafRing (X.restrict O.isOpenEmbedding))
        (ofBase hWO).sub).mapDerivedCategory.obj L) i)) :
    Subsingleton (ShiftedHom ((S.restriction W O hWO).obj K)
      ((S.restriction W O hWO).obj L) i) := by
  let := (subspaceCompareDerivedFullyFaithful hWO).faithful
  let := (subspaceCompareDerivedFullyFaithful hWO).full
  let := faithful_sliceToSubspace_mapDerivedCategory
    (structureSheafRing (X.restrict O.isOpenEmbedding)) (ofBase hWO).sub
  let := full_sliceToSubspace_mapDerivedCategory
    (structureSheafRing (X.restrict O.isOpenEmbedding)) (ofBase hWO).sub
  refine subsingleton_shiftedHom_of_iso (restrictionIsoSubspaceSlice S hWO K)
    (restrictionIsoSubspaceSlice S hWO L) i ?_
  refine subsingleton_shiftedHom_map_of_fullyFaithful
    (subspaceCompare hWO).mapDerivedCategory _ _ i ?_
  exact subsingleton_shiftedHom_map_of_fullyFaithful
    (sliceToSubspace (structureSheafRing (X.restrict O.isOpenEmbedding))
      (ofBase hWO).sub).mapDerivedCategory _ _ i h

end Bridge

/-! ### Tag 0D66 part (1) for a collection covering only an open -/

/-- **The hypothesis of the covering statement, read on the open subspace.** -/
theorem subsingleton_shiftedHom_restrictedCollection (S : LocallyGiven X)
    {𝒟 : Set (Opens X.carrier)} {O : Opens X.carrier} (K L : OpenDerivedCategory X O)
    (hExt : ∀ W ∈ 𝒟, ∀ hWO : W ≤ O, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((S.restriction W O hWO).obj K)
        ((S.restriction W O hWO).obj L) i)) :
    ∀ V ∈ restrictedCollection O 𝒟, ∀ i : ℤ, i < 0 → Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (structureSheafRing (X.restrict O.isOpenEmbedding))
        V).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} (structureSheafRing (X.restrict O.isOpenEmbedding))
        V).mapDerivedCategory.obj L) i) := by
  rintro - ⟨W, hW, hWO, rfl⟩ i hi
  exact subsingleton_shiftedHom_restrictedOpen_of_restriction S hWO K L i (hExt W hW hWO i hi)

/-- The vanishing over an open of `X|O` that the restricted collection covers. -/
private theorem subsingleton_shiftedHom_overFunctor_of_covered (S : LocallyGiven X)
    {𝒟 : Set (Opens X.carrier)} {O : Opens X.carrier}
    (hO : O = sSup {W | W ∈ 𝒟 ∧ W ≤ O})
    (hinter : ∀ U ∈ 𝒟, ∀ V ∈ 𝒟, U ⊓ V = sSup {W | W ∈ 𝒟 ∧ W ≤ U ⊓ V})
    (K L : OpenDerivedCategory X O)
    (hExt : ∀ W ∈ 𝒟, ∀ hWO : W ≤ O, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((S.restriction W O hWO).obj K)
        ((S.restriction W O hWO).obj L) i))
    (P : Opens (X.restrict O.isOpenEmbedding).carrier)
    (hP : P = sSup {V | V ∈ restrictedCollection O 𝒟 ∧ V ≤ P}) (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (structureSheafRing (X.restrict O.isOpenEmbedding))
        P).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} (structureSheafRing (X.restrict O.isOpenEmbedding))
        P).mapDerivedCategory.obj L) i) :=
  subsingleton_shiftedHom_restrict_of_sSup_covered
    (X := X.restrict O.isOpenEmbedding) (restrictedCollection O 𝒟)
    (sSup_restrictedCollection hO) (inf_eq_sSup_restrictedCollection hinter) K L
    (subsingleton_shiftedHom_restrictedCollection S K L hExt) P hP i hi

/-- **[Stacks, Tag 0D66] part (1) with the collection covering only `O`.**  Let `S` be a system of
locally given derived objects on `X`, let `𝒟` be a subcollection of its displayed opens, let `O`
be an open which is the union of the members of `𝒟` contained in it, and assume the intersection
of two members of `𝒟` is the union of the members contained in it.  Let `K`, `L` be objects given
over `O` whose displayed restrictions to the members of `𝒟` below `O` admit no morphisms of
negative degree.  Then for *every* open `P ≤ O` which is the union of the members of `𝒟` contained
in it, the displayed restrictions of `K` and `L` to `P` admit no morphisms of negative degree. -/
theorem subsingleton_shiftedHom_restrict_on_subcollection (S : LocallyGiven X)
    (𝒟 : Set (Opens X.carrier)) (_h𝒟 : 𝒟 ⊆ S.opens) (O : Opens X.carrier)
    (hO : O = sSup {W | W ∈ 𝒟 ∧ W ≤ O})
    (hinter : ∀ U ∈ 𝒟, ∀ V ∈ 𝒟, U ⊓ V = sSup {W | W ∈ 𝒟 ∧ W ≤ U ⊓ V})
    (K L : OpenDerivedCategory X O)
    (hExt : ∀ W ∈ 𝒟, ∀ hWO : W ≤ O, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((S.restriction W O hWO).obj K)
        ((S.restriction W O hWO).obj L) i))
    (P : Opens X.carrier) (hPO : P ≤ O) (hP : P = sSup {W | W ∈ 𝒟 ∧ W ≤ P})
    (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom ((S.restriction P O hPO).obj K)
      ((S.restriction P O hPO).obj L) i) :=
  subsingleton_shiftedHom_restriction_of_restrictedOpen S hPO K L i
    (subsingleton_shiftedHom_overFunctor_of_covered S hO hinter K L hExt
      (restrictedOpen O P) (sSup_covered_restrictedCollection hPO hP) i hi)

/-- **The vanishing clause of [Stacks, Tag 0D68] on the ringed space `O`.**  Under the hypotheses
of `Stacks.DerivedGlueing.subsingleton_shiftedHom_restrict_on_subcollection` the two objects
themselves admit no morphism of negative degree. -/
theorem subsingleton_shiftedHom_of_subcollection (S : LocallyGiven X)
    (𝒟 : Set (Opens X.carrier)) (_h𝒟 : 𝒟 ⊆ S.opens) (O : Opens X.carrier)
    (hO : O = sSup {W | W ∈ 𝒟 ∧ W ≤ O})
    (hinter : ∀ U ∈ 𝒟, ∀ V ∈ 𝒟, U ⊓ V = sSup {W | W ∈ 𝒟 ∧ W ≤ U ⊓ V})
    (K L : OpenDerivedCategory X O)
    (hExt : ∀ W ∈ 𝒟, ∀ hWO : W ≤ O, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((S.restriction W O hWO).obj K)
        ((S.restriction W O hWO).obj L) i))
    (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom K L i) :=
  subsingleton_shiftedHom_of_overTop (structureSheafRing (X.restrict O.isOpenEmbedding)) K L i
    (subsingleton_shiftedHom_overFunctor_of_covered S hO hinter K L hExt ⊤
      (top_eq_sSup_restrictedCollection hO) i hi)

/-! ### The residual of the glueing of morphisms, discharged -/

/-- **The vanishing clause of [Stacks, Tag 0D68] at every open the collection covers.**  If the
intersection of two displayed opens is the union of the displayed opens contained in it, then
`Stacks.DerivedGlueing.HasGlobalNegativeExtVanishing S O` holds at every open `O` which is the
union of the displayed opens contained in it. -/
theorem hasGlobalNegativeExtVanishing_of_sSup_covered (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    {O : Opens X.carrier} (hO : O = sSup {W | W ∈ S.opens ∧ W ≤ O}) :
    HasGlobalNegativeExtVanishing S O := by
  intro K L hExt i hi
  let := faithful_jShriek_mapDerivedCategory (underlyingRingSheaf X) O
  let := full_jShriek_mapDerivedCategory (underlyingRingSheaf X) O
  exact subsingleton_shiftedHom_map_of_fullyFaithful
    (jShriek O (underlyingRingSheaf X)).mapDerivedCategory K L i
    (subsingleton_shiftedHom_of_subcollection S S.opens (subset_refl _) O hO hinter K L hExt i hi)

/-- **The sheaf condition of [Stacks, Tag 0D66] part (2) at an arbitrary open the collection
covers.** -/
theorem hasGluingForHomsAt_of_covers (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    {O : Opens X.carrier} (hO : O = sSup {W | W ∈ S.opens ∧ W ≤ O}) :
    HasGluingForHomsAt S O :=
  hasGluingForHomsAt_of_sSup_covered S hinter hO
    (hasGlobalNegativeExtVanishing_of_sSup_covered S hinter hO)

/-- **The sheaf condition of [Stacks, Tag 0D66] part (2) in the vocabulary of Situation 0D67.**
`Stacks.DerivedGlueing.HasGluingForHomsOver S` holds for every system `S`. -/
theorem hasGluingForHomsOver_of_covers (S : LocallyGiven X) :
    HasGluingForHomsOver S :=
  fun _ hO hinter ↦ hasGluingForHomsAt_of_covers S hinter hO

/-- **The uniqueness clause of [Stacks, Tag 0D68], relativized to every open the collection
covers.**  Only hypothesis (1) of [Stacks, Tag 0D68] on intersections is taken; the collection is
not required to cover `X`. -/
theorem hasUniqueSolutionOverIso_of_covers (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V}) :
    HasUniqueSolutionOverIso S :=
  hasUniqueSolutionOverIso_of_covers_of_vanishing S
    fun _ hO ↦ hasGlobalNegativeExtVanishing_of_sSup_covered S hinter hO

/-! ### The two clauses of Tag 0D69, with nothing granted -/

/-- **The comparison isomorphism over an overlap.**  For members `U` and `V` of the collection
there is a unique isomorphism `ρ_{U,V} : K_U|_{U ∩ V} ≅ K_V|_{U ∩ V}` compatible with the
prescribed transitions on the members contained in `U ∩ V`.  Here `hinter` is hypothesis (1) of
[Stacks, Tag 0D68] and `hExt` is its hypothesis (2); the collection need not cover `X`. -/
@[stacks 0D69 "the comparison isomorphism over an overlap: for `U, V ∈ ℬ` a unique isomorphism
  `K_U|_{U ⊓ V} ≅ K_V|_{U ⊓ V}` compatible with the prescribed transitions on the members of `ℬ`
  contained in `U ⊓ V`, for a collection satisfying `hinter` (condition (1) of 0D68) and `hExt`
  (condition (2) of 0D68)"]
theorem exists_unique_overlapIso_of_covers (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (U V : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens) :
    ∃! φ : (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hU) ≅
        (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hV),
      IsOverlapHom S hU hV inf_le_left inf_le_right φ.hom :=
  exists_unique_overlapIso_of_covers_of_vanishing S hinter hExt U V hU hV
    (hasGlobalNegativeExtVanishing_of_sSup_covered S hinter (hinter U hU V hV))

/-- **The cocycle condition over a triple intersection.**  For members `U`, `V` and `W` and
compatible isomorphisms over the three overlaps, `ρ_{U,W} = ρ_{V,W} ∘ ρ_{U,V}` over `U ∩ V ∩ W`.
By `Stacks.DerivedGlueing.exists_unique_overlapIso_of_covers` the compatible isomorphisms over the
overlaps are unique. -/
@[stacks 0D69 "the cocycle condition `ρ_{U,W} = ρ_{V,W} ∘ ρ_{U,V}` over a triple intersection,
  for any three compatible isomorphisms over the three overlaps -- which by
  `exists_unique_overlapIso_of_covers` are the source's own `ρ_{U,V}`, `ρ_{V,W}` and `ρ_{U,W}`,
  being the unique compatible ones -- for a collection satisfying `hinter` (condition (1) of
  0D68) and `hExt` (condition (2) of 0D68)"]
theorem restrictOverlapHom_cocycle_of_covers (S : LocallyGiven X)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (U V W : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens) (hW : W ∈ S.opens)
    (φUV : (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hU) ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hV))
    (hφUV : IsOverlapHom S hU hV inf_le_left inf_le_right φUV.hom)
    (φVW : (S.restriction (V ⊓ W) V inf_le_left).obj (S.obj V hV) ≅
      (S.restriction (V ⊓ W) W inf_le_right).obj (S.obj W hW))
    (hφVW : IsOverlapHom S hV hW inf_le_left inf_le_right φVW.hom)
    (φUW : (S.restriction (U ⊓ W) U inf_le_left).obj (S.obj U hU) ≅
      (S.restriction (U ⊓ W) W inf_le_right).obj (S.obj W hW))
    (hφUW : IsOverlapHom S hU hW inf_le_left inf_le_right φUW.hom) :
    restrictOverlapHom S hU hW inf_le_left inf_le_right
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right : U ⊓ V ⊓ W ≤ U ⊓ W) φUW.hom =
      restrictOverlapHom S hU hV inf_le_left inf_le_right
          (inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ V) φUV.hom ≫
        restrictOverlapHom S hV hW inf_le_left inf_le_right
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U ⊓ V ⊓ W ≤ V ⊓ W) φVW.hom :=
  restrictOverlapHom_cocycle_of_covers_of_vanishing S hinter hExt U V W hU hV hW
    (hasGlobalNegativeExtVanishing_of_sSup_covered S hinter
      (inf_inf_eq_sSup S hinter U V W hU hV hW))
    φUV hφUV φVW hφVW φUW hφUW

end Stacks.DerivedGlueing

end
