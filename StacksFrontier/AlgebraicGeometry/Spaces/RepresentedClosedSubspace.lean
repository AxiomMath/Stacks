module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffinePushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDefiningIdealSheafComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureProjectionChartSquare

/-!
# A closed subspace of a representable algebraic space is represented

Let `B` be a big fppf site containing a scheme `S`, let `T` be an object of the big fppf category
over `S` and let `Z ⊆ yoneda.obj T` be a closed subspace of the algebraic space it represents.
Base changing the closed immersion `Z ⟶ yoneda.obj T` along the identity produces an object `W`
of the big fppf category over `S` together with a morphism `W ⟶ T`, and the base-change
projection `yoneda.obj W ⟶ Z` is an isomorphism, the morphism it is a base change along being the
identity.  This file records that datum: the representing object, the representing morphism, the
isomorphism of algebraic spaces, and the triangle identifying
`AlgebraicGeometry.Space.representedSpaceMap` of the representing morphism with the inclusion
`AlgebraicGeometry.Space.subspaceInclusion` of the closed subspace.

The representing closed immersion of **schemes** was already in use — it is the morphism of
schemes underlying `W ⟶ T`, which
`AlgebraicGeometry.Space.definingIdealOfHom_obj_selfChart_eq_openChartIdeal` takes the defining
ideal sheaf of.  What this file adds is the identification of the closed *subspace* with the
algebraic space that scheme represents.

## Main definitions

* `AlgebraicGeometry.Space.representingObj`: the object of the big fppf category over `S` that
  represents the closed subspace, namely the base change of `Z ⟶ yoneda.obj T` along the
  identity.
* `AlgebraicGeometry.Space.representingHom`: the morphism `W ⟶ T` of the big fppf category over
  `S` whose represented morphism is the inclusion of the closed subspace.
* `AlgebraicGeometry.Space.representingIso`: the base-change projection
  `yoneda.obj W ⟶ Z`, as an isomorphism of presheaves.
* `AlgebraicGeometry.Space.representedSubspaceIso`: the same, as an isomorphism of algebraic
  spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.representedSpaceMap_representingHom`: **the dictionary** —
  `AlgebraicGeometry.Space.representedSpaceMap` of the representing morphism is the isomorphism
  of algebraic spaces followed by `AlgebraicGeometry.Space.subspaceInclusion` of the closed
  subspace, and `AlgebraicGeometry.Space.subspaceInclusion_eq_representedSpaceMap` is the same
  equation solved for the inclusion.
* `AlgebraicGeometry.Space.rep_snd_selfChart_eq_representingHom`: the representing morphism is
  the base change along the identity chart that
  `AlgebraicGeometry.Space.definingIdealOfHom_obj_selfChart_eq_openChartIdeal` uses, so the two
  halves of the dictionary are about the same morphism.
* `AlgebraicGeometry.Space.isClosedImmersion_map_representingHom`,
  `AlgebraicGeometry.Space.isClosedImmersion_schemeHom_representingHom` and
  `AlgebraicGeometry.Space.isAffineHom_schemeHom_representingHom`: the morphism of schemes
  underlying the representing morphism is a closed immersion, hence affine.  The affineness is
  the hypothesis of the assembled square
  `AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square`, so that
  square applies at the representing morphism with nothing assumed.

## Implementation notes

An *equality* `subspaceInclusion = representedSpaceMap` is not available and is not what is
proved: the source of the first is the subfunctor `Z` and the source of the second is
`yoneda.obj W`, and those are two presheaves that are canonically isomorphic and not equal.  The
triangle through `AlgebraicGeometry.Space.representedSubspaceIso` is the strongest form the
statement has.

The isomorphism is `CategoryTheory.IsPullback.isIso_fst_of_isIso` applied to the representability
square of the closed immersion at the identity: a base change along an isomorphism is an
isomorphism.  Being an isomorphism of presheaves between two objects of a full subcategory of
presheaves it is an isomorphism there, by `CategoryTheory.ObjectProperty.isoMk`.

Every statement about the morphism of schemes is given in both spellings — the image of the
representing morphism under `AlgebraicGeometry.BigFppfOver.toScheme` and
`AlgebraicGeometry.SmallEtale.schemeHom` of the big étale site carried by the same category of
schemes — because the consumers use different ones; the two are equal by
`AlgebraicGeometry.Space.schemeHom_associatedBigEtaleSite`, and each spelling gets its own
declaration.

## What this leaves owed

The comparison `AlgebraicGeometry.Space.RepresentableConormalSheafComparison` itself is proved,
by another route, as `AlgebraicGeometry.Space.representableConormalSheafComparison`, from
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalSheaf_of_scheme` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/RepresentableConormal.lean`; what follows is
what this file's own route would still need.

This is the dictionary, not the kernel step of clause (2) of `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/Conormal.lean` in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/`.
`AlgebraicGeometry.Space.definingIdealSheafIsoKernel` presents the defining ideal sheaf of `Z` as
the kernel of `AlgebraicGeometry.Space.structureProjection`, which is
`AlgebraicGeometry.Space.structureProjectionOfHom` of the inclusion, whereas the assembled square
`AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square` produces
`structureProjectionOfHom` of `representedSpaceMap` of the representing morphism.  With the
triangle below those two morphisms of modules out of `𝒪_{yoneda.obj T}` are
`structureProjectionOfHom` of `e.inv ≫ representedSpaceMap …` and of `representedSpaceMap …`
respectively, so what is still missing is the comparison of
`AlgebraicGeometry.Space.structureProjectionOfHom` of a composite with the composite of the
direct images — equivalently, the action of an isomorphism of algebraic spaces on the structure
projection.  Of that, the geometric and ring-level halves are available in existential form as
`AlgebraicGeometry.Space.exists_compRingIso_isCartesianComposition_comp_fSharp` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleStructureMapComp.lean`, and the module-level
statement is absent.  Nor is the identification of the space-level universal first-order
thickening of a morphism of representable spaces with the scheme-level one in the tree; clause
(2) needs that too.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)
    (Z : ClosedSubspaces B S hS (yoneda.obj T))

/-- **The object of the big fppf category over `S` representing a closed subspace of a
representable algebraic space.**  The inclusion `Z ⟶ yoneda.obj T` is a closed immersion, hence
relatively representable, so its base change along the identity of `yoneda.obj T` is represented;
this is the representing object. -/
noncomputable def representingObj : BigFppfOver B S hS :=
  Z.2.2.rep.pullback (𝟙 (yoneda.obj T))

/-- **The representing morphism of a closed subspace of a representable algebraic space**: the
morphism of the big fppf category over `S` from `AlgebraicGeometry.Space.representingObj` to `T`
produced by the representability of the inclusion `Z ⟶ yoneda.obj T` at the identity chart. -/
noncomputable def representingHom : representingObj B S hS T Z ⟶ T :=
  Z.2.2.rep.snd (𝟙 (yoneda.obj T))

/-- The representing morphism is the base change along the identity chart whose defining ideal
sheaf `AlgebraicGeometry.Space.definingIdealOfHom_obj_selfChart_eq_openChartIdeal` compares with
the ideal sheaf of the closed subspace: the identity chart of a representable presheaf is the
identity. -/
theorem rep_snd_selfChart_eq_representingHom :
    Z.2.2.rep.snd (selfChart B S hS T).1.hom = representingHom B S hS T Z := rfl

/-- **The morphism of schemes underlying the representing morphism is a closed immersion.**  It
is a represented base change of the closed immersion `Z ⟶ yoneda.obj T`, and every represented
base change of a closed immersion of algebraic spaces is a closed immersion of schemes by the
definition of Stacks 02YU (3). -/
theorem isClosedImmersion_map_representingHom :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (representingHom B S hS T Z)) :=
  Z.2.2.property_snd (𝟙 (yoneda.obj T))

/-- `AlgebraicGeometry.Space.isClosedImmersion_map_representingHom` in the spelling the small
étale machinery of the big étale site carried by the same category of schemes uses. -/
theorem isClosedImmersion_schemeHom_representingHom :
    _root_.AlgebraicGeometry.IsClosedImmersion
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (representingHom B S hS T Z).left) :=
  schemeHom_associatedBigEtaleSite B S hS (representingHom B S hS T Z) ▸
    isClosedImmersion_map_representingHom B S hS T Z

/-- **The morphism of schemes underlying the representing morphism is affine**, being a closed
immersion.  This is the hypothesis of the assembled square
`AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square`. -/
theorem isAffineHom_schemeHom_representingHom :
    _root_.AlgebraicGeometry.IsAffineHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (representingHom B S hS T Z).left) :=
  let := isClosedImmersion_schemeHom_representingHom B S hS T Z
  inferInstance

/-- **The presheaf underlying a closed subspace of a representable algebraic space is
represented**, by `AlgebraicGeometry.Space.representingObj`: the base-change projection of the
representability square of the inclusion at the identity is an isomorphism. -/
noncomputable def representingIso :
    yoneda.obj (representingObj B S hS T Z) ≅ Z.1.toFunctor :=
  @asIso _ _ _ _ (Z.2.2.rep.fst (𝟙 (yoneda.obj T))) (isIso_rep_fst_id B S hS Z.1 Z.2)

/-- **A closed subspace of a representable algebraic space is isomorphic, as an algebraic space
over `S`, to the algebraic space represented by `AlgebraicGeometry.Space.representingObj`.**  The
isomorphism of presheaves `AlgebraicGeometry.Space.representingIso` is an isomorphism of the full
subcategory of algebraic spaces, that subcategory being full. -/
noncomputable def representedSubspaceIso :
    (⟨yoneda.obj (representingObj B S hS T Z),
        isAlgebraicSpace_yoneda B S hS (representingObj B S hS T Z)⟩ :
      AlgebraicSpaces B S hS) ≅ ⟨Z.1.toFunctor, Z.2.1⟩ :=
  ObjectProperty.isoMk _ (representingIso B S hS T Z)

/-- **The dictionary: the represented morphism of the representing morphism of a closed subspace
is the inclusion of that subspace**, up to the isomorphism
`AlgebraicGeometry.Space.representedSubspaceIso` of its source.

The underlying equation of morphisms of presheaves is the commutativity of the representability
square of the inclusion at the identity of `yoneda.obj T`. -/
theorem representedSpaceMap_representingHom :
    representedSpaceMap B S hS (representingHom B S hS T Z) =
      (representedSubspaceIso B S hS T Z).hom ≫
        subspaceInclusion B S hS
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z := by
  apply ObjectProperty.hom_ext
  exact ((Z.2.2.rep.w (𝟙 (yoneda.obj T))).trans (Category.comp_id _)).symm

/-- `AlgebraicGeometry.Space.representedSpaceMap_representingHom` solved for the inclusion: the
inclusion of a closed subspace of a representable algebraic space is the inverse of
`AlgebraicGeometry.Space.representedSubspaceIso` followed by the represented morphism of the
representing morphism. -/
theorem subspaceInclusion_eq_representedSpaceMap :
    subspaceInclusion B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ Z =
      (representedSubspaceIso B S hS T Z).inv ≫
        representedSpaceMap B S hS (representingHom B S hS T Z) := by
  rw [representedSpaceMap_representingHom B S hS T Z, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Space

end
