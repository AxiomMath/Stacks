module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison

/-!
# The structure sheaves of the two small étale sites of a chart, as sheaves of *commutative* rings

For `U` an object of the big fppf site over `S`, the small étale site of the represented
algebraic space `yoneda.obj U` is the small étale site of the scheme underlying `U`, read in the
big étale site on the same schemes:
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`, with
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_topology` matching the two topologies.
`AlgebraicGeometry.Space.representedStructureMap` already compares the two structure sheaves and
is the identity, but it is `RingCat`-valued, through
`AlgebraicGeometry.Space.ringStructureSheaf`.  The ringed *site* of the scheme-level recovery
results, `AlgebraicGeometry.smallEtaleRingedSite`, carries the `CommRingCat`-valued
`AlgebraicGeometry.SmallEtale.commRingStructureSheaf`, and so does the ringed topos of an
algebraic space, through `AlgebraicGeometry.Space.structureSheaf`.  This file supplies the
comparison at `CommRingCat`, in both directions, and records that each is an isomorphism.

It is the identity again, for the same reason: both structure presheaves send an object of
either site to the global regular functions on the same scheme, so after restriction along the
equivalence the two underlying presheaves of commutative rings are the *same* presheaf.

## Main definitions

* `AlgebraicGeometry.Space.representedCommRingStructureMap` — the comparison
  `𝒪_{(yoneda.obj U)_étale} ⟶ e_* 𝒪_{U_étale}` of sheaves of commutative rings, where `e` is the
  equivalence of the two small étale sites.
* `AlgebraicGeometry.Space.representedCommRingStructureMapInverse` — the comparison read along
  the inverse equivalence.
* `AlgebraicGeometry.Space.representedCommRingStructureIso` and
  `AlgebraicGeometry.Space.representedCommRingStructureInverseIso` — each comparison as an
  isomorphism of sheaves of commutative rings, with
  `AlgebraicGeometry.Space.representedCommRingStructureMapBack` and
  `AlgebraicGeometry.Space.representedCommRingStructureMapInverseBack` its inverse.

## Main results

* `AlgebraicGeometry.Space.representedCommRingStructureMap_hom` and
  `AlgebraicGeometry.Space.representedCommRingStructureMapInverse_hom` — each comparison is the
  identity on the underlying presheaf.
* `AlgebraicGeometry.Space.isIso_representedCommRingStructureMap` and
  `AlgebraicGeometry.Space.isIso_representedCommRingStructureMapInverse` — each is an
  isomorphism.
* `AlgebraicGeometry.Space.sheafCompose_representedCommRingStructureMap` — forgetting
  commutativity returns `AlgebraicGeometry.Space.representedStructureMap`, so the `RingCat`-level
  comparison already in the development is this one with commutativity forgotten and nothing has
  been restated differently.

## Implementation notes

The two comparisons are *not* definitionally identity morphisms of sheaves of the same type —
their sources and targets are sheaves on different sites — but their `hom` fields are, which is
why `𝟙 _` typechecks and why `IsIso` is proved by exhibiting the identity presheaf map as the
inverse rather than by composing the two comparisons.

What this file supplies is only the comparison of the two structure sheaves.  The transport of
`AlgebraicGeometry.RingedToposHom` and of `AlgebraicGeometry.RingedToposHom.IsLocallyRinged`
along the identification is in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedSmallEtaleRingedToposEquivalence.lean`, and the
transport of `AlgebraicGeometry.RingedToposHom.TwoIso` and of
`AlgebraicGeometry.smallEtaleRingedToposHom` — i.e. that the morphism of small étale ringed
topoi of a morphism of schemes does not depend on which big site the schemes are read in — is in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedSmallEtaleRingedToposTransport.lean`.  The
identity on underlying presheaves recorded here is what makes the last of those computable: it
is why the inverse-image form of the identification's structure map is the identity.

## References

* [Stacks Project, Tag 03G7](https://stacks.math.columbia.edu/tag/03G7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The direct image along the equivalence of the two small étale sites, at `CommRingCat`. -/
noncomputable abbrev representedCommRingPushforward :
    Sheaf (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property) CommRingCat.{u} ⥤
      Sheaf (SmallEtale.topology B S hS (yoneda.obj U)) CommRingCat.{u} :=
  (representedSmallEtaleEquivalence B S hS U).functor.sheafPushforwardContinuous
    CommRingCat.{u} (SmallEtale.topology B S hS (yoneda.obj U))
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)

/-- The direct image along the inverse equivalence of the two small étale sites, at
`CommRingCat`. -/
noncomputable abbrev representedCommRingPushforwardInverse :
    Sheaf (SmallEtale.topology B S hS (yoneda.obj U)) CommRingCat.{u} ⥤
      Sheaf (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property) CommRingCat.{u} :=
  (representedSmallEtaleEquivalence B S hS U).inverse.sheafPushforwardContinuous
    CommRingCat.{u}
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (SmallEtale.topology B S hS (yoneda.obj U))

/-- **The structure sheaf of commutative rings of the small étale site of `yoneda.obj U` is the
structure sheaf of commutative rings of the small étale site of the scheme underlying `U`,
restricted along the equivalence of the two sites.**  Both sides send an object to the global
regular functions on the same scheme, so the comparison is the identity.

This is `AlgebraicGeometry.Space.representedStructureMap` before commutativity is forgotten; the
two agree by `AlgebraicGeometry.Space.sheafCompose_representedCommRingStructureMap`. -/
noncomputable def representedCommRingStructureMap :
    structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⟶
      (representedCommRingPushforward B S hS U).obj
        (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property) where
  hom := 𝟙 _

/-- The underlying presheaf map of `AlgebraicGeometry.Space.representedCommRingStructureMap` is
the identity of the structure presheaf of `yoneda.obj U`. -/
@[simp]
theorem representedCommRingStructureMap_hom :
    (representedCommRingStructureMap B S hS U).hom =
      𝟙 (structurePresheaf B S hS (yoneda.obj U)) :=
  rfl

/-- The comparison of structure sheaves of commutative rings read in the other direction. -/
noncomputable def representedCommRingStructureMapInverse :
    _root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⟶
      (representedCommRingPushforwardInverse B S hS U).obj
        (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) where
  hom := 𝟙 _

/-- The underlying presheaf map of `AlgebraicGeometry.Space.representedCommRingStructureMapInverse`
is the identity of the structure presheaf of commutative rings of the small étale site of the
scheme underlying `U`. -/
@[simp]
theorem representedCommRingStructureMapInverse_hom :
    (representedCommRingStructureMapInverse B S hS U).hom =
      𝟙 (_root_.AlgebraicGeometry.SmallEtale.commRingStructurePresheaf
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :=
  rfl

/-- **Forgetting commutativity in the comparison of structure sheaves of commutative rings
returns the `RingCat`-valued comparison the development already had.**  So nothing has been
restated differently: `AlgebraicGeometry.Space.representedStructureMap` is
`AlgebraicGeometry.Space.representedCommRingStructureMap` with commutativity forgotten. -/
theorem sheafCompose_representedCommRingStructureMap :
    ((sheafCompose (SmallEtale.topology B S hS (yoneda.obj U))
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        (representedCommRingStructureMap B S hS U)).hom =
      (representedStructureMap B S hS U).hom :=
  rfl

/-- The comparison of structure sheaves of commutative rings, read backwards.  Its underlying
presheaf map is the identity again, so it is inverse to
`AlgebraicGeometry.Space.representedCommRingStructureMap`. -/
noncomputable def representedCommRingStructureMapBack :
    (representedCommRingPushforward B S hS U).obj
        (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⟶
      structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) where
  hom := 𝟙 _

/-- **The comparison of structure sheaves of commutative rings is an isomorphism**, since it is
the identity on the underlying presheaf. -/
noncomputable def representedCommRingStructureIso :
    structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ≅
      (representedCommRingPushforward B S hS U).obj
        (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property) where
  hom := representedCommRingStructureMap B S hS U
  inv := representedCommRingStructureMapBack B S hS U
  hom_inv_id := Sheaf.hom_ext (Category.id_comp _)
  inv_hom_id := Sheaf.hom_ext (Category.id_comp _)

/-- `AlgebraicGeometry.Space.representedCommRingStructureMap` is an isomorphism. -/
instance isIso_representedCommRingStructureMap :
    IsIso (representedCommRingStructureMap B S hS U) :=
  ⟨representedCommRingStructureMapBack B S hS U,
    (representedCommRingStructureIso B S hS U).hom_inv_id,
    (representedCommRingStructureIso B S hS U).inv_hom_id⟩

/-- The comparison of structure sheaves of commutative rings along the inverse equivalence, read
backwards. -/
noncomputable def representedCommRingStructureMapInverseBack :
    (representedCommRingPushforwardInverse B S hS U).obj
        (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) ⟶
      _root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property where
  hom := 𝟙 _

/-- **The comparison of structure sheaves of commutative rings along the inverse equivalence is
an isomorphism.** -/
noncomputable def representedCommRingStructureInverseIso :
    _root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ≅
      (representedCommRingPushforwardInverse B S hS U).obj
        (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) where
  hom := representedCommRingStructureMapInverse B S hS U
  inv := representedCommRingStructureMapInverseBack B S hS U
  hom_inv_id := Sheaf.hom_ext (Category.id_comp _)
  inv_hom_id := Sheaf.hom_ext (Category.id_comp _)

/-- `AlgebraicGeometry.Space.representedCommRingStructureMapInverse` is an isomorphism. -/
instance isIso_representedCommRingStructureMapInverse :
    IsIso (representedCommRingStructureMapInverse B S hS U) :=
  ⟨representedCommRingStructureMapInverseBack B S hS U,
    (representedCommRingStructureInverseIso B S hS U).hom_inv_id,
    (representedCommRingStructureInverseIso B S hS U).inv_hom_id⟩

end AlgebraicGeometry.Space

end
