module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleRingedTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf

/-!
# The étale topologies of an algebraic space as ringed sites (Stacks 0DF9)

Both the big étale site `(Spaces/X)_étale` of an algebraic space `X` and its spaces-étale site
`X_{spaces,étale}` carry a structure sheaf: the value at an object `U` is the ring `Γ(U, 𝒪_U)` of
global regular functions on the algebraic space `U`. This file packages the spaces-étale site
with that sheaf as a ringed topos and upgrades the two morphisms of topoi comparing the small
and the big étale topos to morphisms of ringed topoi, the inverse image resp. the direct image
of the big structure sheaf being canonically the small one.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.smallToBigEtaleStructureIso` and
  `AlgebraicGeometry.BigEtaleSpaceSite.smallToBigEtaleRingedMorphism`: the canonical isomorphism
  `i_f⁻¹𝒪 ≅ 𝒪_Y` and the morphism of ringed topoi it makes of `i_f`.
* `AlgebraicGeometry.BigEtaleSpaceSite.iXEtaleRingedMorphism`: the identity-morphism case of the
  previous definition, which is the morphism `i_X`.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleStructureIso` and
  `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleRingedMorphism`: the canonical isomorphism
  `𝒪_X ≅ π_{X,*}𝒪` and the morphism of ringed topoi it makes of `π_X`.
* `AlgebraicGeometry.BigEtaleSpaceSite.smallToBigRestrictionStructureIso` and
  `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallRestrictionStructureIso`: restriction of the big
  étale structure sheaf of `X` along the inclusion of the spaces-étale site of `Y`, identified
  with the spaces-étale structure sheaf of `Y`.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.smallToBigEtaleRingedMorphism_fSharpInverseImage`: the
  inverse-image form of the structure map of `i_f` is that canonical isomorphism.

## Implementation notes

The structure sheaves themselves, and the sheaf condition for them, are
`AlgebraicGeometry.BigEtaleSpaceSite.structureSheaf` and
`AlgebraicGeometry.Space.SpacesEtale.structureSheaf`; the morphism of ringed topoi attached to
`f_small` is `AlgebraicGeometry.Space.smallEtaleRingedToposHom` and the one attached to `f_big`
is `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleRingedMorphism`. They are registered for this
tag below rather than restated.

Both comparison isomorphisms factor the same way. The inverse image, resp. the direct image, of
a sheaf of commutative rings along a morphism of topoi whose relevant functor is restriction
along a continuous functor of sites *is* that restriction, by
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`; and the restriction of the big étale
structure sheaf of `X` to the spaces-étale site of `Y` has the same sections and the same
restriction maps as the spaces-étale structure sheaf of `Y`, because an object étale over `Y`
has one ring of global regular functions however it is regarded. So both isomorphisms are the
identity in each component.

The source only asks for a map `𝒪_X ⟶ π_{X,*}𝒪`; what is available is an isomorphism, which is
recorded as such.

Compatibility of these structure maps with composition is asserted in the source without a
statement or a proof, and is not formalized here.

## References

* [Stacks Project, Tag 0DF9](https://stacks.math.columbia.edu/tag/0DF9)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-! ### The small-to-big morphism `i_f` as a morphism of ringed topoi -/

variable {X Y : T.Spaces}

/-- Restriction of the big étale structure sheaf of `X` along the inclusion of the spaces-étale
site of `Y` is the spaces-étale structure sheaf of `Y`: an object étale over `Y` has the same
ring of global regular functions read in either site, and the restriction maps agree. -/
@[stacks 0DF9 "case (1): restriction along the inclusion functor"]
noncomputable def smallToBigRestrictionStructureIso (f : Y ⟶ X) :
    ((inclusionFunctor T f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        (T.bigEtaleTopology X)).obj (T.structureSheaf X) ≅
      Space.SpacesEtale.structureSheaf T.fppfSite S T.fppf_mem Y :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V g
    ext x
    rfl))

/-- **Stacks 0DF9, case (1).** The canonical isomorphism from the inverse image along `i_f` of
the big étale structure sheaf of `X` to the spaces-étale structure sheaf of `Y`. -/
@[stacks 0DF9 "case (1): the isomorphism i_f⁻¹𝒪 ≅ 𝒪_Y"]
noncomputable def smallToBigEtaleStructureIso (f : Y ⟶ X) :
    (inverseImageCommRingFunctor (smallToBigEtaleMorphism T f)).obj
        (bigEtaleRingedTopos T X).O ≅
      (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y).O :=
  restrictionCommRingIso (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      (T.bigEtaleTopology X) (inclusionFunctor T f) (T.structureSheaf X) ≪≫
    smallToBigRestrictionStructureIso T f

/-- **Stacks 0DF9, case (1).** The morphism `i_f` from the spaces-étale topos of `Y` to the big
étale topos of `X` as a morphism of ringed topoi: the structure map is the adjunct of the
canonical isomorphism of structure sheaves. -/
@[stacks 0DF9 "case (1): i_f as a morphism of ringed topoi"]
noncomputable def smallToBigEtaleRingedMorphism (f : Y ⟶ X) :
    RingedToposHom (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
      (bigEtaleRingedTopos T X) where
  toToposHom := smallToBigEtaleMorphism T f
  fSharp :=
    ((commRingImageAdjunction (smallToBigEtaleMorphism T f)).homEquiv _ _)
      (smallToBigEtaleStructureIso T f).hom

/-- The inverse-image form of the structure map of `i_f` is the canonical isomorphism of
structure sheaves. -/
theorem smallToBigEtaleRingedMorphism_fSharpInverseImage (f : Y ⟶ X) :
    (smallToBigEtaleRingedMorphism T f).fSharpInverseImage =
      (smallToBigEtaleStructureIso T f).hom :=
  Equiv.symm_apply_apply _ _

/-- **Stacks 0DF9, case (2).** The morphism `i_X` as a morphism of ringed topoi: it is the
identity-morphism case `f = 𝟙 X` of `i_f`. -/
@[stacks 0DF9 "case (2): i_X as a morphism of ringed topoi"]
noncomputable abbrev iXEtaleRingedMorphism (X : T.Spaces) :
    RingedToposHom (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
      (bigEtaleRingedTopos T X) :=
  smallToBigEtaleRingedMorphism T (𝟙 X)

/-! ### The big-to-small morphism `π_X` as a morphism of ringed topoi -/

/-- Restriction of the big étale structure sheaf of `X` along the inclusion of the spaces-étale
site of `X` is the spaces-étale structure sheaf of `X`, in the direction needed for the direct
image along `π_X`. -/
@[stacks 0DF9 "case (3): restriction along the inclusion of the spaces-étale site"]
noncomputable def bigToSmallRestrictionStructureIso (X : T.Spaces) :
    Space.SpacesEtale.structureSheaf T.fppfSite S T.fppf_mem X ≅
      ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous
          CommRingCat.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
          (T.bigEtaleTopology X)).obj (T.structureSheaf X) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V g
    ext x
    rfl))

/-- **Stacks 0DF9, case (3).** The canonical isomorphism from the spaces-étale structure sheaf
of `X` to the direct image along `π_X` of the big étale structure sheaf of `X`. -/
@[stacks 0DF9 "case (3): the isomorphism 𝒪_X ≅ π_{X,*}𝒪"]
noncomputable def bigToSmallEtaleStructureIso (X : T.Spaces) :
    (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X).O ≅
      (pushforwardCommRingFunctor (bigToSmallEtaleMorphism T X)).obj
        (bigEtaleRingedTopos T X).O :=
  bigToSmallRestrictionStructureIso T X ≪≫
    (restrictionCommRingIso (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (T.bigEtaleTopology X) (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X)
      (T.structureSheaf X)).symm

/-- **Stacks 0DF9, case (3).** The morphism `π_X` from the big étale topos of `X` to its
spaces-étale topos as a morphism of ringed topoi, with the canonical isomorphism
`𝒪_X ≅ π_{X,*}𝒪` as its structure map. -/
@[stacks 0DF9 "case (3): π_X as a morphism of ringed topoi"]
noncomputable def bigToSmallEtaleRingedMorphism (X : T.Spaces) :
    RingedToposHom (bigEtaleRingedTopos T X)
      (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X) where
  toToposHom := bigToSmallEtaleMorphism T X
  fSharp := (bigToSmallEtaleStructureIso T X).hom

/-! ### The remaining content of the remark -/

add_to_stacks 0DF9 "the big étale structure presheaf is a sheaf"
  AlgebraicGeometry.BigEtaleSpaceSite.structurePresheaf_isSheaf
add_to_stacks 0DF9 "the structure sheaf of the big étale site"
  AlgebraicGeometry.BigEtaleSpaceSite.structureSheaf
add_to_stacks 0DF9 "the spaces-étale structure presheaf is a sheaf"
  AlgebraicGeometry.Space.SpacesEtale.structurePresheaf_isSheaf
add_to_stacks 0DF9 "the structure sheaf of the spaces-étale site"
  AlgebraicGeometry.Space.SpacesEtale.structureSheaf
add_to_stacks 0DF9 "case (4): f_small as a morphism of ringed topoi"
  AlgebraicGeometry.Space.smallEtaleRingedToposHom
add_to_stacks 0DF9 "case (5): the isomorphism f_big⁻¹𝒪₁ ≅ 𝒪₂"
  AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleStructureIso
add_to_stacks 0DF9 "case (5): f_big as a morphism of ringed topoi"
  AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleRingedMorphism

end AlgebraicGeometry.BigEtaleSpaceSite

end
