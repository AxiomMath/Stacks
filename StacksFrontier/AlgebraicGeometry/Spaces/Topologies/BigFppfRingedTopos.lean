module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfEtaleRingedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtaleRingedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBigFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# The big fppf ringed topos of an algebraic space and the morphism `a_X`

Let `T` be a big fppf site of algebraic spaces over a scheme `S` and `X` one of its objects. The
big fppf site `(Spaces/X)_fppf` carries the sheaf of global regular functions, so it is a ringed
topos, and the inclusion of the spaces-étale site `X_{spaces,étale}` into it is a morphism of
sites `a_X : (Spaces/X)_fppf ⟶ X_{spaces,étale}`. Restricting the big structure sheaf along the
inclusion gives the spaces-étale structure sheaf, because both assign to an algebraic space
étale over `X` its ring of global regular functions; so `a_X` is a morphism of ringed topoi
`((Spaces/X)_fppf, 𝒪) ⟶ (X_{spaces,étale}, 𝒪_X)`, the morphism `a_X` of Stacks 0DGM.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.bigFppfRingedTopos`: the big fppf site of `X` with its
  structure sheaf, as a ringed topos.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSpacesEtaleMorphism`: the morphism of topoi `a_X`.
* `AlgebraicGeometry.BigFppfSpaceSite.spacesEtaleRestrictionStructureIso` and
  `AlgebraicGeometry.BigFppfSpaceSite.fppfToSpacesEtaleStructureIso`: the identification of the
  spaces-étale structure sheaf with the restriction, resp. the direct image along `a_X`, of the
  big fppf structure sheaf.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSpacesEtaleRingedHom`: `a_X` as a morphism of ringed
  topoi.

## Implementation notes

The construction mirrors `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleRingedMorphism`
for the comparison `π_X` of the big étale site, with the big fppf topology in place of the big
étale one. Nothing here depends on a choice of big étale site: the morphism of sites is
`AlgebraicGeometry.BigFppfSpaceSite.spacesEtaleInclusion_isMorphismOfSites`.

## References

* [Stacks Project, Tag 0DGM](https://stacks.math.columbia.edu/tag/0DGM)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S)

/-- The big fppf site of an algebraic space together with its sheaf of global regular functions,
as a ringed topos. -/
noncomputable abbrev bigFppfRingedTopos (X : T.Spaces) : RingedTopos where
  C := Over X
  J := BigFppfSpaceOver.topology T X
  O := structureSheaf T X

/-- The morphism of topoi `a_X : Sh((Spaces/X)_fppf) ⟶ Sh(X_{spaces,étale})` of the inclusion of
the spaces-étale site of `X` into its big fppf site. -/
noncomputable abbrev fppfToSpacesEtaleMorphism (X : T.Spaces) :
    MorphismOfTopoi (Sheaf (BigFppfSpaceOver.topology T X) (Type (u + 1)))
      (Sheaf (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X) (Type (u + 1))) :=
  (spacesEtaleInclusion_isMorphismOfSites T X).morphismOfTopoi

/-- Restriction of the big fppf structure sheaf of `X` along the inclusion of the spaces-étale
site of `X` is the spaces-étale structure sheaf of `X`: both assign to an algebraic space étale
over `X` its ring of global regular functions. -/
noncomputable def spacesEtaleRestrictionStructureIso (X : T.Spaces) :
    Space.SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X ≅
      ((Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).sheafPushforwardContinuous
          CommRingCat.{u + 1} (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X)
          (BigFppfSpaceOver.topology T X)).obj (structureSheaf T X) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V g
    ext x
    rfl))

/-- The canonical isomorphism from the spaces-étale structure sheaf of `X` to the direct image
along `a_X` of the big fppf structure sheaf of `X`. -/
noncomputable def fppfToSpacesEtaleStructureIso (X : T.Spaces) :
    (Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O ≅
      (pushforwardCommRingFunctor (fppfToSpacesEtaleMorphism T X)).obj
        (bigFppfRingedTopos T X).O :=
  spacesEtaleRestrictionStructureIso T X ≪≫
    (restrictionCommRingIso (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X)
      (BigFppfSpaceOver.topology T X) (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X)
      (structureSheaf T X)).symm

/-- **The morphism `a_X` of Stacks 0DGM** from the big fppf ringed topos of `X` to its
spaces-étale ringed topos: the morphism of topoi of the inclusion of the spaces-étale site, with
the canonical isomorphism `𝒪_X ≅ a_{X,*}𝒪` as its structure map. -/
noncomputable def fppfToSpacesEtaleRingedHom (X : T.Spaces) :
    RingedToposHom (bigFppfRingedTopos T X)
      (Space.spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X) where
  toToposHom := fppfToSpacesEtaleMorphism T X
  fSharp := (fppfToSpacesEtaleStructureIso T X).hom

end AlgebraicGeometry.BigFppfSpaceSite

/-! ### The other ringed enhancements of Stacks 0DGM -/


end
