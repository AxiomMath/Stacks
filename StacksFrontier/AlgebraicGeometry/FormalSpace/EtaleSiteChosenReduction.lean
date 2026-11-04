module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.GeneralReduction

/-!
# The étale sites of a formal algebraic space, at its reduction

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space
over `S`. **Stacks 0DEA** defines the three étale sites of `X` to be the three étale sites of
its reduction `X_red` — the small étale site of étale scheme charts, the spaces-étale site of
algebraic spaces étale over it, and the affine étale site of étale charts with affine source —
and **Stacks 0DEC** makes them functorial in `X`. The reduction of a formal algebraic space is
constructed in this library, by Stacks 0AIN
(`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`, bundled as
`AlgebraicGeometry.FormalSpace.reduction`), so both tags are stated here for a formal algebraic
space and nothing else: the only hypothesis is
`AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace`.

## Why the constructions live upstream

`StacksFrontier/AlgebraicGeometry/FormalSpace/EtaleSite.lean` carries out the three sites and the
two functorialities for an arbitrary reduction datum
`AlgebraicGeometry.FormalSpace.Reduction`, which it must: the proof of Stacks 0AIN delivers the
reduction *in that shape*, so the file constructing it imports the file defining it. This file
is the instance of those constructions at the reduction Stacks 0AIN provides, and it is where
Stacks 0DEA and Stacks 0DEC are registered.

Which reduction is taken is immaterial. `AlgebraicGeometry.FormalSpace.Reduction.iso`
identifies any two reductions of one formal algebraic space canonically, through the morphisms
of reductions induced by the identity of `X`, so the sites built from any other reduction are
canonically isomorphic to these and the general declarations upstream apply to them verbatim.

## Main definitions

* `AlgebraicGeometry.FormalSpace.SmallEtale`, `AlgebraicGeometry.FormalSpace.SpacesEtale` and
  `AlgebraicGeometry.FormalSpace.AffineEtale`, with their topologies: **Stacks 0DEA**, parts
  (1), (2) and (3).
* `AlgebraicGeometry.FormalSpace.spacesBaseChange` and
  `AlgebraicGeometry.FormalSpace.smallToposMorphism`: **Stacks 0DEC**, parts (1) and (3).

## Main results

* `AlgebraicGeometry.FormalSpace.isContinuous_spacesBaseChange` and
  `AlgebraicGeometry.FormalSpace.spacesBaseChange_isMorphismOfSites`: **Stacks 0DEC**, part
  (1).
* `AlgebraicGeometry.FormalSpace.spacesBaseChangeComp`,
  `AlgebraicGeometry.FormalSpace.spacesBaseChangeComp_projection` and
  `AlgebraicGeometry.FormalSpace.smallToposMorphismComp`: **Stacks 0DEC**, parts (2) and (3).

## References

* [Stacks Project, Tag 0DEA](https://stacks.math.columbia.edu/tag/0DEA)
* [Stacks Project, Tag 0DEC](https://stacks.math.columbia.edu/tag/0DEC)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 0DEA: the three étale sites of a formal algebraic space -/

/-- **Stacks 0DEA, part (1).** The *small étale site* `X_étale` of a formal algebraic space `X`
over `S`, as a category: the small étale site `X_{red, étale}` of the reduction, in the sense of
Stacks 03ED, whose objects are the étale scheme charts of `X_red`. -/
@[stacks 0DEA "(1) the small étale site, as a category"]
abbrev SmallEtale (X : FppfSheaf B S hS) (hX : IsFormalAlgebraicSpace B S hS X) :=
  (reduction B S hS X hX).SmallEtale

/-- **Stacks 0DEA, part (1).** The topology of the small étale site of `X`: that of
`X_{red, étale}`. -/
@[stacks 0DEA "(1) the topology of the small étale site"]
noncomputable abbrev smallEtaleTopology (X : FppfSheaf B S hS)
    (hX : IsFormalAlgebraicSpace B S hS X) :
    GrothendieckTopology (SmallEtale B S hS X hX) :=
  (reduction B S hS X hX).smallEtaleTopology

/-- **Stacks 0DEA, part (2).** The site `X_{spaces, étale}` of a formal algebraic space `X` over
`S`, as a category: the spaces-étale site `X_{red, spaces, étale}` of the reduction, in the
sense of Stacks 03G0, whose objects are the algebraic spaces étale over `X_red`. -/
@[stacks 0DEA "(2) the spaces-étale site, as a category"]
abbrev SpacesEtale (X : FppfSheaf B S hS) (hX : IsFormalAlgebraicSpace B S hS X) :=
  (reduction B S hS X hX).SpacesEtale

/-- **Stacks 0DEA, part (2).** The topology of `X_{spaces, étale}`: that of
`X_{red, spaces, étale}`. -/
@[stacks 0DEA "(2) the topology of the spaces-étale site"]
noncomputable abbrev spacesEtaleTopology (X : FppfSheaf B S hS)
    (hX : IsFormalAlgebraicSpace B S hS X) :
    GrothendieckTopology (SpacesEtale B S hS X hX) :=
  (reduction B S hS X hX).spacesEtaleTopology

/-- **Stacks 0DEA, part (3).** The site `X_{affine, étale}` of a formal algebraic space `X` over
`S`, as a category: the affine étale site `X_{red, affine, étale}` of the reduction, whose
objects are the étale charts of `X_red` with affine source. The site named by Properties of
Spaces Lemma 04JS is `AlgebraicGeometry.Space.AffineEtale`, which in this library carries the
tag Stacks 0H01. -/
@[stacks 0DEA "(3) the affine étale site, as a category"]
abbrev AffineEtale (X : FppfSheaf B S hS) (hX : IsFormalAlgebraicSpace B S hS X) :=
  (reduction B S hS X hX).AffineEtale

/-- **Stacks 0DEA, part (3).** The topology of `X_{affine, étale}`: that of
`X_{red, affine, étale}`. -/
@[stacks 0DEA "(3) the topology of the affine étale site"]
noncomputable abbrev affineEtaleTopology (X : FppfSheaf B S hS)
    (hX : IsFormalAlgebraicSpace B S hS X) :
    GrothendieckTopology (AffineEtale B S hS X hX) :=
  (reduction B S hS X hX).affineEtaleTopology

/-! ### Stacks 0DEC: functoriality of the étale sites -/

variable {X Y Z : FppfSheaf B S hS}

/-- **Stacks 0DEC, part (1).** The functor `Y_{spaces, étale} ⟶ X_{spaces, étale}` induced by a
morphism `f : X ⟶ Y` of formal algebraic spaces: base change along the induced morphism of
reductions, together with its cartesian projection, by Stacks 03G2, part (1). -/
@[stacks 0DEC "(1) the base-change functor `Y_spaces,étale ⟶ X_spaces,étale`"]
noncomputable def spacesBaseChange (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    Space.SpacesBaseChange B S hS
      ((reduction B S hS X hX).map (reduction B S hS Y hY) f) :=
  (reduction B S hS X hX).spacesBaseChange (reduction B S hS Y hY) f

/-- **Stacks 0DEC, part (1).** The functor `Y_{spaces, étale} ⟶ X_{spaces, étale}` is
continuous. -/
@[stacks 0DEC "(1) continuity of the functor"]
theorem isContinuous_spacesBaseChange (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (spacesBaseChange B S hS hX hY f).functor.IsContinuous
      (spacesEtaleTopology B S hS Y hY) (spacesEtaleTopology B S hS X hX) :=
  (reduction B S hS X hX).isContinuous_spacesBaseChange (reduction B S hS Y hY) f

/-- **Stacks 0DEC, part (1).** The continuous functor `Y_{spaces, étale} ⟶ X_{spaces, étale}`
induces a morphism of sites
`f_{spaces, étale} : X_{spaces, étale} ⟶ Y_{spaces, étale}`, in the sense of Stacks 00X1. -/
@[stacks 0DEC "(1) the induced morphism of sites `f_spaces,étale`"]
theorem spacesBaseChange_isMorphismOfSites (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (spacesBaseChange B S hS hX hY f).functor.IsMorphismOfSites
      (spacesEtaleTopology B S hS Y hY) (spacesEtaleTopology B S hS X hX) :=
  (reduction B S hS X hX).spacesBaseChange_isMorphismOfSites (reduction B S hS Y hY) f

/-- **Stacks 0DEC, part (2).** The rule `f ↦ f_{spaces, étale}` is compatible with composition:
the underlying functor of `(f ≫ g)_{spaces, étale}` is canonically isomorphic to the composite
of those of `g_{spaces, étale}` and `f_{spaces, étale}`, which is the composition of morphisms
of sites of Stacks 03CC. -/
@[stacks 0DEC "(2) compatibility with composition, as a canonical isomorphism of the
  underlying functors"]
noncomputable def spacesBaseChangeComp (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hZ : IsFormalAlgebraicSpace B S hS Z) (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (spacesBaseChange B S hS hY hZ g).functor ⋙ (spacesBaseChange B S hS hX hY f).functor ≅
      (spacesBaseChange B S hS hX hZ (f ≫ g)).functor :=
  (reduction B S hS X hX).spacesBaseChangeComp (reduction B S hS Y hY)
    (reduction B S hS Z hZ) f g

/-- **Stacks 0DEC, part (2).** The composition isomorphism is compatible with the cartesian
projections to the original object of `Z_{spaces, étale}`, which pins it down. -/
@[stacks 0DEC "(2) the composition isomorphism is compatible with the cartesian projections,
  which pins it down"]
theorem spacesBaseChangeComp_projection (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hZ : IsFormalAlgebraicSpace B S hS Z) (f : X ⟶ Y)
    (g : Y ⟶ Z) (V : SpacesEtale B S hS Z hZ) :
    ((spacesBaseChangeComp B S hS hX hY hZ f g).hom.app V).hom.left ≫
        (spacesBaseChange B S hS hX hZ (f ≫ g)).projection.app V =
      (spacesBaseChange B S hS hX hY f).projection.app
          ((spacesBaseChange B S hS hY hZ g).functor.obj V) ≫
        (spacesBaseChange B S hS hY hZ g).projection.app V :=
  (reduction B S hS X hX).spacesBaseChangeComp_projection (reduction B S hS Y hY)
    (reduction B S hS Z hZ) f g V

/-- **Stacks 0DEC, part (3).** The morphism of topoi
`f_small : Sh(X_étale) ⟶ Sh(Y_étale)` associated to `f_{spaces, étale}`, via the identification
(0DEB) of the small étale topos with the spaces-étale topos. It is the morphism of small étale
topoi of Stacks 03G2, part (3), at the induced morphism of reductions. -/
@[stacks 0DEC "(3) the morphism of small étale topoi `f_small`, through the identification
  (0DEB)"]
noncomputable def smallToposMorphism (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    MorphismOfTopoi (Sheaf (smallEtaleTopology B S hS X hX) (Type (u + 1)))
      (Sheaf (smallEtaleTopology B S hS Y hY) (Type (u + 1))) :=
  (reduction B S hS X hX).smallToposMorphism (reduction B S hS Y hY) f

/-- **Stacks 0DEC, part (3).** The construction of `f_small` is compatible with composition:
the direct image of the composite of `g_small` and `f_small` is canonically isomorphic to the
direct image of `(f ≫ g)_small`. -/
@[stacks 0DEC "(3) compatibility with composition of the morphisms of small étale topoi, on
  direct images"]
noncomputable def smallToposMorphismComp (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hZ : IsFormalAlgebraicSpace B S hS Z) (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (MorphismOfTopoi.comp (smallToposMorphism B S hS hY hZ g)
        (smallToposMorphism B S hS hX hY f)).pushforward ≅
      (smallToposMorphism B S hS hX hZ (f ≫ g)).pushforward :=
  (reduction B S hS X hX).smallToposMorphismComp (reduction B S hS Y hY)
    (reduction B S hS Z hZ) f g

end AlgebraicGeometry.FormalSpace

end
