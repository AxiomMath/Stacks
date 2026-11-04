module

public import StacksFrontier.AlgebraicGeometry.Conormal.AffineSections
public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization
public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalConormalSheaf

/-!
# An immersion, its universal first-order thickening and its conormal sheaf (Stacks 04F5)

Let `i : Z ⟶ X` be an immersion of schemes. [Stacks Project, Tag 04F5] makes three assertions
about it: that `i` is formally unramified; that the universal first-order thickening of `Z` over
`X` is the first-order infinitesimal neighbourhood `Z₁` of `Z` in `X` of
[Stacks Project, Tag 04EY]; and that the conormal sheaf of `i` as an immersion
([Stacks Project, Tag 01R2]) agrees with the conormal sheaf of `i` as a formally unramified
morphism ([Stacks Project, Tag 04F4]).

Parts (1) and (2) are `Stacks.Thickenings.formallyUnramified_of_isImmersion` and
`Stacks.Thickenings.isUniversalFirstOrderThickening_nthOrderInclusion_one`. Part (2) is also
recorded as an identification of the chosen universal first-order thickening
`Stacks.Thickenings.universalFirstOrderThickening` with `Z₁`, over `X` and compatibly with the two
inclusions of `Z`, and transported to conormal sheaves, which gives part (3).

## Main definitions

* `Stacks.Thickenings.universalThickeningIsoFirstOrderNeighbourhood`: the ambient scheme of the
  chosen universal first-order thickening of an immersion is isomorphic to the first-order
  infinitesimal neighbourhood of [Stacks Project, Tag 04EY], over `X` and compatibly with the
  inclusions of `Z`.
* `Stacks.Thickenings.universalConormalSheafIsoFirstOrderNeighbourhood`: the conormal sheaf
  `𝒞_{Z/X}` of [Stacks Project, Tag 04F4], built from the chosen universal first-order
  thickening, is the conormal sheaf of the inclusion `Z ⟶ Z₁` of `Z` into its first-order
  infinitesimal neighbourhood.
* `Stacks.Thickenings.immersionConormalSheafIsoUniversalConormalSheaf`: part (3) of
  [Stacks Project, Tag 04F5]: the conormal sheaf of `i` as an immersion is the conormal sheaf of
  `i` as a formally unramified morphism.

## Main results

* `Stacks.Thickenings.inclusion_universalThickeningIsoFirstOrderNeighbourhood` and
  `Stacks.Thickenings.universalThickeningIsoFirstOrderNeighbourhood_toBase`: the isomorphism of
  part (2) carries the inclusion of `Z` into the chosen thickening to the inclusion of `Z` into
  `Z₁`, and it commutes with the two structure morphisms to `X`.
* `Stacks.Thickenings.immersionConormalSheafIsoUniversalConormalSheaf_eq`: the isomorphism of
  part (3) is the comparison of [Stacks Project, Tag 04F0], the map
  `Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap` of [Stacks Project, Tag 01R4]
  for the factorization `Z ⟶ Z₁ ⟶ X` (`Stacks.Thickenings.infinitesimalConormalTransitivityMap`),
  composed with the two identifications supplied by part (2).
* `Stacks.Thickenings.immersionConormalSheafIsoUniversalConormalSheaf_hom`: the `hom` of that
  equation with the leading comparison split off.

## Implementation notes

Part (3) rests on [Stacks Project, Tag 04F0]: the canonical morphism `𝒞_{Z/X} ⟶ 𝒞_{Z/Z₁}` of
[Stacks Project, Tag 01R4] to the conormal sheaf of the first-order infinitesimal neighbourhood
is an isomorphism, `Stacks.Thickenings.isIso_conormalTransitivityMap_nthOrderInclusion`.

The transport of part (2) to conormal sheaves is
`Stacks.ClosedImmersion.conormalSheafIsoOfSquare`, the invariance of the conormal sheaf of a
morphism of ringed spaces under a square of isomorphisms, applied to the square
```
Z  --inclusion--→  Z'
|                  |
𝟙                  ≅
↓                  ↓
Z  ----------→     Z₁
```
whose right-hand arrow is the isomorphism of part (2) read on underlying ringed spaces by
`AlgebraicGeometry.RingedSpace.ringedSpaceIso`, followed by
`RingedSpaceModuleAdjunction.modulePullbackId` and `Stacks.Immersion.conormalSheafSelfIso`, which
passes from the conormal sheaf `Stacks.Thickenings.immersionConormalSheaf` of
[Stacks Project, Tag 01R2], built from the factorization over
`AlgebraicGeometry.Scheme.Hom.coborderRange`, to the factorization-free
`Stacks.Thickenings.schemeConormalSheaf`.

No hypothesis beyond `IsImmersion i` is used: nothing is assumed affine, Noetherian,
quasi-compact or of finite type.

## References

* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
* [Stacks Project, Tag 04F0](https://stacks.math.columbia.edu/tag/04F0)
* [Stacks Project, Tag 04F4](https://stacks.math.columbia.edu/tag/04F4)
* [Stacks Project, Tag 04F5](https://stacks.math.columbia.edu/tag/04F5)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

/-! ### Part (1): an immersion is formally unramified -/

add_to_stacks 04F5 "part (1): an immersion of schemes is formally unramified"
  Stacks.Thickenings.formallyUnramified_of_isImmersion

/-! ### Part (2): the universal first-order thickening is the first-order neighbourhood -/

add_to_stacks 04F5 "part (2): the first-order infinitesimal neighbourhood has the universal
  property of a first-order thickening over the base"
  Stacks.Thickenings.isUniversalFirstOrderThickening_nthOrderInclusion_one

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- The ambient scheme of the universal first-order thickening of an immersion `i : Z ⟶ X` chosen
by `Stacks.Thickenings.universalFirstOrderThickening` is isomorphic to the first-order
infinitesimal neighbourhood of `Z` in `X` of [Stacks Project, Tag 04EY].

The isomorphism is the canonical one between two universal first-order thickenings of the same
morphism, `Stacks.Thickenings.UniversalFirstOrderThickening.canonicalIso`. It is the unique
isomorphism of thickenings of `Z` over `X`, by
`Stacks.Thickenings.UniversalFirstOrderThickening.existsUnique_canonicalMap`. -/
@[stacks 04F5 "part (2): the chosen universal first-order thickening is the first-order
  infinitesimal neighbourhood"]
def universalThickeningIsoFirstOrderNeighbourhood :
    (universalFirstOrderThickening i).ambient ≅ firstOrderInfinitesimalNeighbourhood i :=
  UniversalFirstOrderThickening.canonicalIso (universalFirstOrderThickening i)
    (firstOrderInfinitesimalThickening i)

/-- The isomorphism of `Stacks.Thickenings.universalThickeningIsoFirstOrderNeighbourhood` carries
the inclusion of `Z` into the chosen universal first-order thickening to the inclusion of `Z` into
its first-order infinitesimal neighbourhood. -/
@[reassoc]
theorem inclusion_universalThickeningIsoFirstOrderNeighbourhood :
    (universalFirstOrderThickening i).inclusion ≫
        (universalThickeningIsoFirstOrderNeighbourhood i).hom =
      nthOrderInclusion i 1 :=
  UniversalFirstOrderThickening.canonicalMap_inclusion _ _

/-- The isomorphism of `Stacks.Thickenings.universalThickeningIsoFirstOrderNeighbourhood` is an
isomorphism over `X`: composed with the structure morphism of the first-order infinitesimal
neighbourhood it is the structure morphism of the chosen universal first-order thickening. -/
@[reassoc]
theorem universalThickeningIsoFirstOrderNeighbourhood_toBase :
    (universalThickeningIsoFirstOrderNeighbourhood i).hom ≫ nthOrderToBase i 1 =
      (universalFirstOrderThickening i).toBase :=
  UniversalFirstOrderThickening.canonicalMap_toBase _ _

/-! ### The conormal sheaf of the chosen thickening -/

/-- The inclusion of `Z` into the chosen universal first-order thickening, followed by the
isomorphism of `Stacks.Thickenings.universalThickeningIsoFirstOrderNeighbourhood`, is the
inclusion of `Z` into its first-order infinitesimal neighbourhood, read on underlying ringed
spaces. -/
theorem toShHom_inclusion_universalThickeningIsoFirstOrderNeighbourhood :
    (universalFirstOrderThickening i).inclusion.toLRSHom.toShHom ≫
        (RingedSpace.ringedSpaceIso (universalThickeningIsoFirstOrderNeighbourhood i)).hom =
      (Iso.refl Z.toLocallyRingedSpace.toRingedSpace).hom ≫
        (nthOrderInclusion i 1).toLRSHom.toShHom :=
  (congrArg (fun p : Z ⟶ firstOrderInfinitesimalNeighbourhood i => p.toLRSHom.toShHom)
    (inclusion_universalThickeningIsoFirstOrderNeighbourhood i)).trans (Category.id_comp _).symm

/-- The conormal sheaf of the chosen universal first-order thickening is the conormal sheaf of the
first-order infinitesimal neighbourhood. For an immersion `i : Z ⟶ X`, the conormal sheaf
`𝒞_{Z/X}` of [Stacks Project, Tag 04F4], that is the conormal sheaf of the inclusion of `Z` into
the thickening chosen by `Stacks.Thickenings.universalFirstOrderThickening`, is the conormal
sheaf of the inclusion `Z ⟶ Z₁` of `Z` into its first-order infinitesimal neighbourhood.

It is `Stacks.Immersion.conormalSheafSelfIso` followed by
`Stacks.ClosedImmersion.conormalSheafIsoOfSquare` at the square of
`Stacks.Thickenings.toShHom_inclusion_universalThickeningIsoFirstOrderNeighbourhood` and
`RingedSpaceModuleAdjunction.modulePullbackId`. -/
def universalConormalSheafIsoFirstOrderNeighbourhood :
    universalConormalSheaf i ≅ schemeConormalSheaf (nthOrderInclusion i 1) :=
  (Stacks.Immersion.conormalSheafSelfIso (universalFirstOrderThickening i).inclusion).symm ≪≫
    Stacks.ClosedImmersion.conormalSheafIsoOfSquare
      (Iso.refl Z.toLocallyRingedSpace.toRingedSpace)
      (RingedSpace.ringedSpaceIso (universalThickeningIsoFirstOrderNeighbourhood i))
      (universalFirstOrderThickening i).inclusion.toLRSHom.toShHom
      (nthOrderInclusion i 1).toLRSHom.toShHom
      (toShHom_inclusion_universalThickeningIsoFirstOrderNeighbourhood i) ≪≫
    (RingedSpaceModuleAdjunction.modulePullbackId
      Z.toLocallyRingedSpace.toRingedSpace).app _

/-! ### Part (3): the two conormal sheaves agree -/

/-- The conormal comparison of [Stacks Project, Tag 04F0] for an immersion and its first-order
infinitesimal neighbourhood: `Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap` for
the factorization `Z ⟶ Z₁ ⟶ X` of `i` through its first-order infinitesimal neighbourhood, that
is the canonical map `𝒞_{Z/X} ⟶ 𝒞_{Z/Z₁}` of [Stacks Project, Tag 01R4] for the square with
vertical arrows `𝟙_Z` and `Z₁ ⟶ X`, as an isomorphism
(`Stacks.Thickenings.isIso_conormalTransitivityMap_nthOrderInclusion`). -/
abbrev infinitesimalConormalTransitivityMap :
    immersionConormalSheaf i ≅ immersionConormalSheaf (nthOrderInclusion i 1) :=
  @asIso _ _ _ _ _ (isIso_conormalTransitivityMap_nthOrderInclusion i)

/-- For an immersion `i : Z ⟶ X`, the conormal sheaf of `i` in the sense of
[Stacks Project, Tag 01R2], `Stacks.Thickenings.immersionConormalSheaf i`, agrees with the
conormal sheaf of `i` in the sense of [Stacks Project, Tag 04F4],
`Stacks.Thickenings.universalConormalSheaf i`, built from the universal first-order thickening
chosen by `Stacks.Thickenings.universalFirstOrderThickening`.

It is the composite of the comparison `Stacks.Thickenings.infinitesimalConormalTransitivityMap`
of [Stacks Project, Tag 04F0], `Stacks.Immersion.conormalSheafSelfIso` for the inclusion
`Z ⟶ Z₁`, and `Stacks.Thickenings.universalConormalSheafIsoFirstOrderNeighbourhood`. -/
@[stacks 04F5 "part (3): the two conormal sheaves agree"]
def immersionConormalSheafIsoUniversalConormalSheaf :
    immersionConormalSheaf i ≅ universalConormalSheaf i :=
  infinitesimalConormalTransitivityMap i ≪≫
    (Stacks.Immersion.conormalSheafSelfIso (nthOrderInclusion i 1)).symm ≪≫
    (universalConormalSheafIsoFirstOrderNeighbourhood i).symm

/-- The isomorphism of part (3) is the comparison morphism of [Stacks Project, Tag 04F0], the
canonical map `𝒞_{Z/X} ⟶ 𝒞_{Z/Z₁}` of [Stacks Project, Tag 01R4] read as an isomorphism, followed
by the two identifications of the conormal sheaf of `Z ⟶ Z₁` with the conormal sheaf of the
chosen universal first-order thickening. -/
theorem immersionConormalSheafIsoUniversalConormalSheaf_eq :
    immersionConormalSheafIsoUniversalConormalSheaf i =
      infinitesimalConormalTransitivityMap i ≪≫
        (Stacks.Immersion.conormalSheafSelfIso (nthOrderInclusion i 1)).symm ≪≫
        (universalConormalSheafIsoFirstOrderNeighbourhood i).symm := rfl

/-- The `hom` of the isomorphism of part (3), with the leading comparison of
[Stacks Project, Tag 04F0] split off. -/
theorem immersionConormalSheafIsoUniversalConormalSheaf_hom :
    (immersionConormalSheafIsoUniversalConormalSheaf i).hom =
      (infinitesimalConormalTransitivityMap i).hom ≫
        ((Stacks.Immersion.conormalSheafSelfIso (nthOrderInclusion i 1)).symm ≪≫
          (universalConormalSheafIsoFirstOrderNeighbourhood i).symm).hom :=
  Iso.trans_hom (infinitesimalConormalTransitivityMap i)
    ((Stacks.Immersion.conormalSheafSelfIso (nthOrderInclusion i 1)).symm ≪≫
      (universalConormalSheafIsoFirstOrderNeighbourhood i).symm)

end Stacks.Thickenings

end
