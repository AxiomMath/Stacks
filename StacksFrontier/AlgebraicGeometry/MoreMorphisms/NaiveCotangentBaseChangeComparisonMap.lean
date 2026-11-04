module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentComplex
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence

/-!
# The canonical base change map of a square of schemes

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a commutative square of schemes.  This file carries the pullback `(g')^*NL_{X/Y}` and the
canonical map

`(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}`

of complexes of `𝒪_{X'}`-modules attached to a comparison `(g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'}`
of base rings, and nothing else.  It sits below both the file that develops the map and the file
that computes its stalks, so that the two speak about one and the same composite rather than
about two expressions a conversion has to identify.

## Main definitions

* `Stacks.NaiveCotangentFlatBaseChange.pulledComplex`: the pullback `(g')^*NL_{X/Y}`, written as
  the inverse image of `NL_{X/Y}` along `g'` with scalars extended to `𝒪_{X'}`.
* `Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison`: the canonical map
  `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` attached to a comparison
  `(g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'}` compatible with the two structure maps.

## Implementation notes

The towers of the base-change and the relative map share their first and last term but not their
middle one, so the two naive cotangent complexes over `(g')^{-1}f^{-1}𝒪_Y` that must be identified
differ in the structure map they are built from.  They are identified by `eqToHom` along the
compatibility equation, which is why that equation is a hypothesis of
`baseChangeMapOfComparison` rather than a lemma about it.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the base-change and
  relative maps of naive cotangent complexes of a tower of sheaves of rings.
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z), the same for a
  composition of morphisms of ringed spaces.
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of
  the naive cotangent complex.
* [Stacks Project, Tag 0D0H](https://stacks.math.columbia.edu/tag/0D0H), the naive cotangent
  complex of a morphism of schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules
open AlgebraicGeometry.SheafOfModules (inverseImageRingHom stalkFunctor)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf)

universe u

namespace Stacks.NaiveCotangentFlatBaseChange

variable {X Y X' Y' : Scheme.{u}}

/-! ### The pullback of the naive cotangent complex -/

/-- The pullback `(g')^*NL_{X/Y}` of the naive cotangent complex of `f : X ⟶ Y` along a
morphism of schemes `g' : X' ⟶ X`: the inverse image along `g'` of `NL_{X/Y}`, with scalars
extended from `(g')^{-1}𝒪_X` to `𝒪_{X'}`. -/
noncomputable abbrev pulledComplex (f : X ⟶ Y) (g' : X' ⟶ X) :
    CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X'.toRingedSpace.carrier) X'.toRingedSpace.sheaf)) ℤ :=
  pulledNaiveCotangentComplex g'.toLRSHom.toShHom f.toLRSHom.toShHom

/-! ### The canonical base change map -/

/-- **The canonical base change map `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}`** of a commutative square of
schemes, attached to a comparison `bc : (g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'}` whose composite
with the structure map of `f'` is the structure map of the tower
`(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X ⟶ 𝒪_{X'}`.

It is the composite of the identification of `(g')^*NL_{X/Y}` with the base change to
`𝒪_{X'}` of `NL_{(g')^{-1}𝒪_X/(g')^{-1}f^{-1}𝒪_Y}` (Stacks 08TM), the base-change map
`NL_{B/A} ⊗_B C ⟶ NL_{C/A}` of the tower `(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X ⟶ 𝒪_{X'}`, and
the relative map `NL_{C/A} ⟶ NL_{C/B}` of the tower
`(g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}`, the hypothesis on `bc` identifying the
target of the second with the source of the third. -/
noncomputable def baseChangeMapOfComparison (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (bc : inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom ⟶
      inverseImageSheaf f'.toLRSHom.toShHom)
    (hbc : inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom ≫
        ringedSpaceStructureMap g'.toLRSHom.toShHom =
      bc ≫ ringedSpaceStructureMap f'.toLRSHom.toShHom) :
    pulledComplex f g' ⟶ AlgebraicGeometry.Scheme.naiveCotangentComplex f' :=
  (pulledNaiveCotangentComparison g'.toLRSHom.toShHom f.toLRSHom.toShHom).hom ≫
    spaceBaseChangeNaiveCotangentMap
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
        (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (ringedSpaceStructureMap g'.toLRSHom.toShHom) ≫
      eqToHom (congrArg
        (naiveCotangentComplex.{u, u, u, u}
          (Opens.grothendieckTopology X'.toRingedSpace.carrier)
          (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
          X'.toRingedSpace.sheaf) hbc) ≫
        spaceRelativeNaiveCotangentComplexMap
          (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
          (inverseImageSheaf f'.toLRSHom.toShHom) X'.toRingedSpace.sheaf bc
          (ringedSpaceStructureMap f'.toLRSHom.toShHom)

end Stacks.NaiveCotangentFlatBaseChange

end
