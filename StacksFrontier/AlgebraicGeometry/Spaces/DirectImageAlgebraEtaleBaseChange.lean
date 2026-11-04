module

public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange

/-!
# Étale base change for the direct-image algebra of a morphism of algebraic spaces

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale, and let `𝒜 = f_*𝒪_X` be the direct-image algebra of Stacks 03G8.  This file
states the **ring-level** half of étale base change for it:

`f'_*𝒪_{X'} ≅ g^*𝒜`

as sheaves of rings on the small étale site of `Y'`, where `g^*` is étale restriction of sheaves
of rings along small étale postcomposition with `g`.

## Main definitions

* `baseChangeRingIso`: the comparison `baseChangeRingMap` of the two transported sheaves of rings
  is an isomorphism.
* `directImageAlgebraEtaleBaseChangeRingIso`: **the ring-level étale base change of the
  direct-image algebra**, `f'_*𝒪_{X'} ≅ g^*(f_*𝒪_X)`, taking the cartesian square and the
  étaleness of `g` and nothing else.

## Main results

* `baseChangeRingMap_comp_inv` and `baseChangeRingMapInv_comp`: the two composites are the
  identities.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The inverse of `AlgebraicGeometry.Space.baseChangeRingMap`: the same construction at the
inverse of the base-change isomorphism of Stacks 03LR, part (1). -/
noncomputable def baseChangeRingMapInv (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    baseChangeRightRingSheaf B S hS f g hg ⟶
      baseChangeLeftRingSheaf B S hS i f'
        (isEtale_of_isPullback B S hS f' i g f sq.flip hg) :=
  pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y'.1)
    (structureRingSheaf B S hS X)
    (smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg).inv

/-- `AlgebraicGeometry.Space.baseChangeRingMap` followed by its inverse is the identity. -/
theorem baseChangeRingMap_comp_inv (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    baseChangeRingMap B S hS i f' f g sq hg ≫ baseChangeRingMapInv B S hS i f' f g sq hg =
      𝟙 _ := by
  apply (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map_injective
  rw [CategoryTheory.Functor.map_comp, baseChangeRingMap, baseChangeRingMapInv,
    ringSheafMap_pullbackRingSheafMapOfNatTrans,
    ringSheafMap_pullbackRingSheafMapOfNatTrans, CategoryTheory.Functor.map_id]
  exact (smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg).hom_inv_id_app _

/-- The inverse followed by `AlgebraicGeometry.Space.baseChangeRingMap` is the identity. -/
theorem baseChangeRingMapInv_comp (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    baseChangeRingMapInv B S hS i f' f g sq hg ≫ baseChangeRingMap B S hS i f' f g sq hg =
      𝟙 _ := by
  apply (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map_injective
  rw [CategoryTheory.Functor.map_comp, baseChangeRingMapInv,
    ringSheafMap_pullbackRingSheafMapOfNatTrans, baseChangeRingMap,
    ringSheafMap_pullbackRingSheafMapOfNatTrans, CategoryTheory.Functor.map_id]
  exact (smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg).inv_hom_id_app _

/-- **The comparison of the two transported sheaves of rings is an isomorphism.**  The two sides
of base change transport `𝒪_X` along the two composite functors of sheaves of sets around the
square, and `AlgebraicGeometry.Space.baseChangeRingMap` is induced by the base-change
isomorphism of Stacks 03LR, part (1) between those functors. -/
noncomputable def baseChangeRingIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    baseChangeLeftRingSheaf B S hS i f'
        (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ≅
      baseChangeRightRingSheaf B S hS f g hg where
  hom := baseChangeRingMap B S hS i f' f g sq hg
  inv := baseChangeRingMapInv B S hS i f' f g sq hg
  hom_inv_id := baseChangeRingMap_comp_inv B S hS i f' f g sq hg
  inv_hom_id := baseChangeRingMapInv_comp B S hS i f' f g sq hg

/-- **Étale base change for the direct-image algebra of Stacks 03G8, at the level of sheaves of
rings.**  For a cartesian square

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

of algebraic spaces over a scheme `S` contained in a big fppf site `B`, with `g` étale,

`f'_*𝒪_{X'} ≅ g^*(f_*𝒪_X)`

as sheaves of rings on the small étale site of `Y'`.  Only the square and the étaleness of `g`
are taken; `f` carries no hypothesis. -/
noncomputable def directImageAlgebraEtaleBaseChangeRingIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    structureRingSheafDirectImage B S hS f' ≅
      (smallEtaleRingRestriction B S hS g hg).obj
        (structureRingSheafDirectImage B S hS f) :=
  (etaleBaseChangeRingComparison B S hS i f'
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).symm ≪≫
    etaleBaseChangeRingCompIso B S hS i f'
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ≪≫
    baseChangeRingIso B S hS i f' f g sq hg

end AlgebraicGeometry.Space

end
