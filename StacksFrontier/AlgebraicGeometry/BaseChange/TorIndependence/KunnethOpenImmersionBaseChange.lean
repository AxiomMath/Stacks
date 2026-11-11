module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethBaseChangeLeg
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethCompositeCoherence

/-!
# The base-change input of Tag 0FLQ, discharged when the base is restricted to an open

Of the three comparisons the first proof of Tag 0FLQ chains together, the middle one is the
base-change comparison `La^* Rb_* M ⟶ Rp_* Lq^* M` of Lemma 36.22.5 (Tag 08IB), carried in
`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange` as the
hypothesis `hbase`.  Tag 08IB in its stated generality — `f` quasi-compact and quasi-separated,
the two factors Tor independent over the base, `E` with quasi-coherent cohomology — is
`AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent`, which this module does not import.

This module treats the elementary case in which the base-change morphism is an open
immersion, `Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions`.
Composed with the identification
`Stacks.Cohomology.DerivedKunneth.kunnethBaseChangeLeg_eq_derivedBaseChangeMap`, it discharges
`hbase` in that case, and only in that case: the statements below still carry the two projection
formulas of Tag 08EU as hypotheses, and they are *not* the general Künneth isomorphism.

## Main results

* `Stacks.Cohomology.DerivedKunneth.isIso_kunnethBaseChangeLeg_of_isOpenImmersions`: for a
  Cartesian square of ringed spaces whose two horizontal arrows `a` and `q` are open immersions,
  the base-change leg of the Künneth map is invertible, for every derived module and with no
  further hypothesis.
* `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_isOpenImmersions`
  and, in the same namespace,
  `isIso_kunnethGlobalMap_of_projectionFormulas_of_isOpenImmersions`: the two conclusions of
  Tag 0FLQ in that case, with `hbase` gone and the two Tag 08EU projection formulas still
  carried.

## Implementation notes

*Exactly what is restricted.*  In the square of the Künneth map, `q ≫ b = p ≫ a`, the arrow
playing the role of the base-change morphism `g` of Tag 08HY is `a : X ⟶ S`, and the one playing
`g'` is `q : W ⟶ Y`.  So the hypothesis is that `a` is an open immersion and that `W` is the
fibre product, which makes `q` the base change of `a` along `b`.  Over ringed spaces the second
open-immersion hypothesis does not follow from the first and the Cartesian square, so both are
asked for; over schemes it does, by
`Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersion`.

*What is still carried.*  `hproj₁` and `hproj₂`, the two instances of the projection formula of
Tag 08EU, are untouched here; they are the remaining hypotheses of these statements and of the
tag-carrying declarations in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/KunnethIsomorphism.lean`.  The
monoidality coherence between Stacks 079U and Stacks 0D5S is not carried: it is proved there, in
`Stacks.Cohomology.DerivedKunneth.pullbackTensorComparisonComp`.

## References

* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.Cohomology.DerivedBaseChange

universe u

namespace Stacks.Cohomology.DerivedKunneth

attribute [local instance] HasDerivedCategory.standard

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (hq : q ≫ b = p ≫ a)

/-- **The base-change leg of the Künneth map is invertible when the base is restricted to an
open.**  For a Cartesian square of ringed spaces

```
W --q--> Y
|        |
p        b
v        v
X --a--> S
```

in which `a` and `q` are open immersions, the comparison `La^* Rb_* M ⟶ Rp_* Lq^* M` is an
isomorphism, for every `M` in the unbounded derived category of `𝒪_Y`-modules.  Nothing is
assumed of `b`, of `p`, or of `M`.

This is `Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions`,
read through `kunnethBaseChangeLeg_eq_derivedBaseChangeMap`.  It is the restricted case of
Tag 08IB with no hypothesis on `b`, `p` or `M`; the general statement is
`AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent`. -/
theorem isIso_kunnethBaseChangeLeg_of_isOpenImmersions
    [SheafedSpace.IsOpenImmersion a] [SheafedSpace.IsOpenImmersion q]
    (hsq : IsPullback q p b a)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    IsIso (kunnethBaseChangeLeg a b p q hq M) :=
  isIso_kunnethBaseChangeLeg_of_isIso_derivedBaseChangeMap a b p q hq M
    (isIso_derivedBaseChangeMap_of_isOpenImmersions q p b a hsq M)

variable [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The first conclusion of Tag 0FLQ with its base-change input discharged**, in the case where
the base-change morphism is an open immersion.

For a Cartesian square `q ≫ b = p ≫ a` of ringed spaces with `a` and `q` open immersions, the
relative Künneth morphism of Tag 0FLP at `f = p ≫ a` is an isomorphism as soon as the two
projection formulas of Tag 08EU are: `hproj₁` for `a` at `(K, Rb_*M)` and `hproj₂` for `p` at
`(K, Lq^*M)` with the two tensor factors interchanged.  The base-change comparison of Tag 08IB,
which `isIso_kunnethMap_of_projectionFormulas_of_baseChange` carries as `hbase`, is supplied by
`isIso_kunnethBaseChangeLeg_of_isOpenImmersions`; the monoidality coherence between Stacks 079U
and Stacks 0D5S is supplied, as there, by `pullbackTensorComparisonComp`.

This is *not* the general statement of Tag 0FLQ: the two projection formulas remain hypotheses,
and the open-immersion assumption on `a` is a genuine restriction of the source's situation. -/
theorem isIso_kunnethMap_of_projectionFormulas_of_isOpenImmersions
    [SheafedSpace.IsOpenImmersion a] [SheafedSpace.IsOpenImmersion q]
    (hsq : IsPullback q p b a)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hproj₁ : IsIso (projectionFormulaMap a K ((derivedPushforward b).obj M)))
    (hproj₂ : IsIso (adjunctionTensorMapRight (derivedAdjunction p)
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
      (pullbackTensorComparison p) K ((derivedPullback q).obj M))) :
    IsIso (kunnethMap a b p q (p ≫ a) rfl hq K M) :=
  isIso_kunnethMap_of_projectionFormulas_of_baseChange a b p q hq K M
    (pullbackTensorComparisonComp a p _ _) hproj₁
    (isIso_kunnethBaseChangeLeg_of_isOpenImmersions a b p q hq hsq M) hproj₂

/-- **The second conclusion of Tag 0FLQ with its base-change input discharged**, in the same
case.  Over a base whose `A`-linear global cup product is invertible at `(Ra_*K, Rb_*M)`, which
is what affineness of the base supplies and which is carried as `hκ`, the global Künneth
morphism of Tag 0G7V is an isomorphism as soon as the two projection formulas of Tag 08EU are.

The hypotheses are `hκ`, `hproj₁` and `hproj₂`, together with the Cartesian square and the two
open immersions; `hbase` is gone. -/
theorem isIso_kunnethGlobalMap_of_projectionFormulas_of_isOpenImmersions
    [SheafedSpace.IsOpenImmersion a] [SheafedSpace.IsOpenImmersion q]
    (hsq : IsPullback q p b a)
    (κ : Stacks.Cohomology.GlobalKunneth.GlobalCupProduct S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hκ : IsIso (κ.app ((derivedPushforward a).obj K, (derivedPushforward b).obj M)))
    (hproj₁ : IsIso (projectionFormulaMap a K ((derivedPushforward b).obj M)))
    (hproj₂ : IsIso (adjunctionTensorMapRight (derivedAdjunction p)
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
      (pullbackTensorComparison p) K ((derivedPullback q).obj M))) :
    IsIso (Stacks.Cohomology.GlobalKunneth.kunnethGlobalMap a b p q (p ≫ a) rfl hq κ K M) :=
  isIso_kunnethGlobalMap_of_projectionFormulas_of_baseChange a b p q hq κ K M hκ
    (pullbackTensorComparisonComp a p _ _) hproj₁
    (isIso_kunnethBaseChangeLeg_of_isOpenImmersions a b p q hq hsq M) hproj₂

end Stacks.Cohomology.DerivedKunneth

end
