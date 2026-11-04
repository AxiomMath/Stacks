module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ProjectionFormulaOpenImmersionBaseChange

/-!
# Localizing the projection formula on the base

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a commutative square of ringed spaces, `E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)`.  The diagram of
[Stacks, Tag 0B6B] relates the projection-formula morphism of [Stacks, Tag 0B53] for `f` to the
one for `f'`: five of the six maps in it are the comparison of [Stacks, Tag 079U] for `g` and for
`g'`, the derived base-change map of [Stacks, Tag 08HY] at two objects, the identification of the
two iterated derived pullbacks around the square, and the projection-formula morphism for `f'`.
Whenever those five are invertible the diagram forces the sixth leg — the derived pullback along
`g` of the projection-formula morphism for `f` — to be invertible too.

That is the **localization step** in the dévissage of [Stacks, Tag 08EU]: taking `g` to be the
immersion of an open of `Y` and `X'` the fibre product, it reduces invertibility of the
projection-formula morphism for `f`, *after restriction to that open*, to invertibility of the
projection-formula morphism for the base-changed morphism `f'`.  Two of the five inputs are
unconditional and the other two are theorems for an open immersion, so the only hypothesis that
survives is the one over the open.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.isIso_derivedPullback_map_projectionFormulaMap`:
  for a commutative square of ringed spaces, the derived pullback along `g` of the
  projection-formula morphism for `f` is invertible, with the two derived base-change maps and
  the projection-formula morphism for `f'` as hypotheses.  The two comparisons of
  [Stacks, Tag 079U] and the identification of the iterated pullbacks are discharged, being
  isomorphisms for every morphism of ringed spaces.

The abstract chase,
`Stacks.Cohomology.DerivedProjectionFormula.isIso_map_of_projectionFormulaBaseChangeSquare`,
and the scheme-level localization step for an open immersion,
`DerivedProjectionFormula.isIso_derivedPullback_map_projectionFormulaMap_of_isOpenImmersion`,
are in the imported module `ProjectionFormulaOpenImmersionBaseChange` of
`StacksDraft.AlgebraicGeometry.BaseChange.TorIndependence`.

## What this is not

It is not [Stacks, Tag 08EU].  Reducing invertibility of the projection-formula morphism itself
to invertibility after restriction to the members of an affine open cover of `Y` is a separate
step — `Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map` is that statement for
restriction, and bridging it to the derived pullback along the open immersion used here is not
carried out below.  Nor is the affine case: over `Y' = Spec A` the source's dévissage in `K` runs
through the equivalence `D(A) ≌ D_QCoh(𝒪_{Spec A})` of [Stacks, Tag 06Z0] and needs a right
adjoint to the inclusion `D_QCoh(𝒪_{X'}) ⟶ D(𝒪_{X'})`, i.e. [Stacks, Tag 0CR0], which this
repository proves only with compact generation of `D_QCoh` ([Stacks, Tag 09IS] and
[Stacks, Tag 09M1]) as a hypothesis.  So no tag is registered here.

The hypotheses `[HasSheafify …]` and `[… .WEqualsLocallyBijective …]` are the ones
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap` already carries; they hold for
every ringed space (`Stacks.AssociatedSheaf.hasModuleSheafify` and
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective`) and are binders here only
because those are not global instances.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.DerivedProjectionFormula

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### A commutative square of ringed spaces -/

section RingedSpaces

variable {X' X Y' Y : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  (sq : g' ≫ f = f' ≫ g)
  [HasSheafify (Opens.grothendieckTopology X'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Localizing the projection formula along a commutative square of ringed spaces.**  If the
derived base-change map of [Stacks, Tag 08HY] is invertible at `E` and at `E ⊗^L_{𝒪_X} Lf^*K`,
and the projection-formula morphism of [Stacks, Tag 0B53] is invertible for `f'` at
`L(g')^*E` and `Lg^*K`, then the derived pullback along `g` of the projection-formula morphism
for `f` at `E` and `K` is invertible.

This is `isIso_map_of_projectionFormulaBaseChangeSquare` at the diagram of [Stacks, Tag 0B6B],
`projectionFormulaMap_derivedBaseChangeMap`.  Its two remaining inputs are discharged rather than
assumed: the comparison of [Stacks, Tag 079U] is the forward map of the isomorphism of bifunctors
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`, for `g` and for `g'`, and
`derivedPullbackSquareIso` is an isomorphism by construction.  There is no boundedness, flatness
or quasi-coherence hypothesis. -/
theorem isIso_derivedPullback_map_projectionFormulaMap
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hbcE : IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq E))
    (hbc : IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq
      ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
        (E, (derivedPullback f).obj K))))
    (hproj : IsIso (projectionFormulaMap f' ((derivedPullback g').obj E)
      ((derivedPullback g).obj K))) :
    IsIso ((derivedPullback g).map (projectionFormulaMap f E K)) :=
  isIso_map_of_projectionFormulaBaseChangeSquare
    (hsq := projectionFormulaMap_derivedBaseChangeMap g' f' f g sq E K)
    (hαg := ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso g).app
      ((derivedPushforward f).obj E, K)).isIso_hom)
    (hαg' := ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso g').app
      (E, (derivedPullback f).obj K)).isIso_hom)
    (hbcE := hbcE) (hbc := hbc) (hc := ((derivedPullbackSquareIso g' f' f g sq).app K).isIso_inv)
    (hp' := hproj)

end RingedSpaces

end Stacks.Cohomology.DerivedProjectionFormula

end
