module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaBaseChange
public import
  StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.CanonicalPullbackPushforwardMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaPerfect
import StacksCore.Tactic.StacksAttribute

/-!
# Invertibility of the derived projection-formula map is local on the base

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a Cartesian square of ringed spaces whose horizontal arrows are open immersions.  This file
proves that invertibility of the derived projection-formula map of [Stacks, Tag 0B53] descends
along `g`: if the map for `f'` is invertible, then the derived pullback along `g` of the map for
`f` is invertible.

This is the **localization step** of the source's proof of [Stacks, Tag 08EU] and of
[Stacks, Tag 08I9] — "the question is local on `Y`" — and it is unconditional in the two
complexes: no boundedness, quasi-coherence, quasi-compactness or quasi-separatedness hypothesis
enters, and the morphism `f` is arbitrary.

## The two inputs

*The square of [Stacks, Tag 0B6B].*
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_derivedBaseChangeMap` says that
the projection-formula map of [Stacks, Tag 0B53] commutes with the derived base-change map of
[Stacks, Tag 08HY] around any commutative square, with no hypothesis on either complex.  By
itself that is an identity between two composites and says nothing about invertibility.

*Invertibility of the base-change map along an open immersion.*
`Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions` says that
the map of [Stacks, Tag 08HY] is invertible for a Cartesian square whose horizontal arrows are
open immersions, at every object of the unbounded derived category.

Four of the six legs of the square of [Stacks, Tag 0B6B] are then invertible — the two
base-change maps by the second input, the two comparisons of [Stacks, Tag 079U] because
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso` is an isomorphism of
bifunctors, and the identification of the two iterated derived pullbacks because
`Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackSquareIso` is an isomorphism — so the
square becomes a two-out-of-two statement about the remaining two.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.isIso_map_of_projectionFormulaBaseChangeSquare` —
  the abstract two-out-of-two step: in the diagram of [Stacks, Tag 0B6B] over arbitrary functors,
  if the two comparisons, the two base-change maps, the identification and the
  projection-formula map along the other vertical edge are invertible, then so is `Lg` of the
  projection-formula map.
* `isIso_derivedPullback_map_pullbackPushforwardTensorMap`, in the same namespace — the same
  conclusion for the canonical morphism of [Stacks, Tag 08I9] itself.
* `isIso_derivedPullback_map_projectionFormulaMap_of_isOpenImmersion`, in the same namespace —
  the localization step for a Cartesian square of schemes whose bottom arrow is an open
  immersion, which is the form the source's argument is run in.

## Implementation notes

*Why the abstract layer.*  `isIso_map_of_projectionFormulaBaseChangeSquare` is stated over
arbitrary categories, functors and bifunctors, exactly as the `Mate` layer of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaBaseChange` is.  The
canonical statement mentions four derived tensor products, four derived pullbacks and two derived
pushforwards at once; proving the chase with those as variables keeps each canonical proof term a
single application, which is the convention of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap` and is adopted for the
same reason.

*The direction of the conclusion.*  The square of [Stacks, Tag 0B6B] has `Lg` of the
projection-formula map for `f` as one leg, not the map itself, so that is what the conclusion is
about.  It is the shape the source's localization argument produces, `Lg^*` being restriction to
an open of the base.

*The unit comparison.*  The statement for the morphism of [Stacks, Tag 08I9] needs
`Lg'^*(𝒪_X[0]) ≅ 𝒪_{X'}[0]`, the derived shadow of the comparison of [Stacks, Tag 01CD]. It is
supplied by `Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso`, which exists for every
morphism of ringed spaces.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.DerivedProjectionFormula

/-! ### The two-out-of-two step over abstract functors -/

section Abstract

variable {P P' Q Q' : Type*} [Category P] [Category P'] [Category Q] [Category Q']

/-- **The diagram of [Stacks, Tag 0B6B] read as a two-out-of-two statement.**

In the diagram `ProjectionFormulaBaseChangeSquare`, five of the six legs carry an `IsIso`
hypothesis here: the two comparisons `αg` and `αg'` of the tensor products along the horizontal
edges, the two base-change maps `bcE` and `bc`, the identification `c` of the two iterated
pullbacks, and the projection-formula map `p'` along the other vertical edge.  The commuting
square then forces the remaining leg, `Lg` of the projection-formula map `p`, to be invertible.

The six invertibility hypotheses are explicit arguments rather than instance arguments: at the
canonical functors each is produced by a named isomorphism of the library, and handing them over
explicitly avoids instance search having to match an application of a reducible abbreviation
against the shape it unfolds to. -/
theorem isIso_map_of_projectionFormulaBaseChangeSquare
    (Rf : Q ⥤ P) (Rf' : Q' ⥤ P') (Lf : P ⥤ Q) (Lf' : P' ⥤ Q') (Lg : P ⥤ P') (Lg' : Q ⥤ Q')
    (AP : P × P ⥤ P) (AQ : Q × Q ⥤ Q) (AP' : P' × P' ⥤ P') (AQ' : Q' × Q' ⥤ Q')
    (αg : AP ⋙ Lg ⟶ Lg.prod Lg ⋙ AP') (αg' : AQ ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ AQ')
    (E : Q) (K : P)
    (p : AP.obj (Rf.obj E, K) ⟶ Rf.obj (AQ.obj (E, Lf.obj K)))
    (bc : Lg.obj (Rf.obj (AQ.obj (E, Lf.obj K))) ⟶ Rf'.obj (Lg'.obj (AQ.obj (E, Lf.obj K))))
    (bcE : Lg.obj (Rf.obj E) ⟶ Rf'.obj (Lg'.obj E))
    (c : Lg'.obj (Lf.obj K) ⟶ Lf'.obj (Lg.obj K))
    (p' : AP'.obj (Rf'.obj (Lg'.obj E), Lg.obj K) ⟶
      Rf'.obj (AQ'.obj (Lg'.obj E, Lf'.obj (Lg.obj K))))
    (hsq : ProjectionFormulaBaseChangeSquare Rf Rf' Lf Lf' Lg Lg' AP AQ AP' AQ' αg αg' E K
      p bc bcE c p')
    (hαg : IsIso (αg.app (Rf.obj E, K))) (hαg' : IsIso (αg'.app (E, Lf.obj K)))
    (hbcE : IsIso bcE) (hbc : IsIso bc) (hc : IsIso c) (hp' : IsIso p') :
    IsIso (Lg.map p) := by
  have := hαg
  have := hαg'
  have := hbcE
  have := hbc
  have := hc
  have := hp'
  have hbcEprod : IsIso ((bcE ×ₘ 𝟙 (Lg.obj K) :
      ((Lg.obj (Rf.obj E), Lg.obj K) : P' × P') ⟶ (Rf'.obj (Lg'.obj E), Lg.obj K))) :=
    (isIso_prod_iff P' P').2 ⟨hbcE, inferInstance⟩
  have hcprod : IsIso ((𝟙 (Lg'.obj E) ×ₘ c :
      ((Lg'.obj E, Lg'.obj (Lf.obj K)) : Q' × Q') ⟶ (Lg'.obj E, Lf'.obj (Lg.obj K)))) :=
    (isIso_prod_iff Q' Q').2 ⟨inferInstance, hc⟩
  have heq : αg.app (Rf.obj E, K) ≫ AP'.map (bcE ×ₘ 𝟙 (Lg.obj K)) ≫ p' =
      Lg.map p ≫ bc ≫ Rf'.map (αg'.app (E, Lf.obj K) ≫ AQ'.map (𝟙 (Lg'.obj E) ×ₘ c)) := hsq
  have hleft : IsIso (αg.app (Rf.obj E, K) ≫ AP'.map (bcE ×ₘ 𝟙 (Lg.obj K)) ≫ p') :=
    inferInstance
  rw [heq] at hleft
  exact IsIso.of_isIso_comp_right (Lg.map p)
    (bc ≫ Rf'.map (αg'.app (E, Lf.obj K) ≫ AQ'.map (𝟙 (Lg'.obj E) ×ₘ c)))

end Abstract

/-! ### The localization step at the canonical derived functors -/

section Canonical

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X' X Y' Y : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The localization step for the canonical morphism of [Stacks, Tag 08I9].**

For a Cartesian square of ringed spaces whose horizontal arrows are open immersions, the derived
pullback along `g` of the morphism `Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*Lf^*K` of [Stacks, Tag 08I9] is
invertible as soon as the corresponding morphism for `f'` is, at the restricted complex `Lg^*K`.

The comparison `Lg'^*(𝒪_X[0]) ≅ 𝒪_{X'}[0]`, the derived shadow of [Stacks, Tag 01CD], is
supplied by `Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso`, which exists for every
morphism of ringed spaces, so it needs no open-immersion assumption.

This is the localization step for a single Cartesian square, one ingredient of the source's
proof; the full statement of [Stacks, Tag 08I9] is
`AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_unconditional`. -/
theorem isIso_derivedPullback_map_pullbackPushforwardTensorMap
    [SheafedSpace.IsOpenImmersion g'] [SheafedSpace.IsOpenImmersion g]
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (h : IsIso (pullbackPushforwardTensorMap' f' ((derivedPullback g).obj K))) :
    IsIso ((derivedPullback g).map (pullbackPushforwardTensorMap' f K)) := by
  have h' : IsIso (projectionFormulaMap f' ((derivedPullback g').obj (singleUnit X))
      ((derivedPullback g).obj K)) :=
    isIso_projectionFormulaMap_of_iso_left f'
      (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso g').symm _
      ((isIso_pullbackPushforwardTensorMap f' ((derivedPullback g).obj K)).1 h)
  have hp : IsIso ((derivedPullback g).map (projectionFormulaMap f (singleUnit X) K)) :=
    Stacks.Cohomology.ProjectionFormulaPerfect.isIso_derivedPullback_map_projectionFormulaMap
      g' f' f g sq (singleUnit X) K h'
  have hu : IsIso ((derivedPullback g).map ((derivedPushforward f).map
      ((Stacks.RingedSpace.derivedTensorLeftUnitIso X ((derivedPullback f).obj K)).hom))) :=
    ((derivedPullback g).mapIso ((derivedPushforward f).mapIso
      (Stacks.RingedSpace.derivedTensorLeftUnitIso X ((derivedPullback f).obj K)))).isIso_hom
  have heq : (derivedPullback g).map (pullbackPushforwardTensorMap' f K) =
      (derivedPullback g).map (projectionFormulaMap f (singleUnit X) K) ≫
        (derivedPullback g).map ((derivedPushforward f).map
          ((Stacks.RingedSpace.derivedTensorLeftUnitIso X ((derivedPullback f).obj K)).hom)) :=
    (derivedPullback g).map_comp _ _
  rw [heq]
  exact IsIso.comp_isIso' hp hu

end Canonical

/-! ### The localization step for schemes -/

section Schemes

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X'.toRingedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.toRingedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.toRingedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.toRingedSpace.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y'.toRingedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y'.toRingedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.toRingedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.toRingedSpace.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Invertibility of the derived projection-formula map of [Stacks, Tag 0B53] descends along an
open immersion of the base, for schemes.**

For a Cartesian square of schemes whose bottom arrow `g` is an open immersion, the derived
pullback along `g` of the projection-formula map for `f` is invertible as soon as the map for `f'`
at the restricted complexes is.

The other horizontal arrow `g'` is then an open immersion too, being a base change of `g`, and
the square stays Cartesian in ringed spaces by
`Stacks.Cohomology.DerivedBaseChange.isPullback_toShHom_of_isOpenImmersion`, so
`Stacks.Cohomology.ProjectionFormulaPerfect.isIso_derivedPullback_map_projectionFormulaMap`
applies.  This is the form the source's
localization argument is run in: it replaces the base `Y` by an open `V ⊆ Y` and `X` by its
preimage. -/
@[stacks 08EU "the localization step of the source's proof, for schemes: for a Cartesian square \
of schemes whose bottom arrow is an open immersion, invertibility of the projection-formula map \
for f' at the restricted complexes implies invertibility of the derived pullback along g of the \
map for f; unconditional in both complexes, but only one implication of the source's reduction \
— the affine case and the descent from an open cover back to the base are not proved"]
theorem isIso_derivedPullback_map_projectionFormulaMap_of_isOpenImmersion
    [AlgebraicGeometry.IsOpenImmersion g] (sq : IsPullback g' f' f g)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (h : IsIso (projectionFormulaMap f'.toLRSHom.toShHom
      ((derivedPullback g'.toLRSHom.toShHom).obj E)
      ((derivedPullback g.toLRSHom.toShHom).obj K))) :
    IsIso ((derivedPullback g.toLRSHom.toShHom).map
      (projectionFormulaMap f.toLRSHom.toShHom E K)) :=
  have : AlgebraicGeometry.IsOpenImmersion g' :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsOpenImmersion) sq.flip inferInstance
  Stacks.Cohomology.ProjectionFormulaPerfect.isIso_derivedPullback_map_projectionFormulaMap
    _ _ _ _
    (Stacks.Cohomology.DerivedBaseChange.isPullback_toShHom_of_isOpenImmersion g' f' f g sq) E K h

end Schemes

end Stacks.Cohomology.DerivedProjectionFormula

end
