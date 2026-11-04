module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaUnit
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftUnitorNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightUnitorNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative

/-!
# The structure sheaf of a ringed space as a unit, derived

Let `f : X ⟶ Y` be a morphism of ringed spaces. This file collects the three identifications that
make the structure sheaf in degree zero behave as a unit for the derived operations on a ringed
*space*, each of them being a result about a ringed *site* read at the site of the space:

* `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` — the derived pullback of the unit;
* `Z ⊗^𝐋_{𝒪_Y} 𝒪_Y[0] ≅ Z` and `𝒪_Y[0] ⊗^𝐋_{𝒪_Y} Z ≅ Z` — the two unit constraints of the
  derived tensor product, [Stacks, Tag 0FPT].

For the first, the structure sheaf is a flat `𝒪_Y`-module, so the complex `𝒪_Y[0]` is K-flat and
the comparison `Lf^* ⟶ f^*` is invertible on it; the ordinary inverse image `f^*𝒪_Y` is then
`𝒪_X` by the adjunction between inverse and direct image.

## Main results

* `Stacks.RingedSpace.isFlat_unit_of_ringedSpace`: the structure sheaf of a ringed space is a flat
  module over itself.
* `Stacks.RingedSpace.derivedPullbackSingleUnitIso`: the isomorphism `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`.
* `Stacks.RingedSpace.derivedTensorRightUnitIso` and
  `Stacks.RingedSpace.derivedTensorLeftUnitIso`: the two unit constraints of the derived tensor
  product of a ringed space.
* `Stacks.RingedSpace.derivedTensorRightUnitorNatIso` and
  `Stacks.RingedSpace.derivedTensorRightUnitor_naturality`: the right unit constraint as a
  *natural* isomorphism `- ⊗^𝐋_{𝒪_Z} 𝒪_Z[0] ≅ 𝟭 D(𝒪_Z)`, and its naturality square.
* `Stacks.RingedSpace.derivedTensorLeftUnitorNatIso` and
  `Stacks.RingedSpace.derivedTensorLeftUnitor_naturality`: the left unit constraint as a
  *natural* isomorphism `𝒪_Z[0] ⊗^𝐋_{𝒪_Z} - ≅ 𝟭 D(𝒪_Z)`, and its naturality square.  On this
  side the natural isomorphism and the object-wise `derivedTensorLeftUnitIso` are the same
  isomorphism at each object (`derivedTensorLeftUnitorNatIso_app`), so the naturality square is
  stated at the latter and applies directly to every client of it.

## Implementation notes

*Why these statements are restated.* All three are already proved — flatness of the unit as
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit`, the unit constraints as
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso` and `…leftUnitIso` — but for
a sheaf of rings presented as the structure sheaf `X.O` of an `AlgebraicGeometry.RingedSite`,
whereas the derived pullback and the derived projection formula of ringed spaces are indexed by a
`RingedSpace`, and the two presentations are not interchangeable by instance search. The crossing
is performed once below, by `toRingedSite`, which exhibits the opens of the space with their
canonical topology and the structure sheaf as a ringed site; no new mathematics is involved, and
the sheaves of rings on the two sides are the same term.

*The model of the derived categories.* The statements are at `HasDerivedCategory.standard`,
because `Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso` is, and
`HasDerivedCategory` carries the localized category as data, so a result at one model does not
transport to another. For the same reason the categories of modules are spelled
`SheafOfModules (structureSheafRing X)`.

*What this is for.* The statements below are the hypotheses `ν`, `ρX`/`ρY`, `hρX` and
`unitLeft` of
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject` and of
`…derivedPushforwardDerivedPullbackIsoOfIsIso`, which are [Stacks, Tag 08EU] at `K = 𝒪_Y[0]` —
the base case of the source's dévissage for [Stacks, Tag 08EU], hence an input of
[Stacks, Tag 08I9] and of [Stacks, Tag 08IB]. Supplying `ρY` and `ρX` as
`derivedTensorRightUnitorNatIso` rather than as `derivedTensorRightUnitIso` is what makes `hρX`
available, since the former carries its naturality. **One** hypothesis of that base case remains
open and is **not** discharged here: the right-unitor coherence `hcoh` of the comparison of
[Stacks, Tag 079U].

`derivedTensorLeftUnitor_naturality` is what [Stacks, Tag 08I9] needs in order to be natural in
its complex: the isomorphism of
`Stacks.Cohomology.DerivedProjectionFormula.derivedPushforwardDerivedPullbackIsoOfIsIso` is the
projection-formula map followed by the direct image of the left unit law, so its naturality is
that of the projection-formula map together with that of the unit law.

No `@[stacks]` attribute is placed below. `ν` is not a Stacks tag; the unit constraints are
[Stacks, Tag 0FPT], and that tag is already attributed, on the ringed-site statements these are
read off from, at
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/DerivedSymmetryAndUnit.lean`.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

open scoped CategoryTheory.Prod

universe u

namespace Stacks.RingedSpace

attribute [local instance] HasDerivedCategory.standard

/-- The opens of a ringed space, with their canonical topology and the structure sheaf, as a
ringed site. This is only a change of presentation: the three fields are the three pieces of
data a `RingedSpace` already carries. -/
abbrev toRingedSite (Z : RingedSpace.{u, u}) : AlgebraicGeometry.RingedSite.{u, u, u} :=
  { C := Opens Z.carrier
    J := Opens.grothendieckTopology Z.carrier
    O := Z.sheaf }

/-- **The structure sheaf of a ringed space is flat over itself.** This is
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit`, whose sheaf of rings is that of a
ringed site, read at the ringed site of the space. -/
theorem isFlat_unit_of_ringedSpace (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.sheaf)
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) :=
  Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := toRingedSite Z)

section Unitors

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **[Stacks, Tag 0FPT], the unit constraint on the right, for a ringed space**:
`A ⊗^𝐋_{𝒪_Z} 𝒪_Z[0] ≅ A`. This is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso` for the canonical derived
tensor product, read at the ringed site of the space. It is the isomorphism alone, not the
monoidal structure and not its coherence axioms. Its naturality in `A` is *not* part of this
datum, but it is available: the naturality square of the pointwise constraint is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_hom_naturality`, and the
constraint packaged as a natural isomorphism `- ⊗^𝐋_{𝒪_Z} 𝒪_Z[0] ≅ 𝟭 D(𝒪_Z)` is
`derivedTensorRightUnitorNatIso` below — which is built from a different lift, so the two are
not identified with each other. -/
def derivedTensorRightUnitIso
    (A : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Z))) :
    ((derivedTensorProductFunctor Z.sheaf).obj A).obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Z)) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))) ≅ A :=
  DerivedTensorProduct.rightUnitIso (toRingedSite Z) (canonicalDerivedTensorProduct Z.sheaf) A

/-- **[Stacks, Tag 0FPT], the unit constraint on the left, for a ringed space**:
`𝒪_Z[0] ⊗^𝐋_{𝒪_Z} A ≅ A`. This is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso` for the canonical derived
tensor product, read at the ringed site of the space. -/
def derivedTensorLeftUnitIso
    (A : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Z))) :
    ((derivedTensorProductFunctor Z.sheaf).obj
          ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Z)) 0).obj
            (_root_.SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)))).obj A ≅ A :=
  DerivedTensorProduct.leftUnitIso (toRingedSite Z) (canonicalDerivedTensorProduct Z.sheaf) A

/-- **[Stacks, Tag 0FPT], the unit constraint on the right, for a ringed space, as a natural
isomorphism**: `- ⊗^𝐋_{𝒪_Z} 𝒪_Z[0] ≅ 𝟭 D(𝒪_Z)`.

This is `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso` for the
canonical derived tensor product, read at the ringed site of the space. Unlike
`derivedTensorRightUnitIso` it carries its naturality, which is
`derivedTensorRightUnitor_naturality`; no identification of the two isomorphisms is proved. -/
def derivedTensorRightUnitorNatIso :
    (derivedTensorProductFunctor Z.sheaf).flip.obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Z)) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))) ≅
      𝟭 (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Z))) :=
  DerivedTensorProduct.rightUnitorNatIso (toRingedSite Z) (canonicalDerivedTensorProduct Z.sheaf)

/-- **Naturality of the right unit constraint of `⊗^𝐋_{𝒪_Z}` on a ringed space**: for every
`u : W ⟶ W'` in `D(𝒪_Z)`, tensoring `u` with the identity of `𝒪_Z[0]` and then cancelling the
unit is cancelling the unit and then `u`.

The tensor product of `u` with an identity is written as the image of `(u, 𝟙 𝒪_Z[0])` under
`CategoryTheory.Functor.uncurry` of the derived tensor bifunctor, which is the shape in which
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject` — the base
case of [Stacks, Tag 08EU] — carries it as the hypothesis `hρX`. -/
theorem derivedTensorRightUnitor_naturality
    {W W' : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Z))} (u : W ⟶ W') :
    (Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf)).map
          ((u ×ₘ 𝟙 ((DerivedCategory.singleFunctor
                (_root_.SheafOfModules.{u} (structureSheafRing Z)) 0).obj
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)))) :
            ((W, (DerivedCategory.singleFunctor
                  (_root_.SheafOfModules.{u} (structureSheafRing Z)) 0).obj
                (_root_.SheafOfModules.unit
                  (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))) : _ × _) ⟶
              (W', (DerivedCategory.singleFunctor
                    (_root_.SheafOfModules.{u} (structureSheafRing Z)) 0).obj
                  (_root_.SheafOfModules.unit
                    (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)))) ≫
        ((derivedTensorRightUnitorNatIso Z).app W').hom =
      ((derivedTensorRightUnitorNatIso Z).app W).hom ≫ u :=
  DerivedTensorProduct.rightUnitorNatIso_naturality_uncurry (toRingedSite Z)
    (canonicalDerivedTensorProduct Z.sheaf) u

/-- **[Stacks, Tag 0FPT], the unit constraint on the left, for a ringed space, as a natural
isomorphism**: `𝒪_Z[0] ⊗^𝐋_{𝒪_Z} - ≅ 𝟭 D(𝒪_Z)`.

This is `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitNatIso` ([Stacks, Tag
0FPT]) for the
canonical derived tensor product, read at the ringed site of the space.  Unlike the situation
on the right, no comparison of two isomorphisms is involved: its value at an object is
`derivedTensorLeftUnitIso` itself, by `derivedTensorLeftUnitorNatIso_app`. -/
def derivedTensorLeftUnitorNatIso :
    (derivedTensorProductFunctor Z.sheaf).obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Z)) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))) ≅
      𝟭 (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Z))) :=
  DerivedTensorProduct.leftUnitNatIso (toRingedSite Z) (canonicalDerivedTensorProduct Z.sheaf)

/-- The value of `derivedTensorLeftUnitorNatIso` at an object is the object-wise left unit
constraint `derivedTensorLeftUnitIso` there. -/
theorem derivedTensorLeftUnitorNatIso_app
    (A : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Z))) :
    (derivedTensorLeftUnitorNatIso Z).app A = derivedTensorLeftUnitIso Z A :=
  rfl

/-- **Naturality of the left unit constraint of `⊗^𝐋_{𝒪_Z}` on a ringed space**: for every
`u : W ⟶ W'` in `D(𝒪_Z)`, tensoring `u` into the right factor of `𝒪_Z[0] ⊗^𝐋 -` and then
cancelling the unit is cancelling the unit and then `u`.

This is the naturality square of `derivedTensorLeftUnitorNatIso`, stated at
`derivedTensorLeftUnitIso` — which is the same isomorphism at each object — because that is
the form in which
`Stacks.Cohomology.DerivedProjectionFormula.derivedPushforwardDerivedPullbackIsoOfIsIso`
consumes the unit law. -/
theorem derivedTensorLeftUnitor_naturality
    {W W' : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Z))} (u : W ⟶ W') :
    ((derivedTensorProductFunctor Z.sheaf).obj
          ((DerivedCategory.singleFunctor
              (_root_.SheafOfModules.{u} (structureSheafRing Z)) 0).obj
            (_root_.SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)))).map u ≫
        (derivedTensorLeftUnitIso Z W').hom =
      (derivedTensorLeftUnitIso Z W).hom ≫ u :=
  DerivedTensorProduct.leftUnitIso_hom_naturality (toRingedSite Z)
    (canonicalDerivedTensorProduct Z.sheaf) u

end Unitors

section

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The derived pullback of the structure sheaf**: `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`, for an arbitrary
morphism of ringed spaces `f : X ⟶ Y`.

The structure sheaf of `Y` is flat, so `Lf^*` of it in degree zero is the ordinary inverse image
in degree zero (`Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso`), and the
ordinary inverse image of the structure sheaf is the structure sheaf
(`Stacks.RingedSpace.pullbackObjUnitIso`). -/
def derivedPullbackSingleUnitIso :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y)) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))) ≅
      (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
  Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso f
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (isFlat_unit_of_ringedSpace Y) ≪≫
    (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).mapIso
      (Stacks.RingedSpace.pullbackObjUnitIso f)

end

end Stacks.RingedSpace

end
