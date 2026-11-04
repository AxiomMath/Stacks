module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermFirstTerms
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionOnComplexes
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackTwoStep

/-!
# The comparison `Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}`

For composable morphisms of ringed spaces `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and
`t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` this file constructs the canonical morphism

`q : Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}`

of `D(𝒪_X)`: the comparison of the derived pullback of **Stacks 06YJ** with the degreewise one,
followed by the canonical map of complexes `f^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}` of **Stacks 0E1Z**.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.pulledNaiveCotangentComplexIso`: the degreewise
  pullback `f^*𝖭𝖫_{S/S'}` taken with `RingedSpaceModuleAdjunction.modulePullback`, the abstract
  left adjoint of `f_*`, agrees with `Stacks.SheafOfModules.pulledNaiveCotangentComplex`, the
  inverse-image-then-extension-of-scalars model the naive cotangent complex is pulled back with.
* `AlgebraicGeometry.RingedSpaceThickening.naiveCotangentPullbackComplexMap`: the canonical map
  of complexes `f^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}`, with the pullback in the `modulePullback` spelling.
* `AlgebraicGeometry.RingedSpaceThickening.derivedPullbackNaiveCotangentComparison`: the
  comparison `q` itself.

## Implementation notes

The construction identifies the two spellings of the degreewise pullback of `𝖭𝖫`.

* The spelling of `f^*` is identified by `RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep`
  (`StacksFrontier/Topology/Sheaves/Functors/Module/PullbackTwoStep.lean`), which compares the
  abstract left adjoint of `f_*` with inverse image followed by extension of scalars by
  uniqueness of left adjoints.  Applying it in each degree is
  `pulledNaiveCotangentComplexIso`.
* The base ring of `𝖭𝖫_{X/S'}` is identified by
  `Stacks.SheafOfModules.naiveCotangentComplexCompIso`
  (`StacksFrontier/AlgebraicGeometry/MoreMorphisms/NaiveCotangentSixTermFirstTerms.lean`), which
  compares `𝖭𝖫` over `(t ∘ f)^{-1}𝒪_{S'}` with `𝖭𝖫` over the iterated inverse image
  `f^{-1}t^{-1}𝒪_{S'}` that **Stacks 08TM** produces.  This is what makes the base-change map of
  **Stacks 0E1Y** land on `AlgebraicGeometry.RingedSpace.naiveCotangentComplex (f ≫ t)` on the
  nose, with no `eqToHom`: the target of
  `Stacks.SheafOfModules.spaceBaseChangeNaiveCotangentMap` at the tower
  `f^{-1}t^{-1}𝒪_{S'} ⟶ f^{-1}𝒪_S ⟶ 𝒪_X` is literally the right-hand side of that isomorphism.

The three steps of `derivedPullbackNaiveCotangentComparison` — derived to degreewise, change of
spelling, canonical map — are the same three as
`Stacks.NaiveCotangentDerivedFlatBaseChange.derivedBaseChangeMapOfComparison` and
`Stacks.NaiveCotangentSixTermSequence.pullbackToTotalMap`, which assemble them for a morphism of
*schemes*.  Neither applies here: the objects of **Stacks 0GQ3** and **0E3V** are ringed spaces,
and `Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison` used by the first takes a
comparison of base rings for a commutative square, which for a composite is the content of
`Stacks.SheafOfModules.inverseImageCompIso` rather than an input.

`q` is not asserted to be an isomorphism, and no two-term structure on
`derivedPullbackNaiveCotangent` is claimed; see the discussion of K-flatness in
`Stacks.NaiveCotangentDerivedFlatBaseChange`, where invertibility of the first step needs
`𝖭𝖫_{S/S'}` to be K-flat.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ), the derived pullback and
  its comparison with the degreewise one.
* [Stacks Project, Tag 08TN](https://stacks.math.columbia.edu/tag/08TN), the naive cotangent
  complex.
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of the
  naive cotangent complex.
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y) and
  [Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z), the canonical map
  `f^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}`.
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096), the pullback of sheaves
  of modules.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition (derivedPullbackComparisonOnComplex)
open Stacks.SheafOfModules (inverseImageBaseRing inverseImageFirstRingMap inverseImageMiddleRing
  naiveCotangentComplexCompIso pulledNaiveCotangentComparison pulledNaiveCotangentComplex
  ringedSpaceStructureMap spaceBaseChangeNaiveCotangentMap)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}}

/-- **The two models of the degreewise pullback `f^*𝖭𝖫_{S/S'}` agree.**  Pulling `𝖭𝖫_{S/S'}` back
degree by degree along `RingedSpaceModuleAdjunction.modulePullback`, the abstract left adjoint of
`f_*` that the derived pullback of **Stacks 06YJ** is built from, gives
`Stacks.SheafOfModules.pulledNaiveCotangentComplex`, the inverse-image-then-extension-of-scalars
model that **Stacks 08TM** and the base-change map of **Stacks 0E1Y** are stated over.

It is `RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep` applied in each degree; the
differentials commute by naturality of that isomorphism. -/
def pulledNaiveCotangentComplexIso (f : X ⟶ S) (t : S ⟶ S') :
    ((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (RingedSpace.naiveCotangentComplex t) ≅
      pulledNaiveCotangentComplex f t :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (modulePullbackIsoTwoStep f).app ((RingedSpace.naiveCotangentComplex t).X i))
    (fun i j _ => ((modulePullbackIsoTwoStep f).hom.naturality
      ((RingedSpace.naiveCotangentComplex t).d i j)).symm)

/-- **Stacks 0E1Z for the degreewise pullback in the `modulePullback` spelling.**  The canonical
map of complexes `f^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}`, with the pullback taken along
`RingedSpaceModuleAdjunction.modulePullback`.

It is `pulledNaiveCotangentComplexIso` into the model of **Stacks 08TM**, then the identification
`Stacks.SheafOfModules.pulledNaiveCotangentComparison` of that model with the base change of
`𝖭𝖫_{f^{-1}𝒪_S/f^{-1}t^{-1}𝒪_{S'}}`, then the canonical base-change map
`Stacks.SheafOfModules.spaceBaseChangeNaiveCotangentMap` of the tower
`f^{-1}t^{-1}𝒪_{S'} ⟶ f^{-1}𝒪_S ⟶ 𝒪_X`, then the identification
`Stacks.SheafOfModules.naiveCotangentComplexCompIso` of `𝖭𝖫_{X/S'}` with its iterated
spelling. -/
def naiveCotangentPullbackComplexMap (f : X ⟶ S) (t : S ⟶ S') :
    ((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (RingedSpace.naiveCotangentComplex t) ⟶
      RingedSpace.naiveCotangentComplex (f ≫ t) :=
  (pulledNaiveCotangentComplexIso f t).hom ≫
    (pulledNaiveCotangentComparison f t).hom ≫
    spaceBaseChangeNaiveCotangentMap (inverseImageBaseRing f t) (inverseImageMiddleRing f)
      X.sheaf (inverseImageFirstRingMap f t) (ringedSpaceStructureMap f) ≫
    (naiveCotangentComplexCompIso f t).inv

/-- **The comparison `q : Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}` of `D(𝒪_X)`.**  This is the morphism that
the statements of **Stacks 0GQ3**, **0GQ4** and **0E3V** are about.

It is the comparison of **Stacks 06YJ** between the derived and the degreewise pullback at the
complex `𝖭𝖫_{S/S'}`, followed by the image in `D(𝒪_X)` of the canonical map of complexes
`naiveCotangentPullbackComplexMap`. -/
def derivedPullbackNaiveCotangentComparison (f : X ⟶ S) (t : S ⟶ S') :
    derivedPullbackNaiveCotangent f t ⟶ relativeNaiveCotangentObj (f ≫ t) :=
  derivedPullbackComparisonOnComplex f (RingedSpace.naiveCotangentComplex t) ≫
    DerivedCategory.Q.map (naiveCotangentPullbackComplexMap f t)

end AlgebraicGeometry.RingedSpaceThickening

end
