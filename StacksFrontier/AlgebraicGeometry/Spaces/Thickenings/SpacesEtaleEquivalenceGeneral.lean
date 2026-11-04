module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.SpacesEtaleEquivalenceGeneral

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.SpacesEtaleEssSurjLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleHomLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms

/-!
# Base change on spaces-étale sites is an equivalence at a thickening of arbitrary order

Let `f : X ⟶ Y` be a thickening of algebraic spaces over a scheme `S`, of arbitrary order: a
morphism identifying `X` with a closed subspace of `Y` that has the same points. Base change
`V ↦ X ×_Y V` is an equivalence from the spaces-étale site of `Y` to that of `X`. This is
Stacks 05ZH for the inclusion of a thickening, a special case of the source's integral,
universally injective and surjective morphism, Stacks 05ZL; no finite-order or first-order
hypothesis is made.

## Main results

* `AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening_range` (in
  `SpacesEtaleEssSurjThickening`): essential surjectivity, for a monomorphism whose range is a
  thickening.
* `AlgebraicGeometry.Space.C1573.isEquivalence_spacesBaseChange_of_isThickeningHom`:
  **Stacks 05ZH for a thickening of arbitrary order**, the equivalence.
* `AlgebraicGeometry.Space.C1573.isThickeningHom_inclusion`: the inclusion of a thickening
  subspace is a thickening of algebraic spaces.
* `AlgebraicGeometry.Space.C1573.spacesEtaleEquivalenceOfIsThickening`: the equivalence of
  `AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickening` packaged as an
  equivalence of spaces-étale sites `Y_spaces,étale ≌ G_spaces,étale`, whose functor is base
  change.

## Implementation notes

Faithfulness holds for any morphism surjective on points,
`AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isSurjective`, and fullness is the source's
graph argument, `AlgebraicGeometry.Space.full_spacesBaseChange_of_mono_of_isThickening`.

Essential surjectivity follows the last paragraph of the source's proof. The reduction given by
`AlgebraicGeometry.Space.C1573.nonempty_liftedEtalePresentation_of_lifting` followed by
`AlgebraicGeometry.Space.C1573.essSurj_spacesBaseChange_of_liftedEtalePresentation` takes two
inputs, and both are available at arbitrary order:

* over an étale chart `Z` of `Y`, the base change of `f` is a closed immersion `J ⟶ Z` of
  schemes surjective on points,
  `AlgebraicGeometry.Space.C1573.exists_chart_isClosedImmersion_of_mono_of_isThickening`, across
  which étale schemes lift by Stacks 039R — the source's appeal to Étale Cohomology 04DZ, which
  for a thickening is 039R; and
* morphisms into a space étale over `Y` extend uniquely across a base change of `f`,
  `AlgebraicGeometry.Space.existsUnique_hom_presheaf_of_isThickening`, by the same graph
  argument that proves fullness.

The quotient of the lifted étale equivalence relation, Stacks 02WW, is then an object of the
spaces-étale site of `Y` whose base change is the given object.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 05ZL](https://stacks.math.columbia.edu/tag/05ZL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Morphism

variable {X Y : AlgebraicSpaces B S hS}

add_to_stacks 05ZH "the equivalence, for the inclusion of a thickening of arbitrary order"
  AlgebraicGeometry.Space.C1573.isEquivalence_spacesBaseChange_of_isThickeningHom

end Morphism

section Subspace

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

end Subspace

end AlgebraicGeometry.Space

end
