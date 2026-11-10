module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.SpacesEtaleEssSurjLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleHomLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

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
* `AlgebraicGeometry.Space.C1573.isThickeningHom_inclusion`: the inclusion of a thickening subspace
  is a thickening of algebraic spaces.
* `AlgebraicGeometry.Space.C1573.spacesEtaleEquivalenceOfIsThickening`: the equivalence of
  `AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickening` packaged as an
  equivalence of spaces-étale sites `Y_spaces,étale ≌ G_spaces,étale`, whose functor is base
  change.

## Implementation notes

Faithfulness holds for any morphism surjective on points,
`AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isSurjective`, and fullness is the source's
graph argument, `AlgebraicGeometry.Space.full_spacesBaseChange_of_mono_of_isThickening`.

Essential surjectivity follows the last paragraph of the source's proof. The reduction of
the sibling file `SpacesEtaleEssSurjLifting.lean` (in this directory),
`AlgebraicGeometry.Space.C1573.nonempty_liftedEtalePresentation_of_lifting` followed by
`AlgebraicGeometry.Space.C1573.essSurj_spacesBaseChange_of_liftedEtalePresentation`, takes two
inputs, and both are available at arbitrary order:

* over an étale chart `Z` of `Y`, the base change of `f` is a closed immersion `J ⟶ Z` of
  schemes surjective on points,
  `AlgebraicGeometry.Space.C1573.exists_chart_isClosedImmersion_of_mono_of_isThickening`, across
  which étale schemes lift by Stacks 039R — the source's appeal to Étale Cohomology 04DZ, which
  for a thickening is 039R; and
* morphisms into a space étale over `Y` extend uniquely across a base change of `f`,
  `AlgebraicGeometry.Space.existsUnique_hom_presheaf_of_isThickening`, by the same graph argument
  that proves fullness.

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

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Morphism

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 05ZH for a thickening of arbitrary order.** Let `f : X ⟶ Y` be a thickening of
algebraic spaces over `S` — an isomorphism onto a closed subspace of `Y` with the same points —
of arbitrary order. Base change `V ↦ X ×_Y V` is an equivalence from the spaces-étale site of `Y`
to that of `X`.

A thickening is integral, universally injective and surjective, Stacks 05ZL, so this is the
source's statement for that class of morphisms; no order hypothesis is made. Faithfulness is
`AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isSurjective`, fullness is
`AlgebraicGeometry.Space.full_spacesBaseChange_of_mono_of_isThickening` and essential
surjectivity is `AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening_range`. -/
theorem C1573.isEquivalence_spacesBaseChange_of_isThickeningHom (f : X ⟶ Y)
    (hf : IsThickeningHom B S hS f) :
    (spacesBaseChange B S hS f).functor.IsEquivalence :=
  have := hf.mono
  let := full_spacesBaseChange_of_mono_of_isThickening B S hS f hf.2
  let := faithful_spacesBaseChange_of_isSurjective B S hS f hf.surjective_pointsMap
  let := essSurj_spacesBaseChange_of_isThickening_range B S hS f hf.2
  ⟨inferInstance, inferInstance, inferInstance⟩

end Morphism

section Subspace

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- The inclusion of a thickening subspace `G ⊂ X` is a thickening of algebraic spaces: it is a
monomorphism whose range is `G`. -/
theorem C1573.isThickeningHom_inclusion (hG : IsThickening B S hS X G) :
    IsThickeningHom B S hS (IsThickening.inclusion B S hS hG) :=
  have : Mono (IsThickening.inclusion B S hS hG).hom := inferInstanceAs (Mono G.ι)
  (isThickeningHom_iff_of_mono _).2 (by
    rw [show Subfunctor.range (IsThickening.inclusion B S hS hG).hom = G from
      Subfunctor.range_ι G]
    exact hG)

/-- **The spaces-étale sites of a thickening of arbitrary order are equivalent.** Let `G ⊂ X` be a
thickening of algebraic spaces over `S`, of arbitrary order. Base change along the inclusion,
`V ↦ G ×_X V`, is an equivalence of categories from the spaces-étale site of `X` to that of `G`.

This generalises `AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsFirstOrderThickening` to
arbitrary order; it is `AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickening`
packaged as an equivalence. -/
noncomputable def C1573.spacesEtaleEquivalenceOfIsThickening (hG : IsThickening B S hS X G) :
    SpacesEtale B S hS X ≌ SpacesEtale B S hS (IsThickening.space B S hS hG) :=
  letI := isEquivalence_spacesBaseChange_of_isThickening B S hS hG
  (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.asEquivalence

/-- The functor of the equivalence of
`AlgebraicGeometry.Space.C1573.spacesEtaleEquivalenceOfIsThickening` is base change along the
inclusion of the thickening. -/
theorem C1573.spacesEtaleEquivalenceOfIsThickening_functor (hG : IsThickening B S hS X G) :
    (spacesEtaleEquivalenceOfIsThickening B S hS hG).functor =
      (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor :=
  rfl

end Subspace

end AlgebraicGeometry.Space

end
