module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctors

/-!
# The locally Noetherian subcategory of schemes over a base

Let `S` be a locally Noetherian scheme. The locally Noetherian objects of `Sch/S` form a full
subcategory which satisfies conditions (1) and (2) of Stacks 0EUW: an affine open of a locally
Noetherian scheme is locally Noetherian, and an affine scheme of finite presentation over an
affine open of `S` is of finite type over a Noetherian scheme, hence locally Noetherian. Both
conditions hold on the nose rather than up to isomorphism, the witnessing object being the open
subobject respectively the given scheme over `S` itself.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.IsLocallyNoetherianOver`: the full subcategory
  `(Noetherian/S)` of `Sch/S`, as an object property.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.hasAffineOpens_isLocallyNoetherianOver`: condition (1) of
  Stacks 0EUW for the locally Noetherian subcategory.
* `AlgebraicGeometry.ExtendingFunctors.hasFinitePresentationAffines_isLocallyNoetherianOver`:
  condition (2) of Stacks 0EUW for the locally Noetherian subcategory, for a locally Noetherian
  base.

## Implementation notes

Condition (2) needs the base to be locally Noetherian and nothing else: its affine opens are then
Noetherian, and a morphism of finite presentation is in particular locally of finite type, so the
source of such a morphism is locally Noetherian.

## References

* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 0GE1](https://stacks.math.columbia.edu/tag/0GE1)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.ExtendingFunctors

universe u

variable {S : Scheme.{u}}

/-- The objects of `Sch/S` whose underlying scheme is locally Noetherian: the full subcategory
`(Noetherian/S)` of the source. -/
def IsLocallyNoetherianOver : ObjectProperty (Over S) := fun X => IsLocallyNoetherian X.left

/-- An object of `Sch/S` lies in `IsLocallyNoetherianOver` if and only if its underlying scheme
is locally Noetherian. -/
lemma isLocallyNoetherianOver_iff {X : Over S} :
    IsLocallyNoetherianOver X ↔ IsLocallyNoetherian X.left := Iff.rfl

/-- **Condition (1) of Stacks 0EUW for the locally Noetherian subcategory.** An affine open of a
locally Noetherian object of `Sch/S` is again a locally Noetherian object of `Sch/S`. -/
theorem hasAffineOpens_isLocallyNoetherianOver :
    HasAffineOpens (IsLocallyNoetherianOver (S := S)) := fun X hX V =>
  have : IsLocallyNoetherian X.left := hX
  ⟨overOpen X V.1, isLocallyNoetherian_of_isOpenImmersion V.1.ι, ⟨Iso.refl _⟩⟩

/-- **Condition (2) of Stacks 0EUW for the locally Noetherian subcategory.** Over a locally
Noetherian base, an affine scheme of finite presentation over an affine open of the base is a
locally Noetherian object of `Sch/S`. -/
theorem hasFinitePresentationAffines_isLocallyNoetherianOver [IsLocallyNoetherian S] :
    HasFinitePresentationAffines (IsLocallyNoetherianOver (S := S)) := fun U _V g _ hg =>
  have : IsLocallyNoetherian U.1.toScheme := isLocallyNoetherian_of_isOpenImmersion U.1.ι
  have : LocallyOfFinitePresentation g := hg.1
  ⟨Over.mk (g ≫ U.1.ι), LocallyOfFiniteType.isLocallyNoetherian g, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.ExtendingFunctors

end
