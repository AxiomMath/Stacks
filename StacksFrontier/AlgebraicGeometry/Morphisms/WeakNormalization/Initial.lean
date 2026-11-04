module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic

/-!
# Categories of universal homeomorphisms over a scheme

For a scheme `X` there are two categories of schemes over `X` governing its weak
normalization theory: the universal homeomorphisms to `X`, and those among them which
additionally induce isomorphisms on all residue fields. Their initial objects are the
absolute weak normalization and the seminormalization of `X`.

## Main definitions

* `AlgebraicGeometry.UniversalHomeomorphismOver` is the category of universal
  homeomorphisms to a fixed scheme.
* `AlgebraicGeometry.UniversalHomeomorphismOver.pullback` is the base change of a universal
  homeomorphism.
* `AlgebraicGeometry.IsSeminormalizationCandidate` is the property cutting out the objects
  of the seminormalization category.
* `AlgebraicGeometry.SeminormalizationCategory` is the category of universal homeomorphisms
  to `X` which induce isomorphisms on residue fields.
* `AlgebraicGeometry.HasLocallyInitialUniversalHomeomorphismOver` records that the initial
  universal homeomorphism over `X` exists and stays initial after restriction to an open
  subscheme.

## Main results

* `AlgebraicGeometry.isInitial_pullback_initial` supplies the initiality of the pullback of
  the chosen initial object along an open immersion.

## Implementation notes

Both categories are full subcategories of `Over X`. Consequently their morphisms are exactly
scheme morphisms over `X`, and categorical initiality simultaneously records existence and
uniqueness of the compatible map out of the initial object.

`HasLocallyInitialUniversalHomeomorphismOver` also records the compatibility with open
restriction supplied by the affine gluing construction. Its parent instance provides the
usual `HasInitial` interface. Recording both properties together lets an affine-local
argument use restriction without assuming the global statement itself.

## References

* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The category of universal homeomorphisms to `X`, with morphisms over `X`. -/
abbrev UniversalHomeomorphismOver (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (fun Y : Over X =>
    UniversalHomeomorphism Y.hom)

/-- Base change of a universal homeomorphism to `X` along a morphism `U ⟶ X`. -/
noncomputable def UniversalHomeomorphismOver.pullback {X U : Scheme.{u}}
    (f : U ⟶ X) (Y : UniversalHomeomorphismOver X) : UniversalHomeomorphismOver U :=
  ⟨Over.mk (Limits.pullback.fst f Y.obj.hom), ⟨
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f Y.obj.hom |>.flip)
      Y.property.universally_isHomeomorph⟩⟩

/-- The initial universal homeomorphism exists and remains initial after restriction to
any open subscheme, as in the affine gluing construction of 0EUS. -/
class HasLocallyInitialUniversalHomeomorphismOver (X : Scheme.{u}) : Prop
    extends HasInitial (UniversalHomeomorphismOver X) where
  /-- Restricting the chosen initial universal homeomorphism along an open immersion
  gives an initial universal homeomorphism over the open subscheme. -/
  nonempty_isInitial_pullback (U : Scheme.{u}) (f : U ⟶ X) [IsOpenImmersion f] :
    Nonempty (IsInitial (UniversalHomeomorphismOver.pullback f
      (initial (UniversalHomeomorphismOver X))))

/-- The pullback of the chosen absolute weak normalization along an open immersion is
initial among universal homeomorphisms to the open subscheme. In particular, this applies
to every affine open subscheme. -/
noncomputable def isInitial_pullback_initial {X U : Scheme.{u}}
    [HasLocallyInitialUniversalHomeomorphismOver X] (f : U ⟶ X) [IsOpenImmersion f] :
    IsInitial (UniversalHomeomorphismOver.pullback f
      (initial (UniversalHomeomorphismOver X))) :=
  Classical.choice
    (HasLocallyInitialUniversalHomeomorphismOver.nonempty_isInitial_pullback U f)

/-- The property defining the objects among schemes over `X` which occur in the
seminormalization category. -/
def IsSeminormalizationCandidate (X : Scheme.{u}) : ObjectProperty (Over X) :=
  fun Y => UniversalHomeomorphism Y.hom ∧
    ∀ y : Y.left, IsIso (Y.hom.residueFieldMap y)

/-- The category of universal homeomorphisms to `X` which induce isomorphisms on residue
fields. -/
abbrev SeminormalizationCategory (X : Scheme.{u}) :=
  (IsSeminormalizationCandidate X).FullSubcategory

end AlgebraicGeometry

end
