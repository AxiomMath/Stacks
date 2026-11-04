module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by the empty set for sheaves of sets on small étale sites

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`.
Restriction of sheaves of sets along `j` is the direct image of the continuous site functor
`AlgebraicGeometry.smallEtalePostcompose`, that is, precomposition with "an étale scheme over
`U` is an étale scheme over `X`". This file constructs its left adjoint `j_!`, together with
the adjunction that characterises it.

For sheaves of sets the left adjoint extends a sheaf by the *empty* set rather than by zero:
on presheaves it is the left Kan extension `V ↦ ⨿_{V → U} F(V → U)`, an empty coproduct where
`V` admits no map to `U` over `X`, and `j_!F` is the sheafification of that. The names
*extension by zero* and `j_!` are reserved by the source for the abelian and module cases,
parts (2) and (3) of Stacks 03S3, which are in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ExtensionByZeroBaseChange/Adjunction.lean`.

## Main definitions

* `AlgebraicGeometry.setRestriction` — restriction `j^{-1}` of étale sheaves of sets.
* `AlgebraicGeometry.setExtensionByEmpty` — its left adjoint `j_!^{Sh}`.

## Main results

* `AlgebraicGeometry.setExtensionByEmptyAdjunction` — the defining adjunction
  `j_!^{Sh} ⊣ j^{-1}`, which is Stacks 03S3, part (1).

## Implementation notes

The construction is the general sheaf-pullback of a continuous functor of sites, exactly as
for abelian sheaves and sheaves of modules, so the characterising property is the adjunction
rather than a hand-built colimit.

Sheafification of `Type`-valued presheaves on the small étale site is available because that
site is essentially small at `max (u + 1) v`, where `u` is the universe of the schemes; this
is `AlgebraicGeometry.setSheaf_hasWeakSheafify`. The coefficient universe is therefore at
least that of the objects of the site, with the extra parameter `v` left arbitrary, as it is
for the coproducts defining the presheaf extension.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- Presheaves of sets on the small étale site of a scheme in a big étale site admit
sheafification at the universe `max (u + 1) v`: that site is essentially small there, so
sheafification is transported from a small model. -/
public instance (priority := low) setSheaf_hasWeakSheafify :
    HasWeakSheafify (SmallEtale.topology B X hX) (Type (max (u + 1) v)) := by
  have : HasSheafify (SmallEtale.topology B X hX) (Type (max (u + 1) v)) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) v} _ _
  infer_instance

/-- Restriction of étale sheaves of sets along the étale morphism `U ⟶ X`: the direct image
of the continuous site functor `AlgebraicGeometry.smallEtalePostcompose`, that is, the sheaf
`V ↦ F(V ⟶ U ⟶ X)` on the small étale site of `U`. -/
public abbrev setRestriction :
    Sheaf (SmallEtale.topology B X hX) (Type (max (u + 1) v)) ⥤
      Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        (Type (max (u + 1) v)) :=
  (smallEtalePostcompose B X hX U).sheafPushforwardContinuous
    (Type (max (u + 1) v))
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- **Stacks 03S3, part (1).** Extension by the empty set of étale sheaves of sets along the
étale morphism `U ⟶ X`: the sheafification of `V ↦ ⨿_{V → U} F(V → U)`, realised as the sheaf
pullback of the continuous site functor `AlgebraicGeometry.smallEtalePostcompose`. -/
@[stacks 03S3 "sheaves_of_sets"]
public def setExtensionByEmpty :
    Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        (Type (max (u + 1) v)) ⥤
      Sheaf (SmallEtale.topology B X hX) (Type (max (u + 1) v)) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallEtalePostcompose B X hX U)
    (Type (max (u + 1) v))
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- **Stacks 03S3, part (1).** Restriction of étale sheaves of sets along `U ⟶ X` has a left
adjoint, namely extension by the empty set. This adjunction is the property characterising
it. -/
@[stacks 03S3 "sheaves_of_sets"]
public def setExtensionByEmptyAdjunction :
    setExtensionByEmpty.{u, v} B X hX U ⊣ setRestriction.{u, v} B X hX U :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtalePostcompose B X hX U)
    (Type (max (u + 1) v))
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- Extension by the empty set is a left adjoint, hence preserves colimits. -/
public instance setExtensionByEmpty_isLeftAdjoint :
    (setExtensionByEmpty.{u, v} B X hX U).IsLeftAdjoint :=
  (setExtensionByEmptyAdjunction B X hX U).isLeftAdjoint

end AlgebraicGeometry

end
