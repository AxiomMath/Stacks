module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.Equivalence
import StacksCore.Tactic.StacksAttribute

/-!
# Abelian sheaves on the small étale site admit sheafification in every coefficient universe

Étale cohomology of a scheme `X : Scheme.{u}` is computed in the category
`Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}`, whose coefficient universe is one
step above the universe of the scheme: the small étale site `X.Etale` is a category of objects
in `Type (u + 1)` with morphisms in `Type u`, and a sheaf of abelian groups on it has sections
large enough to contain its own matching families. Mathlib's sheafification instance for the
small étale site is stated only for coefficients in `AddCommGrpCat.{u}`, because it asks the
coefficient category to be concrete over `Type u`; it therefore does not apply at the universe
in which étale cohomology lives, for any value of `v`.

This file supplies the missing instance. It is not extra mathematical content: the small étale
site is essentially small in the coefficient universe, abelian groups in the universe of a small
site admit sheafification, and `CategoryTheory.hasSheafifyEssentiallySmallSite` transports that
along the equivalence with a small model.

## Main results

* `AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology`: abelian sheaves on the small étale
  site of a scheme admit sheafification, with coefficients in `AddCommGrpCat.{max (u + 1) v}`
  for every `v`.

## Implementation notes

The instance is stated at the coefficient universe `max (u + 1) v` rather than at an arbitrary
`w`, because that is the shape in which every consumer in this library writes it, and because
`max (u + 1) v` is exactly the family of universes in which the hypothesis is true by this
argument: the small model of `X.Etale` lives in the coefficient universe, which must therefore
be at least `u + 1`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme

/-- Abelian sheaves on the small étale site of a scheme `X : Scheme.{u}` admit sheafification,
for coefficients in `AddCommGrpCat.{max (u + 1) v}` with `v` arbitrary.

The small étale site `X.Etale` has objects in `Type (u + 1)` and morphisms in `Type u`, so it
is essentially small in the coefficient universe `max (u + 1) v`; abelian groups in the
universe of a small site admit sheafification, and
`CategoryTheory.hasSheafifyEssentiallySmallSite` transports that along the equivalence with a
small model. Mathlib's instance for this site covers only `AddCommGrpCat.{u}`, which is never
the universe in which étale cohomology of `X` is computed. -/
instance (priority := low) hasSheafify_smallEtaleTopology (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  letI : HasSheafify ((equivSmallModel.{max (u + 1) v} X.Etale).inverse.inducedTopology
      X.smallEtaleTopology) AddCommGrpCat.{max (u + 1) v} := inferInstance
  hasSheafifyEssentiallySmallSite.{u, _, u + 1, _, max (u + 1) v} X.smallEtaleTopology _

end AlgebraicGeometry.Scheme

end
