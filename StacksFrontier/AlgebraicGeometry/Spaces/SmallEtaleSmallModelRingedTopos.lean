module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleEquiUniverseModel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Morphism

/-!
# The equi-universe model of the small étale ringed topos of an algebraic space

`AlgebraicGeometry.Space.smallEtaleRingedTopos` is an
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`: the objects of the small étale site of an
algebraic space are its étale scheme charts, which live one universe above its morphisms and
above the sections of its structure sheaf.  That is the one universe shape in which the
ringed-topos machinery of this development — Stacks 06YY, 05VD, 07A4, and the localization of
Stacks 04IF — is unavailable.

The small étale site of an algebraic space is nevertheless essentially small at `u`
(`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`), so the generic construction of
`StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSmallModel` applies to it verbatim and
produces a `RingedTopos.{u, u, u}` model with a comparison whose structure map is an
isomorphism.  **Nothing about the construction is special to a scheme, and nothing new has to be
proved for an algebraic space**: this file only names the two comparison morphisms and records
that the model is, on the nose, the ringed topos of the ringed site
`AlgebraicGeometry.Space.smallEtaleModelRingedSite` that the development already carries — so
there is one model and not two.

## Main definitions

* `AlgebraicGeometry.Space.toSmallEtaleModelHom`: the comparison of the model with the small
  étale ringed topos of an algebraic space, as a morphism of ringed topoi
  `(model) ⟶ (X_étale, 𝒪_X)`.
* `AlgebraicGeometry.Space.fromSmallEtaleModelHom`: the comparison in the other direction, whose
  structure map is the identity.

## Main results

* `AlgebraicGeometry.Space.ringedTopos_smallEtaleModelRingedSite`: the generic equi-universe
  model of the small étale ringed topos is the ringed topos of
  `AlgebraicGeometry.Space.smallEtaleModelRingedSite`.
* `AlgebraicGeometry.Space.isIso_toSmallEtaleModelHom_fSharp`: the structure map of the
  comparison is an isomorphism, so the comparison is an equivalence of ringed topoi.

## Implementation notes

No essential-smallness argument is handed over by hand here, unlike in
`AlgebraicGeometry.SmallEtale.toEtaleHom` for the small étale site of a scheme:
`AlgebraicGeometry.Space.smallEtaleRingedTopos` is a reducible abbreviation, so its projection
`.C` reduces at instance transparency and instance search finds
`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall` at the generic spelling on its own.

## References

* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The equi-universe model of the small étale ringed topos of an algebraic space is the
ringed topos of `AlgebraicGeometry.Space.smallEtaleModelRingedSite`.**

The generic model of a ringed topos transports the topology and the structure sheaf along the
comparison of the site with a small model of it, and that is exactly how the small étale ringed
*site* of an algebraic space was transported; so the two agree on the nose, and there is one
model of the small étale ringed topos rather than two. -/
theorem ringedTopos_smallEtaleModelRingedSite
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    (smallEtaleModelRingedSite B S hS F hF).ringedTopos =
      RingedTopos.smallModel (SmallEtale.topology B S hS F) (structureSheaf B S hS F hF) :=
  rfl

variable (X : AlgebraicSpaces B S hS)

/-- **The comparison of the equi-universe model with the small étale ringed topos of an algebraic
space, as a morphism of ringed topoi `(model) ⟶ (X_étale, 𝒪_X)`.**  Its underlying continuous
functor is the comparison of the small étale site with its small model, and its structure map is
an isomorphism by `AlgebraicGeometry.Space.isIso_toSmallEtaleModelHom_fSharp`, so this is an
equivalence of ringed topoi and not merely a morphism.

Both source and target of the generic statements of the Stacks 06YY, 05VD and 07A4 chain are
`RingedTopos.{u, u, u}`, which the model is and `AlgebraicGeometry.Space.smallEtaleRingedTopos`
is not. -/
noncomputable def toSmallEtaleModelHom :
    RingedToposSiteHom
      (RingedTopos.smallModel (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2))
      (smallEtaleRingedTopos B S hS X) :=
  RingedTopos.toSmallModelHom (smallEtaleRingedTopos B S hS X)

/-- **The comparison is an equivalence of ringed topoi, not merely a morphism**: its structure
map is an isomorphism, being the component of the unit isomorphism of an equivalence of sheaf
categories. -/
theorem isIso_toSmallEtaleModelHom_fSharp : IsIso (toSmallEtaleModelHom B S hS X).fSharp :=
  RingedTopos.isIso_toSmallModelHom_fSharp (smallEtaleRingedTopos B S hS X)

/-- **The comparison in the other direction, as a morphism of ringed topoi
`(X_étale, 𝒪_X) ⟶ (model)`.**  Its structure map is the *identity*: the structure sheaf of the
model is by definition the restriction of the structure sheaf of the small étale site along the
comparison, so the two sides of the structure map are the same sheaf.

This is the morphism whose pushforward of sheaves of modules is restriction to the model. -/
noncomputable def fromSmallEtaleModelHom :
    RingedToposSiteHom (smallEtaleRingedTopos B S hS X)
      (RingedTopos.smallModel (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2)) :=
  RingedTopos.fromSmallModelHom (smallEtaleRingedTopos B S hS X)

end AlgebraicGeometry.Space

end
