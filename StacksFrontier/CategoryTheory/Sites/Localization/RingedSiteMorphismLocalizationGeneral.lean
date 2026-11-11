module

public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteMorphismLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral

/-!
# Stacks 04J0 at independent site universes

Let `(f, f^♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites, given by a continuous functor
`u : D ⥤ C`, let `V` be an object of `D` and put `U = u(V)`.  Stacks 04J0 constructs the localized
morphism of ringed sites `(f', (f')^♯) : (C/U, O_U) ⟶ (D/V, O'_V)`.

`AlgebraicGeometry.RingedSite.Hom.localized` does this for
`AlgebraicGeometry.RingedSite.Hom`, whose two endpoints are forced into one
`RingedSite.{u, u, u}`: the objects of a site, its morphisms and the sections of its structure
sheaf all share a universe.  No site of schemes in this development qualifies — the small étale
site of a scheme is a `RingedSite.{u + 1, u, u}` — so the morphism `ε` of Stacks 08H7 is not a
`RingedSite.Hom` and cannot be localized by that declaration.  This file localizes
`AlgebraicGeometry.RingedSite.HomGeneral` instead, whose source and target object and morphism
universes are independent and which asks only that the two sections universes agree.

## The site condition of the localized morphism is a hypothesis

`AlgebraicGeometry.RingedSite.Hom.localized` discharges Stacks 03CF clause (a) — that
`u' = Over.post u` again defines a morphism of sites — by
`CategoryTheory.Functor.isMorphismOfSites_overPost_of_isMorphismOfSites`, which is stated for two
sites that are *small* in one universe: `C D : Type u` with `SmallCategory`, and sheaves of sets
valued in that same `Type u`.  At independent universes no such statement is available, so
`AlgebraicGeometry.RingedSite.HomGeneral.localized` takes it as a hypothesis, in the unrestricted
form `IsMorphismOfSites.{w}` that `HomGeneral` itself uses.  Everything else about the localized
morphism — in particular that its canonical structure map typechecks on the nose — is universe
independent and is supplied here.

The hypothesis is not vacuous and is not the conclusion: on the range where
`AlgebraicGeometry.RingedSite.Hom` is defined it is discharged by the small-site clause (a)
through `CategoryTheory.Functor.IsMorphismOfSites.toIsMorphismOfSites`, and the resulting
localized morphism is the widening of the one `Hom.localized` produces.  That is
`AlgebraicGeometry.RingedSite.Hom.toHomGeneral_localized`.

## The structure map

As in the one-universe case the structure map is "just the restriction of `f^♯`", with no
comparison map inserted: the localized structure sheaves are `O_U = j_U^{-1}O` and
`O'_V = j_V^{-1}O'` by definition of `AlgebraicGeometry.RingedSite.over`, and clause (d) of
Stacks 03CF — `CategoryTheory.sheafPushforwardContinuous_overPost_eq` — is a *strict* equality of
functors which holds at arbitrary universes and for sheaves valued in any category.  So
`j_V^{-1}(f^♯)` already has the type required of `(f')^♯`.

## Main definitions

* `AlgebraicGeometry.RingedSite.HomGeneral.localized`: the localized morphism of ringed sites, at
  independent universes.

## Main results

* `AlgebraicGeometry.RingedSite.HomGeneral.localized_u` and `.localized_fsharp`: its two
  components.
* `AlgebraicGeometry.RingedSite.Hom.toHomGeneral_localized`: the construction extends
  `AlgebraicGeometry.RingedSite.Hom.localized`.

## References

* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
-/

@[expose] public section

open CategoryTheory

universe w uX vX uY vY u

namespace AlgebraicGeometry.RingedSite

namespace HomGeneral

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : HomGeneral X Y) (V : Y.C)

/-- **The construction of Stacks 04J0 at independent site universes.** The localization of a morphism of ringed
sites at an object `V` of the target, with the object and morphism universes of the source
independent of those of the target: the underlying functor is `Over.post u` and the structure map
is the restriction `j_V^{-1}(f^♯)` of the structure map of `f`.

That `j_V^{-1}(f^♯)` typechecks as the structure map is the content of the choice, exactly as at
`AlgebraicGeometry.RingedSite.Hom.localized`: its target is `j_V^{-1}f_*O`, which *is*
`f'_*j_U^{-1}O = f'_*O_U` by the strict identity `sheafPushforwardContinuous_overPost_eq` of
Stacks 03CF clause (d), so no comparison isomorphism intervenes.  That identity is proved at
independent universes, so nothing has to be redone for it here.

Clause (a) of Stacks 03CF, that `Over.post u` again defines a morphism of sites, is the
hypothesis `hu`.  It is available in this repository only for two sites small in one universe
(`CategoryTheory.Functor.isMorphismOfSites_overPost_of_isMorphismOfSites`), which is the one case
in which `AlgebraicGeometry.RingedSite.Hom` already applies; see the module docstring.  Stacks
04J0 itself is registered on `AlgebraicGeometry.RingedSite.Hom.localized`, which needs no such
hypothesis. -/
noncomputable def localized
    (hu : IsMorphismOfSites.{w} (Over.post (X := V) f.u) (Y.J.over V) (X.J.over (f.u.obj V))) :
    HomGeneral (X.over (f.u.obj V)) (Y.over V) where
  u := Over.post (X := V) f.u
  isMorphismOfSites := hu
  fsharp := (Y.J.overPullback CommRingCat.{w} V).map f.fsharp

/-- The underlying functor of the localization of `f` at `V` is `Over.post f.u`. -/
@[simp]
theorem localized_u
    (hu : IsMorphismOfSites.{w} (Over.post (X := V) f.u) (Y.J.over V) (X.J.over (f.u.obj V))) :
    (f.localized V hu).u = Over.post (X := V) f.u := rfl

/-- The structure map of the localization of `f` at `V` is the restriction `j_V^{-1}(f^♯)` of
the structure map of `f`. -/
@[simp]
theorem localized_fsharp
    (hu : IsMorphismOfSites.{w} (Over.post (X := V) f.u) (Y.J.over V) (X.J.over (f.u.obj V))) :
    (f.localized V hu).fsharp = (Y.J.overPullback CommRingCat.{w} V).map f.fsharp := rfl

end HomGeneral

namespace Hom

variable {X Y : RingedSite.{u, u, u}} (f : Hom X Y) (V : Y.C)

/-- **Stacks 03CF clause (a) for the localized functor of a morphism of ringed sites in a single
universe**, in the unrestricted form that `AlgebraicGeometry.RingedSite.HomGeneral` asks for.

This is `CategoryTheory.Functor.isMorphismOfSites_overPost_of_isMorphismOfSites` read through
`CategoryTheory.Functor.IsMorphismOfSites.toIsMorphismOfSites`, and it is what discharges the
hypothesis of `AlgebraicGeometry.RingedSite.HomGeneral.localized` on the range where
`AlgebraicGeometry.RingedSite.Hom` is defined. -/
theorem isMorphismOfSites_overPost :
    IsMorphismOfSites.{u} (Over.post (X := V) f.u) (Y.J.over V) (X.J.over (f.u.obj V)) :=
  (Functor.isMorphismOfSites_overPost_of_isMorphismOfSites Y.J X.J f.u V
    f.isMorphismOfSites).toIsMorphismOfSites

/-- **The localization at independent universes extends the localization of Stacks 04J0.**  The
widening of the localized morphism of ringed sites of
`AlgebraicGeometry.RingedSite.Hom.localized` is the localization of the widened morphism: both
have underlying functor `Over.post u` and structure map `j_V^{-1}(f^♯)`, so they agree by `rfl`,
the site conditions being propositions. -/
theorem toHomGeneral_localized :
    f.toHomGeneral.localized V (f.isMorphismOfSites_overPost V) = (f.localized V).toHomGeneral :=
  rfl

end Hom

end AlgebraicGeometry.RingedSite

end
