module

public import StacksFrontier.CategoryTheory.Sites.SlicePost.MorphismOfSitesGeneral
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 04J0: localizing a morphism of ringed sites

Let `(f, f^♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites, given by a continuous functor
`u : D ⥤ C`, let `V` be an object of `D` and put `U = u(V)`.  Stacks 04J0 constructs the localized
morphism of ringed sites `(f', (f')^♯) : (C/U, O_U) ⟶ (D/V, O'_V)`.

The underlying functor is `Over.post u : Over V ⥤ Over U`, which is a morphism of sites by Stacks
03CF clause (a) — `Functor.isMorphismOfSites_overPost_of_isMorphismOfSites`, available here in the
generality of 03CF, so that no finite-limit or flatness hypothesis is imposed on `u`.  The
structure map is, as Stacks says, "just the restriction of `f^♯`": the localized structure sheaves
are `O_U = j_U^{-1}O` and `O'_V = j_V^{-1}O'` by definition of
`AlgebraicGeometry.RingedSite.over`, and clause (d) of 03CF
(`CategoryTheory.sheafPushforwardContinuous_overPost_eq`) is a *strict* equality of functors, so
`j_V^{-1}(f^♯)` already has the type required of `(f')^♯`, with no comparison map inserted.

`StacksFrontier/CategoryTheory/Sites/Modules/LocalizationRingedSites/MorphismLocalization.lean`
records the characterisation of this structure map
(`AlgebraicGeometry.RingedSite.MorphismLocalization.localizedStructureMap_comp_comparisonIso_hom`)
and the two direct-image formulas, taking the continuity of `Over.post u` as a hypothesis; this
file is what supplies that hypothesis and assembles the morphism of ringed sites itself.

## Main definitions

* `AlgebraicGeometry.RingedSite.Hom.localized`: the localized morphism of ringed sites.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.localized_u` and `.localized_fsharp`: its two components.

## References

* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSite.Hom

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

/-- **Stacks 04J0.** The localization of a morphism of ringed sites at an object `V` of the
target: the underlying functor is `Over.post u`, a morphism of sites by Stacks 03CF clause (a),
and the structure map is the restriction `j_V^{-1}(f^♯)` of the structure map of `f`.

That this typechecks is the content of the choice: the target of `j_V^{-1}(f^♯)` is
`j_V^{-1}f_*O`, which is `f'_*j_U^{-1}O = f'_*O_U` by the strict identity of Stacks 03CF, so no
comparison isomorphism intervenes. -/
@[stacks 04J0 "(1): the localized morphism of ringed sites, with its canonical structure map
  `(f')♯ = j_V^{-1}(f♯)`"]
noncomputable def localized :
    RingedSite.Hom (X.over (f.u.obj V)) (Y.over V) where
  u := Over.post (X := V) f.u
  isMorphismOfSites := Functor.isMorphismOfSites_overPost_of_isMorphismOfSites Y.J X.J f.u V
    f.isMorphismOfSites
  fsharp := (Y.J.overPullback CommRingCat.{u} V).map f.fsharp

/-- The underlying functor of `f.localized V` is `Over.post f.u`. -/
@[simp]
theorem localized_u : (f.localized V).u = Over.post (X := V) f.u := rfl

/-- The structure map of `f.localized V` is the restriction of the structure map of `f` along
`Y.J.overPullback CommRingCat V`. -/
@[simp]
theorem localized_fsharp :
    (f.localized V).fsharp = (Y.J.overPullback CommRingCat.{u} V).map f.fsharp := rfl

end AlgebraicGeometry.RingedSite.Hom

end
