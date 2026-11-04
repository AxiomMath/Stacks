module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRestrictConservative
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationSiteKind
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationSiteKindExtensions

/-!
# A morphism of quasi-coherent modules on the slice `𝒳_τ/x` is invertible over the opens of `U`

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `x` an object of `𝒳` lying
over a scheme `U`.  By Stacks 06W0 the slice `𝒳_τ/x` *is* the big `τ`-site `(Sch/U)_τ`, and
`AlgebraicGeometry.FibredSite.localizationModulesEquivalenceKind'` transports a sheaf of modules
across that identification.  Downstairs, restriction to the small Zariski site of `U` reflects
isomorphisms between modules quasi-coherent on `(Sch/U)_τ`
(`AlgebraicGeometry.BigFppfOver.isIso_of_isIso_val_app_opensToBig`).  This file carries that
across the identification:

> a morphism of modules quasi-coherent on `𝒳_τ/x` is invertible as soon as its components are
> invertible at the objects of `𝒳_τ/x` corresponding to the opens of `U`.

Nothing of Descent, Proposition 03DX is re-proved, and nothing is assumed.  Only two facts about
the transport are used, and both are already in the tree: quasi-coherence is carried across it
(`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_localization_iff_kind'`), and its inverse is
a `CategoryTheory.SheafOfModules.pushforward` — of the structure map
`Stacks.SheafOfModules.reindexBackSharp` along
`AlgebraicGeometry.FibredSite.localizationEquivalence'`'s inverse — so its components are
components of the original morphism, up to a restriction of scalars that reflects invertibility.

## The shape of the hypothesis

The objects of the slice named in the hypothesis are
`(localizationEquivalence' …).inverse.obj ((opensToBig …).obj V)`, one for each open `V` of `U`.
That is the honest form: the equivalence of Stacks 06W0 is got from essential surjectivity of
`CategoryTheory.Over.post p` and has no formula on objects, so the object of `𝒳/x` lying over an
open of `U` can only be named through the inverse.  A consumer that holds its hypothesis at some
*other* object of `𝒳/x` can move it there by
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_iso_obj`, invertibility of a
component depending only on the isomorphism class of the object.

## The module universe

Everything here is at the module universe `u` of the schemes, and that is forced from below
rather than chosen: the statement downstairs is about
`AlgebraicGeometry.BigFppfOver.baseRestrictModule`, whose target is
`AlgebraicGeometry.Scheme.Modules` — `CategoryTheory.SheafOfModules.{u}` with no module universe
parameter at all, because `CategoryTheory.SheafOfModules.isQuasicoherent` takes the module
universe to *be* the universe of the sections of its sheaf of rings.  The two universes `v` and
`w` of `𝒳` stay free.

## Main results

* `AlgebraicGeometry.FibredSite.isIso_of_isIso_val_app_localizationOpens`: **the criterion** —
  invertibility at the slice objects over the opens of `U` suffices.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **A morphism of modules quasi-coherent on the slice `𝒳_τ/x` is invertible as soon as its
components at the slice objects corresponding to the opens of `U = p(x)` are invertible**, with
no hypothesis.

Transported along the identification `𝒳_τ/x = (Sch/U)_τ` of Stacks 06W0, this is
`AlgebraicGeometry.BigFppfOver.isIso_of_isIso_val_app_opensToBig`: restriction to the small
Zariski site of `U` reflects isomorphisms between modules quasi-coherent on the big `τ`-site of
`U`.  The transport costs nothing — quasi-coherence crosses it by
`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_localization_iff_kind'`, its inverse is a
`CategoryTheory.SheafOfModules.pushforward` so the components match, and an equivalence reflects
isomorphisms. -/
public theorem isIso_of_isIso_val_app_localizationOpens (τ : SiteKind) (x : 𝒳)
    {M N : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp τ).over x)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N)
    (h : ∀ V : (baseScheme' B S hS p x).Opens,
      IsIso (φ.val.app (op ((localizationEquivalence' B S hS p hp x).inverse.obj
        ((BigFppfOver.opensToBig B (baseScheme' B S hS p x)
          (contains_baseScheme' B S hS p x)).obj V))))) :
    IsIso φ := by
  have hinv :
      IsIso ((localizationModulesEquivalenceKind' B S hS p hp τ x).symm.functor.map φ) := by
    refine BigFppfOver.isIso_of_isIso_val_app_opensToBig B (baseScheme' B S hS p x)
      (contains_baseScheme' B S hS p x) τ
      ((isQuasicoherentOnSite_localization_iff_kind' B S hS p hp τ x M).1 hM)
      ((isQuasicoherentOnSite_localization_iff_kind' B S hS p hp τ x N).1 hN) _ fun V => ?_
    exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_pushforward_map
      (Stacks.SheafOfModules.reindexBackSharp (localizationEquivalence' B S hS p hp x)
        (baseRingStructureSheaf B (baseScheme' B S hS p x)
          (contains_baseScheme' B S hS p x) τ)) φ
      (op ((BigFppfOver.opensToBig B (baseScheme' B S hS p x)
        (contains_baseScheme' B S hS p x)).obj V)) (h V)
  exact (localizationModulesEquivalenceKind' B S hS p hp τ
    x).symm.fullyFaithfulFunctor.isIso_of_isIso_map φ

end AlgebraicGeometry.FibredSite

end
