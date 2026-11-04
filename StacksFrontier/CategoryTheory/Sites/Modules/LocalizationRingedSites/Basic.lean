module

public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Pullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Localization of a ringed site

Let `(C, O)` be a ringed site and `U` an object of `C`. The localization of `(C, O)` at `U` is
the ringed site whose underlying site is the slice `C/U` and whose structure sheaf is the
restriction `O|_U`, and the localization is realized as a morphism of ringed topoi
`π : (Sh(C/U), O|_U) ⟶ (Sh(C), O)` whose inverse image is restriction along `Over.forget U`.
Sheaves of modules travel along `π` in both directions: the direct image is `j_{U*}`, its left
adjoint extension by zero is `j_{U!}`, and pullback along `π` is restriction to the slice.

This module collects those five constituents of the localization of a ringed site and records
them against the Stacks Project. Each is already available in the library, so nothing is
reconstructed here.

## Main results

The constituents of the localization, in the order the source presents them:

* `AlgebraicGeometry.RingedSite.over` is the localized ringed site.
* `AlgebraicGeometry.RingedSite.localizationMorphism` is the localization morphism of ringed
  topoi.
* `AlgebraicGeometry.RingedSite.localizationDirectImage` is the direct image `j_{U*}` of
  sheaves of modules along it.
* `SheafOfModules.pullback`, with its adjunction
  `SheafOfModules.pullbackPushforwardAdjunction` and the exactness
  `Stacks.Sites.ExtensionByZero.extensionByZero_exact`, is extension by zero `j_{U!}`.
* `SheafOfModules.over` and `SheafOfModules.overFunctor` are restriction of modules to the
  slice; `AlgebraicGeometry.RingedSite.localizationPullbackIsoRestriction_exists` identifies
  it with pullback along the localization morphism, and
  `AlgebraicGeometry.RingedSite.moduleRestriction_obj` computes its sections.

## Implementation notes

Extension by zero is Mathlib's `SheafOfModules.pullback` specialized to `Over.forget U` and the
identity of the restricted sheaf of rings, rather than a separately chosen construction: it is
then the canonical left adjoint of restriction, which is the characterization the source uses.
Restriction of modules is likewise Mathlib's `SheafOfModules.overFunctor`.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

namespace AlgebraicGeometry.RingedSite

add_to_stacks 04IX "localized_ringed_site" AlgebraicGeometry.RingedSite.over
add_to_stacks 04IX "localization_morphism" AlgebraicGeometry.RingedSite.localizationMorphism
add_to_stacks 04IX "localization_direct_image"
  AlgebraicGeometry.RingedSite.localizationDirectImage
add_to_stacks 04IX "extension_by_zero" SheafOfModules.pullback
add_to_stacks 04IX "extension_by_zero" SheafOfModules.pullbackPushforwardAdjunction
add_to_stacks 04IX "extension_by_zero" Stacks.Sites.ExtensionByZero.extensionByZero_exact

end AlgebraicGeometry.RingedSite

end
