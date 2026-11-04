module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite

/-!
# Sheafification of abelian presheaves on the Zariski comparison sites

The comparison morphism of topoi `π_X : Sh(LC_Zar/X) → Sh(X_Zar)` of an object `X` of the
locally quasi-compact Zariski site has a site on each side: the small Zariski site `Opens X` of
the underlying space, and the localized site `LC_Zar/X`. Both sites are essentially small in the
coefficient universe, so abelian presheaves with coefficients in `AddCommGrpCat.{max (u + 1) v}`
admit sheafification on each. For coefficients in `Type` the second statement is
`hasSheafify_zariskiTopology_over`.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.essentiallySmall_opens`: the small
  Zariski site of the space of an object is essentially small in the coefficient universe.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.hasSheafify_opensSite`: abelian
  presheaves on it admit sheafification.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.hasSheafify_zariskiSlice`: abelian
  presheaves on the localized Zariski site admit sheafification.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u w v

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)

/-- The small Zariski site of the space of an object of the locally quasi-compact Zariski site
is essentially small in any universe containing the universe `u` of the spaces: the open subsets
of the space and the inclusions between them both live in `Type u`. -/
theorem essentiallySmall_opens : EssentiallySmall.{max (u + 1) v} (Opens X.obj) :=
  EssentiallySmall.mk' (AsSmall.equiv.{u, u, max (u + 1) v} (C := Opens X.obj))

/-- **Abelian presheaves on the small Zariski site of the space of an object admit
sheafification**, with coefficients in `AddCommGrpCat.{max (u + 1) v}`, because that site is
essentially small in that universe (`essentiallySmall_opens`). -/
theorem hasSheafify_opensSite :
    HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} :=
  have := essentiallySmall_opens.{u, w, v} S X
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) v} _ _

/-- **Abelian presheaves on the localized Zariski site of an object admit sheafification**, with
coefficients in `AddCommGrpCat.{max (u + 1) v}`, because the slice of the bounded site over that
object is essentially small in that universe (`essentiallySmall_over`). This is
`hasSheafify_zariskiTopology_over` at abelian coefficients instead of `Type`. -/
theorem hasSheafify_zariskiSlice :
    HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v} :=
  have := essentiallySmall_over.{u, w, max (u + 1) v} S X
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) v} _ _

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
