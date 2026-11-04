module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverTerminal
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits

/-!
# Generating sections across an equivalence of ringed sites

Let `e : C' ≌ C` be an equivalence of sites which is continuous in both directions and let `R` be
a sheaf of rings on `C`.  Reindexing along `e` is an equivalence of the categories of sheaves of
modules, `Stacks.SheafOfModules.reindexEquivalence`, and it carries the unit module to the unit
module of the transported sheaf of rings on the nose; so it carries a family of generating
sections to a family of generating sections, and through its inverse it *reflects* one.  This
file holds that reflection, and the case of the restriction to the slice over a **terminal**
object, where the equivalence of sites is `CategoryTheory.Over.equivalenceOfIsTerminal`.

The reflection is what a construction of generating sections needs when the module is given only
on another presentation of the site.  The case at hand is a module on the slice of the small
étale site of an algebraic space at an étale chart: such a module is a module on the small étale
site of the chart space by the comparison of Stacks 04M0, and the generating sections produced
there have to travel back to the slice.

## Main definitions

* `Stacks.SheafOfModules.generatingSectionsOfReindex`: **reindexing along an equivalence of sites
  reflects generating sections.**  A family of generating sections of the reindexing of `M` is a
  family of generating sections of `M`.
* `Stacks.SheafOfModules.generatingSectionsOfOverTerminal`: **restriction to the slice over a
  terminal object reflects generating sections.**

## Implementation notes

The transport itself is Mathlib's `SheafOfModules.GeneratingSections.map`, which asks for a
functor of module categories preserving colimits together with an isomorphism of the two unit
modules.  The functor is the inverse of `Stacks.SheafOfModules.reindexEquivalence` and the
isomorphism is the unit isomorphism of that equivalence evaluated at the unit module, which
typechecks at the type required because the reindexing of the unit module *is* the unit module of
the transported sheaf of rings.  The round trip is undone by
`SheafOfModules.GeneratingSections.equivOfIso`; using
`SheafOfModules.GeneratingSections.ofEpi` at the inverse of that isomorphism instead would ask
instance search for `CategoryTheory.Epi` of an `CategoryTheory.Iso.inv`, which it does not find
at this type.

`SheafOfModules.GeneratingSections.map` asks for `CategoryTheory.HasSheafify` on the target site,
where the statements here carry only `CategoryTheory.HasWeakSheafify`; the strengthening is
`AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective`, which applies because the
local equivalences of presheaves of abelian groups are the locally bijective morphisms — the
second standing hypothesis of both statements.

For the slice over a terminal object the equivalence of sites is
`CategoryTheory.Over.equivalenceOfIsTerminal`, whose functor is `CategoryTheory.Over.forget`.
Its continuity is a Mathlib instance; the continuity of its inverse comes from
`CategoryTheory.GrothendieckTopology.isDenseSubsite_overForget` through
`CategoryTheory.Equivalence`'s transfer of a dense-subsite inclusion from one direction of an
equivalence to the other.  With that spelling the transported sheaf of rings is `R.over T` and
the reindexing of a module is its restriction `M.over T`, both on the nose, so no comparison
isomorphism has to be built.

What is proved is the generating-sections half of the invariance asserted by Stacks 03DM, for an
equivalence of the underlying sites rather than for the special cocontinuous functor of the
source; the quasi-coherence clause of that invariance is
`StacksFrontier/AlgebraicGeometry/Topologies/QuasicoherentSiteEquivalence.lean`.

## References

* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u₁ v₁ u₂ v₂

namespace Stacks.SheafOfModules

section Reindex

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Reindexing along an equivalence of sites reflects generating sections.**  A family of
sections generating the reindexing of a sheaf of modules `M` along `e : C' ≌ C`, over the
transported sheaf of rings, is a family of generating sections of `M` itself; the index type is
unchanged, and the sections are the given ones read back through the equivalence. -/
noncomputable def generatingSectionsOfReindex {M : SheafOfModules.{w} R}
    (σ : ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).GeneratingSections) : M.GeneratingSections :=
  letI : HasSheafify J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let E : SheafOfModules.{w} R ≌ SheafOfModules.{w} (reindexRing J' e R) :=
    reindexEquivalence e R
  let η : SheafOfModules.unit R ≅ E.inverse.obj (SheafOfModules.unit (reindexRing J' e R)) :=
    E.unitIso.app (SheafOfModules.unit R)
  SheafOfModules.GeneratingSections.equivOfIso (E.unitIso.app M).symm (σ.map E.inverse η)

end Reindex

section Terminal

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Restriction to the slice over a terminal object reflects generating sections.**  For `T` a
terminal object of the site, a family of sections generating the restriction `M.over T` over
`R.over T` is a family of generating sections of `M`.

This is `Stacks.SheafOfModules.generatingSectionsOfReindex` at the equivalence of sites
`CategoryTheory.Over.equivalenceOfIsTerminal`, for which the transported sheaf of rings is
`R.over T` and the reindexing of `M` is `M.over T`. -/
noncomputable def generatingSectionsOfOverTerminal {T : C} (hT : Limits.IsTerminal T)
    [HasWeakSheafify (J.over T) AddCommGrpCat.{w}]
    [(J.over T).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {M : SheafOfModules.{w} R} (σ : (M.over T).GeneratingSections) :
    M.GeneratingSections :=
  letI hds : (Over.forget T).IsDenseSubsite (J.over T) J :=
    CategoryTheory.GrothendieckTopology.isDenseSubsite_overForget J hT
  letI _hds' : ((Over.equivalenceOfIsTerminal hT).symm).inverse.IsDenseSubsite (J.over T) J := hds
  letI _hds'' : (Over.equivalenceOfIsTerminal hT).inverse.IsDenseSubsite J (J.over T) :=
    inferInstanceAs (((Over.equivalenceOfIsTerminal hT).symm).functor.IsDenseSubsite J (J.over T))
  letI : (Over.equivalenceOfIsTerminal hT).functor.IsContinuous (J.over T) J :=
    inferInstanceAs ((Over.forget T).IsContinuous (J.over T) J)
  generatingSectionsOfReindex (Over.equivalenceOfIsTerminal hT) R σ

end Terminal

end Stacks.SheafOfModules

end
