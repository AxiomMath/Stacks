module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits

/-!
# Colimits of quasi-coherent modules, reduced to a covering family

Quasi-coherence of a sheaf of modules is a local condition: it asks for a covering of each
object on whose members the restricted module has a global presentation.  The covering it
produces, however, depends on the module, so closure of quasi-coherence under colimits does
*not* follow from the definition: a colimit over an infinite shape has infinitely many
members, each supplying its own covering, and an infinite intersection of covering sieves is
not a covering sieve.

What repairs this is a family of objects that covers the final object and on which *every*
quasi-coherent module is globally presented — on a big site of schemes, the affine objects.
This file packages such a family as `Stacks.SheafOfModules.PresentingCover` and turns it into
closure of quasi-coherence under colimits, so that all the site-theoretic bookkeeping is
discharged once and what remains is two statements about the slice sites over the members of
the family.

## Main definitions

* `Stacks.SheafOfModules.PresentingCover`: a family of objects covering the final object on
  whose slice sites every quasi-coherent module is globally presented and global presentations
  are closed under colimits of a given shape.

## Main results

* `Stacks.SheafOfModules.hasGlobalPresentation_of_isColimit_over`: a colimit of quasi-coherent
  modules has a global presentation after restriction to a member of such a family.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_isColimit`: hence it is quasi-coherent.
* `Stacks.SheafOfModules.isClosedUnderColimitsOfShape_isQuasicoherentOnSite`: the same
  conclusion in the form of the
  `CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape` hypothesis that Mathlib's
  full-subcategory API consumes.
* `Stacks.SheafOfModules.hasColimitsOfShape_quasicoherentFullSubcategory` and
  `Stacks.SheafOfModules.preservesColimitsOfShape_quasicoherentι`: the two assertions a
  colimits clause of the source is made of — the quasi-coherent modules have the colimits, and
  the inclusion into all module sheaves preserves them.

## Implementation notes

The two mathematical fields of `Stacks.SheafOfModules.PresentingCover` concern the slice site
over a member rather than the member itself, which is what makes them affine statements: on
the slice site over an affine scheme a quasi-coherent module is globally presented, and a
colimit of globally presented modules is globally presented, both because the quasi-coherent
modules there are the modules over a ring.  Nothing about schemes enters the proofs below, so
everything is stated for an arbitrary sheaf of rings on an arbitrary site.

The two sheafification fields are carried by the structure rather than taken as instances,
because they concern the slice topologies at the members and so depend on a field; on a big
site over a scheme they are supplied by
`AlgebraicGeometry.BigFppfOver.hasWeakSheafify_over` and
`AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective_over`.

The reduction uses two facts about restriction to a slice, both already available: that
quasi-coherence may be tested on a covering family of the final object
(`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation`,
Stacks 03DN), and that restriction preserves colimits
(`Stacks.SheafOfModules.pushforward_preservesColimits`, Stacks 03DC(2)); the latter applies
because `SheafOfModules.overFunctor R U` is by definition the pushforward along
`CategoryTheory.Over.forget U`, which is continuous and cocontinuous for the slice topology.

The shape is a category at the universe of the module sections, which is the size of colimit
the ambient category of module sheaves has.

## References

* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DC](https://stacks.math.columbia.edu/tag/03DC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A family of objects covering the final object of a site on which quasi-coherence of a
sheaf of modules over `R` is witnessed by a *global* presentation, and on whose slice sites
global presentations are closed under colimits of shape `K`.

On a big site of schemes the intended family is the affine objects: there a quasi-coherent
module is the module associated with a module over a ring, hence globally presented, and a
colimit of such is again one. -/
structure PresentingCover (R : Sheaf J RingCat.{w}) (K : Type w) [Category.{w} K] where
  /-- The index type of the family. -/
  I : Type u
  /-- The members of the family. -/
  obj : I → C
  /-- The family covers the final object. -/
  coversTop : J.CoversTop obj
  /-- Sheafification into abelian groups exists on the slice site at each member. -/
  hasWeakSheafify_over (i : I) : HasWeakSheafify (J.over (obj i)) AddCommGrpCat.{w}
  /-- Weak equivalences on the slice site at each member are the locally bijective maps. -/
  wEqualsLocallyBijective_over (i : I) :
    (J.over (obj i)).WEqualsLocallyBijective AddCommGrpCat.{w}
  /-- Every quasi-coherent module is globally presented on the slice site at each member. -/
  hasGlobalPresentation_over (M : _root_.SheafOfModules.{w} R) :
    M.IsQuasicoherentOnSite → ∀ i, (M.over (obj i)).HasGlobalPresentation
  /-- Global presentations on the slice site at each member are closed under colimits of
  shape `K`. -/
  hasGlobalPresentation_of_isColimit (i : I)
    (D : K ⥤ _root_.SheafOfModules.{w} (R.over (obj i))) (c : Cocone D) :
    IsColimit c → (∀ k, (D.obj k).HasGlobalPresentation) → c.pt.HasGlobalPresentation

variable {R : Sheaf J RingCat.{w}} {K : Type w} [Category.{w} K]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Restriction to a member of a presenting cover preserves colimits of sheaves of modules.
This is the localization case of Stacks 03DC(2), read off from
`Stacks.SheafOfModules.pushforward_preservesColimits`: the restriction functor is the
pushforward along `CategoryTheory.Over.forget`. -/
theorem PresentingCover.overFunctor_preservesColimits (P : PresentingCover R K) (i : P.I) :
    PreservesColimitsOfSize.{w, w} (_root_.SheafOfModules.overFunctor.{w} R (P.obj i)) :=
  have := P.hasWeakSheafify_over i
  have := P.wEqualsLocallyBijective_over i
  pushforward_preservesColimits (Over.forget (P.obj i)) (𝟙 _)

/-- A colimit of quasi-coherent modules has a global presentation after restriction to a
member of a presenting cover.  The closure field of the cover is applied to the restricted
diagram, which is a colimit diagram again because restriction preserves colimits. -/
theorem hasGlobalPresentation_of_isColimit_over (P : PresentingCover R K)
    {D : K ⥤ _root_.SheafOfModules.{w} R} {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) (i : P.I) :
    (c.pt.over (P.obj i)).HasGlobalPresentation :=
  have := P.overFunctor_preservesColimits i
  P.hasGlobalPresentation_of_isColimit i _ _
    (isColimitOfPreserves (_root_.SheafOfModules.overFunctor.{w} R (P.obj i)) hc)
    fun k => P.hasGlobalPresentation_over _ (hD k) i

/-- **A colimit of quasi-coherent modules is quasi-coherent**, given a presenting cover for
the shape of the colimit. -/
theorem isQuasicoherentOnSite_of_isColimit (P : PresentingCover R K)
    {D : K ⥤ _root_.SheafOfModules.{w} R} {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) :
    c.pt.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation c.pt).2
    ⟨P.I, P.obj, P.coversTop, fun i =>
      hasGlobalPresentation_of_isColimit_over P hc hD i⟩

/-- A chosen colimit of quasi-coherent modules is quasi-coherent, given a presenting cover for
its shape. -/
theorem isQuasicoherentOnSite_colimit (P : PresentingCover R K)
    (D : K ⥤ _root_.SheafOfModules.{w} R) [HasColimit D]
    (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) :
    (colimit D).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isColimit P (colimit.isColimit D) hD

/-- Quasi-coherence of sheaves of modules is closed under colimits of a given shape, given a
presenting cover for that shape.  This is the form Mathlib's full-subcategory API consumes. -/
theorem isClosedUnderColimitsOfShape_isQuasicoherentOnSite (P : PresentingCover R K) :
    (_root_.SheafOfModules.isQuasicoherentOnSite.{u, v, w, w} R).IsClosedUnderColimitsOfShape
      K := by
  refine ⟨?_⟩
  rintro X ⟨p⟩
  exact isQuasicoherentOnSite_of_isColimit P p.isColimit p.prop_diag_obj

/-- **The quasi-coherent modules have the colimits.**  Given a presenting cover for the shape
and the colimits in the ambient category of all module sheaves, the full subcategory of
quasi-coherent modules has colimits of that shape. -/
theorem hasColimitsOfShape_quasicoherentFullSubcategory
    [HasColimitsOfShape K (_root_.SheafOfModules.{w} R)] (P : PresentingCover R K) :
    HasColimitsOfShape K
      (_root_.SheafOfModules.isQuasicoherentOnSite.{u, v, w, w} R).FullSubcategory :=
  have := isClosedUnderColimitsOfShape_isQuasicoherentOnSite P
  inferInstance

/-- **The colimits of quasi-coherent modules are the colimits of all module sheaves.**  Given
a presenting cover for the shape, the inclusion of the quasi-coherent modules into all module
sheaves preserves colimits of that shape. -/
theorem preservesColimitsOfShape_quasicoherentι
    [HasColimitsOfShape K (_root_.SheafOfModules.{w} R)] (P : PresentingCover R K) :
    PreservesColimitsOfShape K
      (_root_.SheafOfModules.isQuasicoherentOnSite.{u, v, w, w} R).ι :=
  have := isClosedUnderColimitsOfShape_isQuasicoherentOnSite P
  inferInstance

end Stacks.SheafOfModules

end
