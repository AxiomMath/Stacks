module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves on a merely `v`-small site form a Grothendieck abelian category

Mathlib's `CategoryTheory.Sheaf.instIsGrothendieckAbelian` concludes that `Sheaf J A` is a
Grothendieck abelian category from a site `C : Type v` carrying `SmallCategory.{v} C`, so the
site is *literally* small and its hom universe *is* the coefficient universe `v`. That shape
cannot be instantiated when the site and the coefficients have independent universes: for
`C : Type u` with `Category.{w} C` and coefficients `A` with `IsGrothendieckAbelian.{v} A`, the
conclusion `IsGrothendieckAbelian.{v} (Sheaf J A)` needs `u = w = v` as a universe *equation*,
whereas smallness of the site is a smallness *class* and supplies no equation.

This file replaces the equation by the smallness hypotheses the proof actually uses. Three of
the four conditions packaged by `IsGrothendieckAbelian.{v}` are already available at independent
universes: filtered colimits of size `v` and their exactness come from `A` across the
sheafification adjunction (`CategoryTheory.Sheaf.hasFilteredColimitsOfSize` and
`CategoryTheory.Sheaf.ab5ofSize`), and a separator comes from `CategoryTheory.Sheaf.hasSeparator`
once `A` has coproducts indexed by the objects of the site and by its homs. The condition that is
*not* automatic is local `v`-smallness: a morphism of `Sheaf J A` is a family of components
indexed by the objects of the site, so the hom types of `Sheaf J A` live in `max u w v` and are
`v`-small only when the site is `v`-small. That is the gap this file fills, and it is the same
gap that `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SeparatorUnivLE.lean` fills for
`SheafOfModules`; the underlying `CategoryTheory.locallySmall_functor` is reused from there.

## Main results

* `CategoryTheory.Sheaf.locallySmall_of_small`: `Sheaf J A` is locally `v`-small when the site is
  `v`-small and `A` is locally `v`-small.
* `CategoryTheory.Sheaf.isGrothendieckAbelian_of_small` and
  `CategoryTheory.Sheaf.enoughInjectives_of_small`: **sheaves on a `v`-small site with
  coefficients in a Grothendieck abelian category at `v` form a Grothendieck abelian category at
  `v`, and hence have enough injectives** -- with the universes of the site, of its homs and of
  the coefficients independent.

## Implementation notes

The coefficient universe `v` is not the first universe parameter of these declarations and cannot
be made so while the site is introduced by a section variable, so every occurrence is pinned by a
type ascription rather than by a `.{…}` application, as in `SeparatorUnivLE`.

`CategoryTheory.Sheaf.hasSeparator` needs coproducts of `A` at two sizes: `HasCoproducts.{w} A`,
which `CategoryTheory.Sheaf.freeYoneda` already requires in order to exist at all, and
`HasCoproducts.{u} A`, which is what makes the separating family of free sheaves on the Yoneda
presheaves assemble into a single object. Both are discharged by `UnivLE.{u, v}` at
`AddCommGrpCat.{v}` for a site whose homs are already in `v`.

**What this does not give.** For `[HasSheafify J AddCommGrpCat.{v}]` alone -- a site `C : Type u`
with `Category.{v} C` and no relation between `u` and `v` -- the two conditions pull in opposite
directions and no choice of universe `z` is available: `LocallySmall.{z}` wants `z` at least
`max u v`, while `AB5OfSize.{z, z}` wants the coefficients to have `z`-sized colimits, hence `z`
at most `v`. So the `v`-smallness of the site is not an artefact of this route.

## References

* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)
-/

@[expose] public section

universe v₁ v w u u₁

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{w} C] (J : GrothendieckTopology C)
  (A : Type u₁) [Category.{v₁} A]

/-- **Sheaves on a `v`-small site are locally `v`-small**, with the universes of the site, of its
homs and of the coefficients independent: a morphism of sheaves is a family of components indexed
by the objects of the site, so it is determined by `v`-smally many pieces of `v`-small data. This
is the one condition of `IsGrothendieckAbelian.{v}` that is not already available for `Sheaf J A`
at independent universes. -/
@[sga "4 II 4.11" "special case"]
theorem locallySmall_of_small [Small.{v} C] [LocallySmall.{v} A] :
    LocallySmall.{v} (Sheaf J A) :=
  have : LocallySmall.{v} (Cᵒᵖ ⥤ A) := locallySmall_functor
  locallySmall_of_faithful (sheafToPresheaf J A)

/-- **Sheaves on a `v`-small site with coefficients in a Grothendieck abelian category at `v`
form a Grothendieck abelian category at `v`**, with the universes of the site, of its homs and of
the coefficients independent. Mathlib's `CategoryTheory.Sheaf.instIsGrothendieckAbelian` asks the
site to be literally small with its hom universe equal to the coefficient universe; local
`v`-smallness is the condition that generalises, the other three being available already. -/
theorem isGrothendieckAbelian_of_small [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasSheafify J A] [Small.{v} C] [HasCoproducts.{w} A] [HasCoproducts.{u} A] :
    IsGrothendieckAbelian.{v} (Sheaf J A) where
  locallySmall := (locallySmall_of_small J A : LocallySmall.{v} (Sheaf J A))

/-- **Sheaves on a `v`-small site with coefficients in a Grothendieck abelian category at `v`
have enough injectives**, with the universes of the site, of its homs and of the coefficients
independent. -/
@[sga "3 I 5.2" "special case",
  sga "4 I 7.13" "special case",
  sga "4 V 0.1.1" "special case",
  sga "4 V 2.5.2" "special case",
  sga "4½ Arcata 1.6.3" "more general"]
theorem enoughInjectives_of_small [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasSheafify J A] [Small.{v} C] [HasCoproducts.{w} A] [HasCoproducts.{u} A] :
    EnoughInjectives (Sheaf J A) :=
  have : IsGrothendieckAbelian.{v} (Sheaf J A) := isGrothendieckAbelian_of_small J A
  inferInstance

end CategoryTheory.Sheaf

end
