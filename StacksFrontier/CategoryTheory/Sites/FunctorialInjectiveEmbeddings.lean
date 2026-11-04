module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.CategoryTheory.Preadditive.Injective.GrothendieckFunctorial

import StacksCore.Tactic.StacksAttribute

/-!
# Functorial injective embeddings in Grothendieck abelian and sheaf categories

A Grothendieck abelian category has *functorial* injective embeddings in the sense of
[Stacks, Tag 0139]: a functor `J : 𝒜 ⥤ Arrow 𝒜` over the identity whose values are
monomorphisms into injective objects ([Stacks, Tag 079H]). Specialized to the category of
sheaves of abelian groups on a site, this is [Stacks, Tag 01DP], which is what this file
proves.

The Grothendieck abelian case itself is
`Stacks.Injectives.FunctorialEmbedding.hasFunctorialInjectiveEmbeddings`: Mathlib provides a
*functorial* factorization of every morphism as a monomorphism followed by a morphism with
the right lifting property against all monomorphisms, and applying it to the natural family
`A ⟶ 0` gives exactly the data [Stacks, Tag 0139] asks for. Mathlib's own
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives` applies the same factorization to
one object at a time and therefore records only the non-functorial consequence.

## Main results

* `CategoryTheory.Sheaf.hasFunctorialInjectiveEmbeddings`: a category of
  sheaves with values in a Grothendieck abelian category, over an essentially small site,
  has functorial injective embeddings.
* `CategoryTheory.Sheaf.hasFunctorialInjectiveEmbeddings_addCommGrpCat` and
  `CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat`: the two assertions of
  [Stacks, Tag 01DP] for sheaves of abelian groups on a site.

## Implementation notes

Universes. The coefficient category is kept at a single free universe `w`, and the size
hypothesis on the site is `EssentiallySmall.{w} C` for a site `C : Type u` with
`Category.{v} C`; no universe is collapsed and the site's two universes stay independent.
The `max`-shaped alternative, writing the coefficients as `AddCommGrpCat.{max u v t}` and
inferring the smallness, does *not* work: `equivSmallModel C` carries an
`EssentiallySmall.{?w} C` instance argument, and the resulting constraint
`max u ?w =?= max (max u v) t` is one the unifier leaves stuck even though `?w := max v t`
solves it. This is the universe-parameter case where the free form is the easier one. A
consumer working at `AddCommGrpCat.{max u v t}` instantiates `w := max u v t` and the
`EssentiallySmall` hypothesis is then found by instance search.

`HasSheafify J A` is taken as a hypothesis of the sheaf results even though
`CategoryTheory.hasSheafifyEssentiallySmallSite` derives it from the hypotheses already
present. It cannot be dropped: `Abelian (Sheaf J A)` is needed to *state* the conclusion,
it is produced by `sheafIsAbelian` from a `HasSheafify` instance, and taking that instance
from the caller rather than from a local attribute is what makes the conclusion syntactically
the proposition a caller with its own sheafification instance is looking for. Since the
hypothesis is implied by the others it narrows nothing.

It also has to come *first* among the instance binders of the two `AddCommGrpCat` results.
`HasSheafify J AddCommGrpCat.{w}` is the only hypothesis there that mentions `w` and whose
match against a caller's local instance determines `w` outright. With
`EssentiallySmall.{w} C` first, instance search reaches it while `w` is still a
metavariable, solves it against the `UnivLE`-shaped instance as `w := max u ?x`, and a
caller at `AddCommGrpCat.{max u v q t}` then fails with four stuck universe constraints —
even though the conclusion pins `w` completely. In this order the same caller needs no
universe annotation at all.

The limits hypothesis
`∀ X, HasLimitsOfShape (StructuredArrow X (equivSmallModel C).inverse.op) A` and the
sheafification hypothesis on the small model are exactly those of Mathlib's
`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`; both are discharged by
instance search for `A = AddCommGrpCat.{w}`, which is why the two tagged results carry
neither.

## References

* [Stacks Project, Tag 079H](https://stacks.math.columbia.edu/tag/079H)
* [Stacks Project, Tag 01DP](https://stacks.math.columbia.edu/tag/01DP)
* [Stacks Project, Tag 0139](https://stacks.math.columbia.edu/tag/0139)
-/

@[expose] public section

namespace CategoryTheory

open Limits MorphismProperty
open scoped ZeroObject

universe w v₁ v u₁ u

namespace Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Sheaves on an essentially small site with values in a Grothendieck abelian category have
functorial injective embeddings in the sense of [Stacks, Tag 0139]. -/
theorem hasFunctorialInjectiveEmbeddings (A : Type u₁) [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [EssentiallySmall.{w} C]
    [∀ X : Cᵒᵖ, HasLimitsOfShape (StructuredArrow X (equivSmallModel C).inverse.op) A]
    [HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A] [HasSheafify J A] :
    HasFunctorialInjectiveEmbeddings (Sheaf J A) :=
  let _ := Sheaf.isGrothendieckAbelian_of_essentiallySmall J A
  Stacks.Injectives.FunctorialEmbedding.hasFunctorialInjectiveEmbeddings (Sheaf J A)

/-- **Stacks Project, Tag 01DP.** The category of sheaves of abelian groups on a site has
functorial injective embeddings in the sense of [Stacks, Tag 0139]. -/
@[stacks 01DP "functorial injective embeddings",
  sga "4½ Arcata 1.6.3" "enough injectives",
  sga "4 V 0.1.1" "sheaves on a site"]
theorem hasFunctorialInjectiveEmbeddings_addCommGrpCat [HasSheafify J AddCommGrpCat.{w}]
    [EssentiallySmall.{w} C] :
    HasFunctorialInjectiveEmbeddings (Sheaf J AddCommGrpCat.{w}) :=
  hasFunctorialInjectiveEmbeddings J AddCommGrpCat.{w}

/-- **Stacks Project, Tag 01DP.** The category of sheaves of abelian groups on a site has
enough injectives. This is deduced from the functorial statement
`hasFunctorialInjectiveEmbeddings_addCommGrpCat`, as in the source. -/
@[stacks 01DP "enough injectives",
  sga "4½ Arcata 1.6.3" "enough injectives",
  sga "4 V 0.1.1" "sheaves on a site",
  sga "3 I 3.1.2" "special case",
  sga "4 I 7.13" "special case",
  sga "4 V 0.2.1" "special case",
  sga "4 V 2.5.2" "special case"]
theorem enoughInjectives_addCommGrpCat [HasSheafify J AddCommGrpCat.{w}]
    [EssentiallySmall.{w} C] :
    EnoughInjectives (Sheaf J AddCommGrpCat.{w}) :=
  enoughInjectives_of_hasFunctorialInjectiveEmbeddings _
    (hasFunctorialInjectiveEmbeddings_addCommGrpCat J)

end Sheaf

end CategoryTheory

end
