module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoextendScalarsKInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsCoextension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite
public import StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence

/-!
# Restriction of scalars has a right adjoint on derived categories

Let `α : 𝒪 ⟶ 𝒪'` be a homomorphism of sheaves of rings on a site. Restriction of scalars
`Mod(𝒪') ⥤ Mod(𝒪)` is exact and has the right adjoint `coextendScalars α` of
[Stacks, Tag 0932]. This file deduces that the induced functor `D(𝒪') ⥤ D(𝒪)` has a right
adjoint.

The input is the generic statement `CompleteRestrictScalarsEquivalence.exists_derivedAdjunction`:
an adjunction of additive functors whose left member is exact descends to derived categories
once every complex in the target admits a quasi-isomorphism to a K-injective complex. For
sheaves of modules on a site that resolution is
`HomologyComparison.exists_quasiIso_isKInjective_sheafOfModules`, in the namespace
`Stacks.Cohomology.HypercohomologyEdge`, whose Grothendieck-abelian hypothesis is
`Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck`.

## Main results

* `Stacks.SheafOfModules.DerivedRestrictScalars.exists_restrictScalars_derivedAdjunction`:
  `(restrictScalars α).mapDerivedCategory` has a right adjoint.

## Implementation notes

Exactness of the countable products of `Mod(𝒪)` — the hypothesis of [Stacks, Tag 090Y], the
usual source of K-injective resolutions — is *not* available on a general site: a product of
sheaves is computed sectionwise while an epimorphism of sheaves is only locally surjective, and
[Stacks, Tag 0947] (4) obtains that exactness only on a site with enough weakly contractible
objects. The resolution used here instead goes through Grothendieck abelianness, which holds on
every site.

The right adjoint is produced existentially rather than named. Nothing downstream needs to know
which functor it is: the generic
`CompleteRestrictScalarsEquivalence.bijective_postcomp_counit_iff_precomp_unit` tests
invertibility of its counit against the unit of a second adjunction in which it does not appear.

## References

* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
* [Stacks Project, Tag 090Y](https://stacks.math.columbia.edu/tag/090Y)
* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SheafOfModules.DerivedRestrictScalars

attribute [local instance] HasDerivedCategory.standard

/-- **Restriction of scalars has a right adjoint on derived categories.** For a homomorphism
`α : 𝒪 ⟶ 𝒪'` of sheaves of rings on a site, the functor `D(𝒪') ⥤ D(𝒪)` induced by restriction
of scalars has a right adjoint.

Restriction of scalars is exact and is left adjoint to coextension of scalars
([Stacks, Tag 0932]), and every complex of `𝒪`-modules admits a quasi-isomorphism to a
K-injective complex; `CompleteRestrictScalarsEquivalence.exists_derivedAdjunction` turns those
into the adjunction. -/
theorem exists_restrictScalars_derivedAdjunction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {O O' : Sheaf J RingCat.{u}} (α : O ⟶ O') :
    ∃ G : DerivedCategory (SheafOfModules.{u} O) ⥤ DerivedCategory (SheafOfModules.{u} O'),
      Nonempty ((_root_.SheafOfModules.restrictScalars.{u} α).mapDerivedCategory ⊣ G) := by
  let adj := Stacks.SheafOfModules.CoextendScalars.restrictScalars_coextendScalars_adjunction α
  let : (Stacks.SheafOfModules.CoextendScalars.coextendScalars α).Additive :=
    adj.right_adjoint_additive
  obtain ⟨G, adj', -⟩ := CompleteRestrictScalarsEquivalence.exists_derivedAdjunction adj
    fun K ↦ by
      open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison in
      obtain ⟨I, g, hI, hg⟩ := exists_quasiIso_isKInjective_sheafOfModules O K
      exact ⟨I, g, hg, hI⟩
  exact ⟨G, ⟨adj'⟩⟩

end Stacks.SheafOfModules.DerivedRestrictScalars

end
