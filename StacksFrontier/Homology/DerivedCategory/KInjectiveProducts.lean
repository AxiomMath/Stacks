module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite
import all StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits

open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

/-!
# Countable products in a derived category, from K-injective resolutions

Let `A` be an abelian category with countable products in which every cochain complex has a
quasi-isomorphism to a K-injective complex. Then the derived category `D(A)` has countable
products: a termwise product of K-injective complexes is K-injective and represents the product
in `D(A)` ([Stacks, Tag 0BK6]), and every object of `D(A)` is isomorphic to the image of such a
complex.

This is the route to countable products in `D(A)` that does **not** assume the products of `A`
to be exact. `Stacks.DerivedProducts.hasProductsOfShape_derivedCategory` of
`StacksFrontier/Algebra/Homology/DerivedCategory/Products.lean` assumes
`HasExactLimitsOfShape (Discrete ℕ) A` in addition to `HasProductsOfShape ℕ A`, which is
Grothendieck's axiom AB4* for `A` and is the hypothesis of [Stacks, Tag 07KC]. AB4* holds in
`ModuleCat R`, which is why every existing instance of
`HasProductsOfShape ℕ (DerivedCategory (ModuleCat R))` in this repository goes through Tag 07KC.
It is **not** available for sheaves of modules on a site: a countable product of
epimorphisms of sheaves need not be an epimorphism, and `HasExactLimitsOfShape (Discrete ℕ)
(SheafOfModules O)` does not synthesize. The K-injective route below needs no exactness, and
delivers the instance for sheaves of modules.

## Main results

Both in the namespace `Stacks.KInjectiveProducts`.

* `hasProductsOfShape_derivedCategory_of_exists_quasiIso_isKInjective` — countable products in
  `D(A)` from countable products in `A` and the existence of K-injective resolutions.
* `hasProductsOfShape_derivedCategory_sheafOfModules` — the same for `A = SheafOfModules O`,
  the K-injective resolutions being those of
  `exists_quasiIso_isKInjective_sheafOfModules`.

## Implementation notes

The model of the derived category is a free `[HasDerivedCategory.{w}]` binder, so the results
apply at `HasDerivedCategory.standard` as well as at any other model. That matters because the
intended consumer, the derived-completeness predicate
`AlgebraicGeometry.RingedSite.IsDerivedComplete` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/Basic.lean`, is defined
under a file-level `attribute [local instance] HasDerivedCategory.standard` and therefore asks
for `HasProductsOfShape ℕ (DerivedCategory A)` at the standard model.

That predicate carries the countable products as an *existential* over the class rather than
assuming an instance, so without a result of this kind no object could be shown to satisfy it
and the predicate would be vacuously false. Products, unlike coproducts, are available at the
standard model, so no locally small model is needed here.

The step from the Hom-bijection of [Stacks, Tag 0BK6] to a limit cone is the private
`CochainComplex.isLimit_fan_Q_pi` of
`StacksFrontier/Algebra/Homology/DerivedCategory/DerivedLimits.lean`, reached by `import all`
rather than re-proved; it is stated for an arbitrary apex of `D(A)`, which is what the universal
property needs, whereas `Stacks0BK6.product_repr_derived` is stated for an apex of the form
`Q K`.

## References

* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w' w r v u

namespace Stacks.KInjectiveProducts

/-- **Countable products in a derived category from K-injective resolutions.** Let `A` be an
abelian category with countable products in which every cochain complex has a
quasi-isomorphism to a K-injective complex. Then `D(A)` has countable products.

No exactness of the products of `A` is assumed; compare
`Stacks.DerivedProducts.hasProductsOfShape_derivedCategory`, which does assume it. -/
theorem hasProductsOfShape_derivedCategory_of_exists_quasiIso_isKInjective
    {A : Type u} [Category.{v} A] [Abelian A] [HasProductsOfShape ℕ A]
    [HasDerivedCategory.{w} A]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    HasProductsOfShape ℕ (DerivedCategory A) := by
  refine ⟨fun X ↦ ?_⟩
  choose I f hI hf using fun n : ℕ ↦ hres (DerivedCategory.Q.objPreimage (X.obj ⟨n⟩))
  have hiso (n : ℕ) : IsIso (DerivedCategory.Q.map (f n)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A (f n)).2 (hf n)
  have e (n : ℕ) : DerivedCategory.Q.obj (I n) ≅ X.obj ⟨n⟩ :=
    (asIso (DerivedCategory.Q.map (f n))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso (X.obj ⟨n⟩)
  have : HasProduct fun n : ℕ ↦ DerivedCategory.Q.obj (I n) :=
    HasLimit.mk ⟨_, CochainComplex.isLimit_fan_Q_pi I hI⟩
  have e' : Discrete.functor (fun n : ℕ ↦ DerivedCategory.Q.obj (I n)) ≅ X :=
    Discrete.natIso fun n ↦ e n.as
  exact hasLimit_of_iso e'

/-- **Countable products in the derived category of sheaves of modules on a site.** For a sheaf
of rings `O` on any site, the derived category of sheaves of `O`-modules in the ambient universe
has countable products, at any model of the derived category.

The exactness hypothesis of [Stacks, Tag 07KC] is unavailable here, so this goes through
K-injective resolutions, which
  `exists_quasiIso_isKInjective_sheafOfModules`
supplies for a Grothendieck abelian category of sheaves of modules; that the category is
Grothendieck abelian in the ambient universe is
`Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck`. -/
theorem hasProductsOfShape_derivedCategory_sheafOfModules
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (O : Sheaf J RingCat.{r})
    [HasDerivedCategory.{w'} (SheafOfModules.{max u v r w} O)] :
    HasProductsOfShape ℕ (DerivedCategory (SheafOfModules.{max u v r w} O)) := by
  have := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
  have :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u, v, max r w} (J := J)
  have := Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u, v, r, w} O
  exact hasProductsOfShape_derivedCategory_of_exists_quasiIso_isKInjective
    (exists_quasiIso_isKInjective_sheafOfModules O)

end Stacks.KInjectiveProducts

end
