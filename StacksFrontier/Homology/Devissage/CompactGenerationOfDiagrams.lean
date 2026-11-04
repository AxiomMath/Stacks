module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.HomologyOnACategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.CompactGenerationFromWeaklyContractibleObjects
public import StacksFrontier.CategoryTheory.Triangulated.FreeYonedaCompactObject
public import StacksFrontier.Homology.Injectives.DerivedCategory.DiagramCategory

/-!
# Compact generation of the derived category of a category of diagrams

Let `C` be a small category and let `D` be an abelian category which is Grothendieck abelian
relative to the universe `u` of the objects and the morphisms of `C`, has countable products and
has those products exact. Suppose `D` carries a separating family `S` of objects that are
projective and compact. Then the unbounded derived category `D(Cᵒᵖ ⥤ D)` is compactly generated,
by the free diagrams `Presheaf.freeYoneda X (S i)` placed in degree zero.

This is the dévissage input that the comparison of the two derived lower shrieks of
[Stacks, Tag 08QA] needs on the unbounded derived category, and it is the diagram-category
counterpart of `Stacks.Cohomology.isCompactlyGenerated_derivedCategory_of_hasEnoughObjects`,
which is about sheaves of modules on a site.

## Main results

* `StacksDraft.CompactDevissage.isCompactlyGenerated_derivedCategory_diagrams`: the statement
  above.

## Implementation notes

The three properties of the generating family are supplied separately.

* Separating is `CategoryTheory.Presheaf.isSeparating`: a morphism of diagrams out of
  `freeYoneda X (S i)` is a morphism out of `S i` into the value at `X`.
* Projective is `Stacks.CategoryHomology.freeYonedaProjective`, which holds over any abelian
  target, the lifting problem being transported to `S i` by the same corepresentation.
* Compact is `CategoryTheory.Presheaf.isCompactObject_freeYoneda`, the value at `X` of a direct
  sum of diagrams being the direct sum of the values.

`StacksDraft.Perfect.isCompactObject_derived_single` then makes the objects compact in degree
zero, and `Stacks.Cohomology.isWeakTriangulatedGenerator_single_of_projective_separating` makes
the family a weak triangulated generator there.

The model of the derived category is a hypothesis rather than
`CategoryTheory.HasDerivedCategory.standard`, and the index universe of the compactness is the
morphism universe `u` of `Cᵒᵖ ⥤ D`. The two agree only at a model whose morphisms also live in
`Type u`, which is the point of `Stacks.Injectives.hasDerivedCategory_diagrams`
([Stacks, Tag 079Q]); at `HasDerivedCategory.standard` the morphisms of `D(Cᵒᵖ ⥤ D)` are one
level higher. The coefficients are therefore taken with their morphisms in the same universe `u`
as the objects and morphisms of `C`, as they are in both coefficient settings of [Stacks,
Tag 08QA], `AddCommGrpCat.{u}` and `ModuleCat.{u} B`.

## References

* [Stacks Project, Tag 09SQ](https://stacks.math.columbia.edu/tag/09SQ)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe uD u

namespace StacksDraft.CompactDevissage

/-- **The derived category of a category of diagrams is compactly generated** by the free
diagrams on the representables with coefficients in a projective, compact, separating family of
the target, placed in degree zero. -/
theorem isCompactlyGenerated_derivedCategory_diagrams
    (C : Type u) [SmallCategory C] (D : Type uD) [Category.{u} D] [Abelian D]
    [IsGrothendieckAbelian.{u} D] [HasProductsOfShape ℕ D]
    [HasExactLimitsOfShape (Discrete ℕ) D] [HasDerivedCategory.{u} (Cᵒᵖ ⥤ D)]
    {ι : Type u} (S : ι → D) [∀ i, Projective (S i)]
    (hcomp : ∀ i, IsCompactObject.{u} (S i))
    (hS : (ObjectProperty.ofObj S).IsSeparating) :
    Pretriangulated.IsCompactlyGenerated.{u} (DerivedCategory (Cᵒᵖ ⥤ D)) := by
  classical
  let : HasCoproducts.{u} D := fun J ↦ inferInstance
  have hproj : ∀ p : C × ι, Projective (Presheaf.freeYoneda p.1 (S p.2)) := fun p ↦
    Stacks.CategoryHomology.freeYonedaProjective p.1 (S p.2)
  have hsep : (ObjectProperty.ofObj
      (fun p : C × ι ↦ Presheaf.freeYoneda p.1 (S p.2))).IsSeparating :=
    Presheaf.isSeparating C hS
  refine ⟨C × ι, fun p ↦ (DerivedCategory.singleFunctor (Cᵒᵖ ⥤ D) 0).obj
    (Presheaf.freeYoneda p.1 (S p.2)), fun p ↦ ?_, ?_⟩
  · have := Presheaf.isCompactObject_freeYoneda.{u} p.1 (S p.2) (hcomp p.2)
    exact StacksDraft.Perfect.isCompactObject_derived_single _ 0
  · exact Stacks.Cohomology.isWeakTriangulatedGenerator_single_of_projective_separating _ hsep

end StacksDraft.CompactDevissage

end
