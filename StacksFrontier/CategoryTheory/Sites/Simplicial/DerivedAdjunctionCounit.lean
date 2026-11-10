module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedPostnikov

/-!
# The counit of a derived adjunction is the derived functor of the counit

Let `F ⊣ G` be an adjunction of exact functors of abelian categories. Applying the two functors
degreewise to cochain complexes and localizing at the quasi-isomorphisms gives the derived
adjunction `F^L ⊣ G^L` of `CategoryTheory.Adjunction.mapDerivedCategory`, whose unit and counit
are transported along the localizations by `CategoryTheory.Adjunction.localization`. The
transformation `CategoryTheory.derivedNatTrans` sends a transformation of exact functors to one
of their derived functors, and this file says that the counit of the derived adjunction is what
it sends the counit of the given adjunction to.

The statement needs the two comparisons that reconcile `derivedNatTrans` with the derived
adjunction's shape: the counit of `F ⊣ G` is a transformation `G ⋙ F ⟶ 𝟭`, so its image under
`derivedNatTrans` goes between the derived functors of a composite and of the identity, while the
counit of the derived adjunction goes between the composite of the derived functors and the
identity functor of the derived category. Those are `CategoryTheory.derivedCompIso` and
`CategoryTheory.derivedIdIso`.

This is the counit half of the comparison whose unit half is
`CategoryTheory.mapDerivedCategoryAdjunction_unit_app_Q`, in
`StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianDerivedPostnikov.lean`. It is what
carries a
sheaf-level identity stated as a transpose along an adjunction of abelian sheaves to the
corresponding transpose along the adjunction of derived categories: a transpose is the image of a
map under the left adjoint followed by the counit, so the two transposes agree exactly when the
derived counit is the derived functor of the abelian one.

## Main results

* `CategoryTheory.mapDerivedCategoryAdjunction_counit_app_Q`: the counit of the derived
  adjunction, on the image of a complex.
* `CategoryTheory.derivedNatTrans_counit`: **the counit of the derived adjunction is the derived
  functor of the counit**, read through the comparisons of the derived functor of a composite with
  the composite of the derived functors and of the derived functor of the identity with the
  identity.

## References

* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory

section Adjunction

variable {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [Category B] [Abelian B] [HasDerivedCategory B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The counit of the derived adjunction, on the image of a complex: the counit of the given
adjunction applied degreewise, preceded by the two comparisons of the derived functors with the
localizations of the functors on complexes. -/
theorem mapDerivedCategoryAdjunction_counit_app_Q (adj : F ⊣ G) (Y : CochainComplex B ℤ) :
    (CategoryTheory.Adjunction.mapDerivedCategory adj).counit.app
        (DerivedCategory.Q.obj Y) =
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app Y) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex adj.counit (ComplexShape.up ℤ)).app Y) := by
  simp only [CategoryTheory.Adjunction.mapDerivedCategory,
    Adjunction.localization_counit_app]
  rfl

/-- Two composites that differ by a factor that is an identity on each side. This is the shape
the last step of `derivedNatTrans_counit` needs: the two identities there are the image of an
identity under the localization and the identity of an object of the derived category written
through a different presentation of that object, and a rewrite cannot cross either, the two
presentations not being type-correct against one another at `implicit` transparency. -/
private theorem comp_eq_comp_of_id {C : Type*} [Category C] {X Y Z : C} (h : X ⟶ Y)
    (f : Y ⟶ Z) {g : Z ⟶ Z} (hg : g = 𝟙 Z) {e : Y ⟶ Y} (he : e = 𝟙 Y) :
    h ≫ f ≫ g = h ≫ e ≫ f := by
  rw [hg, he, Category.comp_id, Category.id_comp]

/-- **The counit of the derived adjunction is the derived functor of the counit.** Both sides are
transformations of localized functors, so they are compared on the image of a complex, where the
derived counit is `mapDerivedCategoryAdjunction_counit_app_Q` and the derived functor of the
counit is `derivedNatTrans_app_Q'`; the comparisons of the derived functor of the composite and
of the identity contribute the factors that cancel. -/
theorem derivedNatTrans_counit (adj : F ⊣ G) :
    derivedNatTrans (G ⋙ F) (𝟭 B) adj.counit ≫ (derivedIdIso (A := B)).hom =
      (derivedCompIso G F (G ⋙ F) (Iso.refl _)).hom ≫
        (CategoryTheory.Adjunction.mapDerivedCategory adj).counit := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)) fun Y => ?_
  simp only [NatTrans.comp_app, derivedNatTrans_app_Q', derivedIdIso_hom_app_Q,
    derivedCompIso_hom_app_Q, mapDerivedCategoryAdjunction_counit_app_Q, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [SimplicialSiteSituation.natIso_mapHomologicalComplex_refl_hom_app,
    show (Functor.mapHomologicalComplexIdIso B (ComplexShape.up ℤ)).hom.app Y = 𝟙 _ from
      HomologicalComplex.hom_ext _ _ fun _ => rfl]
  have hc : F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app Y) ≫
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app Y) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  simp only [Functor.map_id]
  rw [reassoc_of% hc, Iso.inv_hom_id_app_assoc]
  exact comp_eq_comp_of_id _ _ (DerivedCategory.Q.map_id _) rfl

end Adjunction

end CategoryTheory

end
