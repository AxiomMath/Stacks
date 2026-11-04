module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedAdjunctionCounit

/-!
# The derived counit of the module equivalence is the derived functor of its counit

Let `e` be the equivalence `Stacks.DerivedTensor.AbelianSheaves.moduleEquivalence` of abelian
sheaves with modules over the constant sheaf of rings `ℤ`.  Applying `e⁻¹` and `e` degreewise to
cochain complexes and localizing at the quasi-isomorphisms gives two endofunctors of the derived
category of abelian sheaves whose composite is the identity; that identification is
`Stacks.DerivedTensor.AbelianSheaves.derivedCounitIso`.

This file says that `derivedCounitIso` is what `CategoryTheory.derivedNatTrans` sends the counit
of `e` to, read through the comparisons `CategoryTheory.derivedCompIso` and
`CategoryTheory.derivedIdIso` that reconcile the shapes: the counit of `e` is a transformation
`e⁻¹ ⋙ e ⟶ 𝟭`, so its image under `derivedNatTrans` goes between the derived functors of a
composite and of the identity, while `derivedCounitIso` goes between the composite of the derived
functors and the identity functor of the derived category.

## Main results

* `Stacks.DerivedTensor.AbelianSheaves.derivedCounitIso_hom_app_Q`: `derivedCounitIso` on the
  image of a complex.
* `Stacks.DerivedTensor.AbelianSheaves.mapDerivedCategoryAdjunction_counit_eq_derivedCounitIso`:
  `derivedCounitIso` is the counit of the derived adjunction of the equivalence.
* `Stacks.DerivedTensor.AbelianSheaves.derivedNatTrans_counitIso_eq_derivedCounitIso`:
  **`derivedCounitIso` is the derived functor of the counit of the equivalence.**

## References

* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u

namespace Stacks.DerivedTensor.AbelianSheaves

variable {C : Type u} [SmallCategory.{u} C] (J : GrothendieckTopology C)

attribute [local instance] HasDerivedCategory.standard

/-- **`derivedCounitIso` on the image of a complex**: the counit of the equivalence applied
degreewise, preceded by the two comparisons of the derived functors with the localizations of the
functors on complexes. -/
theorem derivedCounitIso_hom_app_Q (L : CochainComplex (Sheaf J Ab.{u}) ℤ) :
    (derivedCounitIso J).hom.app (DerivedCategory.Q.obj L) =
      (moduleEquivalence J).functor.mapDerivedCategory.map
          ((moduleEquivalence J).inverse.mapDerivedCategoryFactors.hom.app L) ≫
        (moduleEquivalence J).functor.mapDerivedCategoryFactors.hom.app
            (((moduleEquivalence J).inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (moduleEquivalence J).counitIso.hom
              (ComplexShape.up ℤ)).app L) := by
  dsimp only [derivedCounitIso]
  rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso]
  dsimp only [derivedCounitLifting, complexCounitIso]
  simp only [comp_obj, id_obj, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, associator_inv_app, whiskerRight_app,
    associator_hom_app, whiskerLeft_app, Category.id_comp,
    Equivalence.mapHomologicalComplex_inverse, Equivalence.mapHomologicalComplex_functor,
    Equivalence.mapHomologicalComplex_counitIso, isoWhiskerRight_trans, Iso.trans_assoc,
    leftUnitor_hom_app, Category.comp_id, rightUnitor_inv_app, Category.assoc]
  rw [show (mapHomologicalComplexIdIso (Sheaf J Ab.{u}) (ComplexShape.up ℤ)).hom.app L = 𝟙 _ from
    HomologicalComplex.hom_ext _ _ fun _ => rfl, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rfl

/-- **`derivedCounitIso` is the counit of the derived adjunction of the equivalence.** -/
theorem mapDerivedCategoryAdjunction_counit_eq_derivedCounitIso :
    (CategoryTheory.Adjunction.mapDerivedCategory
        (moduleEquivalence J).toAdjunction).counit = (derivedCounitIso J).hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaf J Ab.{u}) (ComplexShape.up ℤ)) fun Y => ?_
  rw [CategoryTheory.mapDerivedCategoryAdjunction_counit_app_Q,
    derivedCounitIso_hom_app_Q]
  rfl

/-- **`derivedCounitIso` is the derived functor of the counit of the equivalence**, read through
the comparison of the derived functor of a composite with the composite of the derived functors
and of the derived functor of the identity with the identity. -/
theorem derivedNatTrans_counitIso_eq_derivedCounitIso :
    derivedNatTrans ((moduleEquivalence J).inverse ⋙ (moduleEquivalence J).functor)
          (𝟭 (Sheaf J Ab.{u})) (moduleEquivalence J).counitIso.hom ≫
        (derivedIdIso (A := Sheaf J Ab.{u})).hom =
      (derivedCompIso (moduleEquivalence J).inverse (moduleEquivalence J).functor
          ((moduleEquivalence J).inverse ⋙ (moduleEquivalence J).functor) (Iso.refl _)).hom ≫
        (derivedCounitIso J).hom := by
  rw [← mapDerivedCategoryAdjunction_counit_eq_derivedCounitIso]
  exact CategoryTheory.derivedNatTrans_counit (moduleEquivalence J).toAdjunction

end Stacks.DerivedTensor.AbelianSheaves

end
