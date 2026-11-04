module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# The composite right derived comparison is the edge morphism

Let `L : C ⥤ D` be an exact additive functor preserving injective objects and let `G : D ⥤ E` be
additive. Two morphisms `Rⁿ G (L ℱ) ⟶ Rⁿ (G ∘ L)(ℱ)` are available in this development:

* `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, whose inverse is this
  morphism, built from the observation that `L` applied to an injective resolution of `ℱ` *is*
  an injective resolution of `L ℱ`, so that both sides are computed by the same complex; and
* `Stacks.Cohomology.RightDerivedEdge.edge`, the edge morphism of the pair `(L, G)`, built with
  no exactness hypothesis on `L` from the comparison of the chosen injective resolution of
  `L ℱ` with `L` applied to the chosen injective resolution of `ℱ`.

They agree (`compRightDerivedNatIso_inv_eq_edge`). Composed with
`Stacks.DerivedIndexing.edge_comp_rightDerivedIsoRes` this computes
`compRightDerivedNatIso` in the `ℤ`-indexed world in which
`Stacks.DerivedIndexing.rightDerivedIsoRes` reads the right derived functors.

## Main results

* `Stacks.DerivedIndexing.compRightDerivedNatIso_inv_eq_edge`: **the inverse of the composite
  right derived comparison is the edge morphism of the pair.**
* `Stacks.DerivedIndexing.compRightDerivedNatIso_inv_app_comp_rightDerivedIsoRes`: **the
  composite right derived comparison, read through the comparison of the two indexings**, is the
  degree-`n` homology of `G` applied to the extension by zero of the comparison of the chosen
  injective resolutions.
* `Stacks.DerivedIndexing.mapInjRes_ι_f_zero`: the augmentation of `L` applied to a resolution is
  `L` applied to the augmentation.
* `Stacks.DerivedIndexing.compRightDerivedNatIso_inv_app`: the closed form of the components of
  the comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace Stacks.DerivedIndexing

universe v v' v'' u u' u''

section PreComposition

open Stacks.Cohomology.CompositeRightDerived Stacks.Cohomology.RightDerivedEdge

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [EnoughInjectives C] [EnoughInjectives D]
  (L : C ⥤ D) (G : D ⥤ E) [L.Additive] [G.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] [L.PreservesInjectiveObjects]

omit [EnoughInjectives C] [EnoughInjectives D] in
/-- The augmentation of the injective resolution obtained by applying `L` termwise is `L`
applied to the augmentation. -/
lemma mapInjRes_ι_f_zero {X : C} (I : InjectiveResolution X) :
    (mapInjRes L I).ι.f 0 = L.map (I.ι.f 0) := by
  dsimp [mapInjRes]
  simp

/-- **The components of the inverse of `compRightDerivedNatIso`**: the comparison of the chosen
resolution of `L X` obtained by applying `L`, followed by the inverse of the comparison for the
composite. -/
lemma compRightDerivedNatIso_inv_app (n : ℕ) (X : C) :
    (compRightDerivedNatIso L G n).inv.app X =
      ((mapInjRes L (injectiveResolution X)).isoRightDerivedObj G n).hom ≫
        ((injectiveResolution X).isoRightDerivedObj (L ⋙ G) n).inv :=
  (show (compRightDerivedNatIso L G n).inv.app X =
      (((mapInjRes L (injectiveResolution X)).isoRightDerivedObj G n).hom ≫
        𝟙 ((HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).obj
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (mapInjRes L (injectiveResolution X)).cocomplex))) ≫
        ((injectiveResolution X).isoRightDerivedObj (L ⋙ G) n).inv from rfl).trans
    (congrArg (fun w => w ≫ ((injectiveResolution X).isoRightDerivedObj (L ⋙ G) n).inv)
      (Category.comp_id
        ((mapInjRes L (injectiveResolution X)).isoRightDerivedObj G n).hom))

/-- The inverse of the composite right derived comparison is the edge morphism. -/
theorem compRightDerivedNatIso_inv_eq_edge (n : ℕ) :
    (compRightDerivedNatIso L G n).inv = edge L G n := by
  ext X
  have hid : HomologicalComplex.homologyMap
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (𝟙 ((L.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution X).cocomplex))) n = 𝟙 _ := by
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
  rw [compRightDerivedNatIso_inv_app,
    edge_app_eq L G n (injectiveResolution X) (mapInjRes L (injectiveResolution X))
      (𝟙 ((L.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution X).cocomplex))
      ((Category.comp_id ((mapInjRes L (injectiveResolution X)).ι.f 0)).trans
        (mapInjRes_ι_f_zero L (injectiveResolution X)))]
  exact congrArg
    (fun w => ((mapInjRes L (injectiveResolution X)).isoRightDerivedObj G n).hom ≫ w)
    ((Category.id_comp ((injectiveResolution X).isoRightDerivedObj (L ⋙ G) n).inv).symm.trans
      (congrArg (fun w => w ≫ ((injectiveResolution X).isoRightDerivedObj (L ⋙ G) n).inv)
        hid.symm))

/-- **The composite right derived comparison, read through the comparison of the two
indexings.** -/
theorem compRightDerivedNatIso_inv_app_comp_rightDerivedIsoRes (n : ℕ) (X : C) :
    (compRightDerivedNatIso L G n).inv.app X ≫ (rightDerivedIsoRes (L ⋙ G) n).hom.app X =
      (rightDerivedIsoRes G n).hom.app (L.obj X) ≫
        (HomotopyCategory.homologyFunctor E (ComplexShape.up ℤ) (n : ℤ)).map
          ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
              (extendResolutionComparison L X))) := by
  rw [compRightDerivedNatIso_inv_eq_edge]
  exact edge_comp_rightDerivedIsoRes L G n X

end PreComposition

end Stacks.DerivedIndexing

end
