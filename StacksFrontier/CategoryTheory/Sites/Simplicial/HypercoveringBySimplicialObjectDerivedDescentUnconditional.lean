module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObject
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectDerivedDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedDescentUnconditional

/-!
# Derived descent along a hypercovering by a simplicial object of the site

Let `C` be a site with fibre products given by a pretopology `P`, let `X` be an object of `C`,
let `U` be a simplicial object of `C` and let `a : U ⟶ X` be an augmentation which is a
hypercovering of `X` in `C` in the sense of Stacks 09X8, that is, which satisfies the three
covering conditions of `Stacks.CategoryTheory.Hypercovering.IsHypercoveringAugmentation`. Write
`(C/U)_total` for the total site of the simplicial semi-representable object `n ↦ {U_n ⟶ X}` over
`X`, and `a : Sh((C/U)_total) ⟶ Sh(C/X)` for the augmentation given by the degree-zero
localization functor. This file proves Stacks 09X9 and Stacks 0DA9 for this augmentation, as the
statements of Stacks 09X7 and of Stacks 0D8M at the simplicial semi-representable object
`n ↦ {U_n ⟶ X}`.

All names are in the namespace `CategoryTheory.SimplicialSemiRepresentable`.

## Main definitions

* `derivedGlobalSectionsInverseImageIsoAugmented'`: Stacks 09X9, the isomorphism
  `RΓ(X, -) ≅ a⁻¹ ⋙ RΓ((C/U)_total, -)` of functors on the unbounded derived category of abelian
  sheaves on `C/X`.
* `derivedTotalInverseImageEquivalenceAugmented'`: Stacks 0DA9, the equivalence
  `D⁺(C/X) ≌ D⁺_𝒜((C/U)_total)`, where `𝒜 ⊂ Ab((C/U)_total)` is the weak Serre subcategory of
  cartesian abelian sheaves of Stacks 0D7J and `D⁺(C/X)` is
  `DerivedCategoryB.derivedCategoryBPlus` of the subcategory of all abelian sheaves on `C/X`.

## Main results

* `derivedGlobalSectionsInverseImageIsoAugmented_hom_app'`: at every `E` of `D(C/X)` the forward
  map of the isomorphism of Stacks 09X9 is `RΓ(X, -)` applied to the canonical map
  `E ⟶ Ra_*a⁻¹E` of Stacks 0D8L, followed by the derived factorisation
  `Ra_* ⋙ RΓ(X, -) ≅ RΓ((C/U)_total, -)` of Stacks 08J6.
* `derivedTotalInverseImageEquivalenceAugmented_functor'` and
  `derivedTotalInverseImageEquivalenceAugmented_inverse'`: the two functors of the equivalence of
  Stacks 0DA9 are the restrictions of `a⁻¹` and of `Ra_*` to the bounded below subcategories.

## References

* [Stacks Project, Tag 09X9](https://stacks.math.columbia.edu/tag/09X9)
* [Stacks Project, Tag 0DA9](https://stacks.math.columbia.edu/tag/0DA9)
* [Stacks Project, Tag 09X7](https://stacks.math.columbia.edu/tag/09X7)
* [Stacks Project, Tag 0D8M](https://stacks.math.columbia.edu/tag/0D8M)
* [Stacks Project, Tag 0DA8](https://stacks.math.columbia.edu/tag/0DA8)
* [Stacks Project, Tag 0D8L](https://stacks.math.columbia.edu/tag/0D8L)
* [Stacks Project, Tag 0D8K](https://stacks.math.columbia.edu/tag/0D8K)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 09X8](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialSiteSituation Opposite

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open Stacks.CategoryTheory.Hypercovering

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)

/-! ### Stacks 09X9: derived global sections are unchanged by the inverse image -/

/-- **Stacks Project, Tag 09X9.** For a site `C` with fibre products, an object `X` of `C` and
a hypercovering `a : U ⟶ X` of `X` in `C` by a simplicial object `U` of `C`, with
`a : Sh((C/U)_total) ⟶ Sh(C/X)` the augmentation of Stacks 09X8, derived global sections over `X`
are derived global sections on the total site of the inverse image:

`RΓ(X, E) = RΓ((C/U)_total, a⁻¹E)`.

The statement is an isomorphism of functors on the unbounded derived category of abelian sheaves
on `C/X`, so it holds at every object `E` of `D(C/X)`. -/
@[stacks 09X9]
def derivedGlobalSectionsInverseImageIsoAugmented'
    (h : IsHypercoveringAugmentation P U a) :
    Augmentation.derivedGlobalSectionsBase (Cat.of (Over X)) (P.toGrothendieck.over X) ≅
      Augmentation.derivedTotalInverseImage (totalSituation P U a) (Cat.of (Over X))
          (P.toGrothendieck.over X) (augmentationAugmented P U a) ⋙
        Augmentation.derivedGlobalSectionsTotal (totalSituation P U a) :=
  derivedGlobalSectionsInverseImageIsoOverOfHypercovering P
    (associatedSimplicialObject.{u} U a) (h.isHypercovering P U a)

/-- **Stacks 09X9, the isomorphism is invertibility of the canonical comparison map.** At every
object `E` of `D(C/X)` the forward map of the isomorphism of Stacks 09X9 is derived global
sections over `X` applied to the canonical map `E ⟶ Ra_*a⁻¹E` of Stacks 0D8L, followed by the
derived factorisation `Ra_* ⋙ RΓ(X, -) ≅ RΓ((C/U)_total, -)` of Stacks 08J6. -/
@[stacks 09X9 "the forward map of the isomorphism is the canonical one — RΓ(X, -) of the
canonical map E ⟶ Ra_*a⁻¹E of Tag 0D8L followed by the derived factorisation of Tag 08J6"]
theorem derivedGlobalSectionsInverseImageIsoAugmented_hom_app'
    (h : IsHypercoveringAugmentation P U a)
    (E : DerivedCategory (Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u})) :
    (derivedGlobalSectionsInverseImageIsoAugmented' P U a h).hom.app E =
      (Augmentation.derivedGlobalSectionsBase (Cat.of (Over X))
          (P.toGrothendieck.over X)).map
        ((Augmentation.derivedAugmentationUnit (totalSituation P U a) (Cat.of (Over X))
          (P.toGrothendieck.over X) (augmentationAugmented P U a)).app E) ≫
        (Augmentation.derivedGlobalSectionsPushforwardIso (totalSituation P U a)
          (Cat.of (Over X)) (P.toGrothendieck.over X) (augmentationAugmented P U a)
            (abelianTotalPushforwardGammaIsoOver P
              (associatedSimplicialObject.{u} U a))).hom.app
            ((Augmentation.derivedTotalInverseImage (totalSituation P U a) (Cat.of (Over X))
              (P.toGrothendieck.over X) (augmentationAugmented P U a)).obj E) := by
  simp only [derivedGlobalSectionsInverseImageIsoAugmented',
    derivedGlobalSectionsInverseImageIsoOverOfHypercovering,
    derivedGlobalSectionsInverseImageIsoOver,
    Augmentation.derivedGlobalSectionsInverseImageIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, asIso_hom, Category.id_comp]

/-! ### Stacks 0DA9: the bounded below equivalence -/

/-- **Stacks Project, Tag 0DA9.** For a site `C` with fibre products, an object `X` of `C`, a
hypercovering `a : U ⟶ X` of `X` in `C` by a simplicial object `U` of `C`, the augmentation
`a : Sh((C/U)_total) ⟶ Sh(C/X)` of Stacks 09X8, and the weak Serre subcategory
`𝒜 ⊂ Ab((C/U)_total)` of cartesian abelian sheaves of Stacks 0D7J, the derived inverse image is
an equivalence

`a⁻¹ : D⁺(C/X) ⟶ D⁺_𝒜((C/U)_total)`

with quasi-inverse `Ra_*`. -/
@[stacks 0DA9]
def derivedTotalInverseImageEquivalenceAugmented'
    (h : IsHypercoveringAugmentation P U a) :
    (DerivedCategoryB.derivedCategoryBPlus
        (⊤ : ObjectProperty
          (Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u}))).FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryBPlus
        ((totalSituation P U a).IsCartesianAbSheaf)).FullSubcategory :=
  derivedTotalInverseImageEquivalenceOverOfHypercovering P
    (associatedSimplicialObject.{u} U a) (h.isHypercovering P U a)

/-- **Stacks 0DA9, the forward functor of the equivalence is `a⁻¹`:** it is the restriction of
the derived inverse image along the augmentation to the bounded below subcategories. -/
@[stacks 0DA9 "the forward functor of the equivalence is a⁻¹"]
theorem derivedTotalInverseImageEquivalenceAugmented_functor'
    (h : IsHypercoveringAugmentation P U a) :
    (derivedTotalInverseImageEquivalenceAugmented' P U a h).functor =
      Augmentation.derivedTotalInverseImagePlus (totalSituation P U a) (Cat.of (Over X))
        (P.toGrothendieck.over X) (augmentationAugmented P U a) :=
  rfl

/-- **Stacks 0DA9, the quasi-inverse of the equivalence is `Ra_*`:** it is the restriction of the
derived direct image along the augmentation to the bounded below subcategories. -/
@[stacks 0DA9 "the quasi-inverse of the equivalence is Ra_*"]
theorem derivedTotalInverseImageEquivalenceAugmented_inverse'
    (h : IsHypercoveringAugmentation P U a) :
    (derivedTotalInverseImageEquivalenceAugmented' P U a h).inverse =
      Augmentation.derivedTotalPushforwardPlus (totalSituation P U a) (Cat.of (Over X))
        (P.toGrothendieck.over X) (augmentationAugmented P U a) :=
  rfl

end CategoryTheory.SimplicialSemiRepresentable

end
