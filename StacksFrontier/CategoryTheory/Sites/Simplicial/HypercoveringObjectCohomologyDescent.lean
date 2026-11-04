module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedDescentUnconditional
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Descent of the cohomology of a single sheaf along a hypercovering of an object

Let `C` be a site with fibre products given by a pretopology `P`, let `X` be an object of `C`,
let `K` be a hypercovering of `X` and let `a : Sh((C/K)_total) → Sh(C/X)` be the augmentation of
Stacks 0D8B read over the slice site. Stacks 09X7 asserts `RΓ(X, E) = RΓ((C/K)_total, a⁻¹E)` on
the derived category of `C/X`. This file reads that isomorphism off on a single abelian sheaf
placed in degree zero and in one cohomological degree: for an abelian sheaf `F` on `C/X`,

`H^n(X, F) ≅ H^n((C/K)_total, a⁻¹F)`,

naturally in `F`, with both sides Mathlib's classical right derived functors of global sections.

## Main definitions

* `SimplicialSiteSituation.Augmentation.derivedTotalInverseImageIsoMapDerivedCategory`:
  the derived inverse image along a total augmentation is the functor induced on derived
  categories by the exact functor `a⁻¹`, as a natural isomorphism.
* `SimplicialSemiRepresentable.rightDerivedGlobalSectionsIsoOfHypercovering`:
  **Stacks 09X7 in each cohomological degree**, for a single abelian sheaf.

## Implementation notes

The two sides of Stacks 09X7 are read on `F[0]` and in degree `n` through
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`, which identifies
`H^n(Rw(F[0]))` with `Rⁿw(F)` naturally in `F`, and the derived inverse image of `F[0]` is
`(a⁻¹F)[0]` because `a⁻¹` is exact. The derived categories are the ones Stacks 09X7 is stated
with; the statement proved here mentions no derived category, so it is independent of that
choice.

## References

* [Stacks Project, Tag 09X7](https://stacks.math.columbia.edu/tag/09X7)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialSiteSituation Opposite

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- **The derived inverse image is the induced functor on derived categories.** The derived
inverse image along the total augmentation is, as a functor, the functor induced on derived
categories by the exact functor `a⁻¹` of abelian sheaves: both extend the degreewise inverse
image followed by localization along the localization functor of the homotopy category. -/
def derivedTotalInverseImageIsoMapDerivedCategory :
    derivedTotalInverseImage S D K a ≅ (totalInverseImageAb S D K a).mapDerivedCategory :=
  have := isIso_derivedTotalInverseImageComparison S D K a
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ)) _).preimageIso
    (asIso (derivedTotalInverseImageComparison S D K a) ≪≫
      (totalInverseImageAb S D K a).mapDerivedCategoryFactorsh.symm)

/-- **`a⁻¹(F[0]) = (a⁻¹F)[0]`, naturally in `F`.** -/
def singleFunctorCompDerivedTotalInverseImageIso :
    DerivedCategory.singleFunctor (Sheaf K AddCommGrpCat.{u}) 0 ⋙
        derivedTotalInverseImage S D K a ≅
      totalInverseImageAb S D K a ⋙
        DerivedCategory.singleFunctor (Sheaf S.totalTopology AddCommGrpCat.{u}) 0 :=
  Functor.isoWhiskerLeft _ (derivedTotalInverseImageIsoMapDerivedCategory S D K a) ≪≫
    (totalInverseImageAb S D K a).mapDerivedCategorySingleFunctor 0

end CategoryTheory.SimplicialSiteSituation.Augmentation

namespace CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard

open Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X))) (hK : IsHypercovering P K)

/-- Global sections of abelian sheaves on the slice site `C/X` are additive, being a right
adjoint and therefore preserving binary products. -/
instance additive_globalSectionsOver :
    (Sheaf.Γ (P.toGrothendieck.over X) AddCommGrpCat.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

include hK in
/-- **Stacks 09X7 in each cohomological degree.** Let `C` be a site with fibre products, `X` an
object of `C`, `K` a hypercovering of `X` and `a : Sh((C/K)_total) → Sh(C/X)` the augmentation of
Stacks 0D8B. For an abelian sheaf `F` on `C/X` and every `n`,

`H^n(X, F) ≅ H^n((C/K)_total, a⁻¹F)`,

naturally in `F`, both sides being the classical right derived functors of global sections. It is
Stacks 09X7, `RΓ(X, E) = RΓ((C/K)_total, a⁻¹E)`, read at `E = F[0]` in degree `n`. -/
def rightDerivedGlobalSectionsIsoOfHypercovering (n : ℕ) :
    (Sheaf.Γ (P.toGrothendieck.over X) AddCommGrpCat.{u}).rightDerived n ≅
      Augmentation.totalInverseImageAb (situationOver P K) (Cat.of (Over X))
          (P.toGrothendieck.over X) (augmentationOver P K) ⋙
        (Sheaf.Γ (situationOver P K).totalTopology AddCommGrpCat.{u}).rightDerived n :=
  (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (Sheaf.Γ (P.toGrothendieck.over X) AddCommGrpCat.{u})
      (Augmentation.derivedGlobalSectionsBase (Cat.of (Over X)) (P.toGrothendieck.over X))
      ((Stacks.DerivedFunctor.homotopyMap
        (Sheaf.Γ (P.toGrothendieck.over X) AddCommGrpCat.{u})).totalRightDerivedUnit
          DerivedCategory.Qh _)
      (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _) n).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (derivedGlobalSectionsInverseImageIsoOverOfHypercovering P K hK) _) ≪≫
    Functor.isoWhiskerRight
      (Augmentation.singleFunctorCompDerivedTotalInverseImageIso (situationOver P K)
        (Cat.of (Over X)) (P.toGrothendieck.over X) (augmentationOver P K))
      (Augmentation.derivedGlobalSectionsTotal (situationOver P K) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
        (Sheaf.Γ (situationOver P K).totalTopology AddCommGrpCat.{u})
        (Augmentation.derivedGlobalSectionsTotal (situationOver P K))
        ((Stacks.DerivedFunctor.homotopyMap
          (Sheaf.Γ (situationOver P K).totalTopology AddCommGrpCat.{u})).totalRightDerivedUnit
            DerivedCategory.Qh _)
        (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _) n)

end CategoryTheory.SimplicialSemiRepresentable

end
