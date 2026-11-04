module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfHypercoveringInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfHypercoveringDerivedDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationDerivedPlusEquivalence

/-!
# The derived category of an fppf hypercovering

Let `S` be a scheme, `X` an algebraic space over `S`, `U` a simplicial algebraic space over `S`
and `a : U → X` an augmentation which is an fppf hypercovering of `X` (Section 0DH4). Let
`a : Sh(U_étale) → Sh(X_étale)` be the morphism of topoi of Section 0DE7 and let
`𝒜 ⊂ Ab(U_étale)` be the weak Serre subcategory of cartesian abelian sheaves (Stacks 0D7J).
Stacks 0DH9 asserts that

`a⁻¹ : D⁺(X_étale) ⟶ D⁺_𝒜(U_étale)`

is an equivalence with quasi-inverse `Ra_*`, where `D⁺_𝒜(U_étale)` consists of the bounded below
complexes of abelian sheaves on `U_étale` whose cohomology sheaves are cartesian.

The proof is the source's: the equivalence is the formal consequence
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedPlusInverseImageEquivalence` of
Stacks 0D7U applied to two inputs. The first is the content of Stacks 0DH6: every cartesian
abelian sheaf on `U_étale` is `a⁻¹` of an abelian sheaf on `X_étale`
(`AlgebraicGeometry.Space.IsFppfHypercovering.mem_essImage_totalInverseImageAb`). The second is
the content of Stacks 0DH7: the unit `K ⟶ Ra_*a⁻¹K` is an isomorphism for every `K` in
`D⁺(X_étale)`, in the namespace `AlgebraicGeometry.Space`
(`IsFppfHypercovering.isIso_abelianTotalAdjunction_rightDerivedFunctorPlus_unit_app`).

## Main results

* `AlgebraicGeometry.Space.derivedPlusEquivalenceOfIsFppfHypercovering`: **Stacks 0DH9**, with
  `AlgebraicGeometry.Space.derivedPlusEquivalenceOfIsFppfHypercovering_functor` and
  `AlgebraicGeometry.Space.derivedPlusEquivalenceOfIsFppfHypercovering_inverse` identifying its
  functors with `a⁻¹` and `Ra_*`.

## Implementation notes

`X = A.right`, `U = A.left` and `a = A.hom`; `X_étale` is the spaces-étale site of `X`, which
Section 0DE7 identifies with the small étale site, and `U_étale` the total site of Section 0DE7.
The derived categories are arbitrary models. The functor `a⁻¹` on `D⁺` is the right derived
functor of the exact functor `a⁻¹`, that is `a⁻¹` applied degreewise, and `D⁺_𝒜(U_étale)` is
`CategoryTheory.SimplicialSiteSituation.Augmentation.cartesianDerivedPlus`.

## References

* [Stacks Project, Tag 0DH9](https://stacks.math.columbia.edu/tag/0DH9)
* [Stacks Project, Tag 0DH6](https://stacks.math.columbia.edu/tag/0DH6)
* [Stacks Project, Tag 0DH7](https://stacks.math.columbia.edu/tag/0DH7)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Section 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open SimplicialSiteSituation.Augmentation

attribute [local instance] additive_totalInverseImageAb_etaleAugmentation
  preservesFiniteLimits_totalInverseImageAb_etaleAugmentation
  preservesFiniteColimits_totalInverseImageAb_etaleAugmentation
  additive_abelianTotalPushforward_etaleAugmentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}
  [HasDerivedCategory (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (etaleSituation A).totalTopology AddCommGrpCat.{u + 1})]

/-- **Stacks Project, Tag 0DH9.** Let `S` be a scheme, `X` an algebraic space over `S`, `U` a
simplicial algebraic space over `S` and `a : U → X` an augmentation, and let
`𝒜 ⊂ Ab(U_étale)` be the weak Serre subcategory of cartesian abelian sheaves. If `U` is an fppf
hypercovering of `X`, then `a⁻¹` defines an equivalence

`D⁺(X_étale) ⟶ D⁺_𝒜(U_étale)`

with quasi-inverse `Ra_*`, where `a : Sh(U_étale) → Sh(X_étale)` is the morphism of topoi of
Section 0DE7 and `D⁺_𝒜(U_étale)` consists of the bounded below complexes whose cohomology sheaves
are cartesian. The functors are identified by
`AlgebraicGeometry.Space.derivedPlusEquivalenceOfIsFppfHypercovering_functor` and
`AlgebraicGeometry.Space.derivedPlusEquivalenceOfIsFppfHypercovering_inverse`.

The proof is the source's: the content of Stacks 0DH6 (every cartesian abelian sheaf on
`U_étale` is `a⁻¹` of an abelian sheaf on `X_étale`) and of Stacks 0DH7 (`K ≅ Ra_*a⁻¹K` on
`D⁺(X_étale)`) are the inputs of the formal equivalence of Stacks 0D7U,
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedPlusInverseImageEquivalence`. -/
@[stacks 0DH9]
def derivedPlusEquivalenceOfIsFppfHypercovering (hA : IsFppfHypercovering A) :
    DerivedCategory.Plus (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1}) ≌
      (cartesianDerivedPlus (etaleSituation A)).FullSubcategory :=
  derivedPlusInverseImageEquivalence (etaleSituation A) _ _ (etaleAugmentation A)
    hA.isIso_abelianTotalAdjunction_rightDerivedFunctorPlus_unit_app
    hA.mem_essImage_totalInverseImageAb

/-- **The equivalence of Tag 0DH9 is `a⁻¹`**: its forward functor, followed by the inclusion of
`D⁺_𝒜(U_étale)` into `D⁺(U_étale)`, is `a⁻¹ : D⁺(X_étale) ⥤ D⁺(U_étale)`, the right derived
functor of the exact functor `a⁻¹`. -/
@[stacks 0DH9 "the equivalence is `a⁻¹`"]
theorem derivedPlusEquivalenceOfIsFppfHypercovering_functor (hA : IsFppfHypercovering A) :
    (derivedPlusEquivalenceOfIsFppfHypercovering hA).functor ⋙
        (cartesianDerivedPlus (etaleSituation A)).ι =
      (totalInverseImageAb (etaleSituation A) _ _ (etaleAugmentation A)).rightDerivedFunctorPlus :=
  rfl

/-- **The quasi-inverse of the equivalence of Tag 0DH9 is `Ra_*`**: its inverse functor is the
inclusion of `D⁺_𝒜(U_étale)` into `D⁺(U_étale)` followed by `Ra_* : D⁺(U_étale) ⥤ D⁺(X_étale)`. -/
@[stacks 0DH9 "the quasi-inverse is `Ra_*`"]
theorem derivedPlusEquivalenceOfIsFppfHypercovering_inverse (hA : IsFppfHypercovering A) :
    (derivedPlusEquivalenceOfIsFppfHypercovering hA).inverse =
      (cartesianDerivedPlus (etaleSituation A)).ι ⋙
        (abelianTotalPushforward (etaleSituation A) _ _
          (etaleAugmentation A)).rightDerivedFunctorPlus :=
  rfl

end AlgebraicGeometry.Space

end
