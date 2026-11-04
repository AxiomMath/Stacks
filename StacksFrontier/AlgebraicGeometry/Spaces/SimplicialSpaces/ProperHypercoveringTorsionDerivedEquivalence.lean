module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.ProperHypercoveringDerivedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.ProperHypercoveringFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationTorsionDerivedPlusEquivalence

/-!
# The derived category of a proper hypercovering for torsion coefficients

Let `S` be a scheme, `X` an algebraic space over `S`, `U` a simplicial algebraic space over `S`
and `a : U → X` an augmentation which is a proper hypercovering of `X` (Section 0DHI). Let
`a : Sh(U_étale) → Sh(X_étale)` be the morphism of topoi of Section 0DE7 and let
`𝒜 ⊂ Ab(U_étale)` be the weak Serre subcategory of cartesian abelian sheaves (Stacks 0D7J).
Tag 0DHN asserts that `a⁻¹ : D⁺(X_étale) ⟶ D⁺_𝒜(U_étale)` is an equivalence with quasi-inverse
`Ra_*`. This file proves it for complexes with torsion cohomology sheaves:

`a⁻¹ : D⁺_tors(X_étale) ⟶ D⁺_{𝒜, tors}(U_étale)`

is an equivalence with quasi-inverse `Ra_*`, where `D⁺_{𝒜, tors}(U_étale)` consists of the bounded
below complexes whose cohomology sheaves are cartesian and torsion. For arbitrary coefficients the
statement is false; see
`AlgebraicGeometry.Space.derivedPlusTorsionEquivalenceOfIsProperHypercovering`.

The proof is the source's: the equivalence is the formal consequence
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedPlusTorsionEquivalence` of Stacks 0D7U
applied to two inputs. The first is Stacks 0DHK: `a⁻¹` on abelian sheaves is fully faithful with
essential image the cartesian abelian sheaves. The second is Stacks 0DHL: the unit
`K ⟶ Ra_*a⁻¹K` is an isomorphism for every `K` in `D⁺_tors(X_étale)`.

## Main results

* `AlgebraicGeometry.Space.faithful_totalInverseImageAb_etaleAugmentation`: `a⁻¹` is faithful on
  abelian sheaves.
* `AlgebraicGeometry.Space.mem_essImage_totalInverseImageAb_etaleAugmentation`: every cartesian
  abelian sheaf on `U_étale` is `a⁻¹` of an abelian sheaf on `X_étale`.
* `AlgebraicGeometry.Space.isIso_abelianTotalAdjunction_rightDerivedFunctorPlus_unit_app`: the
  unit `K ⟶ Ra_*a⁻¹K` of the adjunction `a⁻¹ ⊣ Ra_*` on `D⁺` is an isomorphism on
  `D⁺_tors(X_étale)`.
* `AlgebraicGeometry.Space.derivedPlusTorsionEquivalenceOfIsProperHypercovering`: **Tag 0DHN**
  for torsion coefficients, with
  `AlgebraicGeometry.Space.derivedPlusTorsionEquivalenceOfIsProperHypercovering_functor` and
  `AlgebraicGeometry.Space.derivedPlusTorsionEquivalenceOfIsProperHypercovering_inverse`
  identifying its functors with `a⁻¹` and `Ra_*`.

## Implementation notes

`X = A.right`, `U = A.left` and `a = A.hom`; `X_étale` is the spaces-étale site of `X` and
`U_étale` the total site of Section 0DE7. The derived categories are the standard models, those
in which Stacks 0DHL is stated. The functor `a⁻¹` on `D⁺` is the right derived functor of the
exact functor `a⁻¹`, that is `a⁻¹` applied degreewise.

## References

* [Stacks Project, Tag 0DHN](https://stacks.math.columbia.edu/tag/0DHN)
* [Stacks Project, Tag 0DHK](https://stacks.math.columbia.edu/tag/0DHK)
* [Stacks Project, Tag 0DHL](https://stacks.math.columbia.edu/tag/0DHL)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Section 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace AlgebraicGeometry.Space

open SimplicialSiteSituation.Augmentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

/-- The inverse image of abelian sheaves along `a : Sh(U_étale) → Sh(X_étale)` is additive. The
general instance does not apply syntactically, the augmentation of Section 0DE7 being given in its
continuous form. -/
local instance additive_totalInverseImageAb_etaleAugmentation :
    (totalInverseImageAb (etaleSituation A) _ _ (etaleAugmentation A)).Additive :=
  additive_totalInverseImageAb _ _ _ _

/-- The inverse image of abelian sheaves along `a : Sh(U_étale) → Sh(X_étale)` is left exact. -/
local instance preservesFiniteLimits_totalInverseImageAb_etaleAugmentation :
    PreservesFiniteLimits (totalInverseImageAb (etaleSituation A) _ _ (etaleAugmentation A)) :=
  preservesFiniteLimits_totalInverseImageAb _ _ _ _

/-- The inverse image of abelian sheaves along `a : Sh(U_étale) → Sh(X_étale)` is right exact. -/
local instance preservesFiniteColimits_totalInverseImageAb_etaleAugmentation :
    PreservesFiniteColimits (totalInverseImageAb (etaleSituation A) _ _ (etaleAugmentation A)) :=
  preservesFiniteColimits_totalInverseImageAb _ _ _ _

/-- The direct image of abelian sheaves along `a : Sh(U_étale) → Sh(X_étale)` is additive. -/
local instance additive_abelianTotalPushforward_etaleAugmentation :
    (abelianTotalPushforward (etaleSituation A) _ _ (etaleAugmentation A)).Additive :=
  additive_abelianTotalPushforward _ _ _ _

/-- `a⁻¹ : Ab(X_étale) ⥤ Ab(U_étale)` is faithful for a proper hypercovering (Stacks 0DHK). -/
theorem faithful_totalInverseImageAb_etaleAugmentation (hA : IsProperHypercovering B S hS A) :
    (totalInverseImageAb (etaleSituation A) _ _ (etaleAugmentation A)).Faithful :=
  (BigPHSpaceSite.etaleAugmentation_abelianInverseImage_fullyFaithful_of_isProperHypercovering
    (B.bigPHSpaceSite S hS) hA).2.1

/-- Every cartesian abelian sheaf on `U_étale` is `a⁻¹` of an abelian sheaf on `X_étale`, for a
proper hypercovering (Stacks 0DHK). -/
theorem mem_essImage_totalInverseImageAb_etaleAugmentation (hA : IsProperHypercovering B S hS A)
    (G : Sheaf (etaleSituation A).totalTopology AddCommGrpCat.{u + 1})
    (hG : SimplicialSiteSituation.IsCartesianAbSheaf (etaleSituation A) G) :
    (totalInverseImageAb (etaleSituation A) _ _ (etaleAugmentation A)).essImage G :=
  ((BigPHSpaceSite.etaleAugmentation_abelianInverseImage_fullyFaithful_of_isProperHypercovering
    (B.bigPHSpaceSite S hS) hA).2.2.1 G).2 hG

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Cohomological descent on `D⁺_tors(X_étale)` (Stacks 0DHL).** For a proper hypercovering the
unit `K ⟶ Ra_*a⁻¹K` of the adjunction `a⁻¹ ⊣ Ra_*` on `D⁺` is an isomorphism at every `K` with
torsion cohomology sheaves, `a⁻¹` on `D⁺` being the right derived functor of the exact `a⁻¹`. -/
theorem isIso_abelianTotalAdjunction_rightDerivedFunctorPlus_unit_app
    (hA : IsProperHypercovering B S hS A)
    (K : DerivedCategory.Plus (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1}))
    (hK : (DerivedCategoryB.derivedCategoryB
      (Stacks.Torsion.torsionSheafProperty.{u + 1, u + 1, u + 1}
        (SpacesEtale.topology B S hS A.right))).inverseImage
        DerivedCategory.Plus.ι K) :
    IsIso ((abelianTotalAdjunction (etaleSituation A) _ _
      (etaleAugmentation A)).rightDerivedFunctorPlus.unit.app K) :=
  (isIso_rightDerivedFunctorPlus_unit_app_iff (etaleSituation A) _ _ (etaleAugmentation A) K).2
    (isIso_etaleAugmentation_derivedPlusUnit_of_isProperHypercovering hA K hK)

/-- **Stacks Project, Tag 0DHN**, for torsion coefficients. Let `S` be a scheme, `X` an algebraic
space over `S`, `U` a simplicial algebraic space over `S` and `a : U → X` an augmentation, and let
`𝒜 ⊂ Ab(U_étale)` be the weak Serre subcategory of cartesian abelian sheaves. If `U` is a proper
hypercovering of `X`, then `a⁻¹` defines an equivalence

`D⁺_tors(X_étale) ⟶ D⁺_{𝒜, tors}(U_étale)`

with quasi-inverse `Ra_*`, where `a : Sh(U_étale) → Sh(X_étale)` is the morphism of topoi of
Section 0DE7, `D⁺_tors(X_étale)` consists of the bounded below complexes with torsion cohomology
sheaves and `D⁺_{𝒜, tors}(U_étale)` of those whose cohomology sheaves are cartesian and torsion.
The functors are identified by
`AlgebraicGeometry.Space.derivedPlusTorsionEquivalenceOfIsProperHypercovering_functor` and
`AlgebraicGeometry.Space.derivedPlusTorsionEquivalenceOfIsProperHypercovering_inverse`.

The source states this for `D⁺(X_étale) ⟶ D⁺_𝒜(U_étale)`, and as written it is false: its proof
uses Stacks 0DHL, whose proof cites Stacks 0DGU, which holds only for complexes with torsion
cohomology sheaves. For a counterexample with rational coefficients let `X` be a normal surface
over an algebraically closed field with a cusp singularity `x`, let `π : X̃ → X` be a resolution
whose exceptional curve `E` over `x` is a cycle of rational curves, and let `U` be the Čech nerve
of the proper surjective morphism `X̃ ⊔ {x} → X`, a proper hypercovering. If `a⁻¹` were fully
faithful on `D⁺(X_étale)` with quasi-inverse `Ra_*`, then `ℚ = Ra_*a⁻¹ℚ`, and the spectral sequence
of the hypercovering would give `H²(X_étale, ℚ) ≠ 0`, coming from `H¹(E, ℚ) = ℚ`; but
`Hⁱ(X_étale, ℚ) = 0` for `i > 0` because `X` is normal. The torsion hypothesis is therefore part of
the statement, and this is the corrected form.

The proof is the source's: Stacks 0DHK (`a⁻¹` on abelian sheaves is fully faithful with essential
image the cartesian sheaves) and Stacks 0DHL (`K ≅ Ra_*a⁻¹K` on `D⁺_tors(X_étale)`) are the inputs
of the formal equivalence of Stacks 0D7U,
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedPlusTorsionEquivalence`. -/
@[stacks 0DHN "torsion coefficients: `a⁻¹ : D⁺_tors(X_étale) ≌ D⁺_{𝒜, tors}(U_étale)`; the
  statement for all of `D⁺(X_étale)` is false"]
def derivedPlusTorsionEquivalenceOfIsProperHypercovering (hA : IsProperHypercovering B S hS A) :
    ((DerivedCategoryB.derivedCategoryB
      (Stacks.Torsion.torsionSheafProperty.{u + 1, u + 1, u + 1}
        (SpacesEtale.topology B S hS A.right))).inverseImage
          DerivedCategory.Plus.ι).FullSubcategory ≌
      ((DerivedCategoryB.derivedCategoryB
        (cartesianTorsionAbSheaf (etaleSituation A))).inverseImage
          DerivedCategory.Plus.ι).FullSubcategory :=
  letI := faithful_totalInverseImageAb_etaleAugmentation hA
  derivedPlusTorsionEquivalence (etaleSituation A) _ _ (etaleAugmentation A)
    (mem_essImage_totalInverseImageAb_etaleAugmentation hA)
    (isIso_abelianTotalAdjunction_rightDerivedFunctorPlus_unit_app hA)

/-- **The equivalence of Tag 0DHN is `a⁻¹`**: its forward functor, followed by the inclusion into
`D⁺(U_étale)`, is the inclusion of `D⁺_tors(X_étale)` followed by
`a⁻¹ : D⁺(X_étale) ⥤ D⁺(U_étale)`, the right derived functor of the exact functor `a⁻¹`. -/
@[stacks 0DHN "the equivalence is `a⁻¹`"]
theorem derivedPlusTorsionEquivalenceOfIsProperHypercovering_functor
    (hA : IsProperHypercovering B S hS A) :
    (derivedPlusTorsionEquivalenceOfIsProperHypercovering hA).functor ⋙
        ((DerivedCategoryB.derivedCategoryB
          (cartesianTorsionAbSheaf (etaleSituation A))).inverseImage DerivedCategory.Plus.ι).ι =
      ((DerivedCategoryB.derivedCategoryB
        (Stacks.Torsion.torsionSheafProperty.{u + 1, u + 1, u + 1}
          (SpacesEtale.topology B S hS A.right))).inverseImage DerivedCategory.Plus.ι).ι ⋙
        (totalInverseImageAb (etaleSituation A) _ _
          (etaleAugmentation A)).rightDerivedFunctorPlus :=
  rfl

/-- **The quasi-inverse of the equivalence of Tag 0DHN is `Ra_*`**: its inverse functor, followed
by the inclusion into `D⁺(X_étale)`, is the inclusion of `D⁺_{𝒜, tors}(U_étale)` followed by
`Ra_* : D⁺(U_étale) ⥤ D⁺(X_étale)`. -/
@[stacks 0DHN "the quasi-inverse is `Ra_*`"]
theorem derivedPlusTorsionEquivalenceOfIsProperHypercovering_inverse
    (hA : IsProperHypercovering B S hS A) :
    (derivedPlusTorsionEquivalenceOfIsProperHypercovering hA).inverse ⋙
        ((DerivedCategoryB.derivedCategoryB
          (Stacks.Torsion.torsionSheafProperty.{u + 1, u + 1, u + 1}
            (SpacesEtale.topology B S hS A.right))).inverseImage DerivedCategory.Plus.ι).ι =
      ((DerivedCategoryB.derivedCategoryB
        (cartesianTorsionAbSheaf (etaleSituation A))).inverseImage DerivedCategory.Plus.ι).ι ⋙
        (abelianTotalPushforward (etaleSituation A) _ _
          (etaleAugmentation A)).rightDerivedFunctorPlus :=
  rfl

end Derived

end AlgebraicGeometry.Space

end
