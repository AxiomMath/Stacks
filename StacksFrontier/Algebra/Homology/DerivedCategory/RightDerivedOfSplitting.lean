module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveHomologySplitting
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition

/-!
# Right derived functors on a single complex

Let `T : 𝒜 ⥤ 𝓑` be an exact functor and `E : 𝓑 ⥤ 𝒞` an additive functor between abelian
categories, `𝓑` having enough injectives. This file identifies the cohomology of `RE(RT(V[-a]))`,
for `V` an object of `𝒜` placed in degree `a`:

`Hⁿ(RE(RT(V[-a]))) ≅ R^{n-a}E(T(V))`,

naturally in `V`. Two inputs: `RT(V[-a]) = T(V)[-a]` because `T` is exact, and
`Hⁿ(RE(M[-a])) = R^{n-a}E(M)` because `RE` commutes with shifts. This is the computation on each
summand of the sum decomposition used in the proof of [Stacks, Tag 0BEF].

## Main definitions

* `DerivedCategory.Plus.rightDerivedSingleHomologyIso`: `Hⁿ(RE(M[-a])) ≅ RᵇE(M)` for
  `a + b = n`, natural in `M`.
* `DerivedCategory.Plus.singleDerivedHomologyIso`: `Hⁿ(RE(RT(V[-a]))) ≅ RᵇE(T(V))` for
  `a + b = n`, natural in `V`.

## References

* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

namespace DerivedCategory.Plus

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
  [Abelian C] [EnoughInjectives A] [EnoughInjectives B] [HasDerivedCategory A]
  [HasDerivedCategory B] [HasDerivedCategory C]

section Single

variable (E : B ⥤ C) [E.Additive]

/-- **`Hⁿ(RE(M[-a])) ≅ RᵇE(M)`** for `a + b = n`, natural in `M`, where `RE` is the right
derived functor of `E` on bounded below derived categories. -/
def rightDerivedSingleHomologyIso (a b n : ℤ) (h : a + b = n) :
    singleFunctor B a ⋙ E.rightDerivedFunctorPlus ⋙ homologyFunctor C n ≅
      E.rightDerivedPlus b :=
  eqToIso (by rw [← h, add_comm]) ≪≫
    singleFunctorCompHomologyFunctorShiftIso E.rightDerivedFunctorPlus b a

variable (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- **`Hⁿ(RE(RT(V[-a]))) ≅ RᵇE(T(V))`** for `a + b = n` and an exact functor `T`, natural
in `V`. -/
def singleDerivedHomologyIso (a b n : ℤ) (h : a + b = n) :
    singleFunctor A a ⋙ (T.rightDerivedFunctorPlus ⋙ E.rightDerivedFunctorPlus) ⋙
        homologyFunctor C n ≅ T ⋙ E.rightDerivedPlus b :=
  calc singleFunctor A a ⋙ (T.rightDerivedFunctorPlus ⋙ E.rightDerivedFunctorPlus) ⋙
        homologyFunctor C n
    _ ≅ (singleFunctor A a ⋙ T.rightDerivedFunctorPlus) ⋙
        E.rightDerivedFunctorPlus ⋙ homologyFunctor C n :=
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm
    _ ≅ (T ⋙ singleFunctor B a) ⋙ E.rightDerivedFunctorPlus ⋙ homologyFunctor C n :=
      Functor.isoWhiskerRight
        (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso T a).symm _
    _ ≅ T ⋙ E.rightDerivedPlus b :=
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T (rightDerivedSingleHomologyIso E a b n h)

end Single

end DerivedCategory.Plus
