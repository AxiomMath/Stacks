module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# The unbounded right derived functor restricts to the bounded below one

Let `F : A ⥤ B` be an additive functor out of a Grothendieck abelian category. It has two right
derived functors: Mathlib's `F.rightDerivedFunctorPlus : D⁺(A) ⥤ D⁺(B)`, built from injective
resolutions, and the unbounded `Stacks.DerivedFunctor.totalRightDerived F : D(A) ⥤ D(B)`, built
from K-injective resolutions. They agree on bounded below objects: the square

```
D⁺(A) --RF⁺--> D⁺(B)
  |              |
  ι              ι
  v              v
D(A) ---RF---> D(B)
```

commutes up to a canonical isomorphism, compatible with the two comparison maps out of `F`
applied degreewise.

## Main definitions

* `Stacks.DerivedFunctor.rightDerivedFunctorPlusCompιIso`: `RF⁺ ⋙ ι ≅ ι ⋙ RF`.
* `Stacks.DerivedFunctor.totalRightDerivedIsoOfIso`: `RF ≅ RG` for `F ≅ G`.

## Main results

* `Stacks.DerivedFunctor.rightDerivedFunctorPlusCompιIso_hom_app`: the isomorphism carries the
  comparison map through `RF⁺` to the comparison map through `RF`.

## References

* [Stacks Project, Tag 05T5](https://stacks.math.columbia.edu/tag/05T5)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

universe v u vB uB wG wD wE

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
  [HasDerivedCategory.{wD} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wE} B]
  (F : A ⥤ B) [F.Additive]

/-- **The unbounded right derived functor only depends on the functor up to isomorphism**: an
isomorphism `e : F ≅ G` of additive functors induces `RF ≅ RG`, the uniqueness isomorphism of the
right derived functors of isomorphic functors on the homotopy category. -/
def totalRightDerivedIsoOfIso {G : A ⥤ B} [G.Additive] (e : F ≅ G) :
    totalRightDerived F ≅ totalRightDerived G :=
  Functor.rightDerivedNatIso _ _
    ((homotopyMap F).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    ((homotopyMap G).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso e (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- Degreewise `F` on a bounded below complex, read in `D(B)`. -/
abbrev boundedHomotopyMap : HomotopyCategory.Plus A ⥤ DerivedCategory B :=
  HomotopyCategory.Plus.ι A ⋙ homotopyMap F

/-- The comparison `F(K) ⟶ RF⁺(K)`, read in `D(B)`. -/
def boundedUnitPlus :
    boundedHomotopyMap F ⟶
      DerivedCategory.Plus.Qh ⋙ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) :=
  Functor.whiskerRight F.rightDerivedFunctorPlusUnit DerivedCategory.Plus.ι

/-- The comparison `F(K) ⟶ RF(K)` for a bounded below complex `K`. -/
def boundedUnitBig :
    boundedHomotopyMap F ⟶
      DerivedCategory.Plus.Qh ⋙ (DerivedCategory.Plus.ι ⋙ totalRightDerived F) :=
  Functor.whiskerLeft (HomotopyCategory.Plus.ι A)
    ((homotopyMap F).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))

/-- The comparison through `RF⁺` is invertible on a bounded below complex of injectives. -/
instance isIso_boundedUnitPlus_app (Z : HomotopyCategory.Plus (InjectiveObject A)) :
    IsIso ((boundedUnitPlus F).app ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Z)) := by
  have h : IsIso (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Z)) :=
    (HomotopyCategory.Plus.localizerMorphism_derives
        (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).isIso_of_isRightDerivedFunctor
      F.rightDerivedFunctorPlusUnit Z
  exact @Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Plus.ι _ h

/-- The comparison through the unbounded `RF` is invertible on a bounded below complex of
injectives. -/
instance isIso_boundedUnitBig_app (Z : HomotopyCategory.Plus (InjectiveObject A)) :
    IsIso ((boundedUnitBig F).app ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Z)) := by
  obtain ⟨n, hn⟩ := (HomotopyCategory.plus_quotient_obj_iff
    ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Z).obj.as).1
    ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Z).2
  have := hn
  have : CochainComplex.IsKInjective
      ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj Z).obj.as :=
    CochainComplex.isKInjective_of_injective _ n
  have : CochainComplex.IsKInjective (((InjectiveObject.ι A).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((HomotopyCategory.Plus.ι (InjectiveObject A)).obj Z).as) := this
  exact isIso_totalRightDerivedUnit_app_of_isKInjective F _

/-- `RF⁺` followed by `D⁺(B) ⥤ D(B)` is a right derived functor of degreewise `F` on `K⁺(A)`. -/
instance isRightDerivedFunctor_boundedUnitPlus :
    (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).IsRightDerivedFunctor
      (boundedUnitPlus F) (HomotopyCategory.Plus.quasiIso A) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (boundedHomotopyMap F)).isRightDerivedFunctor_of_isIso
    (boundedUnitPlus F) (fun _ => inferInstance)

/-- `D⁺(A) ⥤ D(A)` followed by the unbounded `RF` is a right derived functor of degreewise `F` on
`K⁺(A)`. -/
instance isRightDerivedFunctor_boundedUnitBig :
    (DerivedCategory.Plus.ι ⋙ totalRightDerived F).IsRightDerivedFunctor (boundedUnitBig F)
      (HomotopyCategory.Plus.quasiIso A) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (boundedHomotopyMap F)).isRightDerivedFunctor_of_isIso
    (boundedUnitBig F) (fun _ => inferInstance)

/-- **The unbounded right derived functor restricts to the bounded below one**: an isomorphism
`RF⁺ ⋙ ι ≅ ι ⋙ RF` of functors `D⁺(A) ⥤ D(B)`, the uniqueness isomorphism of the right derived
functors of degreewise `F` on `K⁺(A)`. -/
def rightDerivedFunctorPlusCompιIso :
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ totalRightDerived F :=
  Functor.rightDerivedUnique _ _ (boundedUnitPlus F) (boundedUnitBig F)
    (HomotopyCategory.Plus.quasiIso A)

/-- **The isomorphism carries the comparison through `RF⁺` to the comparison through `RF`.** -/
theorem rightDerivedFunctorPlusCompιIso_fac :
    boundedUnitPlus F ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh
        (rightDerivedFunctorPlusCompιIso F).hom = boundedUnitBig F := by
  simp [rightDerivedFunctorPlusCompιIso]

/-- The componentwise form of `rightDerivedFunctorPlusCompιIso_fac`, at a bounded below
complex. -/
theorem rightDerivedFunctorPlusCompιIso_hom_app (K : HomotopyCategory.Plus A) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
        (rightDerivedFunctorPlusCompιIso F).hom.app (DerivedCategory.Plus.Qh.obj K) =
      ((homotopyMap F).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).app
        ((HomotopyCategory.Plus.ι A).obj K) :=
  NatTrans.congr_app (rightDerivedFunctorPlusCompιIso_fac F) K

end Stacks.DerivedFunctor
