module

public import StacksFrontier.CategoryTheory.Abelian.DerivedFunctorDuality
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Derived functors across an anti-equivalence, in the derived category

This file complements `StacksFrontier/CategoryTheory/Abelian/DerivedFunctorDuality.lean` on the side
of derived categories.

* The identification `CategoryTheory.Equivalence.leftDerivedCompIsoOfAntiEquivalence` of
  `L_n F' ∘ e` with `δ ∘ (R^n F)ᵒᵖ` is restated with the library's `ℤ`-indexed
  `CategoryTheory.Functor.rightDerivedPlus` in place of Mathlib's `ℕ`-indexed
  `CategoryTheory.Functor.rightDerived`, through `Stacks.DerivedIndexing.rightDerivedIso`.
* A left derived functor on bounded above complexes is packaged through the opposite category.
  For an additive functor `F' : C' ⥤ A'` out of an abelian category with enough projectives,
  `C'ᵒᵖ` has enough injectives, so `F'.op : C'ᵒᵖ ⥤ A'ᵒᵖ` has a right derived functor
  `F'.op.rightDerivedFunctorPlus : D⁺(C'ᵒᵖ) ⥤ D⁺(A'ᵒᵖ)`. Since the opposite of a bounded above
  complex of `C'` is a bounded below complex of `C'ᵒᵖ`, `D⁺(C'ᵒᵖ)` is `D⁻(C')ᵒᵖ`, and this functor
  is the opposite of the left derived functor `LF' : D⁻(C') ⥤ D⁻(A')`. Mathlib has neither
  `D⁻` nor that identification, so the functor is recorded on `D⁺(C'ᵒᵖ)`, as
  `CategoryTheory.Functor.leftDerivedFunctorMinusOfOp`, together with the computation of its
  cohomology on an object placed in degree `0`: it is the opposite of `L_n F'`.

## Main definitions

* `CategoryTheory.Equivalence.leftDerivedCompRightDerivedPlusIsoOfAntiEquivalence`:
  `e.functor ⋙ F'.leftDerived n ≅ (F.rightDerivedPlus n).op ⋙ δ`.
* `CategoryTheory.Functor.leftDerivedFunctorMinusOfOp`: `F'.op.rightDerivedFunctorPlus`.
* `CategoryTheory.Functor.leftDerivedFunctorMinusOfOpHomologyIso`: its `n`-th cohomology on an
  object in degree `0` is `(F'.leftDerived n).op`.

## References

* [Stacks: Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

namespace Equivalence

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
  {A : Type*} [Category* A] [Abelian A] {A' : Type*} [Category* A'] [Abelian A']
  {C' : Type*} [Category* C'] [Abelian C'] [HasProjectiveResolutions C']
  [HasDerivedCategory C] [HasDerivedCategory A]

/-- `CategoryTheory.Equivalence.leftDerivedCompIsoOfAntiEquivalence` with the `ℤ`-indexed right
derived functors `CategoryTheory.Functor.rightDerivedPlus` of the library:
`e.functor ⋙ F'.leftDerived n ≅ (F.rightDerivedPlus n).op ⋙ δ`. -/
def leftDerivedCompRightDerivedPlusIsoOfAntiEquivalence (e : Cᵒᵖ ≌ C') (F : C ⥤ A)
    [F.Additive] (F' : C' ⥤ A') [F'.Additive] (δ : Aᵒᵖ ⥤ A') [δ.Additive]
    [δ.PreservesHomology] (α : e.functor ⋙ F' ≅ F.op ⋙ δ) (n : ℕ) :
    e.functor ⋙ F'.leftDerived n ≅ (F.rightDerivedPlus (n : ℤ)).op ⋙ δ :=
  e.leftDerivedCompIsoOfAntiEquivalence F F' δ α n ≪≫
    Functor.isoWhiskerRight (NatIso.op (Stacks.DerivedIndexing.rightDerivedIso F n)).symm δ

end Equivalence

namespace Functor

variable {C' : Type*} [Category* C'] [Abelian C'] [EnoughProjectives C']
  {A' : Type*} [Category* A'] [Abelian A'] [HasDerivedCategory C'ᵒᵖ] [HasDerivedCategory A'ᵒᵖ]
  (F' : C' ⥤ A') [F'.Additive]

/-- **The left derived functor of `F'` on bounded above complexes, through the opposite
category.** It is the right derived functor `D⁺(C'ᵒᵖ) ⥤ D⁺(A'ᵒᵖ)` of `F'.op`; as
`D⁺(C'ᵒᵖ)` is `D⁻(C')ᵒᵖ`, this is the opposite of `LF' : D⁻(C') ⥤ D⁻(A')`. -/
abbrev leftDerivedFunctorMinusOfOp :
    DerivedCategory.Plus C'ᵒᵖ ⥤ DerivedCategory.Plus A'ᵒᵖ :=
  F'.op.rightDerivedFunctorPlus

/-- The `n`-th cohomology of `CategoryTheory.Functor.leftDerivedFunctorMinusOfOp` on an object
placed in degree `0` is the opposite of the `n`-th left derived functor `L_n F'`. -/
def leftDerivedFunctorMinusOfOpHomologyIso (n : ℕ) :
    DerivedCategory.Plus.singleFunctor C'ᵒᵖ 0 ⋙ F'.leftDerivedFunctorMinusOfOp ⋙
        DerivedCategory.Plus.homologyFunctor A'ᵒᵖ (n : ℤ) ≅ (F'.leftDerived n).op :=
  (Stacks.DerivedIndexing.rightDerivedIso F'.op n).symm ≪≫ F'.rightDerivedOpIso n

end Functor

end CategoryTheory
