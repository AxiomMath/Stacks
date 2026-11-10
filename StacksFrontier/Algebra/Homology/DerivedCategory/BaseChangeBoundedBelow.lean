module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons

/-!
# Base change for right derived functors on the bounded below derived categories

Let `A`, `A'`, `B`, `B'` be abelian categories with derived categories, with `A`, `A'`, `B`
having enough injectives, let `α : A ⥤ A'` and `β : B ⥤ B'` be exact, and let `F : A ⥤ B`,
`F' : A' ⥤ B'` be additive, with an isomorphism `α ⋙ F' ≅ F ⋙ β`. If `α` carries every
injective object of `A` to an object right acyclic for `F'`, then

`Dα ⋙ RF' ≅ RF ⋙ Dβ` as functors `D⁺(A) ⥤ D⁺(B')`,

where `Dα`, `Dβ` are the functors on bounded below derived categories induced by the exact
functors `α`, `β`, and `RF`, `RF'` are the right derived functors on `D⁺`.

This is the bounded below counterpart of
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIso`, which assumes instead that `α`
preserves K-injectivity of complexes.

## Main definitions

* `CategoryTheory.Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus`: for an exact
  functor the right derived functor on `D⁺` is the induced functor.
* `Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso`: the base change
  isomorphism `Dα ⋙ RF' ≅ RF ⋙ Dβ`.

## Main results

* `CategoryTheory.Functor.rightAcyclic_of_exact`: every object is right acyclic for an exact
  functor.

## References

* [Stacks, Tag 015E], Leray's acyclicity lemma
* [Stacks, Tag 015M], the composition of right derived functors
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe vA uA vA' uA' vB uB vB' uB' wA wA' wB wB'

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

section Exact

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

/-- For an exact functor the right derived functor on `D⁺` is the induced functor. -/
def rightDerivedFunctorPlusIsoMapDerivedCategoryPlus :
    F.rightDerivedFunctorPlus ≅ F.mapDerivedCategoryPlus :=
  haveI : IsIso F.rightDerivedFunctorPlusUnith :=
    isIso_rightDerivedFunctorPlusUnit_of_preservesHomology F
  haveI : Localization.Lifting (DerivedCategory.Plus.Qh (C := A))
      (HomotopyCategory.Plus.quasiIso A)
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) F.rightDerivedFunctorPlus :=
    ⟨(asIso F.rightDerivedFunctorPlusUnith).symm⟩
  Localization.liftNatIso DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    F.rightDerivedFunctorPlus F.mapDerivedCategoryPlus (Iso.refl _)

/-- Every object is right acyclic for an exact functor. -/
theorem rightAcyclic_of_exact (X : A) : F.rightAcyclic X := by
  have : IsIso F.rightDerivedFunctorPlusUnith :=
    isIso_rightDerivedFunctorPlusUnit_of_preservesHomology F
  have hd := (F.rightDerivedFunctorPlus.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    F.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso A) _
    ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A))).1 inferInstance
  change IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)).app _)
  rw [← F.rightDerivedFunctorPlus.rightDerived_fac_app F.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A)]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (NatIso.isIso_app_of_isIso _ _)
    (NatIso.isIso_app_of_isIso _ _)

end Exact

end CategoryTheory.Functor

namespace Stacks.Cohomology.BoundedBelowComplexes

section BaseChange

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{wA'} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{wB'} B']
  [EnoughInjectives A] [EnoughInjectives A'] [EnoughInjectives B]
  (α : A ⥤ A') [α.Additive] [PreservesFiniteLimits α] [PreservesFiniteColimits α]
  (β : B ⥤ B') [β.Additive] [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  (F : A ⥤ B) [F.Additive] (F' : A' ⥤ B') [F'.Additive]

/-- Base change for right derived functors on the bounded below derived categories: let
`α : A ⥤ A'` and `β : B ⥤ B'` be exact functors of abelian categories, with `A`, `A'`, `B` having
enough injectives, let `F : A ⥤ B` and `F' : A' ⥤ B'` be additive, let `α ⋙ F' ≅ F ⋙ β`, and assume
that `α` carries every injective object of `A` to an object right acyclic for `F'`. Then
`Dα ⋙ RF' ≅ RF ⋙ Dβ` as functors `D⁺(A) ⥤ D⁺(B')`. -/
def derivedBaseChangePlusIso (e : α ⋙ F' ≅ F ⋙ β)
    (hacyclic : ∀ I : A, Injective I → F'.rightAcyclic (α.obj I)) :
    α.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ β.mapDerivedCategoryPlus :=
  Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus α).symm
      F'.rightDerivedFunctorPlus ≪≫
    (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic α F' hacyclic).symm ≪≫
    Functor.rightDerivedFunctorPlusNatIso e ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic F β
      (fun I _ ↦ Functor.rightAcyclic_of_exact β (F.obj I)) ≪≫
    Functor.isoWhiskerLeft F.rightDerivedFunctorPlus
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus β)

end BaseChange

end Stacks.Cohomology.BoundedBelowComplexes

end
