module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusHomologyComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusRestriction

/-!
# A base change isomorphism on `D` restricts to `D⁺`, and can be transported along exact functors

Let `g : A ⥤ A'` and `G : S ⥤ S'` be additive functors between abelian categories, and let
`π : A ⥤ S` and `π' : A' ⥤ S'` be exact. Suppose an identification
`Rg ⋙ π' ≅ π ⋙ RG` is given on unbounded derived categories, for some unbounded right derived
functors `Rg` and `RG`. Base change theorems in étale cohomology are often proved in that
form, with K-injective resolutions. This file deduces the corresponding identification on
bounded below derived categories, with the right derived functors `Rg⁺`, `RG⁺` built from
injective resolutions. It then transports the right-hand functor `G` along exact functors
`e : S ⥤ T`, `e' : S' ⥤ T'` that intertwine `G` with an additive `F : T ⥤ T'`.

## Main definitions

* `Stacks.DerivedFunctor.boundedBelowBaseChangeIsoOfUnbounded`: `Rg⁺ ⋙ π' ≅ π ⋙ RG⁺` on `D⁺`.
* `Stacks.DerivedFunctor.boundedBelowBaseChangeIsoOfUnboundedTransport`:
  `Rg⁺ ⋙ (π' ⋙ e') ≅ (π ⋙ e) ⋙ RF⁺` on `D⁺`.

## Implementation notes

The bounded below right derived functors are the restrictions of the unbounded ones,
`CategoryTheory.Functor.boundedDerivedIso`, as soon as the source categories have K-injective
resolutions. Both sides of the bounded below identification lie in `D⁺`, so it is obtained
from the unbounded one by full faithfulness of the inclusion `D⁺ ⥤ D`. The transport is
`Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso`. It needs `e` to carry
injective objects to `F`-acyclic ones, which holds for instance when `e` is an equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.DerivedFunctor

variable {A A' S S' T T' : Type*} [Category A] [Category A'] [Category S] [Category S']
  [Category T] [Category T'] [Abelian A] [Abelian A'] [Abelian S] [Abelian S'] [Abelian T]
  [Abelian T'] [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory S]
  [HasDerivedCategory S'] [HasDerivedCategory T] [HasDerivedCategory T']
  [EnoughInjectives A] [EnoughInjectives S]
  (g : A ⥤ A') [g.Additive] (G : S ⥤ S') [G.Additive]
  (π : A ⥤ S) [π.Additive] [PreservesFiniteLimits π] [PreservesFiniteColimits π]
  (π' : A' ⥤ S') [π'.Additive] [PreservesFiniteLimits π'] [PreservesFiniteColimits π']
  (Rg : DerivedCategory A ⥤ DerivedCategory A')
  (αg : g.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg)
  [Rg.IsRightDerivedFunctor αg (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (RG : DerivedCategory S ⥤ DerivedCategory S')
  (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG)
  [RG.IsRightDerivedFunctor αG (HomotopyCategory.quasiIso S (ComplexShape.up ℤ))]

/-- **An unbounded base change isomorphism restricts to `D⁺`.** From
`Rg ⋙ π' ≅ π ⋙ RG` on unbounded derived categories, for right derived functors `Rg` and `RG`,
there is `Rg⁺ ⋙ π' ≅ π ⋙ RG⁺` on bounded below ones, provided `A` and `S` have K-injective
resolutions. -/
def boundedBelowBaseChangeIsoOfUnbounded
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (q : K ⟶ I),
      I.IsKInjective ∧ QuasiIso q)
    (hS : ∀ K : CochainComplex S ℤ, ∃ (I : CochainComplex S ℤ) (q : K ⟶ I),
      I.IsKInjective ∧ QuasiIso q)
    (e : Rg ⋙ π'.mapDerivedCategory ≅ π.mapDerivedCategory ⋙ RG) :
    g.rightDerivedFunctorPlus ⋙ π'.mapDerivedCategoryPlus ≅
      π.mapDerivedCategoryPlus ⋙ G.rightDerivedFunctorPlus :=
  (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerRight (g.boundedDerivedIso Rg αg hA) π'.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι e ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerLeft π.mapDerivedCategoryPlus (G.boundedDerivedIso RG αG hS).symm ≪≫
      (Functor.associator _ _ _).symm)

variable (F : T ⥤ T') [F.Additive]
  (eS : S ⥤ T) [eS.Additive] [PreservesFiniteLimits eS] [PreservesFiniteColimits eS]
  (eS' : S' ⥤ T') [eS'.Additive] [PreservesFiniteLimits eS'] [PreservesFiniteColimits eS']
  [EnoughInjectives T] [EnoughInjectives S']

/-- **An unbounded base change isomorphism, restricted to `D⁺` and transported along exact
functors.** Let `eS : S ⥤ T` and `eS' : S' ⥤ T'` be exact and intertwine `G` with an additive
`F : T ⥤ T'`, let `eS` carry injective objects to `F`-acyclic ones, and let `S'` have enough
injectives. From
`Rg ⋙ π' ≅ π ⋙ RG` on unbounded derived categories there is
`Rg⁺ ⋙ (π' ⋙ eS') ≅ (π ⋙ eS) ⋙ RF⁺` on bounded below ones. -/
def boundedBelowBaseChangeIsoOfUnboundedTransport
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (q : K ⟶ I),
      I.IsKInjective ∧ QuasiIso q)
    (hS : ∀ K : CochainComplex S ℤ, ∃ (I : CochainComplex S ℤ) (q : K ⟶ I),
      I.IsKInjective ∧ QuasiIso q)
    (e : Rg ⋙ π'.mapDerivedCategory ≅ π.mapDerivedCategory ⋙ RG)
    (eF : eS ⋙ F ≅ G ⋙ eS') (hacyclic : ∀ I : S, Injective I → F.rightAcyclic (eS.obj I)) :
    g.rightDerivedFunctorPlus ⋙ (π' ⋙ eS').mapDerivedCategoryPlus ≅
      (π ⋙ eS).mapDerivedCategoryPlus ⋙ F.rightDerivedFunctorPlus :=
  Functor.isoWhiskerLeft g.rightDerivedFunctorPlus (mapDerivedCategoryPlusCompIso π' eS').symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedBelowBaseChangeIsoOfUnbounded g G π π' Rg αg RG αG hA hS e)
      eS'.mapDerivedCategoryPlus ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft π.mapDerivedCategoryPlus
      (Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso eS eS' G F eF
        hacyclic).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapDerivedCategoryPlusCompIso π eS) F.rightDerivedFunctorPlus

end Stacks.DerivedFunctor
