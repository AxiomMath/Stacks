module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksCore.Tactic.StacksAttribute

/-!
# Exact functors and right derived functors

An exact functor between abelian categories commutes with every construction that computes
cohomology, and this file records the five comparisons that are needed to identify the higher
direct images on a site with the sheafification of the cohomology presheaf (Stacks 03Q8).

* `complexHomologyIso` is the comparison on homological complexes: an additive functor
  preserving homology commutes with the degree-`i` homology functor.
* `rightDerivedIso` turns a natural isomorphism of additive functors into a natural
  isomorphism of their right derived functors; it is `NatTrans.rightDerived` packaged as an
  isomorphism.
* `rightDerivedEvaluationIso` moves an exact functor `T` through a right derived functor,
  objectwise, by evaluating both sides on the same chosen injective resolution.
* `postcompHomotopyIso` and `derivedHomologyIso` are the corresponding statements one level
  up, on the homotopy category and on the unbounded derived category: postcomposition with an
  exact functor commutes with localization, and with taking homology.

All five are deduced from the chosen injective resolution, respectively from the universal
property of the localization, so none of them involves a choice beyond the one Mathlib
already makes.

## Main definitions

* `Stacks.DerivedFunctor.complexHomologyIso`
* `Stacks.DerivedFunctor.rightDerivedIso`
* `Stacks.DerivedFunctor.rightDerivedEvaluationIso`
* `Stacks.DerivedFunctor.postcompHomotopyIso`
* `Stacks.DerivedFunctor.derivedHomologyIso`

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

/-- An additive functor preserving homology commutes with the degree-`i` homology functor on
homological complexes. -/
public def complexHomologyIso
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    (E : A ⥤ D) [E.Additive] [E.PreservesHomology]
    {ι : Type*} (c : ComplexShape ι) (i : ι) :
    E.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c i ≅
      HomologicalComplex.homologyFunctor A c i ⋙ E :=
  Functor.isoWhiskerLeft _ (HomologicalComplex.homologyFunctorIso D c i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Iso.refl (E.mapHomologicalComplex c ⋙
      HomologicalComplex.shortComplexFunctor D c i)) (ShortComplex.homologyFunctor D) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor A c i)
      (ShortComplex.homologyFunctorIso E) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (HomologicalComplex.homologyFunctorIso A c i).symm E

/-- A natural isomorphism of additive functors induces a natural isomorphism of their right
derived functors. -/
public def rightDerivedIso
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasInjectiveResolutions A] {P Q : A ⥤ D} [P.Additive] [Q.Additive]
    (e : P ≅ Q) (p : ℕ) : P.rightDerived p ≅ Q.rightDerived p where
  hom := NatTrans.rightDerived e.hom p
  inv := NatTrans.rightDerived e.inv p
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- An exact functor `T` passes through a right derived functor, objectwise: both sides are
computed on the chosen injective resolution of the same object. -/
public def rightDerivedEvaluationIso
    {A D E : Type*} [Category A] [Category D] [Category E]
    [Abelian A] [Abelian D] [Abelian E] [HasInjectiveResolutions A]
    (P : A ⥤ D) [P.Additive] (T : D ⥤ E) [T.Additive] [T.PreservesHomology]
    (F : A) (p : ℕ) :
    T.obj ((P.rightDerived p).obj F) ≅ ((P ⋙ T).rightDerived p).obj F :=
  T.mapIso ((injectiveResolution F).isoRightDerivedObj P p) ≪≫
    (complexHomologyIso T (.up ℕ) p).symm.app
      ((P.mapHomologicalComplex (.up ℕ)).obj (injectiveResolution F).cocomplex) ≪≫
    ((injectiveResolution F).isoRightDerivedObj (P ⋙ T) p).symm

/-- Postcomposition with an exact functor commutes with passing to the derived category: if
`P ⋙ T ≅ G`, then the localization of `P` followed by `T` is the localization of `G`. -/
public def postcompHomotopyIso
    {A D E : Type*} [Category A] [Category D] [Category E]
    [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E]
    (P : A ⥤ D) [P.Additive] (T : D ⥤ E) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (G : A ⥤ E) [G.Additive] (e : P ⋙ T ≅ G) :
    (P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ T.mapDerivedCategory ≅
      G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ T.mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso e (.up ℤ)) _

/-- An exact functor commutes with taking homology in the unbounded derived category. -/
public def derivedHomologyIso
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D]
    (E : A ⥤ D) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (i : ℤ) :
    E.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D i ≅
      DerivedCategory.homologyFunctor A i ⋙ E := by
  letI : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
      (E.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor D (.up ℤ) i)
      (E.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D i) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors D i)⟩
  letI : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
      (HomologicalComplex.homologyFunctor A (.up ℤ) i ⋙ E)
      (DerivedCategory.homologyFunctor A i ⋙ E) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors A i) E⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _ _ _ _ (complexHomologyIso E (.up ℤ) i)

end Stacks.DerivedFunctor
