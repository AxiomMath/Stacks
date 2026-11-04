module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-!
# A total left derived functor is computed by a K-projective complex

Let `A` be an abelian category and let `G` be a functor on the homotopy category of cochain
complexes of `A` admitting a pointwise total left derived functor relative to the
quasi-isomorphisms, with comparison `α : Qh ⋙ LG ⟶ G`. The comparison is invertible at every
K-projective complex: the pointwise right Kan extension computing `LG` at such a complex is a
limit over a category with an initial object, namely the complex itself.

This is the mechanism by which a derived functor is *computed*. For a right exact functor out of
a category with enough projectives it says that the derived functor of a bounded above complex
of projectives is the complex obtained by applying the functor degreewise
(`CochainComplex.isKProjective_of_projective`), which is the classical computation of a left
derived functor by a projective resolution.

## Main definitions

* `Stacks.Homology.isInitialStructuredArrowOfIsKProjective`: a K-projective complex is initial in
  the category of objects of the homotopy category under its own image in the derived category.

## Main results

* `Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective`: the comparison of a total left
  derived functor is invertible at a K-projective complex.
* `Stacks.Homology.isKProjective_single`: a projective object placed in degree zero is a
  K-projective complex.

## Implementation notes

The initiality is exactly `CochainComplex.IsKProjective.Qh_map_bijective`: morphisms out of a
K-projective complex in the homotopy category are the morphisms out of its image in the derived
category, so the structured arrow on the identity is initial. From there
`CategoryTheory.Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor` and
`CategoryTheory.Limits.IsLimit.isIso_π_app_of_isInitial` give the conclusion.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe v u

namespace Stacks.Homology

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]

/-- **A K-projective complex is initial in the category of objects of the homotopy category
under its own image in the derived category**, because `DerivedCategory.Qh` is bijective on
morphisms out of a K-projective complex. -/
def isInitialStructuredArrowOfIsKProjective (P : CochainComplex A ℤ) [P.IsKProjective] :
    IsInitial (StructuredArrow.mk
      (𝟙 (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)))) :=
  let e : ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P ⟶ X) ≃
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ⟶
          DerivedCategory.Qh.obj X) :=
    fun X => Equiv.ofBijective _ (CochainComplex.IsKProjective.Qh_map_bijective P X)
  IsInitial.ofUniqueHom
    (fun g => StructuredArrow.homMk ((e g.right).symm g.hom) (by
      have : DerivedCategory.Qh.map ((e g.right).symm g.hom) = g.hom :=
        (e g.right).apply_symm_apply g.hom
      simpa using this))
    (fun g m => by
      apply StructuredArrow.hom_ext
      refine (e g.right).injective ?_
      have hw : DerivedCategory.Qh.map m.right = g.hom := by
        simpa using StructuredArrow.w m
      exact hw.trans ((e g.right).apply_symm_apply g.hom).symm)

/-- **The comparison of a total left derived functor is invertible at a K-projective complex.**
The pointwise right Kan extension computing the derived functor there is a limit over a category
with an initial object, so its projection at that object is invertible. -/
theorem isIso_leftDerivedCounit_app_of_isKProjective {E : Type*} [Category* E]
    {G : HomotopyCategory A (ComplexShape.up ℤ) ⥤ E}
    (LG : DerivedCategory A ⥤ E) (α : DerivedCategory.Qh ⋙ LG ⟶ G)
    [LG.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [G.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (P : CochainComplex A ℤ) [P.IsKProjective] :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)) := by
  have hptw : (RightExtension.mk LG α).IsPointwiseRightKanExtension :=
    isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor LG α
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  have hat := hptw (DerivedCategory.Qh.obj
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P))
  have h := hat.isIso_π_app_of_isInitial _ (isInitialStructuredArrowOfIsKProjective P)
  simpa using h

omit [HasDerivedCategory A] in
/-- **A projective object placed in degree zero is a K-projective complex**: it is strictly
bounded above and all of its terms are projective, the terms other than the zeroth being zero.
-/
theorem isKProjective_single (X : A) [Projective X] :
    CochainComplex.IsKProjective ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X) := by
  have hproj : ∀ i : ℤ,
      Projective (((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X).X i) := by
    intro i
    by_cases h : i = 0
    · subst h
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).symm
        ‹Projective X›
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X i h).projective
  exact CochainComplex.isKProjective_of_projective _ 0

end Stacks.Homology

end
