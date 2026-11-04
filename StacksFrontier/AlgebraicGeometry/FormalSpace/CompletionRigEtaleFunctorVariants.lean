module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtaleFunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtaleVariants

/-!
# Variants of the results of `StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtaleFunctor`

The declarations below extend `StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtaleFunctor`
and are kept in a module of their own so that that module stays unchanged. A primed name `X'` is a
variant of the declaration `X` there.

## Main declarations

* `completionFiniteTypeModificationFunctor'`
* `completionFiniteTypeModificationFunctor_obj'`
* `completionFiniteTypeModificationFunctor_comp_ι'`
* `completionFiniteTypeModificationFunctorBaseChangeIso'`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

variable {B S hS}

/-- **Stacks 0AR5, as a functor.** Sending a finite-type modification `f : X' ⟶ X` of `X`
outside `U` to `f_{/T} : X'_{/T'} ⟶ X_{/T}` is a functor to the rig-étale morphisms with
locally Noetherian source over `X_{/T}`. -/
def completionFiniteTypeModificationFunctor' {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideModifications T) :
    Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ) ⥤
      RigEtaleOverCompletion B S hS X T :=
  ObjectProperty.lift _
    (ObjectProperty.ι (Space.IsFiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS X Tᶜ)) ⋙ Space.completionOverFunctor B S hS T)
    fun M => (completionOfFiniteTypeModification' T hT hX M hnoeth (hred M)).property

/-- On objects the functor of Stacks 0AR5 is the assignment
`AlgebraicGeometry.FormalSpace.completionOfFiniteTypeModification` that Stacks 0AR5
displays. -/
theorem completionFiniteTypeModificationFunctor_obj' {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideModifications T)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ)) :
    (completionFiniteTypeModificationFunctor' T hT hX hnoeth hred).obj M =
      completionOfFiniteTypeModification' T hT hX M hnoeth (hred M) :=
  rfl

/-- Composing the functor of Stacks 0AR5 with the inclusion of the right-hand collection into
the sheaves over `X_{/T}` is completion along `T` on the finite-type modifications: the functor
is completion, on objects and on arrows alike. -/
theorem completionFiniteTypeModificationFunctor_comp_ι'
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideModifications T) :
    completionFiniteTypeModificationFunctor' T hT hX hnoeth hred ⋙
        ObjectProperty.ι (fun W : Over (Space.completionSheaf B S hS X T) =>
          IsFormalAlgebraicSpace B S hS W.left ∧ IsLocallyNoetherian B S hS W.left ∧
            IsRigEtale B S hS W.hom) =
      ObjectProperty.ι (Space.IsFiniteTypeModification B S hS
          (Space.openSubspaceOfPoints B S hS X Tᶜ)) ⋙ Space.completionOverFunctor B S hS T :=
  rfl

/-- **The square of Stacks 0GDQ**, for the categories of Stacks 0AS2 and 0AR5 and conditional
on its right vertical arrow. Base change along `g : X₁ ⟶ X` on finite-type modifications
followed by the functor of Stacks 0AR5 for `X₁` and `T₁ = |g|⁻¹T` agrees with the functor of
Stacks 0AR5 for `X` and `T` followed by any functor restricting base change along
`X_{1, /T_1} ⟶ X_{/T}`.

The commutativity is the one the source's proof gives: the completion functor
`(h : Y ⟶ X) ↦ Y_{/T}` commutes with fibre products, which is
`AlgebraicGeometry.Space.completionBaseChangeIso` and, after restriction to the two
subcategories, `AlgebraicGeometry.Space.restrictedCompletionBaseChangeSquareIso`. -/
def completionFiniteTypeModificationFunctorBaseChangeIso'
    {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₁ ⟶ X)
    (hX₁sp : IsAlgebraicSpace B S hS X₁) (hXsp : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideModifications T)
    (hX₁ : Space.IsLocallyNoetherian B S hS X₁)
    (hnoeth₁ : IsLocallyNoetherianCompletionSheaf B S hS X₁
      (Space.pointsMap B S hS X₁ g ⁻¹' T))
    (hred₁ : ChartSquareReducesToIsEtaleOutsideModifications
      (Space.pointsMap B S hS X₁ g ⁻¹' T))
    {D : RigEtaleOverCompletion B S hS X T ⥤
      RigEtaleOverCompletion B S hS X₁ (Space.pointsMap B S hS X₁ g ⁻¹' T)}
    (hD : D ⋙ ObjectProperty.ι (fun W : Over (Space.completionSheaf B S hS X₁
            (Space.pointsMap B S hS X₁ g ⁻¹' T)) =>
          IsFormalAlgebraicSpace B S hS W.left ∧ IsLocallyNoetherian B S hS W.left ∧
            IsRigEtale B S hS W.hom) ≅
      ObjectProperty.ι (fun W : Over (Space.completionSheaf B S hS X T) =>
          IsFormalAlgebraicSpace B S hS W.left ∧ IsLocallyNoetherian B S hS W.left ∧
            IsRigEtale B S hS W.hom) ⋙
        Over.pullback (Space.completionSheafMap B S hS g T)) :
    Space.finiteTypeBaseChangePointsFunctor hX₁sp hXsp g T ⋙
        completionFiniteTypeModificationFunctor' (Space.pointsMap B S hS X₁ g ⁻¹' T)
          (hT.preimage (Space.continuous_pointsMap B S hS g)) hX₁ hnoeth₁ hred₁ ≅
      completionFiniteTypeModificationFunctor' T hT hX hnoeth hred ⋙ D :=
  Space.restrictedCompletionBaseChangeSquareIso B S hS g T
    (Space.finiteTypeBaseChangePointsFunctorCompιIso hX₁sp hXsp g T)
    (eqToIso (completionFiniteTypeModificationFunctor_comp_ι' T hT hX hnoeth hred))
    (eqToIso (completionFiniteTypeModificationFunctor_comp_ι'
      (Space.pointsMap B S hS X₁ g ⁻¹' T)
      (hT.preimage (Space.continuous_pointsMap B S hS g)) hX₁ hnoeth₁ hred₁))
    hD

end AlgebraicGeometry.FormalSpace

end
