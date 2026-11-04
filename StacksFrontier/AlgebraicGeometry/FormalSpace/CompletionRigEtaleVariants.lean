module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas

/-!
# Variants of the results of `StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale`

The declarations below extend `StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale`.
A primed name `X'` is a variant of the declaration `X` there.

## Main declarations

* `completionOfFiniteTypeModification'`
* `completionOfFiniteTypeModification_obj'`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

variable {B S hS}

section Completion

attribute [local instance] Space.pointTopology

variable (B S hS)

variable {B S hS}

/-- **Stacks 0AR5.** The arrow of the displayed equation: a morphism `f : X' ⟶ X` of algebraic
spaces over `S` which is locally of finite type and an isomorphism over `U` is sent to
`f_{/T} : X'_{/T'} ⟶ X_{/T}`, a rig-étale morphism with locally Noetherian source.

That `f_{/T}` is rig-étale is Stacks 0AR2 applied to `U' ⟶ U`, which is an isomorphism — and
hence étale — because `U'` is the fibre product of `U` with `f`. -/
def completionOfFiniteTypeModification' {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutside B S hS M.obj.hom T) :
    RigEtaleOverCompletion B S hS X T :=
  ⟨Over.mk (Space.completionSheafMap B S hS M.obj.hom T),
    isFormalAlgebraicSpace_completionSheaf_of_isClosed M.property.1.1 _
      (hT.preimage (Space.continuous_pointsMap B S hS M.obj.hom)),
    hnoeth hT hX M.obj.hom M.property.1.1 M.property.2,
    isRigEtale_completionSheafMap M.obj.hom T hX M.property.2
      (Space.isEtale_openComplementRestriction B S hS M.obj.hom T M.property.1.2) hred⟩

/-- The arrow of Stacks 0AR5 sends `f : X' ⟶ X` to `f_{/T} : X'_{/T'} ⟶ X_{/T}`. -/
theorem completionOfFiniteTypeModification_obj' {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutside B S hS M.obj.hom T) :
    (completionOfFiniteTypeModification' T hT hX M hnoeth hred).obj =
      Over.mk (Space.completionSheafMap B S hS M.obj.hom T) :=
  rfl

end Completion

end AlgebraicGeometry.FormalSpace

end
