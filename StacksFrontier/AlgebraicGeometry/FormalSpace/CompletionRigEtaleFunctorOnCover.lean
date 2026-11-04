module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtaleFunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtaleOnCover

/-!
# The functor of Stacks 0AR5, from the affine data on one covering

This file continues `StacksFrontier/AlgebraicGeometry/FormalSpace/CompletionRigEtaleFunctor.lean`.
There, the functor of **Stacks 0AR5** from the finite-type modifications of `X` outside the open
subspace with point set `Tᶜ` to the rig-étale morphisms with locally Noetherian source over
`X_{/T}`, and the square of **Stacks 0GDQ**, are built from the reduction of Stacks 0AR2 to the
affine case asked at every affine representable étale square. Here the same constructions are
made from the cover-shaped reduction
`AlgebraicGeometry.FormalSpace.ChartSquareReducesToIsEtaleOutsideOnCover` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/CompletionRigEtaleOnCover.lean`, together with the
three locality inputs `hasc`, `hdesc` and `href` of Stacks 0GCZ that its descent to every
square needs.

## Main definitions

* `AlgebraicGeometry.FormalSpace.ChartSquareReducesToIsEtaleOutsideModificationsOnCover`: the
  cover-shaped reduction, asked of every finite-type modification.
* `AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctor_onCover`: the functor
  of Stacks 0AR5.
* `AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctorOnCoverBaseChangeIso`:
  the square of Stacks 0GDQ, conditional on its right vertical arrow.

## References

* [Stacks Project, Tag 0AR2](https://stacks.math.columbia.edu/tag/0AR2)
* [Stacks Project, Tag 0AR5](https://stacks.math.columbia.edu/tag/0AR5)
* [Stacks Project, Tag 0AS2](https://stacks.math.columbia.edu/tag/0AS2)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
* [Stacks Project, Tag 0GDQ](https://stacks.math.columbia.edu/tag/0GDQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

variable {B S hS}

/-- The reduction of **Stacks 0AR2** to the affine case, asked of every finite-type
modification of `X` outside the open subspace with point set `Tᶜ` rather than of a single one.

For each modification this is the algebraization datum of condition (8) of Stacks 0AKG on one
affine étale covering of its completed source, which is the shape of condition (4) of Stacks
0GCZ; see `AlgebraicGeometry.FormalSpace.ChartSquareReducesToIsEtaleOutside`.

This is the cover-shaped variant of
`AlgebraicGeometry.FormalSpace.ChartSquareReducesToIsEtaleOutsideModifications`, built from
`AlgebraicGeometry.FormalSpace.ChartSquareReducesToIsEtaleOutsideOnCover`. -/
abbrev ChartSquareReducesToIsEtaleOutsideModificationsOnCover
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X)) : Prop :=
  ∀ M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ),
    ChartSquareReducesToIsEtaleOutsideOnCover B S hS M.obj.hom T

/-- **Stacks 0AR5, as a functor.** Sending a finite-type modification `f : X' ⟶ X` of `X`
outside `U` to `f_{/T} : X'_{/T'} ⟶ X_{/T}` is a functor to the rig-étale morphisms with
locally Noetherian source over `X_{/T}`. -/
def completionFiniteTypeModificationFunctor_onCover {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideModificationsOnCover T)
    (hasc : ChartPropertyAscendsAlongAffineEtale B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (href : ∀ M : Space.FiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS X Tᶜ),
      HasEtaleRefinementOfSourceCover B S hS
        (Space.completionSheafMap B S hS M.obj.hom T)) :
    Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ) ⥤
      RigEtaleOverCompletion B S hS X T :=
  ObjectProperty.lift _
    (ObjectProperty.ι (Space.IsFiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS X Tᶜ)) ⋙ Space.completionOverFunctor B S hS T)
    fun M => (completionOfFiniteTypeModification_onCover T hT hX M h0AIZ hnoeth (hred M)
      hasc hdesc (href M)).property

/-- On objects the functor of Stacks 0AR5 is the assignment
`AlgebraicGeometry.FormalSpace.completionOfFiniteTypeModification` that Stacks 0AR5
displays. -/
theorem completionFiniteTypeModificationFunctor_onCover_obj {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideModificationsOnCover T)
    (hasc : ChartPropertyAscendsAlongAffineEtale B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (href : ∀ M : Space.FiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS X Tᶜ),
      HasEtaleRefinementOfSourceCover B S hS
        (Space.completionSheafMap B S hS M.obj.hom T))
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ)) :
    (completionFiniteTypeModificationFunctor_onCover T hT hX h0AIZ hnoeth hred hasc hdesc
        href).obj M =
      completionOfFiniteTypeModification_onCover T hT hX M h0AIZ hnoeth (hred M)
        hasc hdesc (href M) :=
  rfl

/-- Composing the functor of Stacks 0AR5 with the inclusion of the right-hand collection into
the sheaves over `X_{/T}` is completion along `T` on the finite-type modifications: the functor
is completion, on objects and on arrows alike. -/
theorem completionFiniteTypeModificationFunctor_onCover_comp_ι
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideModificationsOnCover T)
    (hasc : ChartPropertyAscendsAlongAffineEtale B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (href : ∀ M : Space.FiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS X Tᶜ),
      HasEtaleRefinementOfSourceCover B S hS
        (Space.completionSheafMap B S hS M.obj.hom T)) :
    completionFiniteTypeModificationFunctor_onCover T hT hX h0AIZ hnoeth hred hasc hdesc href ⋙
        ObjectProperty.ι (fun W : Over (Space.completionSheaf B S hS X T) =>
          IsFormalAlgebraicSpace B S hS W.left ∧ IsLocallyNoetherian B S hS W.left ∧
            IsRigEtale B S hS W.hom) =
      ObjectProperty.ι (Space.IsFiniteTypeModification B S hS
          (Space.openSubspaceOfPoints B S hS X Tᶜ)) ⋙ Space.completionOverFunctor B S hS T :=
  rfl

/-! ### Base change of the functor of Stacks 0AR5 -/

/-- **The square of Stacks 0GDQ**, for the categories of Stacks 0AS2 and 0AR5 and conditional
on its right vertical arrow. Base change along `g : X₁ ⟶ X` on finite-type modifications
followed by the functor of Stacks 0AR5 for `X₁` and `T₁ = |g|⁻¹T` agrees with the functor of
Stacks 0AR5 for `X` and `T` followed by any functor restricting base change along
`X_{1, /T_1} ⟶ X_{/T}`.

The commutativity is the one the source's proof gives: the completion functor
`(h : Y ⟶ X) ↦ Y_{/T}` commutes with fibre products, which is
`AlgebraicGeometry.Space.completionBaseChangeIso` and, after restriction to the two
subcategories, `AlgebraicGeometry.Space.restrictedCompletionBaseChangeSquareIso`. -/
def completionFiniteTypeModificationFunctorOnCoverBaseChangeIso
    {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₁ ⟶ X)
    (hX₁sp : IsAlgebraicSpace B S hS X₁) (hXsp : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideModificationsOnCover T)
    (hasc : ChartPropertyAscendsAlongAffineEtale B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (href : ∀ M : Space.FiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS X Tᶜ),
      HasEtaleRefinementOfSourceCover B S hS
        (Space.completionSheafMap B S hS M.obj.hom T))
    (hX₁ : Space.IsLocallyNoetherian B S hS X₁)
    (h0AIZ₁ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X₁
      (Space.pointsMap B S hS X₁ g ⁻¹' T))
    (hnoeth₁ : IsLocallyNoetherianCompletionSheaf B S hS X₁
      (Space.pointsMap B S hS X₁ g ⁻¹' T))
    (hred₁ : ChartSquareReducesToIsEtaleOutsideModificationsOnCover
      (Space.pointsMap B S hS X₁ g ⁻¹' T))
    (href₁ : ∀ M : Space.FiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS X₁ (Space.pointsMap B S hS X₁ g ⁻¹' T)ᶜ),
      HasEtaleRefinementOfSourceCover B S hS
        (Space.completionSheafMap B S hS M.obj.hom (Space.pointsMap B S hS X₁ g ⁻¹' T)))
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
        completionFiniteTypeModificationFunctor_onCover (Space.pointsMap B S hS X₁ g ⁻¹' T)
          (hT.preimage (Space.continuous_pointsMap B S hS g)) hX₁ h0AIZ₁ hnoeth₁ hred₁
          hasc hdesc href₁ ≅
      completionFiniteTypeModificationFunctor_onCover T hT hX h0AIZ hnoeth hred hasc hdesc
          href ⋙ D :=
  Space.restrictedCompletionBaseChangeSquareIso B S hS g T
    (Space.finiteTypeBaseChangePointsFunctorCompιIso hX₁sp hXsp g T)
    (eqToIso (completionFiniteTypeModificationFunctor_onCover_comp_ι T hT hX h0AIZ hnoeth hred
      hasc hdesc href))
    (eqToIso (completionFiniteTypeModificationFunctor_onCover_comp_ι
      (Space.pointsMap B S hS X₁ g ⁻¹' T)
      (hT.preimage (Space.continuous_pointsMap B S hS g)) hX₁ h0AIZ₁ hnoeth₁ hred₁
      hasc hdesc href₁))
    hD

end AlgebraicGeometry.FormalSpace

end
