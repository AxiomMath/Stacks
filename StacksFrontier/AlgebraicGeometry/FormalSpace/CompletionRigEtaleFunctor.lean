module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionOverFunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale

/-!
# The arrow of Stacks 0AR5 is a functor

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a locally Noetherian algebraic
space over `S` and let `T ⊆ |X|` be a closed subset, with `U ⊂ X` the open subspace with
`|U| = |X| ∖ T`. **Stacks 0AR5** displays an assignment from the morphisms `f : X' ⟶ X` of
algebraic spaces which are locally of finite type and an isomorphism over `U` — the finite-type
modifications of Stacks 0AS2 — to the rig-étale morphisms with locally Noetherian source over
`X_{/T}`, sending `f` to `f_{/T}`.

`AlgebraicGeometry.FormalSpace.completionOfFiniteTypeModification` is that assignment on
objects. It is in fact a functor: a morphism `a : M ⟶ N` of finite-type modifications is a
morphism over `X`, and completion along `T` is functorial on the presheaves over `X`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctor`: the functor of Stacks
  0AR5 from the category of finite-type modifications of `X` outside `U` to the category of
  rig-étale morphisms with locally Noetherian source over `X_{/T}`, with its three target
  conditions as hypotheses. The same functor with no hypotheses beyond the source's is
  `AlgebraicGeometry.FormalSpace.completionModificationFunctor`, which carries the Stacks 0AR5
  attribute.

## Main results

* `AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctor_obj`: on objects the
  functor is `AlgebraicGeometry.FormalSpace.completionOfFiniteTypeModification`, so it is the
  assignment Stacks 0AR5 displays and not some other one.
* `AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctor_comp_ι`: composed with
  the inclusion of the right-hand collection it is completion along `T`, on arrows as well as
  on objects.
* `AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctorBaseChangeIso`: the
  square of Stacks 0GDQ for these categories, with its right vertical arrow given as data:
  base change on finite-type modifications followed by the functor for `X₁` and `T₁` agrees
  with the functor for `X` and `T` followed by any functor restricting base change along
  `X_{1, /T_1} ⟶ X_{/T}`.

## What is assumed

Exactly the three hypotheses of
`AlgebraicGeometry.FormalSpace.completionOfFiniteTypeModification`, two of them unchanged and
the third made uniform in the object:

* `AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpaceCompletionSheaf`, that is Stacks 0AIZ
  for the algebraic spaces over `X`, proved as
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpaceCompletionSheaf`;
* `AlgebraicGeometry.FormalSpace.IsLocallyNoetherianCompletionSheaf`, the locally Noetherian
  half of Stacks 0AQ1 in the form Stacks 0AR5 uses it, proved as
  `AlgebraicGeometry.FormalSpace.isLocallyNoetherianCompletionSheaf`;
* the reduction of Stacks 0AR2 to the affine case, which
  `AlgebraicGeometry.FormalSpace.completionOfFiniteTypeModification` carries for the one object
  it is applied to and which is carried here for every object of the source category, as
  `AlgebraicGeometry.FormalSpace.ChartSquareReducesToIsEtaleOutsideModifications`. Stacks 0AR2
  itself is proved without it, as
  `AlgebraicGeometry.FormalSpace.isRigEtale_completionSheafMap_of_isEtale`.

The first two are already stated uniformly in the object — they quantify over all algebraic
spaces over `X` — so nothing about them changes here. No hypothesis is added: what makes the
assignment a functor is the arrow map, which is
`AlgebraicGeometry.Space.completionOverFunctor` and carries no hypotheses at all.

## The right vertical arrow of Stacks 0GDQ

The square of Stacks 0GDQ is stated here with its right vertical arrow, base change along
`X_{1, /T_1} ⟶ X_{/T}` on the rig-étale morphisms with locally Noetherian source, as data:
no such functor is constructed for the categories of this file. Base change of the three
defining conditions needs the base change of a rig-étale morphism to be rig-étale (Stacks 0GD1),
together with a formal algebraic space and a locally Noetherian condition on the fibre product.
These are proved, and the right vertical arrow constructed, for the functor with no hypotheses
`AlgebraicGeometry.FormalSpace.completionModificationFunctor`: the square of Stacks 0GDQ for it
is `AlgebraicGeometry.FormalSpace.completionModificationFunctorBaseChangeIso`.

## References

* [Stacks Project, Tag 0GDQ](https://stacks.math.columbia.edu/tag/0GDQ)
* [Stacks Project, Tag 0GD1](https://stacks.math.columbia.edu/tag/0GD1)
* [Stacks Project, Tag 0AR5](https://stacks.math.columbia.edu/tag/0AR5)
* [Stacks Project, Tag 0AS2](https://stacks.math.columbia.edu/tag/0AS2)
* [Stacks Project, Tag 0AIZ](https://stacks.math.columbia.edu/tag/0AIZ)
* [Stacks Project, Tag 0AQ1](https://stacks.math.columbia.edu/tag/0AQ1)
* [Stacks Project, Tag 0AR2](https://stacks.math.columbia.edu/tag/0AR2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

variable {B S hS}

/-- The reduction of **Stacks 0AR2** to the affine case, asked of every finite-type
modification of `X` outside the open subspace with point set `Tᶜ` rather than of a single
one. -/
abbrev ChartSquareReducesToIsEtaleOutsideModifications
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X)) : Prop :=
  ∀ M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ),
    ChartSquareReducesToIsEtaleOutside B S hS M.obj.hom T

/-- The functor of Stacks 0AR5 with its three target conditions supplied as hypotheses: sending
a finite-type modification `f : X' ⟶ X` of `X` outside `U` to `f_{/T} : X'_{/T'} ⟶ X_{/T}` is a
functor to the rig-étale morphisms with locally Noetherian source over `X_{/T}`.

The three hypotheses are proved in this library, and Stacks 0AR5 itself is
`AlgebraicGeometry.FormalSpace.completionModificationFunctor`, which takes none of them; the two
functors are equal by
`completionFiniteTypeModificationFunctor_eq_completionModificationFunctor`. -/
def completionFiniteTypeModificationFunctor {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideModifications T) :
    Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ) ⥤
      RigEtaleOverCompletion B S hS X T :=
  ObjectProperty.lift _
    (ObjectProperty.ι (Space.IsFiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS X Tᶜ)) ⋙ Space.completionOverFunctor B S hS T)
    fun M => (completionOfFiniteTypeModification T hT hX M h0AIZ hnoeth (hred M)).property

/-- On objects the functor of Stacks 0AR5 is the assignment
`AlgebraicGeometry.FormalSpace.completionOfFiniteTypeModification` that Stacks 0AR5
displays. -/
theorem completionFiniteTypeModificationFunctor_obj {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideModifications T)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ)) :
    (completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred).obj M =
      completionOfFiniteTypeModification T hT hX M h0AIZ hnoeth (hred M) :=
  rfl

/-- Composing the functor of Stacks 0AR5 with the inclusion of the right-hand collection into
the sheaves over `X_{/T}` is completion along `T` on the finite-type modifications: the functor
is completion, on objects and on arrows alike. -/
theorem completionFiniteTypeModificationFunctor_comp_ι
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideModifications T) :
    completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred ⋙
        ObjectProperty.ι (fun W : Over (Space.completionSheaf B S hS X T) =>
          IsFormalAlgebraicSpace B S hS W.left ∧ IsLocallyNoetherian B S hS W.left ∧
            IsRigEtale B S hS W.hom) =
      ObjectProperty.ι (Space.IsFiniteTypeModification B S hS
          (Space.openSubspaceOfPoints B S hS X Tᶜ)) ⋙ Space.completionOverFunctor B S hS T :=
  rfl

/-! ### Base change of the functor of Stacks 0AR5 -/

/-- The square of Stacks 0GDQ for the functor with hypotheses
`AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctor`, with its right vertical
arrow given as data `D`. Stacks 0GDQ itself is
`AlgebraicGeometry.FormalSpace.completionModificationFunctorBaseChangeIso`. Base change along
`g : X₁ ⟶ X` on finite-type modifications followed by the functor of Stacks 0AR5 for `X₁` and
`T₁ = |g|⁻¹T` agrees with the functor of Stacks 0AR5 for `X` and `T` followed by any functor
restricting base change along `X_{1, /T_1} ⟶ X_{/T}`.

The commutativity is the one the source's proof gives: the completion functor
`(h : Y ⟶ X) ↦ Y_{/T}` commutes with fibre products, which is
`AlgebraicGeometry.Space.completionBaseChangeIso` and, after restriction to the two
subcategories, `AlgebraicGeometry.Space.restrictedCompletionBaseChangeSquareIso`. -/
def completionFiniteTypeModificationFunctorBaseChangeIso
    {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₁ ⟶ X)
    (hX₁sp : IsAlgebraicSpace B S hS X₁) (hXsp : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideModifications T)
    (hX₁ : Space.IsLocallyNoetherian B S hS X₁)
    (h0AIZ₁ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X₁
      (Space.pointsMap B S hS X₁ g ⁻¹' T))
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
        completionFiniteTypeModificationFunctor (Space.pointsMap B S hS X₁ g ⁻¹' T)
          (hT.preimage (Space.continuous_pointsMap B S hS g)) hX₁ h0AIZ₁ hnoeth₁ hred₁ ≅
      completionFiniteTypeModificationFunctor T hT hX h0AIZ hnoeth hred ⋙ D :=
  Space.restrictedCompletionBaseChangeSquareIso B S hS g T
    (Space.finiteTypeBaseChangePointsFunctorCompιIso hX₁sp hXsp g T)
    (eqToIso (completionFiniteTypeModificationFunctor_comp_ι T hT hX h0AIZ hnoeth hred))
    (eqToIso (completionFiniteTypeModificationFunctor_comp_ι
      (Space.pointsMap B S hS X₁ g ⁻¹' T)
      (hT.preimage (Space.continuous_pointsMap B S hS g)) hX₁ h0AIZ₁ hnoeth₁ hred₁))
    hD

end AlgebraicGeometry.FormalSpace

end
