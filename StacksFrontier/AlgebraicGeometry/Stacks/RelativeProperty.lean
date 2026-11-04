module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory

/-!
# Relative properties of a representable 1-morphism of stacks (Stacks 03YK)

Let `P` be a property of morphisms of algebraic spaces over `S` which is stable under base change
and local on the target for the fppf precoverage. A 1-morphism `f : 𝒳 ⟶ 𝒴` of categories fibred in
groupoids over the big fppf site of `S` which is representable by algebraic spaces *has `P`* when,
for every scheme-valued point of `𝒴` and every algebraic space representing the base change of `f`
along it, the structural morphism of that algebraic space has `P`.

## Main definitions

* `AlgebraicGeometry.Stack.HasRelativeProperty`: a 1-morphism representable by algebraic spaces
  has the property `P`.
* `AlgebraicGeometry.Stack.HasRelativePropertyBased`: the same condition for a based functor, so
  that source and target may have different object and morphism universes.
* `AlgebraicGeometry.Stack.RelativeProperty`: the same condition, with no representability witness
  and no hypotheses on `P`.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_iff_based`: `HasRelativeProperty` agrees with
  `HasRelativePropertyBased` on the underlying based functor.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w
universe v₁ w₁ v₂ w₂

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *has the property `P`* when every algebraic space representing
its base change along a scheme-valued point of the target has structural morphism with `P`, read
as a morphism of algebraic spaces over `S`. -/
@[stacks 03YK]
abbrev HasRelativeProperty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (_hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))

/-- The condition of `AlgebraicGeometry.Stack.HasRelativeProperty` for a based functor
`f : 𝒳 ⥤ᵇ 𝒴` between based categories over the big fppf site of `S`, whose source and target may
have different object and morphism universes: every algebraic space representing the base change
of `f` along a scheme-valued point of `𝒴` has structural morphism with `P`, read as a morphism of
algebraic spaces over `S`. -/
abbrev HasRelativePropertyBased
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 : BasedCategory.{v₁, w₁} (BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{v₂, w₂} (BigFppfOver B S hS)}
    (f : 𝒳 ⥤ᵇ 𝒴) (_hf : IsRepresentableByAlgebraicSpaces B S hS f) :
    Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj)
    (_hy : y ⋙ 𝒴.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y f.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))

/-- `HasRelativeProperty` for a 1-morphism `f` is `HasRelativePropertyBased` for its underlying
based functor. -/
theorem hasRelativeProperty_iff_based
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    HasRelativeProperty B S hS P f hf ↔ HasRelativePropertyBased B S hS P f.hom hf :=
  Iff.rfl

/-- The condition of `AlgebraicGeometry.Stack.HasRelativeProperty` on a 1-morphism `f : 𝒳 ⟶ 𝒴`
of categories fibred in groupoids over the big fppf site of `S`, with no representability witness
and no hypotheses on `P`: every algebraic space representing the base change of `f` along a
scheme-valued point of `𝒴` has structural morphism with `P`, read as a morphism of algebraic
spaces over `S`. -/
abbrev RelativeProperty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) :
    Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))

end AlgebraicGeometry.Stack

end
