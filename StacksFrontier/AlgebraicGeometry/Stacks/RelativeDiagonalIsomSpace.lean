module

public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordIsomCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangePoint

/-!
# Base changes of a relative diagonal are isomorphism spaces

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` whose target has faithful structure
functor, for instance the structure morphism `𝒳 ⟶ S` (Stacks 050D). The base change of the relative
diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` along a scheme-valued point `y = (x₁, x₂, α)` over `U` is the
isomorphism space `Isom_𝒳(x₁, x₂)` of Stacks 04YP. This file shows that, for an arbitrary property
of morphisms of presheaves respecting isomorphisms (such as separatedness, quasi-separatedness or
quasi-compactness, which are not étale-local on the source), the structure morphism of the
algebraic space `F` representing the base change, viewed over `S` (Stacks 04SG), has the property
exactly when the structure morphism of `Isom_𝒳(x₁, x₂)` has it.

## Main results

* `AlgebraicGeometry.Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace`: a property
  respecting isomorphisms holds for the algebraic space representing a base change of `Δ_f`
  exactly when it holds for the corresponding isomorphism space.

## References

* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0CL0](https://stacks.math.columbia.edu/tag/0CL0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The base change of a relative diagonal is the isomorphism space of the two components, for
any property respecting isomorphisms.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks whose
target has faithful structure functor, and let `F` be an algebraic space representing the base
change of the relative diagonal `Δ_f` along a scheme-valued point `y = (x₁, x₂, α)` of
`𝒳 ×_𝒴 𝒳` over `U`. For a property `P` of morphisms of presheaves on the big fppf site of `S`
respecting isomorphisms, the structural morphism of `F`, read over `S`, has `P` exactly when the
structural morphism of `Isom_𝒳(x₁, x₂)` over `U`, read over `S` along `U ⟶ S` (Stacks 04SG),
has it. -/
theorem prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) [P.RespectsIso]
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hq : 𝒴.val.val.p.Faithful)
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
    (hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p =
      Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hE : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
        (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p y
        (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom).toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom ↔
      P (OverShriek.relocalizeToYoneda U.hom (isomSpace B S hS 𝒳.val U
          (Functor.sliceValue 𝒳.val.val.p U (Y₁' y) (h1' hy))
          (Functor.sliceValue 𝒳.val.val.p U (Y₂' y) (h2' hy)))) := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  obtain ⟨e⟩ := (nonempty_equivalenceOver_fst_iff 𝒴.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids hy f.hom.hom.w F).mp hE
  have _ := isIso_relVertHomInclusion_of_faithful 𝒴.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids hy f.hom.hom.w
  let iI : F ≅ isomSpace B S hS 𝒳.val U
      (Functor.sliceValue 𝒳.val.val.p U (Y₁' y) (h1' hy))
      (Functor.sliceValue 𝒳.val.val.p U (Y₂' y) (h2' hy)) :=
    (((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso e).symm ≪≫
      asIso (relVertHomInclusion _ _ hy f.hom.hom.w) ≪≫
      Functor.vertHomPresheafIsoIsomPresheafOfFunctors 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids U (Y₁' y) (Y₂' y) (h1' hy) (h2' hy)
  let Q : MorphismProperty (AlgebraicSpaces B S hS) := P.inverseImage (ObjectProperty.ι _)
  have _ : Q.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  refine (prop_algebraicSpaceMap_iff B S hS Q U F hF).trans ?_
  show P (OverShriek.relocalizeToYoneda U.hom F) ↔ _
  rw [← OverShriek.relocalizePresheafFunctor_map_comp_relocalizeToYoneda U.hom iI.hom]
  exact P.cancel_left_of_respectsIso _ _

end AlgebraicGeometry.Stack

end
