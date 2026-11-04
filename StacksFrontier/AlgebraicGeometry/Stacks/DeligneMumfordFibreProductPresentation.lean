module

public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordSpecialPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated

/-!
# Étale presentations of 2-fibre products along a DM morphism (Stacks 0CIA)

Let `f : 𝒳 ⟶ 𝒴` be a DM 1-morphism of algebraic stacks. **Stacks 0CIA** says that for every DM
algebraic stack `𝒵` over `𝒴` (part (1)), and in particular for every algebraic space `Z` over
`𝒴` (part (2)), the 2-fibre product `𝒳 ×_𝒴 𝒵` has a surjective étale 1-morphism from a scheme.

`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordSpecialPresentation` proves that the apex is
DM and reduces the statement to the substantial direction of Stacks 06N3, which it takes as a
hypothesis. That direction is now a theorem,
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`, so both parts hold outright.
The site of a scheme always contains the terminal scheme
(`AlgebraicGeometry.BigFppfSite.contains_terminal`), which the absolute DM notion of Stacks 050D
is stated over.

## Main results

* `Stack.AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_of_isDM_of_dm`:
  **Stacks 0CIA**, part (1).
* `Stack.AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_of_isDM_algebraicSpace`:
  **Stacks 0CIA**, part (2).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CIA, part (1).** Let `f : 𝒳 ⟶ 𝒴` be a DM 1-morphism of algebraic stacks. For every
DM algebraic stack `𝒵` and 1-morphism `g : 𝒵 ⟶ 𝒴` there is a scheme with a surjective étale
1-morphism onto `𝒳 ×_{f, 𝒴, g} 𝒵`. -/
@[stacks 0CIA "part (1)"]
theorem isDeligneMumfordStack_twoFibreProduct_of_isDM_of_dm
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hf : Stack.IsDM B S hS f) (h𝒵 : IsAbsolutelyDM B S hS B.contains_terminal 𝒵) :
    Stack.IsDeligneMumfordStack.{u, w} B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.val :=
  isDeligneMumfordStack_twoFibreProduct_of_isDM.{u, w} B S hS B.contains_terminal
    (Stack.existsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal) f g hf h𝒵

/-- **Stacks 0CIA, part (2).** Let `f : 𝒳 ⟶ 𝒴` be a DM 1-morphism of algebraic stacks. For every
algebraic space `Z` and 1-morphism `g : Z ⟶ 𝒴` there is a scheme with a surjective étale
1-morphism onto `𝒳 ×_{f, 𝒴, g} Z`. -/
@[stacks 0CIA "part (2)"]
theorem isDeligneMumfordStack_twoFibreProduct_of_isDM_algebraicSpace
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : Stack.IsDM B S hS f)
    (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
    (g : Stack.algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒴) :
    Stack.IsDeligneMumfordStack.{u, w} B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.val :=
  isDeligneMumfordStack_twoFibreProduct_algebraicSpace.{u, w} B S hS B.contains_terminal
    (Stack.existsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal) f hf Z hZ g

end AlgebraicGeometry.Stack.AlgebraicStacks

end
