module

public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedEtaleDiagram
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IdentityCospan

/-!
# Unramified 1-morphisms pass the étale diagram test (Stacks 0CIY, (1) ⇒ (2))

Let `f : 𝒳 ⟶ 𝒴` be an unramified 1-morphism of algebraic stacks (Stacks 0CIT). **Stacks 0CIY**,
(1) ⇒ (2), says that for every algebraic space `V` over `𝒴` and every étale `U ⟶ V ×_𝒴 𝒳` from an
algebraic space, `U ⟶ V` is unramified. The source's argument: the base change
`V ×_𝒴 𝒳 ⟶ V` is unramified, and `U ⟶ V ×_𝒴 𝒳 ⟶ V` is a diagram of the universal test of
Stacks 0CIF over it whose right-hand vertical 1-morphism is the identity of `V`, hence smooth.

The base change step is `AlgebraicGeometry.Stack.isUnramified_baseChange`, stated with the
substantial direction of Stacks 06N3 as a hypothesis; that direction is now
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`. The 2-fibre product of the
identity of `V` with the base change is the identity-cospan square
(`CategoryTheory.Bicategory.isTwoFibreProduct_idCospan`), whose comparison out of the diagram is
the étale `U ⟶ V ×_𝒴 𝒳` itself.

With (1) ⇒ (2) in hand, **Stacks 0CIV** holds for an arbitrary 2-fibre product square, through
the base-change stability of condition (2); it is
`AlgebraicGeometry.Stack.isUnramified_baseChange_of_isUnramifiedOnEveryEtaleDiagram`, in
`StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedBaseChange`, which imports this file.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleDiagram_of_hasEtaleSmoothLocalProperty`: the
  same for every property induced by Stacks 0CIG from a base-change stable étale-smooth local
  property, in particular for étaleness
  (`AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleDiagram_isEtale_of_isEtale`).
* `AlgebraicGeometry.Stack.isUnramifiedOnEveryEtaleDiagram_of_isUnramified`: **Stacks 0CIY**,
  the implication (1) ⇒ (2).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A property induced by Stacks 0CIG passes the étale diagram test.** Let `P` be étale-smooth
local on the source-and-target and stable under base change, and let `f` have the induced
property. Then every étale diagram of algebraic spaces over `f` has top horizontal morphism in
`P`: the base change of `f` along the diagram's `V ⟶ 𝒴` has the induced property, and the
diagram is one of the universal test over that base change, with the identity of `V` as its
smooth right-hand vertical 1-morphism. -/
theorem hasPropertyOnEveryEtaleDiagram_of_hasEtaleSmoothLocalProperty
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P) [P.IsStableUnderBaseChange]
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    (hf : HasEtaleSmoothLocalProperty B S hS P f) :
    HasPropertyOnEveryEtaleDiagram B S hS P f := by
  intro U V hU hV a b h η hk
  let C := AlgebraicStacks.twoFibreProductSquare B S hS f b
  have hg' : HasEtaleSmoothLocalProperty B S hS P C.snd :=
    hasEtaleSmoothLocalProperty_baseChange.{u, w} B S hS P hP f b hf
  let Cu := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom
  have hCu : Bicategory.IsTwoFibreProduct Cu :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  let k := Bicategory.twoFibreProductPreHom (Bicategory.isTwoFibreProduct_swap hCu)
    (diagramCone B S hS f.hom a.hom b.hom h η)
  let a' : algebraicSpaceStack.{u, w} B S hS U hU ⟶ C.pt := Bicategory.InducedBicategory.mkHom k.hom
  let 𝒱 := algebraicSpaceStack.{u, w} B S hS V hV
  let η' : (associatedMap B S hS h).1 ≫ (𝟙 𝒱 : 𝒱 ⟶ 𝒱).hom ≅ a'.hom ≫ C.snd.hom :=
    Bicategory.rightUnitor _ ≪≫ k.isoFst
  exact hg'.2 U V hU hV a' (𝟙 _) h η'
    (isRelativelySmooth_id B S hS (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV))
    (isRelativelyEtale_preHom_of_one B S hS (Bicategory.isTwoFibreProduct_idCospan C.snd.hom)
      (Bicategory.toIdCospan (diagramCone B S hS C.snd.hom a'.hom _ h η'))
      (hk _ (Bicategory.isTwoFibreProduct_swap hCu) k))

/-- **Stacks 0CIY, the implication (1) ⇒ (2).** An unramified 1-morphism of algebraic stacks is
DM and every étale diagram of algebraic spaces over it has unramified top horizontal morphism. -/
@[stacks 0CIY "the implication (1) => (2)"]
theorem isUnramifiedOnEveryEtaleDiagram_of_isUnramified
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} (hf : IsUnramified B S hS f) :
    IsUnramifiedOnEveryEtaleDiagram.{u, w} B S hS f :=
  let : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  ⟨hf.1, hasPropertyOnEveryEtaleDiagram_of_hasEtaleSmoothLocalProperty B S hS
    (Space.unramifiedMorphismProperty B S hS)
    (Space.isUnramified_isEtaleSmoothLocalOnSourceAndTarget B S hS) hf⟩

/-- **An étale 1-morphism of algebraic stacks passes the étale diagram test**: every étale
diagram of algebraic spaces over it has étale top horizontal morphism. The étale reading of
`AlgebraicGeometry.Stack.isUnramifiedOnEveryEtaleDiagram_of_isUnramified`. -/
theorem hasPropertyOnEveryEtaleDiagram_isEtale_of_isEtale
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} (hf : IsEtale B S hS f) :
    HasPropertyOnEveryEtaleDiagram B S hS
      (fun {_ _} (g : _ ⟶ _) => Space.IsEtale B S hS g.hom) f :=
  hasPropertyOnEveryEtaleDiagram_of_hasEtaleSmoothLocalProperty B S hS
    (Space.etaleMorphisms B S hS) (Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget B S hS) hf

end AlgebraicGeometry.Stack

end
