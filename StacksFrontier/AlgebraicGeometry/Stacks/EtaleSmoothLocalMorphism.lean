module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# Étale-smooth local properties of Deligne–Mumford morphisms (Stacks 0CIF, 0CIG, 0CIJ, 0CIT)

Let `P` be a property of morphisms of algebraic spaces over `S`. Stacks 0CIF tests `P` on a
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks through diagrams

    U ---h---> V
    |          |
    a          b
    v          v
    𝒳 ---f---> 𝒴

of algebraic spaces over `S` in which `b` is smooth and every comparison 1-morphism from the
diagram's cone to a 2-fibre product of `(b, f)` is **étale** — where the corresponding test of
Stacks 06FM asks for that comparison to be smooth. This file introduces that universal test and
its existential companion, and then the two notions Stacks 0CIG and 0CIT define with it: the
property of a Deligne–Mumford stack morphism induced by an étale-smooth local property of space
morphisms, and unramifiedness of a morphism of algebraic stacks.

## Main definitions

* `AlgebraicGeometry.Stack.IsRelativelyEtale`: étaleness of a representable 1-morphism of
  categories fibred in groupoids, in the relative sense of **Stacks 03YK**.
* `AlgebraicGeometry.Stack.HasPropertyOnEveryEtaleSmoothDiagram`: condition (1) of
  **Stacks 0CIF**.
* `AlgebraicGeometry.Stack.HasPropertyOnSomeEtaleSmoothDiagram`: condition (2) of
  **Stacks 0CIF**.
* `AlgebraicGeometry.Stack.HasEtaleSmoothLocalProperty`: **Stacks 0CIG**, the definition
  itself — a DM 1-morphism `f` of algebraic stacks has the property induced by `P` when
  `IsDM f` holds and `f` passes the universal étale-smooth diagram test at `P`. This is the
  declaration that carries `@[stacks 0CIG]`.
* `AlgebraicGeometry.Stack.IsUnramified`: **Stacks 0CIT**.
* `AlgebraicGeometry.Stack.IsEtale`: **Stacks 0CIL**.

## Main results

* `AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_mono`: **Stacks 0CIJ**, an implication
  between properties of morphisms of algebraic spaces passes to the induced properties of
  1-morphisms of algebraic stacks.

## Implementation notes

Tag 0CIG is carried by one declaration, `AlgebraicGeometry.Stack.HasEtaleSmoothLocalProperty`,
and that declaration is the source's definition: `IsDM f` together with the étale-smooth diagram
test at `P`. The two diagram tests themselves,
`AlgebraicGeometry.Stack.HasPropertyOnEveryEtaleSmoothDiagram` and
`AlgebraicGeometry.Stack.HasPropertyOnSomeEtaleSmoothDiagram`, are conditions (1) and (2) of
Stacks 0CIF and are untagged here: the covering set of 0CIF is its three comparison theorems —
the equivalence of the two tests, the represented case and the representable case — which are
proved in `StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismDiagramTests`,
`…EtaleSmoothLocalMorphismRepresented` and `…EtaleSmoothLocalMorphismRelativeConverse`.

The source defines 0CIG by "the equivalent conditions of Lemma 101.16.1", which is tag 06FM,
the *smooth*-local lemma; its hypothesis is that `P` is smooth local on source-and-target,
which 0CIG does not assume, so the literal cross-reference is ill-posed. The intended lemma is
101.34.1 = Stacks 0CIF, the étale-smooth lemma immediately preceding the definition in the same
section, and Remark 101.34.3 (Stacks 0CIH) settles it: it unwinds the definition using diagrams
with `V → 𝒴` surjective smooth and `U → 𝒳 ×_𝒴 V` surjective étale, which are 0CIF's diagrams.
The definition below takes the 0CIF reading.

`IsRelativelyEtale` is the longhand of Stacks 03YK at étaleness of morphisms of algebraic
spaces, written out rather than stated through
`AlgebraicGeometry.Stack.HasRelativeProperty` for the same reason as
`AlgebraicGeometry.Stack.IsDM`: that definition takes base-change stability and fppf
local-at-target-ness of the property as instance arguments, which for étaleness are not available,
while its body uses neither — so the longhand is the same proposition with no hypothesis on the
property. Compare `AlgebraicGeometry.Stack.IsRelativelySmooth`, which *can* use the short
spelling because both instances are discharged for smoothness.

The diagrams are indexed by algebraic spaces viewed as algebraic stacks,
`AlgebraicGeometry.Stack.algebraicSpaceStack`, and their cone is
`AlgebraicGeometry.Stack.diagramCone` of Stacks 06FM, so the étale-smooth tests differ from the
smooth tests `AlgebraicGeometry.Stack.HasPropertyOnEverySmoothDiagram` and
`…OnSomeSmoothDiagram` in exactly one clause: `IsRelativelyEtale` in place of
`AlgebraicGeometry.Stack.IsRelativelySmooth` on the comparison. The comparison is required over
*every* 2-fibre product of `(b, f)` and *every* induced 1-morphism to it, so the condition does
not depend on a chosen product.

Note that `AlgebraicGeometry.Stack.IsUnramified` (Stacks 0CIT, morphisms of algebraic *stacks*)
and `AlgebraicGeometry.Space.IsUnramified` (Stacks 03ZH part (1), morphisms of algebraic
*spaces*) are different notions; inside this namespace the bare name is the stack one, so the
space one is written out qualified. The same holds for
`AlgebraicGeometry.Stack.IsEtale` (Stacks 0CIL) against `AlgebraicGeometry.Space.IsEtale`
(Stacks 03FR).

## References

* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIG](https://stacks.math.columbia.edu/tag/0CIG)
* [Stacks Project, Tag 0CIJ](https://stacks.math.columbia.edu/tag/0CIJ)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` *is étale* when
it is representable by algebraic spaces and every algebraic space representing its base change
along a scheme-valued point of the target has étale structural morphism, read as a morphism of
algebraic spaces over `S`. This is the notion of Stacks 04XB at
`AlgebraicGeometry.Space.IsEtale`, i.e. the relative property of Stacks 03YK there. -/
abbrev IsRelativelyEtale
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (g : 𝒜 ⟶ ℬ) : Prop :=
  ∃ _hg : IsRepresentableByAlgebraicSpaces B S hS g.hom,
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ ℬ.val.obj)
      (_hy : y ⋙ ℬ.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒜.val.p ℬ.val.p y
          (CatFiberedInGroupoids.homFunctor g))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsEtale B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- **Condition (1) of Stacks 0CIF.** For every 2-commutative square of algebraic spaces over
`f` whose right-hand vertical 1-morphism is smooth and whose every comparison 1-morphism to a
2-fibre product of `(b, f)` is étale, the top horizontal morphism of algebraic spaces has `P`. -/
abbrev HasPropertyOnEveryEtaleSmoothDiagram
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hU : IsAlgebraicSpace B S hS U)
    (hV : IsAlgebraicSpace B S hS V)
    (a : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
    (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b.hom ≅ a.hom ≫ f.hom),
      IsRelativelySmooth B S hS b.hom →
      (∀ (Q : Bicategory.TwoCommSq b.hom f.hom)
        (_hQ : Bicategory.IsTwoFibreProduct Q)
        (k : Bicategory.TwoCommSq.PreHom
          (diagramCone B S hS f.hom a.hom b.hom h η) Q),
          IsRelativelyEtale B S hS k.hom) →
      P (ObjectProperty.homMk h : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩)

/-- **Condition (2) of Stacks 0CIF.** There is a 2-commutative square of algebraic spaces over
`f` whose right-hand vertical 1-morphism is smooth, whose left-hand vertical 1-morphism is
surjective, whose every comparison 1-morphism to a 2-fibre product of `(b, f)` is étale, and
whose top horizontal morphism of algebraic spaces has `P`. -/
abbrev HasPropertyOnSomeEtaleSmoothDiagram
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hU : IsAlgebraicSpace B S hS U)
    (hV : IsAlgebraicSpace B S hS V)
    (a : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
    (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b.hom ≅ a.hom ≫ f.hom),
      IsSurjective B S hS a ∧
      IsRelativelySmooth B S hS b.hom ∧
      (∀ (Q : Bicategory.TwoCommSq b.hom f.hom)
        (_hQ : Bicategory.IsTwoFibreProduct Q)
        (k : Bicategory.TwoCommSq.PreHom
          (diagramCone B S hS f.hom a.hom b.hom h η) Q),
          IsRelativelyEtale B S hS k.hom) ∧
      P (ObjectProperty.homMk h : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩)

/-- **Stacks 0CIG.** The property of Deligne–Mumford morphisms of algebraic stacks induced by an
étale-smooth local property `P` of morphisms of algebraic spaces over `S`: the morphism is
Deligne–Mumford and passes the universal étale-smooth diagram test at `P`.

For an étale-smooth local `P` — `AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget`,
**Stacks 0CFZ** — Stacks 0CIF identifies that test with the existential one. -/
@[stacks 0CIG "the property of a DM morphism of algebraic stacks induced by an etale-smooth \
local property P of morphisms of algebraic spaces: IsDM f together with the universal \
etale-smooth diagram test at P, which is condition (1) of Stacks 0CIF"]
abbrev HasEtaleSmoothLocalProperty
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsDM B S hS f ∧ HasPropertyOnEveryEtaleSmoothDiagram B S hS P f

/-- The universal étale-smooth diagram test is monotone in the property being tested. -/
theorem hasPropertyOnEveryEtaleSmoothDiagram_mono
    {P P' : MorphismProperty (AlgebraicSpaces B S hS)} (hPP' : P ≤ P')
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    (hf : HasPropertyOnEveryEtaleSmoothDiagram B S hS P f) :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS P' f :=
  fun U V hU hV a b h η hb hk => hPP' _ (hf U V hU hV a b h η hb hk)

/-- **Stacks 0CIJ.** An implication between properties of morphisms of algebraic spaces over `S`
also holds for the properties of 1-morphisms of algebraic stacks that Stacks 0CIG induces from
them. No étale-smooth locality hypothesis on either property is needed. -/
@[stacks 0CIJ]
theorem hasEtaleSmoothLocalProperty_mono
    {P P' : MorphismProperty (AlgebraicSpaces B S hS)} (hPP' : P ≤ P')
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    (hf : HasEtaleSmoothLocalProperty B S hS P f) :
    HasEtaleSmoothLocalProperty B S hS P' f :=
  ⟨hf.1, hasPropertyOnEveryEtaleSmoothDiagram_mono B S hS hPP' hf.2⟩

/-- **Stacks 0CIT.** A 1-morphism of algebraic stacks over `S` is *unramified* when it is
Deligne–Mumford and its universal étale-smooth diagram tests are unramified morphisms of
algebraic spaces, in the sense of `AlgebraicGeometry.Space.IsUnramified` (**Stacks 03ZH**,
part (1)). -/
@[stacks 0CIT]
abbrev IsUnramified {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsDM B S hS f ∧
    HasPropertyOnEveryEtaleSmoothDiagram B S hS
      (fun {_ _} (g : _ ⟶ _) => Space.IsUnramified B S hS g.hom :
        MorphismProperty (AlgebraicSpaces B S hS)) f

/-- **Stacks 0CIL.** A 1-morphism of algebraic stacks over `S` is *étale* when it is
Deligne–Mumford and its universal étale-smooth diagram tests are étale morphisms of algebraic
spaces, in the sense of `AlgebraicGeometry.Space.IsEtale` (**Stacks 03FR**). -/
@[stacks 0CIL]
abbrev IsEtale {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsDM B S hS f ∧
    HasPropertyOnEveryEtaleSmoothDiagram B S hS
      (fun {_ _} (g : _ ⟶ _) => Space.IsEtale B S hS g.hom :
        MorphismProperty (AlgebraicSpaces B S hS)) f

end AlgebraicGeometry.Stack

end
