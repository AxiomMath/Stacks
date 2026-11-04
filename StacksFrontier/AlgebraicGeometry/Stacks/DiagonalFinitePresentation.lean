module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDiagonal

/-!
# Finiteness of the relative diagonal of a 1-morphism of algebraic stacks (Stacks 0CMG)

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S`, with relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`. **Stacks 0CMG**
says that `Δ_f` is locally of finite presentation as soon as `f` is locally of finite type, and
that `Δ_f` is of finite presentation as soon as `f` is in addition quasi-separated.

The source's proof of the first assertion reads `Δ_f` as a 1-morphism *over* `𝒳`, through the
first projection of the 2-fibre product: the composite `Δ_f ≫ pr₁` is the identity of `𝒳`, which
is locally of finite presentation, while `pr₁` is locally of finite type as a base change of `f`
(**Stacks 06FU**). Cancelling local finite presentation against local finite type
(**Stacks 06Q6**) leaves `Δ_f` locally of finite presentation.

Being of finite presentation is being locally of finite presentation, quasi-compact and
quasi-separated (**Stacks 06Q2**, part (2)), and being quasi-separated is by definition
(**Stacks 04YW**) quasi-compactness and quasi-separatedness of the relative diagonal in the
relative sense of Properties of Stacks, Section 04XB. So the second assertion needs three things
beyond the first, all of them read off the hypothesis that `f` is quasi-separated:

* quasi-compactness of `Δ_f` in the sense of Definition 050U, which is part (2) of
  **Stacks 04Z0**;
* Section 04XB quasi-compactness of the second relative diagonal `Δ_{Δ_f}`, which is part (2) of
  **Stacks 04YZ** — the half of it recorded as
  `AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated` — applied to
  `Δ_f`;
* Section 04XB quasi-separatedness of `Δ_{Δ_f}`, which holds unconditionally: `Δ_f` is
  representable by algebraic spaces by part (1) of **Stacks 04XS**, so `Δ_{Δ_f}` is separated by
  part (4) of **Stacks 04YQ**, and a separated morphism of algebraic spaces is quasi-separated by
  **Stacks 03KK**.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_id`: the identity
  1-morphism of an algebraic stack over `S` is locally of finite presentation.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_relativeDiagonal`:
  **Stacks 0CMG**, first assertion.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFinitePresentation_relativeDiagonal`:
  **Stacks 0CMG**, second assertion.

## Implementation notes

The diagonal is the 1-morphism of algebraic stacks
`AlgebraicGeometry.Stack.AlgebraicStacks.relativeDiagonal`, at the canonical model
`AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProduct` of the 2-fibre product, because the
finiteness notions of Stacks 06FS and Stacks 06Q2 are properties of a 1-morphism of algebraic
stacks. No 2-isomorphism appears anywhere: at that model the first projection undoes the
diagonal *on the nose*, which is
`AlgebraicGeometry.Stack.AlgebraicStacks.relativeDiagonal_comp_fst`, so the composite rewritten
in the cancellation step is literally `𝟙 𝒳`. The source phrases the same step through the second
projection; the two projections are interchangeable here, and the first is the one Stacks 06FU
concludes about.

`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_id` is new. Identity facts
in this library are stated for morphisms of algebraic spaces
(`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_id`) or for a 1-morphism whose source is
representable by one (`AlgebraicGeometry.Stack.isRelativelySmooth_id`), and neither covers the
identity of an arbitrary algebraic stack, which is what "`𝒳` is of finite presentation over `𝒳`"
asks for. It is proved at the *existential* smooth-diagram criterion of **Stacks 06FM** and
transported to the universal one that Stacks 06Q2 part (1) is defined over: a smooth presentation
of `𝒳` by an algebraic space, surjective on objects, serves as both vertical 1-morphism of a
diagram over `𝟙 𝒳` whose top horizontal morphism is the identity of that algebraic space. The
2-cell of that diagram is `AlgebraicGeometry.Stack.nonempty_twoIso_associatedMap_id` whiskered
with the presentation and composed with the two unitors.

The three statements below are at the same universe pinning as the surrounding modules, and the
relative diagonal needs none: `AlgebraicGeometry.Stack.AlgebraicStacks.relativeDiagonal` pins the
three levels of `AlgebraicGeometry.Stack.relativeDiagonal` internally.

## References

* [Stacks Project, Tag 03KK](https://stacks.math.columbia.edu/tag/03KK)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 04YZ](https://stacks.math.columbia.edu/tag/04YZ)
* [Stacks Project, Tag 04Z0](https://stacks.math.columbia.edu/tag/04Z0)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06Q6](https://stacks.math.columbia.edu/tag/06Q6)
* [Stacks Project, Tag 0CMG](https://stacks.math.columbia.edu/tag/0CMG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The identity 1-morphism of an algebraic stack over `S` is locally of finite presentation.**
A smooth presentation of `𝒳` by an algebraic space `V`, surjective on objects, is a diagram of
Stacks 06FM over `𝟙 𝒳` whose two vertical 1-morphisms are that presentation and whose top
horizontal morphism is `𝟙 V`, which is locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_id (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    IsLocallyOfFinitePresentation B S hS (𝟙 𝒳) := by
  obtain ⟨V, hV, b, hbsm, hbsu⟩ :=
    Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS
      𝒳.property
  obtain ⟨κ⟩ := Stack.nonempty_twoIso_associatedMap_id B S hS V
  refine (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    𝒳.property 𝒳.property _).2
    ⟨V, V, hV, hV, b, b, 𝟙 V, ⟨?_⟩, hbsm, hbsu, hbsm,
      Space.isLocallyOfFinitePresentation_id B S hS hV⟩
  exact Bicategory.whiskerRightIso κ b ≪≫ Bicategory.leftUnitor b ≪≫
    (Bicategory.rightUnitor b).symm

/-- **Stacks 0CMG, first assertion.** The relative diagonal of a 1-morphism of algebraic stacks
over `S` which is locally of finite type is locally of finite presentation.

The first projection of the 2-fibre product undoes the diagonal, is a base change of `f` and is
therefore locally of finite type by Stacks 06FU, so Stacks 06Q6 cancels it against the identity
of `𝒳`. -/
@[stacks 0CMG "locally of finite presentation"]
theorem isLocallyOfFinitePresentation_relativeDiagonal
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFinitePresentation B S hS (relativeDiagonal B S hS f) := by
  have hfst : IsLocallyOfFiniteType B S hS (twoFibreProductSquare B S hS f f).fst :=
    isLocallyOfFiniteType_baseChange B S hS f f (twoFibreProductSquare B S hS f f)
      (isTwoFibreProduct_twoFibreProductSquare B S hS f f) hf
  refine isLocallyOfFinitePresentation_of_comp B S hS (relativeDiagonal B S hS f)
    (twoFibreProductSquare B S hS f f).fst ?_ hfst
  rw [relativeDiagonal_comp_fst]
  exact isLocallyOfFinitePresentation_id B S hS 𝒳

/-- **Stacks 0CMG, second assertion.** The relative diagonal of a quasi-separated 1-morphism of
algebraic stacks over `S` which is locally of finite type is of finite presentation.

Local finite presentation is the first assertion; quasi-compactness of the diagonal is part (2)
of Stacks 04Z0 read off quasi-separatedness of `f`; and quasi-separatedness of the diagonal is
Section 04XB quasi-compactness of the second diagonal, which is part (2) of Stacks 04YZ at the
same hypothesis, together with Section 04XB quasi-separatedness of the second diagonal, which is
unconditional by part (4) of Stacks 04YQ and Stacks 03KK. -/
@[stacks 0CMG "finite presentation"]
theorem isFinitePresentation_relativeDiagonal
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsLocallyOfFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    IsFinitePresentation B S hS (relativeDiagonal B S hS f) := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal B S hS f).hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  obtain ⟨-, hsep⟩ := Stack.isSeparated_relativeDiagonal_of_isRepresentableByAlgebraicSpaces
    B S hS (relativeDiagonal B S hS f) hrep
  have hqc : Stack.IsQuasiCompactMorphism B S hS (relativeDiagonal B S hS f) :=
    ((Stack.isQuasiSeparated_iff_isQuasiCompactMorphism_diagonals B S hS f).1 hqs).1
  have hqc₂ : Stack.IsQuasiCompact B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (twoFibreProduct B S hS f f).val (relativeDiagonal B S hS f).hom) :=
    (Stack.isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated B S hS
      (relativeDiagonal B S hS f) hrep).2 hqs.2
  exact ⟨isLocallyOfFinitePresentation_relativeDiagonal B S hS f hf, hqc, hqc₂,
    fun U y hy F hF he => Space.isQuasiSeparated_of_isSeparated B S hS (hsep U y hy F hF he)⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
