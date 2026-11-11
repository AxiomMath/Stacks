module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteDMEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBaseSource
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Deligne–Mumford 2-fibre products of a Deligne–Mumford 1-morphism

Let `f : 𝒳 ⟶ 𝒴` be a Deligne–Mumford 1-morphism of algebraic stacks over a scheme `S`. This
file shows that the 2-fibre product `𝒳 ×_{f, 𝒴, g} 𝒵` is then a Deligne–Mumford algebraic stack
for every Deligne–Mumford `𝒵` over `𝒴`, and in particular for every algebraic space `𝒵` over
`𝒴`, the algebraic space case resting on the fact — proved here — that an algebraic space read
as an algebraic stack is Deligne–Mumford.

Two of the statements are about the Deligne–Mumford *condition* on the 2-fibre product; the two
after them turn that condition into the presentation **Stacks 0CIA** asserts, a scheme with a
surjective étale 1-morphism onto the 2-fibre product. The step from one to the other is the
structure theorem **Stacks 06N3**, whose substantial direction enters here as the hypothesis
`AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM`, named explicitly in the two
presentation statements. That direction is proved, as
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`, in a file this one cannot
import, so the unconditional forms of Stacks 0CIA, which carry its tag, are in
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordFibreProductPresentation`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isDMOver_algebraicSpaceStack`: an algebraic space
  over `S`, read as an algebraic stack over `S`, is Deligne–Mumford over `S`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_algebraicSpaceStack`: the same in the
  absolute sense.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_twoFibreProduct_of_isDM`: the apex of
  the canonical square of a Deligne–Mumford 1-morphism and a 1-morphism out of a
  Deligne–Mumford algebraic stack is Deligne–Mumford.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_twoFibreProduct_algebraicSpaceStack`:
  the case of an algebraic space, which is the one that needs no hypothesis on `𝒵` at all.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_of_isDM`:
  part (1) of Stacks 0CIA — a scheme with a surjective étale 1-morphism onto the 2-fibre
  product — given the substantial direction of Stacks 06N3 as a hypothesis.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_algebraicSpace`:
  part (2) of Stacks 0CIA, the same for an algebraic space, under the same hypothesis.

## Implementation notes

The two lemmas the source cites for the Deligne–Mumford condition, Stacks 050F for the base
change and Stacks 050L for the composition, already carry their keys at
`AlgebraicGeometry.Stack.AlgebraicStacks.isDM_baseChange` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_of_isDM`, and the first two results
below are applications of them.

Passing from the condition to the presentation is the one application of **Stacks 06N3** the
source makes. Only its substantial direction is used here, so the two presentation statements
take `AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM` as a named hypothesis
`hForward` and nothing else. The tagged statements of Stacks 0CIA,
`isDeligneMumfordStack_twoFibreProduct_of_isDM_of_dm` and
`isDeligneMumfordStack_twoFibreProduct_of_isDM_algebraicSpace` (both in the namespace
`AlgebraicGeometry.Stack.AlgebraicStacks`), discharge `hForward` with
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`.

The algebraic space case is the source's own reduction of part (2) of Stacks 0CIA to part (1).
It is obtained at the structure 1-morphism: a 1-morphism out of something representable by an
algebraic space into an algebraic stack is representable by algebraic spaces, and a 1-morphism
representable by algebraic spaces is Deligne–Mumford.

## References

* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space over `S`, read as an algebraic stack over `S`, is Deligne–Mumford over
`S`.** Its structure 1-morphism goes from something representable by an algebraic space into an
algebraic stack, hence is representable by algebraic spaces, and a 1-morphism representable by
algebraic spaces is Deligne–Mumford. -/
theorem isDMOver_algebraicSpaceStack (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hZ : IsAlgebraicSpace B S hS Z) :
    Stack.IsDMOver B S hS (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ) :=
  Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS
    (Stack.structureMorphism.{u, w} B S hS (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ))
    (Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS
      (Stack.schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).property
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)
      (Stack.structureMorphism.{u, w} B S hS
        (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)).hom)

variable (hT : B.Contains (⊤_ Scheme.{u}))

/-- **An algebraic space over `S`, read as an algebraic stack over `S`, is Deligne–Mumford.**
The absolute form of `AlgebraicGeometry.Stack.AlgebraicStacks.isDMOver_algebraicSpaceStack`,
through the equivalence of the absolute and relative conditions. -/
theorem isAbsolutelyDM_algebraicSpaceStack (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hZ : IsAlgebraicSpace B S hS Z) :
    IsAbsolutelyDM B S hS hT (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ) :=
  isAbsolutelyDM_of_isDMOver.{u, w} B S hS hT (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)
    (isDMOver_algebraicSpaceStack.{u, w} B S hS Z hZ)

/-- **A 2-fibre product of a Deligne–Mumford 1-morphism over a Deligne–Mumford algebraic stack
is Deligne–Mumford.** The projection of the canonical square of `(f, g)` to `𝒵` is a base change
of `f`, so it is Deligne–Mumford by Stacks 050F, and a stack Deligne–Mumford over a
Deligne–Mumford stack is Deligne–Mumford by Stacks 050L.

This is the first half of the argument for part (1) of Stacks 0CIA; the half left is the
structure theorem Stacks 06N3, which turns the conclusion into a surjective étale presentation
of the apex by a scheme and is applied in
`AlgebraicGeometry.Stack.AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_of_isDM`. -/
theorem isAbsolutelyDM_twoFibreProduct_of_isDM
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hf : Stack.IsDM B S hS f) (h𝒵 : IsAbsolutelyDM B S hS hT 𝒵) :
    IsAbsolutelyDM B S hS hT (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt :=
  isAbsolutelyDM_of_isDM B S hS hT
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd h𝒵
    (isDM_baseChange B S hS f g hf)

/-- **A 2-fibre product of a Deligne–Mumford 1-morphism over an algebraic space is
Deligne–Mumford.** The source's reduction of part (2) of Stacks 0CIA to part (1): an algebraic
space is Deligne–Mumford when read as an algebraic stack, so no hypothesis beyond
Deligne–Mumfordness of `f` is needed.

As for `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_twoFibreProduct_of_isDM`, what is
left of Stacks 0CIA after this is one application of Stacks 06N3, made in
`AlgebraicGeometry.Stack.AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_algebraicSpace`. -/
theorem isAbsolutelyDM_twoFibreProduct_algebraicSpaceStack
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : Stack.IsDM B S hS f)
    (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
    (g : Stack.algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒴) :
    IsAbsolutelyDM B S hS hT (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt :=
  isAbsolutelyDM_twoFibreProduct_of_isDM.{u, w} B S hS hT f g hf
    (isAbsolutelyDM_algebraicSpaceStack.{u, w} B S hS hT Z hZ)

/-- **Stacks 0CIA, part (1).** Let `f : 𝒳 ⟶ 𝒴` be a Deligne–Mumford 1-morphism of algebraic
stacks. For every Deligne–Mumford algebraic stack `𝒵` over `𝒴` there is a scheme of the site
with a surjective étale 1-morphism onto `𝒳 ×_{f, 𝒴, g} 𝒵`.

The apex is a Deligne–Mumford algebraic stack by
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_twoFibreProduct_of_isDM`, and the
presentation comes from the structure theorem Stacks 06N3, carried here as the hypothesis
`hForward`. The unconditional statement, which carries the tag of Stacks 0CIA, is
`AlgebraicGeometry.Stack.AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_of_isDM_of_dm`. -/
theorem isDeligneMumfordStack_twoFibreProduct_of_isDM
    (hForward : Stack.ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hT)
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hf : Stack.IsDM B S hS f) (h𝒵 : IsAbsolutelyDM B S hS hT 𝒵) :
    Stack.IsDeligneMumfordStack.{u, w} B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.val :=
  hForward _ (isAbsolutelyDM_twoFibreProduct_of_isDM.{u, w} B S hS hT f g hf h𝒵)

/-- **Stacks 0CIA, part (2).** Let `f : 𝒳 ⟶ 𝒴` be a Deligne–Mumford 1-morphism of algebraic
stacks. For every algebraic space `Z` over `𝒴` there is a scheme of the site with a surjective
étale 1-morphism onto `𝒳 ×_{f, 𝒴, g} Z`, with no further hypothesis on `Z`.

This is part (1) applied to the algebraic space read as an algebraic stack, which is
Deligne–Mumford by
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_algebraicSpaceStack`, with the
substantial direction of Stacks 06N3 carried as the hypothesis `hForward`. The unconditional
statement, which carries the tag of Stacks 0CIA, is
`isDeligneMumfordStack_twoFibreProduct_of_isDM_algebraicSpace`. -/
theorem isDeligneMumfordStack_twoFibreProduct_algebraicSpace
    (hForward : Stack.ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hT)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : Stack.IsDM B S hS f)
    (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
    (g : Stack.algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒴) :
    Stack.IsDeligneMumfordStack.{u, w} B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.val :=
  hForward _ (isAbsolutelyDM_twoFibreProduct_algebraicSpaceStack.{u, w} B S hS hT f hf Z hZ g)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
