module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial

/-!
# An open subspace of an algebraic space is an open substack of its stack

Let `F` be an algebraic space over `S` and let `i : V ⟶ F` be an open immersion of algebraic
spaces. The 1-morphism `S_V ⟶ S_F` of **Stacks 0458** between the algebraic stacks of
**Stacks 03YS** that `V` and `F` determine is then an open immersion of algebraic stacks
(**Stacks 04YL**, part (1)), and its essential image is an
`AlgebraicGeometry.Stack.OpenSubstack` of `S_F`.

## Main results

* `AlgebraicGeometry.Stack.isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion`: the
  1-morphism of algebraic stacks attached to an open immersion of algebraic spaces is an open
  immersion.
* `AlgebraicGeometry.Stack.exists_openSubstack_algebraicSpaceStack_of_isOpenImmersion`: the open
  substack of `S_F` it cuts out.

## Why this is here

Both halves are mirrors at open immersions of the smoothness statements
`AlgebraicGeometry.Stack.isSmooth_algebraicSpaceStackMap_iff` and
`AlgebraicGeometry.Stack.isSmooth_algebraicSpaceStackMap_of_isOpenImmersion` of
`StacksFrontier/AlgebraicGeometry/Stacks/OpenImageSubstack.lean`, but they cannot be proved the same
way: that route is the smooth-diagram test of **Stacks 06FM**, which asks of the property that it
be smooth local on source *and* target, and being an open immersion is not local on the source.
What replaces it is the direct relative test of **Stacks 03YK**,
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`, whose induced morphism of
representing presheaves at the identity comparisons is the morphism of algebraic spaces itself by
`AlgebraicGeometry.Stack.representingMap_associatedMap`. The locality hypothesis it carries is the
fppf form of **Stacks 041X**, `AlgebraicGeometry.Space.openImmersion_isLocalAtTarget_fppf`, which
is in the library.

This is the step that distinguishes **Stacks 06ME** and **Stacks 06N2** from **Stacks 06M3**. The
locus of Stacks 06M3 is an open substack of a general algebraic stack, and reading an invariant
open subspace of a smooth chart as one is where the source cites **Stacks 0505**; the chart
construction of `StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyLocus` does it through the
points of the stack instead, with no appeal to that tag. In Stacks 06ME and
Stacks 06N2 the 1-morphism whose locus is wanted has an algebraic *space* for its source, so the
locus is an open subspace of that space, descent along the smooth chart happens among algebraic
spaces — **Stacks 04P1**,
`AlgebraicGeometry.Space.existsUnique_openSubspace_of_fpqcCovering` — and the passage to an open
substack is the unconditional construction below rather than Stacks 0505.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03YS](https://stacks.math.columbia.edu/tag/03YS)
* [Stacks Project, Tag 041X](https://stacks.math.columbia.edu/tag/041X)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 04P1](https://stacks.math.columbia.edu/tag/04P1)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 0505](https://stacks.math.columbia.edu/tag/0505)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06M3](https://stacks.math.columbia.edu/tag/06M3)
* [Stacks Project, Tag 06ME](https://stacks.math.columbia.edu/tag/06ME)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The 1-morphism of algebraic stacks attached to an open immersion of algebraic spaces is an
open immersion.** Representability by algebraic spaces holds because both source and target are
represented by algebraic spaces, and the relative test of **Stacks 03YK** at
`AlgebraicGeometry.Space.openImmersionProperty` reduces to the morphism of algebraic spaces
itself.

This is the mirror at open immersions of
`AlgebraicGeometry.Stack.isSmooth_algebraicSpaceStackMap_iff`; it cannot go through the
smooth-diagram test, which needs locality on the source. -/
theorem isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion
    {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) {g : T ⟶ G}
    (hg : Space.IsOpenImmersion B S hS g) :
    AlgebraicStacks.IsOpenImmersion B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hT hG g) := by
  have : (Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.openImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  have hrep : IsRepresentableByAlgebraicSpaces B S hS (associatedMap B S hS g).1.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
      (associatedMap B S hS g).1
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS G hG)
  refine ⟨hrep, ?_⟩
  refine (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (Space.openImmersionProperty B S hS) (associatedMap B S hS g).1 hrep T G hT hG
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)).mpr ?_
  rw [representingMap_associatedMap B S hS T G g]
  exact hg

/-- **An open subspace of an algebraic space is an open substack of the algebraic stack the space
determines.** For an open immersion `g : T ⟶ G` of algebraic spaces over `S` there is an open
substack of `S_G` whose objects are exactly those in the essential image of the induced
1-morphism `S_T ⟶ S_G`.

The 1-morphism is an open immersion by
`AlgebraicGeometry.Stack.isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion`, and
**Stacks 0506**, `AlgebraicGeometry.Stack.AlgebraicStacks.exists_openSubstack_essImage`, turns an
open immersion into an open substack. -/
theorem exists_openSubstack_algebraicSpaceStack_of_isOpenImmersion
    {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) {g : T ⟶ G}
    (hg : Space.IsOpenImmersion B S hS g) :
    ∃ W : OpenSubstack (algebraicSpaceStack.{u, w} B S hS G hG),
      W.property = (CatFiberedInGroupoids.homFunctor
        (algebraicSpaceStackMap.{u, w} B S hS hT hG g).hom).essImage :=
  AlgebraicStacks.exists_openSubstack_essImage
    (algebraicSpaceStackMap.{u, w} B S hS hT hG g)
    (isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion.{u, w} B S hS hT hG hg)

end AlgebraicGeometry.Stack

end
