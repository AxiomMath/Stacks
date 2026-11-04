module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia
public import StacksFrontier.CategoryTheory.Sites.Stack.PresheafElementsStack
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge

/-!
# A stack represented by an algebraic space is a stack in setoids (Stacks 04SZ)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in
groupoids over the big fppf site of `S`. Stacks 04SZ says that, for `𝒳` an algebraic stack, the
following are equivalent: (1) `𝒳` is a stack in setoids; (2) the canonical 1-morphism
`I_𝒳 ⟶ 𝒳` from the inertia is an equivalence; (3) `𝒳` is representable by an algebraic space.

This file proves the implications out of (3), for an arbitrary category fibred in groupoids —
algebraicity is not needed for them, and is not assumed. An algebraic space is in particular an
fppf sheaf, so the category it represents is a stack in sets, and the stack-in-setoids condition
transports along the equivalence over the site that representability provides.

It also records (1) ⟺ (2) with the stack condition supplied as a hypothesis; see the
implementation notes for why that hypothesis cannot be read off the algebraic-stack condition.

## Main results

* `AlgebraicGeometry.Stack.isStackInSetoids_of_isRepresentableByAlgebraicSpace`:
  **Stacks 04SZ**, the implication (3) ⟹ (1).
* `AlgebraicGeometry.Stack.isStackInGroupoids_of_isRepresentableByAlgebraicSpace`: such a
  category is a stack in groupoids in the sense of Stacks 02ZI, at every descent universe.
* `AlgebraicGeometry.Stack.isEquivalence_inertiaProjection_of_isRepresentableByAlgebraicSpace`:
  **Stacks 04SZ**, the implication (3) ⟹ (2).
* `AlgebraicGeometry.Stack.isStackInSetoids_iff_inertiaProjection_isEquivalence_of_isStack`:
  the equivalence (1) ⟺ (2) for a category fibred in groupoids which is a stack in the sense of
  Stacks 026F.

## Implementation notes

(3) ⟹ (1) is
`CategoryTheory.PresheafOfCategories.isStackInSetoids_of_equivalenceOver_discreteProjection`
applied to the sheaf condition `AlgebraicGeometry.IsAlgebraicSpace.isSheaf` of the representing
algebraic space; the remaining content of Stacks 03YS (2), that the category attached to an
algebraic space is Deligne-Mumford, is not needed for it and is not proved here.

(1) ⟺ (2) is Stacks 04ZM, `CategoryTheory.RelativeInertia.π_isEquivalence_iff`, which is already
in the library; (3) ⟹ (2) is (3) ⟹ (1) composed with it, the stack condition coming from the
conclusion of (3) ⟹ (1).

The equivalence (1) ⟺ (2) is stated with `𝒳.val.p.IsStack` — the rendering of Stacks 026F over
covering *sieves* — as an explicit hypothesis, and it is *not* stated under the hypothesis that
`𝒳` is an algebraic stack. The reason is that `AlgebraicGeometry.Stack.IsAlgebraicStack` carries
the stack condition in the other of the library's two renderings,
`CategoryTheory.Functor.IsStackInGroupoids` (Stacks 02ZI), over covering *families* with supplied
genuine fibre-product overlaps and with the index type of the family confined to a universe
parameter `w`; while `CategoryTheory.Functor.IsStackInSetoids`, the conclusion, contains
`CategoryTheory.Functor.IsStack` (Stacks 026F), which is sieve-indexed and universe-free. The
implication 026F ⟹ 02ZI is `CategoryTheory.Functor.IsStack.isStackInGroupoids`; the converse is
the implication (1) ⟹ (3) of Stacks 02ZJ and is not in the library — see the module docstring of
`StacksFrontier/CategoryTheory/Sites/Stack/StackBridge.lean` — and it is in any case not applicable
at a `w` smaller than the universe `u + 1` in which the index types of the fppf coverings of the
big site live.

## References

* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04ZM](https://stacks.math.columbia.edu/tag/04ZM)
* [Stacks Project, Tag 03YS](https://stacks.math.columbia.edu/tag/03YS)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **Stacks 04SZ**, the implication (3) ⟹ (1). A category fibred in groupoids over the big fppf
site of `S` which is representable by an algebraic space over `S` is a stack in setoids for the
fppf topology.

The representing presheaf is an fppf sheaf, so the category of its elements is a stack in sets,
and the equivalence over the site that representability provides carries that back to `𝒳`. No
part of the algebraic-stack condition is used. -/
@[stacks 04SZ "the implication (3) ⟹ (1)"]
theorem isStackInSetoids_of_isRepresentableByAlgebraicSpace
    (h : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) := by
  obtain ⟨F, hF, ⟨e⟩⟩ := h
  exact PresheafOfCategories.isStackInSetoids_of_equivalenceOver_discreteProjection
    F _ hF.isSheaf e

/-- A category fibred in groupoids over the big fppf site of `S` which is representable by an
algebraic space over `S` is a stack for the fppf topology in the sense of Stacks 026F.

This is the implication (3) ⟹ (1) of Stacks 04SZ followed by the `isStack` field of
`CategoryTheory.Functor.IsStackInSetoids`. It supplies the sieve-indexed half of the stack clause
of `AlgebraicGeometry.Stack.IsAlgebraicStack` for a representable category fibred in groupoids. -/
theorem isStack_of_isRepresentableByAlgebraicSpace
    (h : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    𝒳.val.p.IsStack (BigFppfOver.topology B S hS) :=
  (isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h).isStack

/-- A category fibred in groupoids over the big fppf site of `S` which is representable by an
algebraic space over `S` is a stack in groupoids in the sense of Stacks 02ZI, at every descent
universe.

This is the implication (3) ⟹ (1) followed by `CategoryTheory.Functor.IsStack.isStackInGroupoids`,
the implication 026F ⟹ 02ZI of Stacks 02ZJ. It supplies the first nontrivial clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack` for a representable category fibred in groupoids,
which is what Stacks 03YS (2) and Stacks 045H need of it. -/
theorem isStackInGroupoids_of_isRepresentableByAlgebraicSpace
    (h : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    𝒳.val.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS) :=
  (isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h).isStack.isStackInGroupoids
    𝒳.isFiberedInGroupoids

/-- **Stacks 04SZ**, the implication (3) ⟹ (2). For a category fibred in groupoids over the big
fppf site of `S` which is representable by an algebraic space over `S`, the canonical projection
from its inertia category is an equivalence.

This is the implication (3) ⟹ (1) composed with Stacks 04ZM. -/
@[stacks 04SZ "the implication (3) ⟹ (2)"]
theorem isEquivalence_inertiaProjection_of_isRepresentableByAlgebraicSpace
    (h : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    (RelativeInertia.π 𝒳.val.p :
      AbsoluteInertia 𝒳.val.p ⥤ 𝒳.val.obj).IsEquivalence :=
  have hs := isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h
  (RelativeInertia.π_isEquivalence_iff _ 𝒳.val.p hs.isStack hs.fiber_isGroupoid).2 hs

/-- The equivalence (1) ⟺ (2) of Stacks 04SZ for a category fibred in groupoids over the big
fppf site of `S` which is a stack for the fppf topology in the sense of Stacks 026F: it is a
stack in setoids if and only if the canonical projection from its inertia category is an
equivalence.

This is Stacks 04ZM read over the big fppf site. The hypothesis `hst` is the sieve-indexed stack
condition of Stacks 026F and is not the one `AlgebraicGeometry.Stack.IsAlgebraicStack` carries;
see the implementation notes of this module. -/
theorem isStackInSetoids_iff_inertiaProjection_isEquivalence_of_isStack
    (hst : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS)) :
    𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) ↔
      (RelativeInertia.π 𝒳.val.p :
        AbsoluteInertia 𝒳.val.p ⥤ 𝒳.val.obj).IsEquivalence :=
  (RelativeInertia.π_isEquivalence_iff _ 𝒳.val.p hst
    𝒳.isFiberedInGroupoids.fiber_isGroupoid).symm

end AlgebraicGeometry.Stack

end
