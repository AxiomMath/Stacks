module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack

/-!
# The structure morphism of an algebraic stack to its base (Stacks 050D)

Let `𝒳` be an algebraic stack over a scheme `S` in a big fppf site `B`. Stacks 050D reads the
relative properties of `𝒳` over `S` — DM, quasi-DM, separated, quasi-separated — as properties of
the canonical 1-morphism from `𝒳` to the algebraic stack represented by `S` itself. This file
builds that 1-morphism.

The stack representing `S` over `S` is the big fppf site of the *identity* of `S`, that is
`AlgebraicGeometry.Stack.schemeStack B S hS (Over.mk (𝟙 (B.obj hS)))`, and the 1-morphism is the
structure functor of `𝒳` followed by the inverse of the iterated-slice equivalence
`CategoryTheory.Over.iteratedSliceEquiv (Over.mk (𝟙 (B.obj hS)))`, which identifies the big fppf
category over `S` with the slice of itself over the identity.

## Main definitions

* `CategoryTheory.Over.iteratedSliceBackward_mk_id_comp_forget`: the iterated-slice equivalence
  at an identity morphism is a section of the forgetful functor on the nose.
* `AlgebraicGeometry.Stack.structureMorphism`: the canonical 1-morphism of an algebraic stack
  over `S` to the stack represented by `S`, the 1-morphism whose properties **Stacks 050D** reads
  off.

## Main results

* `AlgebraicGeometry.Stack.comp_structureMorphism`: the structure morphisms are natural, in the
  sense that every 1-morphism of algebraic stacks over `S` composed with the structure morphism
  of its target is the structure morphism of its source.

## Implementation notes

`structureMorphism` carries no Stacks tag: Stacks 050D's own part keys are its four relative and
four absolute properties, each of which is a predicate *about* this 1-morphism, and none of them
is proved here. **A formalization of Stacks 050D must reuse this declaration rather than
re-coin it**, or the library gains a duplicate constant. It is `implicit_reducible` so
that the eight predicates of Stacks 050D — all of them abbreviations applied to this 1-morphism —
unfold through it.

That the composite is a 1-morphism over the site — the `CategoryTheory.BasedFunctor.w` field — is
`CategoryTheory.Over.iteratedSliceBackward_mk_id_comp_forget` transported along composition with
the structure functor of `𝒳`. It is supplied as a term rather than by `change`-and-`rw`, so that
the spellings of the two slice categories, which differ only up to unfolding, are reconciled by
definitional unfolding instead of by syntactic rewriting.

Algebraicity of the base stack is `AlgebraicGeometry.Stack.isAlgebraicStack_schemeFibredCategory`
(**Stacks 026O** for the big fppf site of a scheme, proved alongside **Stacks 03YS**, part (3)),
through `AlgebraicGeometry.Stack.schemeStack`.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YS](https://stacks.math.columbia.edu/tag/03YS)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Over

universe v₁ u₁

/-- **The iterated-slice equivalence at an identity morphism is a section of the forgetful
functor.** For an object `X`, the backward functor of
`CategoryTheory.Over.iteratedSliceEquiv (Over.mk (𝟙 X))` followed by the forgetful functor of the
slice over `Over.mk (𝟙 X)` is the identity of `Over X`, since that forgetful composite is
`CategoryTheory.Over.map` of the identity. -/
theorem iteratedSliceBackward_mk_id_comp_forget {C : Type u₁} [Category.{v₁} C] (X : C) :
    iteratedSliceBackward (Over.mk (𝟙 X)) ⋙ forget (Over.mk (𝟙 X)) = 𝟭 (Over X) :=
  (iteratedSliceBackward_forget (Over.mk (𝟙 X))).trans (mapId_eq X)

end CategoryTheory.Over

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The structure morphism of Stacks 050D.** The canonical 1-morphism from an algebraic stack
`𝒳` over `S` to the algebraic stack represented by `S` itself, namely the big fppf site of the
identity of `S`: the structure functor of `𝒳`, followed by the inverse of the iterated-slice
equivalence identifying the big fppf category over `S` with its own slice over the identity. -/
@[implicit_reducible]
noncomputable def structureMorphism (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    𝒳 ⟶ schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))) :=
  Bicategory.InducedBicategory.mkHom <|
    Bicategory.InducedBicategory.mkHom
      { toFunctor := 𝒳.val.val.p ⋙ (Over.iteratedSliceEquiv (Over.mk (𝟙 (B.obj hS)))).inverse
        w := (congrArg
          (fun F : BigFppfOver B S hS ⥤ BigFppfOver B S hS => 𝒳.val.val.p ⋙ F)
          (Over.iteratedSliceBackward_mk_id_comp_forget (B.obj hS))).trans
            (Functor.comp_id 𝒳.val.val.p) }

/-- **Naturality of the structure morphism of Stacks 050D.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S` followed by the structure morphism of `𝒴` is the structure morphism of
`𝒳`: both are a composite of structure functors with the same inverse iterated-slice equivalence,
and the structure functor of `𝒳` is the one of `𝒴` precomposed with `f`, which is the
`CategoryTheory.BasedFunctor.w` field of `f`. -/
@[simp]
theorem comp_structureMorphism {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    f ≫ structureMorphism B S hS 𝒴 = structureMorphism B S hS 𝒳 :=
  Bicategory.InducedBicategory.hom_ext <| Bicategory.InducedBicategory.hom_ext <|
    BasedCategory.BasedFunctor.ext' <|
      (Functor.assoc f.hom.hom.toFunctor 𝒴.val.val.p
        (Over.iteratedSliceEquiv (Over.mk (𝟙 (B.obj hS)))).inverse).symm.trans
        (congrArg (· ⋙ (Over.iteratedSliceEquiv (Over.mk (𝟙 (B.obj hS)))).inverse)
          f.hom.hom.w)

end AlgebraicGeometry.Stack

end
