module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackBootstrap
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.CategoryTheory.FiberedCategory.ShrinkHomsModel

/-!
# The quotient stack of a smooth groupoid as an object of the 2-category of algebraic stacks

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a scheme `S` of a big fppf site.
The quotient stack `[U/R]` of Stacks 044Q is built by stackification, and the morphisms of a
stackification live one universe above the morphisms of the objects of
`AlgebraicGeometry.Stack.AlgebraicStacks`. This file shows that this is a matter of presentation
only: the hom sets of `[U/R]` are small, so shrinking them gives a category over the site
equivalent over the site to `[U/R]` whose morphisms live in the universe of the site, and when
`G` is smooth that category is an object of `AlgebraicGeometry.Stack.AlgebraicStacks`.

## Main definitions

* `AlgebraicGeometry.Stack.quotientStackSmall`: the hom-shrunk model of `[U/R]`.
* `AlgebraicGeometry.Stack.quotientStackSmallEquivalenceOver`: its equivalence over the site with
  `[U/R]`.
* `AlgebraicGeometry.Stack.smoothQuotientAlgebraicStack`: for a smooth groupoid, the model as an
  object of `AlgebraicGeometry.Stack.AlgebraicStacks`.

## Main results

* `AlgebraicGeometry.Stack.locallySmall_quotientStack`: the hom sets of `[U/R]` are small.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isSmooth_unconditional`:
  **Stacks 04TK**, that the quotient stack of a smooth groupoid in algebraic spaces is an
  algebraic stack, with nothing carried.
* `AlgebraicGeometry.Stack.exists_algebraicStacks_equivalenceOver_quotientStack`: a smooth
  groupoid has a model of its quotient stack in `AlgebraicGeometry.Stack.AlgebraicStacks`.

## Implementation notes

A morphism of `[U/R]` is determined by its image in the site together with a morphism of the fibre
(`CategoryTheory.Functor.locallySmall_of_small_fiberHom`), and the site is locally small. A
morphism `x ⟶ y` of the fibre over `T` is determined by its pullback along the isomorphism
`Over.mk (𝟙 T.left) ⟶ T` of the iterated slice, which is a section of the isomorphism presheaf
`Isom(x, y)` — every morphism of a fibre is an isomorphism, `[U/R]` being fibred in groupoids — and
`AlgebraicGeometry.Stack.exists_shrunk_isomPresheaf` identifies the sections of `Isom(x, y)` with
those of a presheaf of `Type u`.

Algebraicity is Stacks 04TK in the form
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isSmooth_of_bootstrap`, whose one input,
part (3) of Stacks 04S6, is `AlgebraicGeometry.Stack.bootstrap04S6`; it is transported to the model
along the equivalence over the site by
`AlgebraicGeometry.Stack.isAlgebraicStack_of_equivalenceOver`.

## References

* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **The morphisms of a fibre of a quotient stack form a small set.** A morphism of the fibre
over `T` is determined by its pullback along the isomorphism `Over.mk (𝟙 T.left) ⟶ T` of the
iterated slice (`CategoryTheory.Functor.eq_of_pullbackFiberHom_eq`), which is a section of
`Isom(x, y)`, and `AlgebraicGeometry.Stack.exists_shrunk_isomPresheaf` puts the sections of
`Isom(x, y)` in bijection with those of a presheaf of `Type u`. -/
theorem small_quotientStack_fiberHom (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) (x y : (quotientStack G).p.Fiber T) : Small.{u} (x ⟶ y) := by
  obtain ⟨F, -, ⟨e, -⟩, -⟩ := exists_shrunk_isomPresheaf C S hS B G T x y
  let g : Over T := (Over.iteratedSliceBackward T).obj (Over.mk (𝟙 T.left))
  have hg : IsIso g.hom := by
    have : IsIso ((Over.forget _).map g.hom) := by
      show IsIso (𝟙 T.left)
      infer_instance
    exact isIso_of_reflects_iso _ (Over.forget _)
  have hgroupoid := (isFiberedInGroupoids_quotientStack G).fiber_isGroupoid g.left
  let toIsom : (x ⟶ y) → ((quotientStack G).p.isomPresheaf x y).obj (Opposite.op g) :=
    fun α => ⟨Functor.pullbackFiberHom α g.hom, by
      rw [Functor.mem_isomSubpresheaf_obj]
      infer_instance⟩
  have hinj : Function.Injective toIsom := fun α β h =>
    Functor.eq_of_pullbackFiberHom_eq α β g.hom (congrArg Subtype.val h)
  have : Small.{u} (((quotientStack G).p.isomPresheaf x y).obj (Opposite.op g)) :=
    small_of_injective (e (Opposite.op (Over.mk (𝟙 T.left)))).injective
  exact small_of_injective hinj

/-- **The hom sets of a quotient stack are small**: `[U/R]` is locally small at the universe of
the site, although its morphisms are built one universe up. -/
theorem locallySmall_quotientStack (G : GroupoidInAlgebraicSpaces C S hS B) :
    LocallySmall.{u} (quotientStack G).obj :=
  have : LocallySmall.{u} (BigFppfOver C S hS) := inferInstance
  Functor.locallySmall_of_small_fiberHom (quotientStack G).p
    (small_quotientStack_fiberHom G)

/-- **The hom-shrunk model of a quotient stack.** The category `ShrinkHoms [U/R]`, with the same
objects as `[U/R]` and morphisms in the universe of the site, over the site through the structure
functor of `[U/R]`. -/
noncomputable def quotientStackSmall (G : GroupoidInAlgebraicSpaces C S hS B) :
    BasedCategory.{u, u + 1} (BigFppfOver C S hS) :=
  letI := locallySmall_quotientStack G
  { obj := ShrinkHoms.{u + 1} (quotientStack G).obj
    p := ShrinkHoms.inverse (quotientStack G).obj ⋙ (quotientStack G).p }

/-- The hom-shrunk model of a quotient stack is equivalent over the site to the quotient stack. -/
noncomputable def quotientStackSmallEquivalenceOver (G : GroupoidInAlgebraicSpaces C S hS B) :
    StacksRepresentableCFG.EquivalenceOver (quotientStack G).p (quotientStackSmall G).p :=
  letI := locallySmall_quotientStack G
  StacksRepresentableCFG.shrinkHomsEquivalenceOver.{u} (quotientStack G).p

/-- The hom-shrunk model of a quotient stack is fibred in groupoids. -/
theorem isFiberedInGroupoids_quotientStackSmall (G : GroupoidInAlgebraicSpaces C S hS B) :
    (quotientStackSmall G).p.IsFiberedInGroupoids :=
  StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver
    (quotientStackSmallEquivalenceOver G).symm (isFiberedInGroupoids_quotientStack G)

/-- **Stacks 04TK.** Let `S` be a scheme contained in a big fppf site and let
`G = (U, R, s, t, c)` be a smooth groupoid in algebraic spaces over an algebraic space over `S`.
Then the quotient stack `[U/R]` is an algebraic stack over `S`.

This is `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isSmooth_of_bootstrap` with part
(3) of Stacks 04S6 supplied by `AlgebraicGeometry.Stack.bootstrap04S6`. -/
@[stacks 04TK]
theorem isAlgebraicStack_quotientStack_of_isSmooth_unconditional
    {G : GroupoidInAlgebraicSpaces C S hS B} (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) :=
  isAlgebraicStack_quotientStack_of_isSmooth_of_bootstrap (bootstrap04S6 C S hS) hG

/-- The hom-shrunk model of the quotient stack of a smooth groupoid is an algebraic stack. -/
theorem isAlgebraicStack_quotientStackSmall {G : GroupoidInAlgebraicSpaces C S hS B}
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    IsAlgebraicStack.{u, w} C S hS (quotientStackSmall G) :=
  isAlgebraicStack_of_equivalenceOver C S hS (quotientStackSmallEquivalenceOver G)
    (isAlgebraicStack_quotientStack_of_isSmooth_unconditional.{u, w} hG)

/-- **The quotient stack of a smooth groupoid in algebraic spaces, as an algebraic stack.** The
hom-shrunk model `AlgebraicGeometry.Stack.quotientStackSmall`, an object of
`AlgebraicGeometry.Stack.AlgebraicStacks`. -/
noncomputable def smoothQuotientAlgebraicStack {G : GroupoidInAlgebraicSpaces C S hS B}
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) : AlgebraicStacks.{u, w} C S hS :=
  ⟨⟨quotientStackSmall G, isFiberedInGroupoids_quotientStackSmall G⟩,
    isAlgebraicStack_quotientStackSmall.{u, w} hG⟩

/-- The model `AlgebraicGeometry.Stack.smoothQuotientAlgebraicStack` is equivalent over the site
to the quotient stack. -/
noncomputable def smoothQuotientAlgebraicStackEquivalenceOver
    {G : GroupoidInAlgebraicSpaces C S hS B} (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    StacksRepresentableCFG.EquivalenceOver (quotientStack G).p
      (smoothQuotientAlgebraicStack.{u, w} hG).val.val.p :=
  quotientStackSmallEquivalenceOver G

/-- **A smooth groupoid in algebraic spaces has a model of its quotient stack in the 2-category of
algebraic stacks**: an object of `AlgebraicGeometry.Stack.AlgebraicStacks` equivalent over the site
to `[U/R]`. -/
theorem exists_algebraicStacks_equivalenceOver_quotientStack
    {G : GroupoidInAlgebraicSpaces C S hS B} (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    ∃ 𝒳 : AlgebraicStacks.{u, w} C S hS,
      Nonempty (StacksRepresentableCFG.EquivalenceOver (quotientStack G).p 𝒳.val.val.p) :=
  ⟨smoothQuotientAlgebraicStack.{u, w} hG, ⟨smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG⟩⟩

end AlgebraicGeometry.Stack

end
