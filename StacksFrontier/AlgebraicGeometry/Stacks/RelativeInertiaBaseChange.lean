module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.JointlyFaithful
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The relative inertia of a base change (Stacks 06PQ)

Let `π : 𝒳 ⟶ 𝒴` and `f : 𝒴' ⟶ 𝒴` be 1-morphisms of algebraic stacks over `S` and set
`𝒳' = 𝒳 ×_𝒴 𝒴'`, with `π' : 𝒳' ⟶ 𝒴'` the second projection. Stacks 06PQ says that both
squares of
```
  I_{𝒳'/𝒴'} --> 𝒳' --π'--> 𝒴'
      |          |          |
      v          v          v
  I_{𝒳/𝒴}  -->  𝒳  --π-->  𝒴
```
are 2-fibre products of algebraic stacks. The right square is the defining base-change
square, which is a 2-fibre product in the 2-category of algebraic stacks by
`AlgebraicGeometry.Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks`
(Stacks 04T2). This file supplies the left square and its universal property.

## Main definitions

* `AlgebraicGeometry.Stack.relativeInertiaStack`: the relative inertia of a 1-morphism of
  algebraic stacks, as an object of the 2-category of algebraic stacks.
* `AlgebraicGeometry.Stack.relativeInertiaProjection`: its forgetful 1-morphism.
* `AlgebraicGeometry.Stack.CartesianRelativeInertiaSquare`: the left square, together with
  the prescribed action of its comparison 1-morphism and its universal property.
* `AlgebraicGeometry.Stack.cartesianRelativeInertiaSquare`: the canonical such square.

## Main results

* `AlgebraicGeometry.Stack.exists_cartesianRelativeInertiaSquare`: **Stacks 06PQ**, the left
  square exists and is a 2-fibre product of algebraic stacks.

## Implementation notes

The mathematics is the categorical statement proved in
`StacksFrontier.CategoryTheory.FiberedCategory.InertiaBaseChange`: the canonical comparison
`Θ : I_{𝒳'/𝒴'} ⥤ I_{𝒳/𝒴} ×_𝒳 𝒳'` is an equivalence over the site, under the hypothesis that
`π` is a 1-morphism over the site, which here is the `w` field of `π`. Everything else is
formal.

* The explicit 2-fibre product `I_{𝒳/𝒴} ×_𝒳 𝒳'` of categories over the site, with its
  canonical square, is a 2-fibre product in the 2-category of categories fibred in groupoids
  (`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare`).
* Reindexing that square along `Θ` (`CategoryTheory.Bicategory.TwoCommSq.precompose`) gives a
  square with apex `I_{𝒳'/𝒴'}` receiving the tautological pre-morphism
  `CategoryTheory.Bicategory.TwoCommSq.PreHom.ofPrecompose`, so
  `CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to` makes it a 2-fibre product
  too.
* That square has the cospan in the order `(I_{𝒳/𝒴}, 𝒳')`, so its legs are exchanged by
  `CategoryTheory.Bicategory.isTwoFibreProduct_swap`, and the 2-category of algebraic stacks
  is a full sub-2-category, so `CategoryTheory.Bicategory.isTwoFibreProduct_of_underlying`
  reads the result there.

No transport is needed anywhere: the second leg of the reindexed square *is* the forgetful
1-morphism of `I_{𝒳'/𝒴'}` on the nose, because `Θ` sends `(x', α')` to a quadruple whose
`𝒳'`-component is `x'` and `Θ φ` to one whose `𝒳'`-component is `φ`. For the same reason the
three clauses pinning the action of the comparison 1-morphism hold by `rfl`.

The relative inertia is read as an algebraic stack by pairing the canonical
`AlgebraicGeometry.Stack.relativeInertia` with the algebraicity of Stacks 050Q, so the
underlying category fibred in groupoids is the canonical one and carries no choice.

## References

* [Stacks Project, Tag 06PQ](https://stacks.math.columbia.edu/tag/06PQ)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04Z4](https://stacks.math.columbia.edu/tag/04Z4)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The relative inertia `I_{𝒳/𝒴}` of a 1-morphism of algebraic stacks over `S`, as an object
of the 2-category of algebraic stacks (Stacks 03YP): the canonical
`AlgebraicGeometry.Stack.relativeInertia` together with its algebraicity, which is Stacks
050Q. -/
def relativeInertiaStack {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    AlgebraicStacks.{u, w} B S hS :=
  ⟨relativeInertia B S hS f.hom,
    isAlgebraicStack_relativeInertia.{u, w} B S hS 𝒳.val 𝒴.val f.hom 𝒳.property 𝒴.property⟩

/-- The forgetful 1-morphism `I_{𝒳/𝒴} ⟶ 𝒳`, `(x, α) ↦ x`, read in the 2-category of algebraic
stacks. Its underlying 1-morphism of categories over the site is
`CategoryTheory.RelativeInertia.basedProjection`, since the 1-morphisms of the 2-category of
algebraic stacks are those of the ambient 2-category of categories over the site. -/
def relativeInertiaProjection {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    relativeInertiaStack B S hS f ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (RelativeInertia.basedProjection f.hom.hom))

/-- **The left square of Stacks 06PQ.** For 1-morphisms `π : 𝒳 ⟶ 𝒴` and `f : 𝒴' ⟶ 𝒴` of
algebraic stacks over `S`, a comparison 1-morphism from the relative inertia of the base change
`π' : 𝒳 ×_𝒴 𝒴' ⟶ 𝒴'` to the relative inertia of `π`, filling the left square of the diagram of
Stacks 06PQ, acting on objects, automorphisms and morphisms by the canonical formula of
Categories, Equation 04Z4, and exhibiting that square as a 2-fibre product of algebraic
stacks. -/
structure CartesianRelativeInertiaSquare
    {𝒳 𝒴' 𝒴 : AlgebraicStacks.{u, w} B S hS} (π : 𝒳 ⟶ 𝒴) (f : 𝒴' ⟶ 𝒴) where
  /-- the comparison 1-morphism `I_{𝒳'/𝒴'} ⟶ I_{𝒳/𝒴}` -/
  toInertia :
    relativeInertiaStack B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS π f).snd ⟶
      relativeInertiaStack B S hS π
  /-- the 2-commutativity of the left square -/
  commutes :
    relativeInertiaProjection B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS π f).snd ≫
        (twoFibreProductSquareAlgebraicStacks B S hS π f).fst ≅
      toInertia ≫ relativeInertiaProjection B S hS π
  /-- the comparison sends `(x', α')` to a pair whose underlying object is the `𝒳`-component
  of `x'` -/
  canonical_obj : ∀ A, ((toInertia.hom.hom.toFunctor).obj A).obj = A.obj.x
  /-- the automorphism of that pair is the `𝒳`-component of `α'` -/
  canonical_auto : ∀ A, HEq ((toInertia.hom.hom.toFunctor).obj A).auto.hom A.auto.hom.a
  /-- the comparison sends a morphism to its `𝒳`-component -/
  canonical_map : ∀ {A D} (φ : A ⟶ D), HEq ((toInertia.hom.hom.toFunctor).map φ).hom φ.hom.a
  /-- the left square is a 2-fibre product of algebraic stacks -/
  cartesian : Bicategory.IsTwoFibreProduct
    { pt := relativeInertiaStack B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS π f).snd
      fst := relativeInertiaProjection B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS π f).snd
      snd := toInertia
      iso := commutes }

section Construction

variable {𝒳 𝒴' 𝒴 : AlgebraicStacks.{u, w} B S hS} (π : 𝒳 ⟶ 𝒴) (f : 𝒴' ⟶ 𝒴)

/-- The canonical 2-commutative square of the cospan `I_{𝒳/𝒴} ⟶ 𝒳 ⟵ 𝒳 ×_𝒴 𝒴'` of categories
fibred in groupoids over the site, whose apex is the explicit 2-fibre product
`I_{𝒳/𝒴} ×_𝒳 𝒳'` of Stacks 0040 and which is the model the left square of Stacks 06PQ is
compared with. -/
def inertiaBaseChangeModel : Bicategory.TwoCommSq
    (relativeInertiaProjection B S hS π).hom
    (twoFibreProductSquareAlgebraicStacks B S hS π f).fst.hom :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (relativeInertiaProjection B S hS π).hom
    (twoFibreProductSquareAlgebraicStacks B S hS π f).fst.hom

/-- The canonical comparison `Θ : I_{𝒳'/𝒴'} ⟶ I_{𝒳/𝒴} ×_𝒳 𝒳'` of Stacks 06PQ, as a 1-morphism
of categories fibred in groupoids over the site. It is
`CategoryTheory.RelativeInertia.toBaseChangeFibreProduct`, which is over the site by
`CategoryTheory.RelativeInertia.toBaseChangeFibreProduct_comp_structureFunctor`. -/
def inertiaBaseChangeComparison :
    (relativeInertiaStack B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS π f).snd).val ⟶
      (inertiaBaseChangeModel B S hS π f).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := RelativeInertia.toBaseChangeFibreProduct 𝒳.val.val.p 𝒴'.val.val.p
        𝒴.val.val.p π.hom.hom.toFunctor f.hom.hom.toFunctor
      w := RelativeInertia.toBaseChangeFibreProduct_comp_structureFunctor _ _ _ _ _ }

/-- **The left square of Stacks 06PQ is a 2-fibre product of categories fibred in groupoids,**
in the order `(I_{𝒳/𝒴}, 𝒳')` of the cospan.

The model square is a 2-fibre product, and reindexing it along the comparison `Θ` leaves `Θ`
itself as a pre-morphism into it; `Θ` is an equivalence of the underlying categories by
Stacks 06PQ, the hypothesis there being that `π` is a 1-morphism over the site, which is its
`w` field. -/
noncomputable def isTwoFibreProduct_inertiaBaseChangePrecompose :
    Bicategory.IsTwoFibreProduct
      ((inertiaBaseChangeModel B S hS π f).precompose
        (inertiaBaseChangeComparison B S hS π f)) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
    (Bicategory.TwoCommSq.PreHom.ofPrecompose _ _)
    (RelativeInertia.toBaseChangeFibreProduct_isEquivalence π.hom.hom.w)

/-- **The canonical left square of Stacks 06PQ.** Its comparison 1-morphism is the composite of
`AlgebraicGeometry.Stack.inertiaBaseChangeComparison` with the first projection of the model, so
its action on objects, automorphisms and morphisms is the prescribed one by the `rfl`-lemmas of
`CategoryTheory.RelativeInertia.toBaseChangeFibreProduct`; its second leg is the forgetful
1-morphism of `I_{𝒳'/𝒴'}` on the nose, so no transport intervenes; and its universal property
is `AlgebraicGeometry.Stack.isTwoFibreProduct_inertiaBaseChangePrecompose` with the legs
exchanged, read in the full sub-2-category of algebraic stacks. -/
noncomputable def cartesianRelativeInertiaSquare :
    CartesianRelativeInertiaSquare B S hS π f where
  toInertia := Bicategory.InducedBicategory.mkHom
    (inertiaBaseChangeComparison B S hS π f ≫ (inertiaBaseChangeModel B S hS π f).fst)
  commutes := Bicategory.InducedBicategory.isoMk
    (((inertiaBaseChangeModel B S hS π f).precompose
      (inertiaBaseChangeComparison B S hS π f)).iso.symm)
  canonical_obj _ := rfl
  canonical_auto _ := HEq.rfl
  canonical_map _ := HEq.rfl
  cartesian := Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_inertiaBaseChangePrecompose B S hS π f))

/-- **Stacks 06PQ, the left square.** Both squares of the diagram of Stacks 06PQ are 2-fibre
products of algebraic stacks: the right one is the defining base-change square of Stacks 04T2,
and this provides the left one, a comparison 1-morphism from the relative inertia of the base
change to the relative inertia of `π`, with the prescribed action on objects and automorphisms,
exhibiting the left square as a 2-fibre product in the 2-category of algebraic stacks. -/
@[stacks 06PQ "left square of algebraic stacks"]
theorem exists_cartesianRelativeInertiaSquare :
    Nonempty (CartesianRelativeInertiaSquare B S hS π f) :=
  ⟨cartesianRelativeInertiaSquare B S hS π f⟩

end Construction

end AlgebraicGeometry.Stack

end
