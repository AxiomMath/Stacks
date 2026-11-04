module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs
public import StacksFrontier.Deformation.Artin.LimitPreserving

/-!
# Limit preserving 1-morphisms of categories fibred in groupoids (Stacks 0CMR)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category
of a scheme `S`. Following Stacks 0CMR, `f` *is limit preserving* when for every cofiltered
inverse system `D` of affine schemes over `S` whose limit in schemes is `U = lim Uᵢ` the square

```
colim 𝒳_{Uᵢ} ⟶ 𝒳_U
     |            |
     f            f
     ↓            ↓
colim 𝒴_{Uᵢ} ⟶ 𝒴_U
```

of fibre categories is 2-cartesian.

The two horizontal functors are the canonical comparison `Deformation.Artin.colimitComparison`
of Stacks 07XL, built from the strict diagram of fibres
`Deformation.Artin.fiberDiagram`; the absolute condition that a single such comparison be an
equivalence is `Deformation.Artin.IsLimitPreserving`, and this file is its relative form.

## Main definitions

* `AlgebraicGeometry.Stack.IsLimitPreserving`: **Stacks 0CMR**, the 2-cartesian square
  criterion for a 1-morphism.
* `AlgebraicGeometry.Stack.splitFiberMap`: the functor on strict split fibres induced by a
  1-morphism of categories fibred in groupoids.

## Main results

* `AlgebraicGeometry.Stack.isFibredOneMorphism`: the underlying functor of a 1-morphism of
  categories fibred in groupoids is a morphism of fibred categories, so it has the
  base-change comparison isomorphisms `CategoryTheory.IsFibredOneMorphism.mapPullbackFiberIso`
  that the 2-cell of the square is pinned to.

## Implementation notes

The left vertical functor of the square is *not* determined by `f` alone: the colimit of the
stage fibres is a colimit in `Cat`, so a functor out of it is the datum of a cocone, and the
cocone `f` induces is the one whose stage components are the maps of strict split fibres. The
statement therefore quantifies over the natural transformation `T` of strict diagrams, the
functor `H` out of the colimit and the 2-cell `η` filling the square, and pins all three down:
`T` is componentwise `AlgebraicGeometry.Stack.splitFiberMap`, `H` is the colimit of `T`, and
`η` is, on every colimit generator, the canonical base-change comparison of the fibred
1-morphism. Only then is "the square" of Stacks 0CMR a single determinate square, and its
being 2-cartesian a property of `f`.

`AlgebraicGeometry.Stack.splitFiberMap` is `@[implicit_reducible]` because the components of
`T` are compared to it by an equation of 1-morphisms of `Cat`, which the elaborator has to see
through the `Functor.SplitFiber` projections to typecheck.

The pinning of `η` is a heterogeneous equality: the 2-cell component at a colimit generator
and the base-change isomorphism live in fibres of the target which are equal, but only after
rewriting along `Deformation.Artin.colimitComparison_ι`, and the equality of the two fibres is
not a definitional one.

The square is formed in `Cat` at a single universe, reached by `AsSmall`, which raises the
object and morphism universes of the fibres to one containing the index category as well and
imposes no smallness hypothesis. The universe of the fibres of `𝒳` and `𝒴` is independent of
the universe of the schemes, as for every category fibred in groupoids over the big fppf
category.

## References

* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w uX vX

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S hS)}

/-- The underlying functor of a 1-morphism of categories fibred in groupoids is a morphism of
fibred categories over the big fppf category of `S`. -/
theorem isFibredOneMorphism (f : 𝒳 ⟶ 𝒴) :
    Functor.IsFibredOneMorphism 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f) :=
  𝒴.2.isFibredOneMorphism (CatFiberedInGroupoids.homFunctor_comp_p f)

/-- The functor on the strict split fibres of Stacks 004A induced by a 1-morphism of
categories fibred in groupoids: an object of the split fibre of `𝒳` over `V` is an object of
`𝒳` over some `W` together with a morphism `W ⟶ V`, and it is sent to its image in `𝒴` over
the same `W` with the same morphism. -/
@[implicit_reducible]
noncomputable def splitFiberMap (f : 𝒳 ⟶ 𝒴) (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    𝒳.val.p.SplitFiber V ⥤ 𝒴.val.p.SplitFiber V :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let hF := isFibredOneMorphism B S hS f
  { obj := fun o => ⟨o.base,
      (Functor.fiberFunctorOfCompEq hF.comp_eq o.base).obj o.obj, o.hom⟩
    map := fun {o o'} α =>
      Functor.SplitFiber.ofFiberHom
        ((hF.mapPullbackFiberIso o.obj o.hom).hom ≫
          (Functor.fiberFunctorOfCompEq hF.comp_eq V).map
            (Functor.SplitFiber.toFiberHom α) ≫
          (hF.mapPullbackFiberIso o'.obj o'.hom).inv)
    map_id := by
      intro o
      apply Functor.SplitFiber.toFiberHom_injective
      simp
    map_comp := by
      intro o o' o'' α β
      apply Functor.SplitFiber.toFiberHom_injective
      simp [Category.assoc] }

/-- **Stacks 0CMR.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big
fppf category of `S` is *limit preserving* when, for every cofiltered inverse system of affine
schemes over `S` whose image in schemes has a limiting cone, the canonical square

`colim 𝒳_{Uᵢ} ⟶ 𝒳_U`, `colim 𝒴_{Uᵢ} ⟶ 𝒴_U`

of fibre categories, with vertical maps induced by `f`, is a 2-fibre product.

The square is the determinate one: the vertical map out of the colimit is the colimit of the
componentwise maps `AlgebraicGeometry.Stack.splitFiberMap` of strict split fibres, and the
filling 2-cell is, on every colimit generator, the canonical base-change comparison of the
fibred 1-morphism underlying `f`. -/
@[stacks 0CMR]
abbrev IsLimitPreserving (f : 𝒳 ⟶ 𝒴) : Prop :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
    IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
      let E := D ⋙ BigAffineFppf.inclusion B S hS
      let d := (BigAffineFppf.inclusion B S hS).mapCone c
      ∃ (T : Deformation.Artin.fiberDiagram 𝒳.val.p E ⟶
          Deformation.Artin.fiberDiagram 𝒴.val.p E)
        (H : (colimit (Deformation.Artin.fiberDiagram 𝒳.val.p E) : Cat) ⥤
          (colimit (Deformation.Artin.fiberDiagram 𝒴.val.p E) : Cat))
        (η : (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙
            AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}) ⋙
            AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
            Functor.fiberFunctorOfCompEq
              (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
              AsSmall.up.{vX, uX, max v w vX (u + 1) uX u} ≅
          H ⋙ Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙
            AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}),
        (∀ i : I, T.app (op i) =
          (AsSmall.down ⋙ splitFiberMap B S hS f (E.obj i) ⋙
            AsSmall.up).toCatHom) ∧
          (H = (colimMap T).toFunctor) ∧
          (∀ (i : I) (x : 𝒳.val.p.SplitFiber (E.obj i)),
            HEq
              (AsSmall.down.map
                ((η.app
                  ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E)
                      (op i)).toFunctor.obj
                    (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj x))).hom))
              ((isFibredOneMorphism B S hS f).mapPullbackFiberIso x.obj
                (d.π.app i ≫ x.hom)).inv) ∧
          Nonempty (Bicategory.IsTwoFibreProduct
            ({ pt := (colimit (Deformation.Artin.fiberDiagram 𝒳.val.p E) : Cat)
               fst := (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙
                 AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom
               snd := H.toCatHom
               iso := Cat.Hom.isoMk η } :
              Bicategory.TwoCommSq
                (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
                  Functor.fiberFunctorOfCompEq
                  (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
                  AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom
                (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙
                  AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom))

end AlgebraicGeometry.Stack

end
