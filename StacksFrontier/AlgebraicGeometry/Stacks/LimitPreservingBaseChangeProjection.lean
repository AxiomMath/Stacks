module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingBaseChangeComparison
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatTwoFibreProductProjections
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibrePullbackProjections

/-!
# The first projection of a base change, and the components of the stagewise comparison

The base change `𝒳 ×_𝒴 𝒵` of `p : 𝒳 ⟶ 𝒴` along `q : 𝒵 ⟶ 𝒴` carries a second projection to `𝒵`,
`AlgebraicGeometry.BigFppfOver.twoFibreProductSnd`, whose limit preservation is **Stacks 0CMT**.
This file adds the first projection to `𝒳` and identifies the two components of the stagewise
comparison `AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp` with the split fibres
of the two projections.

The content of the identification is that the chosen pullback of a component of an object of the
2-fibre product is the component of the chosen pullback, in the two ways that statement can be
read: as the base-change comparison of the projection seen as a fibred 1-morphism, which is what
`AlgebraicGeometry.Stack.splitFiberMap` conjugates by, and as
`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids`, which is what the
stagewise comparison conjugates by. Those are mutually inverse by
`CategoryTheory.TwoFibreProductOver.mapPullbackFiberIso_fst_eq`, and the two conjugations then
agree.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.twoFibreProductFst`: the first projection of the base change.

## Main results

* `AlgebraicGeometry.BigFppfOver.homFunctor_twoFibreProductFst`: its underlying functor is
  `CategoryTheory.TwoFibreProductOver.fst`.
* `AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp_comp_π₁` and `…_π₂`.

## References

* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
    (BigFppfOver B S hS))
  (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)

/-- The canonical projection of the base change to the first factor, the companion of
`AlgebraicGeometry.BigFppfOver.twoFibreProductSnd`. -/
def twoFibreProductFst : twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.fst 𝒳.val.p 𝒵.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
      w := TwoFibreProductOver.fst_comp_eq }

/-- The functor underlying the first projection is `CategoryTheory.TwoFibreProductOver.fst`. -/
lemma homFunctor_twoFibreProductFst :
    CatFiberedInGroupoids.homFunctor (twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) =
      TwoFibreProductOver.fst 𝒳.val.p 𝒵.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q) := rfl

/-- The functor underlying the second projection is `CategoryTheory.TwoFibreProductOver.snd`. -/
lemma homFunctor_twoFibreProductSnd :
    CatFiberedInGroupoids.homFunctor (twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) =
      TwoFibreProductOver.snd 𝒳.val.p 𝒵.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q) := rfl

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] AsSmall AsSmall.up AsSmall.down
  Bicategory.InducedBicategory Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.SplitFiber.restrict Deformation.Artin.fiberCocone
  Deformation.Artin.fiberDiagram Functor.splitPresheaf Cat.asSmallFunctor
  Deformation.Artin.colimitComparison Deformation.Artin.evaluateSplitFiber
  BigFppfOver.twoFibreProduct BasedCategory.ofFunctor Functor.fiberMap

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
    (BigFppfOver B S hS))
  (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)

/-- **The first component of the stagewise comparison is the split fibre of the first
projection.** Both conjugate the first component of a morphism of the fibre by the comparison of
the chosen pullback of the `𝒳`-component with the `𝒳`-component of the chosen pullback -- in
opposite directions, and those comparisons are mutually inverse by
`CategoryTheory.TwoFibreProductOver.mapPullbackFiberIso_fst_eq`. -/
lemma splitFiberTwoFibreProductComparisonApp_comp_π₁ (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q V ⋙
        CategoricalPullback.π₁ (splitFiberMap B S hS p V) (splitFiberMap B S hS q V) =
      splitFiberMap B S hS (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) V := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)).IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun o o' m => ?_)
  refine Cat.eq_eqToHom_conj _ _ _ _ (heq_of_eq ?_)
  refine Functor.SplitFiber.toFiberHom_injective ?_
  exact TwoFibreProductOver.conj_mapPullbackFiberIso_fst 𝒳.val.p 𝒵.val.p 𝒴.val.p
    (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
    (CatFiberedInGroupoids.homFunctor_comp_p p) (CatFiberedInGroupoids.homFunctor_comp_p q)
    o.obj o.hom o'.obj o'.hom 𝒳.isFiberedInGroupoids
    (isFibredOneMorphism B S hS (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)) _

/-- **The second component of the stagewise comparison is the split fibre of the second
projection**, by the argument of
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp_comp_π₁` on the other side. -/
lemma splitFiberTwoFibreProductComparisonApp_comp_π₂ (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q V ⋙
        CategoricalPullback.π₂ (splitFiberMap B S hS p V) (splitFiberMap B S hS q V) =
      splitFiberMap B S hS (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) V := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)).IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun o o' m => ?_)
  refine Cat.eq_eqToHom_conj _ _ _ _ (heq_of_eq ?_)
  refine Functor.SplitFiber.toFiberHom_injective ?_
  exact TwoFibreProductOver.conj_mapPullbackFiberIso_snd 𝒳.val.p 𝒵.val.p 𝒴.val.p
    (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
    (CatFiberedInGroupoids.homFunctor_comp_p p) (CatFiberedInGroupoids.homFunctor_comp_p q)
    o.obj o.hom o'.obj o'.hom 𝒵.isFiberedInGroupoids
    (isFibredOneMorphism B S hS (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)) _

end AlgebraicGeometry.Stack

end
