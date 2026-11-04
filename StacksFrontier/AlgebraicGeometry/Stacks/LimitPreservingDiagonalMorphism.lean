module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingBaseChangeComparison
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverSplitFibreDiagonal

/-!
# The diagonal 1-morphism at the universes of Stacks 0CMW

Condition (1) of Stacks 0CMW is limit preservation of the relative diagonal
`Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` of a 1-morphism `f : 𝒳 ⟶ 𝒴`. Limit preservation
(`AlgebraicGeometry.Stack.IsLimitPreserving`) is stated for a 1-morphism between two categories
fibred in groupoids *at one and the same universe shape*, so the statement of condition (1)
requires the 2-fibre product to be a category fibred in groupoids at the shape of `𝒳` and `𝒴`.

`AlgebraicGeometry.BigFppfOver.twoFibreProduct` is stated at the shape
`{u, max u v, u + 1, max (u + 1) v w}`, which is absorbing: the 2-fibre product of two
categories fibred in groupoids at that shape again lies at it. That is also the shape at which
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparison` compares the split fibres of a
2-fibre product with the stagewise 2-fibre product of the split fibres. So this is the shape at
which Stacks 0CMW is statable, and the diagonal is built here at it.

`AlgebraicGeometry.Stack.relativeDiagonal` is the same functor packaged into
`AlgebraicGeometry.Stack.twoFibreProduct`, whose three total categories have independent
universes and whose value is therefore *not* at the shape above.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.twoFibreProductDiagonal`: the relative diagonal
  `Δ : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`, as a 1-morphism of the 2-category of categories fibred in groupoids
  over the big fppf category of `S`.

## Main results

* `AlgebraicGeometry.BigFppfOver.splitFiberMap_twoFibreProductDiagonal_comp_comparison`: the
  split fibre of the diagonal, read componentwise through
  `AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp`, *is* the diagonal of the
  split fibres -- an equality of functors, not merely an isomorphism. On objects both sides give
  the triple `(x, x, 𝟙)`, the base change of an identity being an identity
  (`CategoryTheory.Functor.pullbackFiberHom_id`); on morphisms both give the pair `(α, α)`, the
  comparisons of the chosen pullbacks that the split model inserts being exactly the two
  components of the base-change comparison of the diagonal
  (`CategoryTheory.TwoFibreProductOver.toFiberPullback_map_mapPullbackFiberIso_hom_fst`).

## Implementation notes

The three identities the proof needs about the composite -- its `iso` field and the two
components of its action on morphisms -- are taken as `rfl` hypotheses stated in full inside the
proof. Unfolding `AlgebraicGeometry.Stack.splitFiberMap` and
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp` with `dsimp` instead leaves a
goal that is not type-correct at `implicit` transparency -- those definitions carry their
`IsFibered` instances as `letI`s -- and then neither `rw` nor `simp` applies to it.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.BigFppfOver

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS))
  (f : 𝒳 ⟶ 𝒴)

/-- The relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` of a 1-morphism of categories fibred in
groupoids over the big fppf category of `S`, as a 1-morphism into
`AlgebraicGeometry.BigFppfOver.twoFibreProduct`: on an object `x` it is the triple
`(x, x, 𝟙_{f x})` and on a morphism the pair `(φ, φ)`. -/
def twoFibreProductDiagonal : 𝒳 ⟶ twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.diagonal (CatFiberedInGroupoids.homFunctor_comp_p f)
      w := rfl }

/-- The functor underlying the relative diagonal is
`CategoryTheory.TwoFibreProductOver.diagonal`. -/
lemma homFunctor_twoFibreProductDiagonal :
    CatFiberedInGroupoids.homFunctor (twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) =
      TwoFibreProductOver.diagonal (CatFiberedInGroupoids.homFunctor_comp_p f) := rfl

/-- Conjugating a morphism by two isomorphisms and then undoing both conjugations gives the
morphism back. Stated over an abstract category because `simp` does not reach the composition of
a fibre category reached through the `letI` instances of
`AlgebraicGeometry.Stack.splitFiberMap`. -/
private lemma isoConj_cancel {C : Type*} [Category C] {a b a' b' : C}
    (e : a ≅ b) (e' : a' ≅ b') (g : b ⟶ b') :
    e.inv ≫ (e.hom ≫ g ≫ e'.inv) ≫ e'.hom = g := by
  simp

/-- **The split fibre of the relative diagonal, read componentwise, is the diagonal of the split
fibres.** The split fibre of `Δ_f` sends `(x, h)` to the triple `(x, x, 𝟙)` with its `𝟙`
base-changed along `h`, which is again an identity, and a morphism `α` to the pair `(α, α)` read
through the comparisons of the chosen pullbacks -- and those cancel, the two components of a
diagonal coinciding. -/
theorem splitFiberMap_twoFibreProductDiagonal_comp_comparison (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    Stack.splitFiberMap B S hS (twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) V ⋙
        Stack.splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒳 f f V =
      CategoricalPullback.diagonal (Stack.splitFiberMap B S hS f V) := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  let : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)).IsFibered :=
    (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  have hΔ : Functor.IsFibredOneMorphism 𝒳.val.p
      (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒳.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f))
      (TwoFibreProductOver.diagonal (Stack.isFibredOneMorphism B S hS f).comp_eq) :=
    Stack.isFibredOneMorphism B S hS (twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f)
  have hobj : ∀ o : 𝒳.val.p.SplitFiber V,
      Functor.SplitFiber.toFiberHom
          ((Stack.splitFiberMap B S hS (twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) V ⋙
            Stack.splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒳 f f V).obj o).iso.hom =
        Functor.pullbackFiberHom
          ((TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒳.val.p 𝒴.val.p
              (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
              (Stack.isFibredOneMorphism B S hS f).comp_eq
              (Stack.isFibredOneMorphism B S hS f).comp_eq o.base).obj
            ((Functor.fiberFunctorOfCompEq hΔ.comp_eq o.base).obj o.obj)).iso.hom o.hom :=
    fun _ => rfl
  have hfst : ∀ {o o' : 𝒳.val.p.SplitFiber V} (α : o ⟶ o'),
      Functor.SplitFiber.toFiberHom
          (((Stack.splitFiberMap B S hS (twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) V ⋙
            Stack.splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒳 f f V).map α).fst) =
        (TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids 𝒳.val.p 𝒳.val.p 𝒴.val.p
            (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
            (Stack.isFibredOneMorphism B S hS f).comp_eq
            (Stack.isFibredOneMorphism B S hS f).comp_eq
            ((Functor.fiberFunctorOfCompEq hΔ.comp_eq o.base).obj o.obj) o.hom
            𝒳.isFiberedInGroupoids).inv ≫
          ((TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒳.val.p 𝒴.val.p
              (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
              (Stack.isFibredOneMorphism B S hS f).comp_eq
              (Stack.isFibredOneMorphism B S hS f).comp_eq V).map
            ((hΔ.mapPullbackFiberIso o.obj o.hom).hom ≫
              (Functor.fiberFunctorOfCompEq hΔ.comp_eq V).map
                (Functor.SplitFiber.toFiberHom α) ≫
              (hΔ.mapPullbackFiberIso o'.obj o'.hom).inv)).fst ≫
          (TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids 𝒳.val.p 𝒳.val.p 𝒴.val.p
            (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
            (Stack.isFibredOneMorphism B S hS f).comp_eq
            (Stack.isFibredOneMorphism B S hS f).comp_eq
            ((Functor.fiberFunctorOfCompEq hΔ.comp_eq o'.base).obj o'.obj) o'.hom
            𝒳.isFiberedInGroupoids).hom :=
    fun _ => rfl
  have hsnd : ∀ {o o' : 𝒳.val.p.SplitFiber V} (α : o ⟶ o'),
      Functor.SplitFiber.toFiberHom
          (((Stack.splitFiberMap B S hS (twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) V ⋙
            Stack.splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒳 f f V).map α).snd) =
        (TwoFibreProductOver.pullbackFiberSndIsoOfFiberedInGroupoids 𝒳.val.p 𝒳.val.p 𝒴.val.p
            (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
            (Stack.isFibredOneMorphism B S hS f).comp_eq
            (Stack.isFibredOneMorphism B S hS f).comp_eq
            ((Functor.fiberFunctorOfCompEq hΔ.comp_eq o.base).obj o.obj) o.hom
            𝒳.isFiberedInGroupoids).inv ≫
          ((TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒳.val.p 𝒴.val.p
              (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
              (Stack.isFibredOneMorphism B S hS f).comp_eq
              (Stack.isFibredOneMorphism B S hS f).comp_eq V).map
            ((hΔ.mapPullbackFiberIso o.obj o.hom).hom ≫
              (Functor.fiberFunctorOfCompEq hΔ.comp_eq V).map
                (Functor.SplitFiber.toFiberHom α) ≫
              (hΔ.mapPullbackFiberIso o'.obj o'.hom).inv)).snd ≫
          (TwoFibreProductOver.pullbackFiberSndIsoOfFiberedInGroupoids 𝒳.val.p 𝒳.val.p 𝒴.val.p
            (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
            (Stack.isFibredOneMorphism B S hS f).comp_eq
            (Stack.isFibredOneMorphism B S hS f).comp_eq
            ((Functor.fiberFunctorOfCompEq hΔ.comp_eq o'.base).obj o'.obj) o'.hom
            𝒳.isFiberedInGroupoids).hom :=
    fun _ => rfl
  refine CategoryTheory.Functor.ext (fun o => ?_) (fun o o' α => ?_)
  · refine Cat.categoricalPullback_obj_ext rfl rfl ?_
    refine Cat.eq_eqToHom_conj _ _ _ _ (heq_of_eq (Functor.SplitFiber.toFiberHom_injective ?_))
    rw [hobj o]
    exact TwoFibreProductOver.pullbackFiberHom_toFiberPullback_obj_diagonal_iso_hom
      𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f) hΔ o.obj o.hom
  · refine CategoricalPullback.Hom.ext ?_ ?_
    · simp only [CategoricalPullback.comp_fst, Cat.categoricalPullback_eqToHom_fst,
        CategoricalPullback.diagonal_map_fst]
      refine Cat.eq_eqToHom_conj _ _ _ _ (heq_of_eq (Functor.SplitFiber.toFiberHom_injective ?_))
      rw [hfst α]
      simp only [Functor.map_comp, CategoricalPullback.comp_fst,
        TwoFibreProductOver.toFiberPullback_map_mapPullbackFiberIso_hom_fst
          𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f) hΔ 𝒳.isFiberedInGroupoids
          o.obj o.hom,
        TwoFibreProductOver.toFiberPullback_map_mapPullbackFiberIso_inv_fst
          𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f) hΔ 𝒳.isFiberedInGroupoids
          o'.obj o'.hom,
        TwoFibreProductOver.toFiberPullback_map_fiberFunctorOfCompEq_map_fst
          𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f) hΔ
          (Functor.SplitFiber.toFiberHom α)]
      exact isoConj_cancel _ _ _
    · simp only [CategoricalPullback.comp_snd, Cat.categoricalPullback_eqToHom_snd,
        CategoricalPullback.diagonal_map_snd]
      refine Cat.eq_eqToHom_conj _ _ _ _ (heq_of_eq (Functor.SplitFiber.toFiberHom_injective ?_))
      rw [hsnd α]
      simp only [Functor.map_comp, CategoricalPullback.comp_snd,
        TwoFibreProductOver.toFiberPullback_map_mapPullbackFiberIso_hom_snd
          𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f) hΔ 𝒳.isFiberedInGroupoids
          o.obj o.hom,
        TwoFibreProductOver.toFiberPullback_map_mapPullbackFiberIso_inv_snd
          𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f) hΔ 𝒳.isFiberedInGroupoids
          o'.obj o'.hom,
        TwoFibreProductOver.toFiberPullback_map_fiberFunctorOfCompEq_map_snd
          𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f) hΔ
          (Functor.SplitFiber.toFiberHom α)]
      exact isoConj_cancel _ _ _

end AlgebraicGeometry.BigFppfOver

end
