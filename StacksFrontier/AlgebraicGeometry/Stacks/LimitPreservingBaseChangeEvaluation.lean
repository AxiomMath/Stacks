module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingBaseChangeComparison

/-!
# The componentwise reading of the split fibre of a base change is an equivalence

`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp` reads an object `(U, P, h)` of
the split fibre of `𝒳 ×_𝒴 𝒵` over `V` as the pair `(U, P.x, h)`, `(U, P.y, h)`. It is defined
directly, rather than as the composite of
`CategoryTheory.Functor.SplitFiber.fiberEquiv` (Stacks 004A, fibrewise) with
`CategoryTheory.TwoFibreProductOver.fiberEquiv` (Stacks 02XI), because the composite is natural
in `V` only up to isomorphism while `CategoryTheory.Limits.colimMap` needs strict naturality.

This file supplies the comparison with that composite: evaluating the two components of the
componentwise reading is, up to the two base-change comparisons of
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibrePullback`, the same as evaluating in the
split fibre of the 2-fibre product and then passing to the 2-fibre product of the fibres. Since
all three evaluations and the comparison of Stacks 02XI are equivalences, and the functor
induced on 2-fibre products by three equivalences is one (Stacks 02XB (3)), the componentwise
reading is an equivalence too.

That is what makes `CategoryTheory.Cat.isEquivalence_colimitTwoFibreProductComparison` —
"filtered colimits of categories commute with 2-fibre products" — applicable to the diagrams of
split fibres: the stagewise comparison
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparison` is an equivalence at every stage.

## Main results

* `AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp_evaluationIso`: the
  componentwise reading, followed by the three evaluations, is evaluation followed by the
  comparison of Stacks 02XI.
* `AlgebraicGeometry.Stack.isEquivalence_splitFiberTwoFibreProductComparisonApp`: the
  componentwise reading of the split fibre of a 2-fibre product is an equivalence.

## Implementation notes

The object-level content of the isomorphism is
`CategoryTheory.TwoFibreProductOver.mapPullbackFiberIso_conj_obj_iso`, and its naturality is
the cancellation of the conjugating comparisons that the componentwise reading of a morphism
inserts. Both are reached from the goal by one `rfl`-stated bridging equality, since `simp` does
not see the composition of a fibre category reached through the `letI` instances of
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp`; the two pieces of pure
category theory the goals then reduce to are stated over an abstract category for the same
reason.

## References

* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
* [Stacks Project, Tag 02XB](https://stacks.math.columbia.edu/tag/02XB)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] Bicategory.InducedBicategory Functor.Fiber
  Functor.Fiber.fiberInclusion Functor.SplitFiber.restrict Functor.fiberMap

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
    (BigFppfOver B S hS))
  (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)

/-- An identity conjugated by an isomorphism on the left, read with the conjugation moved to the
other side. Stated over an abstract category because `simp` does not reach the composition of a
fibre category reached through the `letI` instances of
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp`. -/
lemma eq_isoInv_comp₃ {C : Type*} [Category C] {a b c d e : C}
    (i : a ≅ b) (x : b ⟶ e) (f : a ⟶ c) (g : c ⟶ d) (h : d ⟶ e)
    (key : i.hom ≫ x = f ≫ g ≫ h) : x = (i.inv ≫ f ≫ g) ≫ h := by
  rw [Category.assoc, Category.assoc, ← key, Iso.inv_hom_id_assoc]

/-- A morphism conjugated by an isomorphism on the right, followed by the inverse of that
isomorphism, is the morphism. Stated over an abstract category for the reason given at
`AlgebraicGeometry.Stack.eq_isoInv_comp₃`. -/
lemma isoConj_comp_inv {C : Type*} [Category C] {a b c d : C} (f : a ⟶ b) (x : b ⟶ c)
    (j : c ≅ d) : (f ≫ x ≫ j.hom) ≫ j.inv = f ≫ x := by
  simp

/-- **The componentwise reading of the split fibre of a 2-fibre product, followed by the three
evaluations of Stacks 004A, is evaluation followed by the comparison of Stacks 02XI.** On an
object `(U, P, h)` of the split fibre the two sides give the chosen pullbacks along `h` of the
two components of `P` and the two components of the chosen pullback of `P`, which are compared
by `CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids` and
`…pullbackFiberSndIsoOfFiberedInGroupoids`; that those comparisons are compatible with the two
filling isomorphisms is
`CategoryTheory.TwoFibreProductOver.mapPullbackFiberIso_conj_obj_iso`.

This is the composite that the module documentation of
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingBaseChangeComparison` records as natural in
`V` only up to isomorphism. -/
noncomputable def splitFiberTwoFibreProductComparisonApp_evaluationIso
    (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q V ⋙
        CategoricalPullback.map (splitFiberMap B S hS p V) (splitFiberMap B S hS q V)
          (Deformation.Artin.evaluateSplitFiber 𝒳.val.p V)
          (Deformation.Artin.evaluateSplitFiber 𝒵.val.p V)
          (Deformation.Artin.evaluateSplitFiber 𝒴.val.p V)
          (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) V)
          (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p q) V)
          (splitEvaluationIso B S hS q V) (splitEvaluationIso B S hS p V).symm ≅
      Deformation.Artin.evaluateSplitFiber
          (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p V ⋙
        TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒵.val.p 𝒴.val.p
          (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
          (CatFiberedInGroupoids.homFunctor_comp_p p)
          (CatFiberedInGroupoids.homFunctor_comp_p q) V := by
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  letI : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)).IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  refine NatIso.ofComponents (fun o => CategoricalPullback.mkIso
    (TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
      (CatFiberedInGroupoids.homFunctor_comp_p p) (CatFiberedInGroupoids.homFunctor_comp_p q)
      o.obj o.hom 𝒳.isFiberedInGroupoids).symm
    (TwoFibreProductOver.pullbackFiberSndIsoOfFiberedInGroupoids 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
      (CatFiberedInGroupoids.homFunctor_comp_p p) (CatFiberedInGroupoids.homFunctor_comp_p q)
      o.obj o.hom 𝒵.isFiberedInGroupoids).symm
    ?_) ?_
  · have key := TwoFibreProductOver.mapPullbackFiberIso_conj_obj_iso 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
      (isFibredOneMorphism B S hS p) (isFibredOneMorphism B S hS q)
      𝒳.isFiberedInGroupoids 𝒵.isFiberedInGroupoids o.obj o.hom
    have hlhs : ((splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q V ⋙
          CategoricalPullback.map (splitFiberMap B S hS p V) (splitFiberMap B S hS q V)
            (Deformation.Artin.evaluateSplitFiber 𝒳.val.p V)
            (Deformation.Artin.evaluateSplitFiber 𝒵.val.p V)
            (Deformation.Artin.evaluateSplitFiber 𝒴.val.p V)
            (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) V)
            (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p q) V)
            (splitEvaluationIso B S hS q V) (splitEvaluationIso B S hS p V).symm).obj
          o).iso.hom =
        ((isFibredOneMorphism B S hS p).mapPullbackFiberIso
            ((TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒵.val.p 𝒴.val.p
              (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
              (CatFiberedInGroupoids.homFunctor_comp_p p)
              (CatFiberedInGroupoids.homFunctor_comp_p q) o.base).obj o.obj).fst o.hom).inv ≫
          Functor.pullbackFiberHom
              ((TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒵.val.p 𝒴.val.p
                (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
                (CatFiberedInGroupoids.homFunctor_comp_p p)
                (CatFiberedInGroupoids.homFunctor_comp_p q) o.base).obj o.obj).iso.hom o.hom ≫
            ((isFibredOneMorphism B S hS q).mapPullbackFiberIso
              ((TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒵.val.p 𝒴.val.p
                (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
                (CatFiberedInGroupoids.homFunctor_comp_p p)
                (CatFiberedInGroupoids.homFunctor_comp_p q) o.base).obj o.obj).snd o.hom).hom :=
      rfl
    rw [hlhs]
    exact eq_isoInv_comp₃ _ _ _ _ _ key
  · intro o o' m
    refine CategoricalPullback.hom_ext ?_ ?_
    · exact isoConj_comp_inv _ _ _
    · exact isoConj_comp_inv _ _ _

/-- **The componentwise reading of the split fibre of a 2-fibre product is an equivalence.** By
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp_evaluationIso` it becomes, after
composition with the functor induced on 2-fibre products by the three evaluations of Stacks
004A, the composite of two equivalences — evaluation in the split fibre of the 2-fibre product
and the comparison of Stacks 02XI. That induced functor is itself an equivalence by Stacks
02XB (3), so the componentwise reading is one. -/
lemma isEquivalence_splitFiberTwoFibreProductComparisonApp (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    (splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q V).IsEquivalence := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)).IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  have : (Deformation.Artin.evaluateSplitFiber 𝒳.val.p V).IsEquivalence :=
    inferInstanceAs ((Functor.SplitFiber.evaluation 𝒳.val.p V).IsEquivalence)
  have : (Deformation.Artin.evaluateSplitFiber 𝒵.val.p V).IsEquivalence :=
    inferInstanceAs ((Functor.SplitFiber.evaluation 𝒵.val.p V).IsEquivalence)
  have : (Deformation.Artin.evaluateSplitFiber 𝒴.val.p V).Full :=
    inferInstanceAs ((Functor.SplitFiber.evaluation 𝒴.val.p V).Full)
  have : (Deformation.Artin.evaluateSplitFiber 𝒴.val.p V).Faithful :=
    inferInstanceAs ((Functor.SplitFiber.evaluation 𝒴.val.p V).Faithful)
  let G := CategoricalPullback.map (splitFiberMap B S hS p V) (splitFiberMap B S hS q V)
    (Deformation.Artin.evaluateSplitFiber 𝒳.val.p V)
    (Deformation.Artin.evaluateSplitFiber 𝒵.val.p V)
    (Deformation.Artin.evaluateSplitFiber 𝒴.val.p V)
    (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) V)
    (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p q) V)
    (splitEvaluationIso B S hS q V) (splitEvaluationIso B S hS p V).symm
  have : G.IsEquivalence := induced_isEquivalence_of_isEquivalence _ _ _ _ _
  have : (splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q V ⋙ G).IsEquivalence :=
    let : (Deformation.Artin.evaluateSplitFiber
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p V ⋙
        TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒵.val.p 𝒴.val.p
          (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
          (CatFiberedInGroupoids.homFunctor_comp_p p)
          (CatFiberedInGroupoids.homFunctor_comp_p q) V).IsEquivalence :=
      ((Functor.SplitFiber.fiberEquiv
          (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p V).trans
        (TwoFibreProductOver.fiberEquiv 𝒳.val.p 𝒵.val.p 𝒴.val.p
          (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
          (CatFiberedInGroupoids.homFunctor_comp_p p)
          (CatFiberedInGroupoids.homFunctor_comp_p q) V)).isEquivalence_functor
    Functor.isEquivalence_of_iso
      (splitFiberTwoFibreProductComparisonApp_evaluationIso B S hS 𝒳 𝒴 𝒵 p q V).symm
  exact Functor.isEquivalence_of_comp_right
    (splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q V) G

end AlgebraicGeometry.Stack

end
