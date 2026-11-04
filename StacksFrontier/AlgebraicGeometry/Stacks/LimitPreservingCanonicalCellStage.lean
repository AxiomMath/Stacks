module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalCell
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonalColimit

/-!
# The canonical square of Stacks 0CMR read at one stage of the colimit

The two squares that Stacks 0CMW compares have the colimit `colim 𝒳_{Uᵢ}` of the diagram of
split fibres for their common upper left corner, and every object of that colimit is the image
of an object of a stage. So each of the two comparisons of
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer`
between them is determined by what it does at a stage, and this file computes the three pieces
of the canonical square of Stacks 0CMR there:

* the colimit comparison `colim 𝒳_{Uᵢ} ⟶ 𝒳_U` restricted to a stage is restriction to the cone
  point followed by evaluation (`AlgebraicGeometry.Stack` has this already at the level of
  `CategoryTheory.Cat`; here it is given after the universe lift, together with the two forms of
  its action on morphisms that a transport argument needs);
* the 2-cell `η` of the square, at an object of a stage, is the base-change comparison
  `AlgebraicGeometry.Stack.splitEvaluationIso` of the fibred 1-morphism at the restricted
  object, conjugated by the transports that the colimit descent contributes;
* the comparison `AlgebraicGeometry.Stack.colimitSplitFiberTwoFibreProductComparison` of the
  lower left corners, restricted to a stage, is the stagewise comparison followed by the
  stagewise comparison into the 2-fibre product of the colimits.

## Main results

* `Deformation.Artin.ι_comp_colimitComparison_comp_up`: the lifted colimit comparison at a
  stage.
* `AlgebraicGeometry.Stack.canonicalTwoCellUp_hom_app_ι` and
  `…canonicalTwoCellUp_inv_app_ι`: the 2-cell `η` of Stacks 0CMR at an object of a stage.
* `AlgebraicGeometry.Stack.ι_comp_colimitSplitFiberTwoFibreProductComparison`: the comparison of
  the lower left corners at a stage.

## Implementation notes

`AlgebraicGeometry.Stack.canonicalTwoCellUp_app_ι` already pins the 2-cell at a stage, but as a
heterogeneous equality, which is what the determinacy argument of
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalDiagonal` needs. Transporting a
square along it instead needs the homogeneous form, with the transports written out; that is
what is proved here, from the definition of
`AlgebraicGeometry.Stack.canonicalTwoCell` rather than from the heterogeneous statement.

The helper lemmas of `Deformation.Artin` are stated for an arbitrary fibred functor rather than
for the structure functor of a category fibred in groupoids: the three legs of a square of
Stacks 0CMR live over `𝒳`, `𝒴` and the 2-fibre product, and instantiating a statement whose
`CategoryTheory.Functor.IsFibered` instance is a `letI` of its own binder at three different
functors is what makes the unifier diverge.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- **A natural transformation read at two equal objects.** The two components differ by the
transports the equality induces on the source and the target. -/
lemma natTrans_app_eq_of_obj_eq {D E : Type*} [Category D] [Category E] {F G : D ⥤ E}
    (σ : F ⟶ G) {a b : D} (h : a = b) :
    σ.app a = eqToHom (congrArg F.obj h) ≫ σ.app b ≫ eqToHom (congrArg G.obj h).symm := by
  subst h
  simp

/-- The identity 2-cell of a change of cospan, read at an object. Stated because `simp` does not
reduce `CategoryTheory.eqToIso` at a reflexivity proof that it has to look through a chain of
universe lifts to recognize. -/
lemma eqToIso_rfl_hom_app {D E : Type*} [Category D] [Category E] (F : D ⥤ E) (Y : D) :
    (eqToIso (rfl : F = F)).hom.app Y = 𝟙 _ := rfl

/-- The identity 2-cell of a change of cospan, read at an object, on the inverse side. -/
lemma eqToIso_rfl_inv_app {D E : Type*} [Category D] [Category E] (F : D ⥤ E) (Y : D) :
    (eqToIso (rfl : F = F)).inv.app Y = 𝟙 _ := rfl

end CategoryTheory

namespace Deformation.Artin

universe t v w uC vC uX vX

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion CategoryTheory.Functor.SplitFiber.restrict
  Deformation.Artin.fiberCocone Deformation.Artin.fiberDiagram
  CategoryTheory.Functor.splitPresheaf CategoryTheory.Cat.asSmallFunctor

variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
  (pX : X ⥤ C) [pX.IsFibered] {I : Type v} [Category.{w} I]

/-- **The object equality underlying the colimit descent at a stage.** The descent of the
restriction cocone of Stacks 004A carries the image of an object `x` of a stage to the
restriction of `x` to the cone point. -/
lemma colimitDesc_ι_down_obj (E : I ⥤ C) (d : Cone E) (j : Iᵒᵖ)
    (x : pX.SplitFiber (E.obj j.unop)) :
    ((colimit.desc (fiberDiagram pX E) (fiberCocone pX E d)).toFunctor ⋙
          AsSmall.down.{vX, max uC uX vC, max v w}).obj
        ((colimit.ι (fiberDiagram pX E) j).toFunctor.obj
          (AsSmall.up.{vX, max uC uX vC, max v w}.obj x)) =
      (Functor.SplitFiber.restrict pX (d.π.app j.unop)).obj x :=
  congrArg AsSmall.down.{vX, max uC uX vC, max v w}.obj
    (Functor.congr_obj
      (congrArg Cat.Hom.toFunctor (colimit.ι_desc (fiberCocone pX E d) j))
      (AsSmall.up.{vX, max uC uX vC, max v w}.obj x))

/-- **The colimit comparison at a stage, after the universe lift.** This is
`Deformation.Artin.colimitComparison_ι` in the shape the squares of Stacks 0CMR are stated in,
where every corner has been lifted. -/
lemma ι_comp_colimitComparison_comp_up (E : I ⥤ C) (d : Cone E) (j : Iᵒᵖ) :
    (colimit.ι (fiberDiagram pX E) j).toFunctor ⋙
        (colimitComparison pX E d ⋙ AsSmall.up.{vX, uX, t}) =
      AsSmall.down.{vX, max uC uX vC, max v w} ⋙
        Functor.SplitFiber.restrict pX (d.π.app j.unop) ⋙
        evaluateSplitFiber pX d.pt ⋙ AsSmall.up.{vX, uX, t} := by
  rw [← Functor.assoc, colimitComparison_ι pX E d j.unop]
  rfl

/-- **The lifted colimit comparison on a morphism coming from a stage.** The transports are the
ones `Deformation.Artin.ι_comp_colimitComparison_comp_up` induces; the statement is in the shape
the components are left in after the two universe lifts have been separated, which is what lets
it be used as a rewrite inside a 2-fibre product. -/
lemma up_map_colimitComparison_map_ι_map (E : I ⥤ C) (d : Cone E) (j : Iᵒᵖ)
    {a b : ↑((fiberDiagram pX E).obj j)} (g : a ⟶ b) :
    AsSmall.up.{vX, uX, t}.map ((colimitComparison pX E d).map
        ((colimit.ι (fiberDiagram pX E) j).toFunctor.map g)) =
      eqToHom (Functor.congr_obj (ι_comp_colimitComparison_comp_up.{t} pX E d j) a) ≫
        AsSmall.up.{vX, uX, t}.map ((evaluateSplitFiber pX d.pt).map
          ((Functor.SplitFiber.restrict pX (d.π.app j.unop)).map
            (AsSmall.down.{vX, max uC uX vC, max v w}.map g))) ≫
        eqToHom (Functor.congr_obj (ι_comp_colimitComparison_comp_up.{t} pX E d j) b).symm :=
  Functor.congr_hom (ι_comp_colimitComparison_comp_up.{t} pX E d j) g

/-- **The lifted colimit comparison on a transport.** -/
lemma up_map_colimitComparison_map_eqToHom (E : I ⥤ C) (d : Cone E)
    {A A' : ↑(colimit (fiberDiagram pX E))} (h : A = A') :
    AsSmall.up.{vX, uX, t}.map ((colimitComparison pX E d).map (eqToHom h)) =
      eqToHom (congrArg (colimitComparison pX E d ⋙ AsSmall.up.{vX, uX, t}).obj h) := by
  subst h
  simp

end Deformation.Artin

namespace AlgebraicGeometry.Stack

universe u v w uX vX

attribute [local implicit_reducible] Bicategory.InducedBicategory Functor.Fiber
  Functor.Fiber.fiberInclusion Functor.SplitFiber.restrict Deformation.Artin.fiberCocone
  Deformation.Artin.fiberDiagram Functor.splitPresheaf Cat.asSmallFunctor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S hS)}
  {I : Type v} [Category.{w} I]

/-- **The 2-cell `η` of the square of Stacks 0CMR at an object of a stage.** It is the
base-change comparison `AlgebraicGeometry.Stack.splitEvaluationIso` of the fibred 1-morphism at
the restriction of the object to the cone point, conjugated by the transports the colimit
descent contributes. This is
`AlgebraicGeometry.Stack.canonicalTwoCellUp_app_ι` read homogeneously. -/
lemma canonicalTwoCellUp_hom_app_ι (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS) (d : Cone E)
    (j : Iᵒᵖ) (x : 𝒳.val.p.SplitFiber (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (canonicalTwoCellUp.{u, v, w, uX, vX} B S hS f E d).hom.app
        ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
          (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj x)) =
      AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}.map
        (eqToHom (congrArg (Deformation.Artin.evaluateSplitFiber 𝒳.val.p d.pt ⋙
              Functor.fiberFunctorOfCompEq
                (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt).obj
            (Deformation.Artin.colimitDesc_ι_down_obj 𝒳.val.p E d j x)) ≫
          (splitEvaluationIso B S hS f d.pt).hom.app
            ((Functor.SplitFiber.restrict 𝒳.val.p (d.π.app j.unop)).obj x) ≫
          eqToHom (congrArg (splitFiberMap B S hS f d.pt ⋙
              Deformation.Artin.evaluateSplitFiber 𝒴.val.p d.pt).obj
            (Deformation.Artin.colimitDesc_ι_down_obj 𝒳.val.p E d j x)).symm ≫
          eqToHom (Functor.congr_obj (colimitComparison_comp_splitFiberMap B S hS f E d)
            ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
              (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj x)))) := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  show AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}.map
      ((Functor.isoWhiskerLeft
          ((colimit.desc (Deformation.Artin.fiberDiagram 𝒳.val.p E)
            (Deformation.Artin.fiberCocone 𝒳.val.p E d)).toFunctor ⋙ AsSmall.down)
          (splitEvaluationIso B S hS f d.pt) ≪≫
        eqToIso (colimitComparison_comp_splitFiberMap B S hS f E d)).hom.app _) = _
  rw [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, eqToIso.hom,
    Functor.whiskerLeft_app, eqToHom_app,
    natTrans_app_eq_of_obj_eq (splitEvaluationIso B S hS f d.pt).hom
      (Deformation.Artin.colimitDesc_ι_down_obj 𝒳.val.p E d j x)]
  simp only [Category.assoc]

/-- **The 2-cell `η` of the square of Stacks 0CMR at an object of a stage, inverse side.** -/
lemma canonicalTwoCellUp_inv_app_ι (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS) (d : Cone E)
    (j : Iᵒᵖ) (x : 𝒳.val.p.SplitFiber (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (canonicalTwoCellUp.{u, v, w, uX, vX} B S hS f E d).inv.app
        ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
          (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj x)) =
      AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}.map
        (eqToHom (Functor.congr_obj (colimitComparison_comp_splitFiberMap B S hS f E d)
            ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
              (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj x))).symm ≫
          eqToHom (congrArg (splitFiberMap B S hS f d.pt ⋙
              Deformation.Artin.evaluateSplitFiber 𝒴.val.p d.pt).obj
            (Deformation.Artin.colimitDesc_ι_down_obj 𝒳.val.p E d j x)) ≫
          (splitEvaluationIso B S hS f d.pt).inv.app
            ((Functor.SplitFiber.restrict 𝒳.val.p (d.π.app j.unop)).obj x) ≫
          eqToHom (congrArg (Deformation.Artin.evaluateSplitFiber 𝒳.val.p d.pt ⋙
              Functor.fiberFunctorOfCompEq
                (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt).obj
            (Deformation.Artin.colimitDesc_ι_down_obj 𝒳.val.p E d j x)).symm) := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  show AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}.map
      ((Functor.isoWhiskerLeft
          ((colimit.desc (Deformation.Artin.fiberDiagram 𝒳.val.p E)
            (Deformation.Artin.fiberCocone 𝒳.val.p E d)).toFunctor ⋙ AsSmall.down)
          (splitEvaluationIso B S hS f d.pt) ≪≫
        eqToIso (colimitComparison_comp_splitFiberMap B S hS f E d)).inv.app _) = _
  rw [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv, eqToIso.inv,
    Functor.whiskerLeft_app, eqToHom_app,
    natTrans_app_eq_of_obj_eq (splitEvaluationIso B S hS f d.pt).inv
      (Deformation.Artin.colimitDesc_ι_down_obj 𝒳.val.p E d j x)]

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
    (BigFppfOver B S hS))
  (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴) {I : Type v} [Category.{w} I]

/-- **The comparison of the lower left corners of the two squares of Stacks 0CMW, restricted to
a stage.** It is the stagewise comparison of
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparison` followed by the stagewise
comparison `CategoryTheory.Cat.twoFibreProductStage` into the 2-fibre product of the
colimits. -/
lemma ι_comp_colimitSplitFiberTwoFibreProductComparison (E : I ⥤ BigFppfOver B S hS)
    (j : Iᵒᵖ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (colimit.ι (Deformation.Artin.fiberDiagram
          (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E) j).toFunctor ⋙
        colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E =
      ((splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E).app j).toFunctor ⋙
        Cat.twoFibreProductStage
          (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
          (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E) j := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  rw [show colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E =
      (colimMap (splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E)).toFunctor ⋙
        Cat.colimitTwoFibreProductComparison
          (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
          (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E) from rfl,
    ← Functor.assoc, Cat.ι_colimMap_toFunctor, Functor.assoc,
    Cat.colimitTwoFibreProductComparison_ι]

end AlgebraicGeometry.Stack

end
