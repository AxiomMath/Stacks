module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonalColimitLegIso

/-!
# The fillers of the two squares of Stacks 0CMW agree through the three comparisons

The square of Stacks 0CMR for the relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` and the square of
relative diagonals of the square of `f` are compared by `K` on their lower left corners
(`AlgebraicGeometry.Stack.colimitSplitFiberTwoFibreProductComparison`), by `M` on their lower
right ones (`AlgebraicGeometry.Stack.diagonalFiberPullback`) and by `iu`, `ip`, `ib` on their
three legs. This file proves the last input of
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer`: the
filler of the diagonal square is the filler of `Δ`'s square read through those comparisons.

The filler of the diagonal square is the identity in both components
(`CategoryTheory.Limits.CategoricalPullback.diagonalSquareFiller`), so at an object of a stage the
identity to prove is that the right-hand composite collapses. It does because the base-change
comparison of the diagonal and the comparison of Stacks 02XI are, on the image of the diagonal,
inverse chosen-pullback comparisons of one and the same object of the fibre at the cone point:
`AlgebraicGeometry.Stack.diagonalLegFiberIso_inv_app_fst` produces
`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids` and
`AlgebraicGeometry.Stack.diagonalFiberCompare_map_splitEvaluationIso_hom_app_fst` produces its
inverse, at the same object and the same morphism, so the two cancel.

## Implementation notes

The two components are proved separately because the single `simp only` that normalizes one of
them exhausts the heartbeat budget of a declaration on its own; they are then assembled by
`CategoryTheory.Limits.CategoricalPullback.hom_ext`.

Inside that `simp only` the two leading rewrites have to be simp entries rather than `rw` steps:
the goal is stated at an object of the form `colimMap … (ι … a)`, which
`AlgebraicGeometry.Stack.diagonalLegIso_inv_app_ι` only describes after
`CategoryTheory.natTrans_app_eq_of_obj_eq` has moved it to `ι … (… a)`, and `rw` cannot abstract
either occurrence.

The final cancellation of the two chosen-pullback comparisons is a private term-mode lemma
applied with `exact` rather than a further `simp` step. The two comparisons are one and the same
isomorphism, but its type mentions the chosen pullback of the fibre through
`CategoryTheory.TwoFibreProductOver.structureFunctor` on one side of the goal and through
`AlgebraicGeometry.BigFppfOver.twoFibreProduct` on the other, so `CategoryTheory.Functor.map_comp`
is not applicable at `implicit` transparency: the composite it would produce is type-correct only
at default transparency, which is where `exact` elaborates.

The quantified form is deduced from the stagewise one by
`CategoryTheory.Cat.exists_stage_obj_of_colimit`, every object of the colimit being the image of
an object of a stage. Its proof installs no `CategoryTheory.Functor.IsFibered` instance: such an
instance would enter as a local definition rather than as the term the statement carries, and
comparing the two makes the concluding unification diverge.

## Main results

* `AlgebraicGeometry.Stack.diagonalFillerCoherence`: the filler of the square of relative
  diagonals of `f`'s square is the filler of `Δ`'s square conjugated by `ip`, `ib` and `iu`. This
  is the hypothesis `hα` of
  `CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer` for
  the two squares of Stacks 0CMW.
* `AlgebraicGeometry.Stack.diagonalFillerCoherence_ι_fst` and `…_snd`: its two components at an
  object of a stage.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] AsSmall AsSmall.up AsSmall.down
  Bicategory.InducedBicategory Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.SplitFiber.restrict Deformation.Artin.fiberCocone
  Deformation.Artin.fiberDiagram Functor.splitPresheaf Cat.asSmallFunctor
  Deformation.Artin.colimitComparison Deformation.Artin.evaluateSplitFiber
  BigFppfOver.twoFibreProduct BasedCategory.ofFunctor Functor.fiberMap

/-- **An isomorphism and its inverse cancel across a chain of transports.** Stated in term mode,
and applied with `exact`, because the two occurrences of the isomorphism in the goal it closes
have types that agree only at default transparency; a rewriting tactic cannot merge the two
images under the functor. -/
private lemma id_eq_eqToHom_map_inv_comp_map_hom {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E)
    {P Q P' : D} (A : P ≅ Q) (ea : P = P') {Z Z₁ : E} (e₁ : Z = Z₁) (e₂ : Z₁ = F.obj Q)
    (e₃ : F.obj P' = F.obj P) (e₄ : F.obj Q = Z) :
    𝟙 Z = eqToHom e₁ ≫ (eqToHom e₂ ≫ F.map (A.inv ≫ eqToHom ea)) ≫
      eqToHom e₃ ≫ F.map A.hom ≫ eqToHom e₄ := by
  subst ea
  have h : F.map A.inv ≫ F.map A.hom = 𝟙 (F.obj Q) := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc,
    reassoc_of% h, eqToHom_trans, eqToHom_refl]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS))
  (f : 𝒳 ⟶ 𝒴) {I : Type v} [Category.{w} I]

/-- The image of an object of a stage under the colimit of the diagonal's fibre maps is its image
under the fibre map of that stage, pushed into the colimit. -/
private lemma colimMap_diagonal_obj_eq (E : I ⥤ BigFppfOver B S hS) (j : Iᵒᵖ)
    (y₀ : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.SplitFiber (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
          (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E)).toFunctor.obj
        ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
          (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀)) =
      (colimit.ι (Deformation.Artin.fiberDiagram
          (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E) j).toFunctor.obj
        (((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
          (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E).app j).toFunctor.obj
          (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀)) :=
  Functor.congr_obj (Cat.ι_colimMap_toFunctor
      (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
        (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E) j)
      (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀)

/-- **The first component of the coherence of the two fillers, at an object of a stage.** On the
image of the diagonal the base-change comparison of the diagonal (through the comparison `M` of
Stacks 02XI) and the first component of `ib` are inverse chosen-pullback comparisons of one and
the same object of the fibre at the cone point, so the composite is the identity -- which is the
first component of the filler of the diagonal square. -/
lemma diagonalFillerCoherence_ι_fst (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ)
    (y₀ : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.SplitFiber (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    ((CategoricalPullback.diagonalSquareFiller
          (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
          (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
          (AsSmall.down ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
            AsSmall.up)
          (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
          (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d)).hom.app
        ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
          (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))).fst =
      ((diagonalFiberLegIso B S hS 𝒳 𝒴 f d.pt).inv.app
            ((Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up).obj
              ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
                (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) ≫
          (diagonalFiberPullback B S hS 𝒳 𝒴 f d.pt).map
            ((canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
              (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E d).hom.app
              ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
                (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) ≫
          (diagonalLegIso B S hS 𝒳 𝒴 f E d).inv.app
            ((colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
                (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E)).toFunctor.obj
              ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
                (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) ≫
          (CategoricalPullback.mapDiagonal
              (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
              (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
                B S hS f E)).toFunctor
              (AsSmall.down ⋙
                Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
                AsSmall.up)
              (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
              (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d)).map
            ((eqToIso (BigFppfOver.colimMap_twoFibreProductDiagonal_comp_comparison.{u, v, w}
              B S hS 𝒳 𝒴 f E)).hom.app
              ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
                (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀)))).fst := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  let := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  simp only [natTrans_app_eq_of_obj_eq (diagonalLegIso B S hS 𝒳 𝒴 f E d).inv
      (colimMap_diagonal_obj_eq B S hS 𝒳 𝒴 f E j y₀),
    diagonalLegIso_inv_app_ι, CategoricalPullback.comp_fst,
    Cat.categoricalPullback_eqToHom_fst,
    CategoricalPullback.diagonalSquareFiller_hom_app_fst, eqToIso.inv, eqToIso.hom,
    CategoryTheory.eqToHom_app, diagonalFiberPullback_map_canonicalTwoCellUp_hom_app_fst,
    diagonalLegFiberIso_inv_app_fst, diagonalFiberLegIso, canonicalTwoCell_hom_app_ι,
    Functor.map_comp, eqToHom_map, Functor.SplitFiber.restrict_obj_base,
    Functor.SplitFiber.restrict_obj_obj, Functor.SplitFiber.restrict_obj_hom,
    diagonalFiberCompare_map_splitEvaluationIso_hom_app_fst,
    diagonalLegRestrict_obj_fiberDiagramMap_obj, diagonalLegRestrict_obj_fiberDiagramMap_hom,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  exact id_eq_eqToHom_map_inv_comp_map_hom _ _ _ _ _ _ _

/-- The second component of
`AlgebraicGeometry.Stack.diagonalFillerCoherence_ι_fst`, with the second factor of the 2-fibre
product. -/
lemma diagonalFillerCoherence_ι_snd (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ)
    (y₀ : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.SplitFiber (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    ((CategoricalPullback.diagonalSquareFiller
          (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
          (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
          (AsSmall.down ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
            AsSmall.up)
          (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
          (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d)).hom.app
        ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
          (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))).snd =
      ((diagonalFiberLegIso B S hS 𝒳 𝒴 f d.pt).inv.app
            ((Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up).obj
              ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
                (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) ≫
          (diagonalFiberPullback B S hS 𝒳 𝒴 f d.pt).map
            ((canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
              (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E d).hom.app
              ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
                (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) ≫
          (diagonalLegIso B S hS 𝒳 𝒴 f E d).inv.app
            ((colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
                (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E)).toFunctor.obj
              ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
                (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) ≫
          (CategoricalPullback.mapDiagonal
              (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
              (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
                B S hS f E)).toFunctor
              (AsSmall.down ⋙
                Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
                AsSmall.up)
              (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
              (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d)).map
            ((eqToIso (BigFppfOver.colimMap_twoFibreProductDiagonal_comp_comparison.{u, v, w}
              B S hS 𝒳 𝒴 f E)).hom.app
              ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
                (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀)))).snd := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  let := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  simp only [natTrans_app_eq_of_obj_eq (diagonalLegIso B S hS 𝒳 𝒴 f E d).inv
      (colimMap_diagonal_obj_eq B S hS 𝒳 𝒴 f E j y₀),
    diagonalLegIso_inv_app_ι, CategoricalPullback.comp_snd,
    Cat.categoricalPullback_eqToHom_snd,
    CategoricalPullback.diagonalSquareFiller_hom_app_snd, eqToIso.inv, eqToIso.hom,
    CategoryTheory.eqToHom_app, diagonalFiberPullback_map_canonicalTwoCellUp_hom_app_snd,
    diagonalLegFiberIso_inv_app_snd, diagonalFiberLegIso, canonicalTwoCell_hom_app_ι,
    Functor.map_comp, eqToHom_map, Functor.SplitFiber.restrict_obj_base,
    Functor.SplitFiber.restrict_obj_obj, Functor.SplitFiber.restrict_obj_hom,
    diagonalFiberCompare_map_splitEvaluationIso_hom_app_snd,
    diagonalLegRestrict_obj_fiberDiagramMap_obj, diagonalLegRestrict_obj_fiberDiagramMap_hom,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  exact id_eq_eqToHom_map_inv_comp_map_hom _ _ _ _ _ _ _

/-- **The coherence of the two fillers, at an object of a stage.** The two components of
`AlgebraicGeometry.Stack.diagonalFillerCoherence_ι_fst` and `…_snd` assembled by
`CategoryTheory.Limits.CategoricalPullback.hom_ext`. -/
lemma diagonalFillerCoherence_ι (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ)
    (y₀ : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.SplitFiber (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (CategoricalPullback.diagonalSquareFiller
          (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
          (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
          (AsSmall.down ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
            AsSmall.up)
          (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
          (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d)).hom.app
        ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
          (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀)) =
      (diagonalFiberLegIso B S hS 𝒳 𝒴 f d.pt).inv.app
            ((Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up).obj
              ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
                (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) ≫
          (diagonalFiberPullback B S hS 𝒳 𝒴 f d.pt).map
            ((canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
              (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E d).hom.app
              ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
                (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) ≫
          (diagonalLegIso B S hS 𝒳 𝒴 f E d).inv.app
            ((colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
                (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E)).toFunctor.obj
              ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
                (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) ≫
          (CategoricalPullback.mapDiagonal
              (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
              (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
                B S hS f E)).toFunctor
              (AsSmall.down ⋙
                Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
                AsSmall.up)
              (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
              (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d)).map
            ((eqToIso (BigFppfOver.colimMap_twoFibreProductDiagonal_comp_comparison.{u, v, w}
              B S hS 𝒳 𝒴 f E)).hom.app
              ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
                (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))) :=
  CategoricalPullback.hom_ext (diagonalFillerCoherence_ι_fst B S hS 𝒳 𝒴 f E d j y₀)
    (diagonalFillerCoherence_ι_snd B S hS 𝒳 𝒴 f E d j y₀)

/-- **The coherence hypothesis `hα` of the transfer lemma for the two squares of Stacks 0CMW.**
The filler of the square of relative diagonals of `f`'s square is the filler of the square of
`Δ : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` read through the comparison `ip` of the lower right legs, the
comparison `M` of the lower right corners, the comparison `ib` of the lower legs and the
comparison `iu` of the left legs.

It is checked at an object of a stage of the colimit, every object of the colimit being of that
form by `CategoryTheory.Cat.exists_stage_obj_of_colimit`; no filteredness is needed. -/
lemma diagonalFillerCoherence (E : I ⥤ BigFppfOver B S hS) (d : Cone E) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    ∀ x : ↑(colimit (Deformation.Artin.fiberDiagram 𝒳.val.p E)),
      (CategoricalPullback.diagonalSquareFiller
            (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
            (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
            (AsSmall.down ⋙
              Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
              AsSmall.up)
            (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
            (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d)).hom.app x =
        (diagonalFiberLegIso B S hS 𝒳 𝒴 f d.pt).inv.app
            ((Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up).obj x) ≫
          (diagonalFiberPullback B S hS 𝒳 𝒴 f d.pt).map
            ((canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
              (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E d).hom.app x) ≫
          (diagonalLegIso B S hS 𝒳 𝒴 f E d).inv.app
            ((colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
              (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E)).toFunctor.obj x) ≫
          (CategoricalPullback.mapDiagonal
              (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
              (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
                B S hS f E)).toFunctor
              (AsSmall.down ⋙
                Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
                AsSmall.up)
              (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
              (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d)).map
            ((eqToIso (BigFppfOver.colimMap_twoFibreProductDiagonal_comp_comparison.{u, v, w}
              B S hS 𝒳 𝒴 f E)).hom.app x) :=
  fun x => by
    let := hasColimitsOfSize_sSet_fiberDiagram.{u, v, w}
    obtain ⟨j, y, rfl⟩ := Cat.exists_stage_obj_of_colimit.{u + 1, v, w} _ x
    obtain ⟨y₀, rfl⟩ :
        ∃ y₀, AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀ = y :=
      ⟨AsSmall.down.{max u v, max (u + 1) v w, max v w}.obj y, rfl⟩
    exact diagonalFillerCoherence_ι B S hS 𝒳 𝒴 f E d j y₀

end AlgebraicGeometry.Stack

end
