module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonalColimitLegStage

/-!
# The lower leg of Stacks 0CMW's diagonal square at one stage of the colimit

Stacks 0CMW compares two squares of `CategoryTheory.Cat`: the canonical square of Stacks 0CMR for
the colimit of a diagram of affine stages, and the canonical square for the cone point. At one
stage of the colimit, the stagewise comparison of the 2-fibre products, followed by the change of
cospan along the colimit comparisons of Stacks 07XL with the 2-cell `η` of Stacks 0CMR for a
filler, is strict restriction to the cone point followed by evaluation of split fibres there.

## Main results

* `AlgebraicGeometry.Stack.splitFiberCospanUp_comp_twoFibreProductStage_comp_mapDiagonal_fiber`:
  the stagewise identity of the lower legs, in the cospan of fibres at the cone point.
* `AlgebraicGeometry.Stack.splitFiberCospanUp_comp_twoFibreProductStage_comp_mapDiagonal`: the
  same identity after the universe lift.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 02XA](https://stacks.math.columbia.edu/tag/02XA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] AsSmall AsSmall.up AsSmall.down
  Deformation.Artin.colimitComparison Limits.CategoricalPullback.map
  Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  Limits.CategoricalPullback.π₁ Limits.CategoricalPullback.π₂
  Bicategory.InducedBicategory Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.SplitFiber.restrict Deformation.Artin.fiberCocone
  Deformation.Artin.fiberDiagram Functor.splitPresheaf Cat.asSmallFunctor
  fiberDiagramMap Cat.twoFibreProductStage

/-- **A chain of transports on either side of two morphisms is a single transport.** A composite
`g ≫ m ≫ g'` interleaved with `eqToHom`s equals the same composite interleaved with fewer
`eqToHom`s between the same endpoints. -/
private lemma conj_chain₃_eq {C : Type*} [Category C]
    {a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆ : C}
    (e₁ : a₁ = a₂) (g : a₂ ⟶ a₃) (e₂ : a₃ = a₄) (e₃ : a₄ = a₅) (e₄ : a₅ = a₆)
    (m : a₆ ⟶ b₁) (e₅ : b₁ = b₂) (e₆ : b₂ = b₃) (e₇ : b₃ = b₄)
    (g' : b₄ ⟶ b₅) (e₈ : b₅ = b₆)
    (f₁ : a₁ = a₂) (f₂ : a₃ = a₆) (f₃ : b₁ = b₄) (f₄ : b₅ = b₆) :
    eqToHom e₁ ≫ g ≫ eqToHom e₂ ≫ eqToHom e₃ ≫ eqToHom e₄ ≫ m ≫
        eqToHom e₅ ≫ eqToHom e₆ ≫ eqToHom e₇ ≫ g' ≫ eqToHom e₈ =
      eqToHom f₁ ≫ g ≫ eqToHom f₂ ≫ m ≫ eqToHom f₃ ≫ g' ≫ eqToHom f₄ := by
  subst e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
  simp

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS))
  (f : 𝒳 ⟶ 𝒴) {I : Type v} [Category.{w} I]

/-- **The lower leg of Stacks 0CMW's diagonal square at a stage, in the cospan of fibres at the
cone point.** The stagewise comparison of the 2-fibre products of the diagrams of split fibres,
followed by the change of cospan along the colimit comparisons of Stacks 07XL with the 2-cell `η`
of Stacks 0CMR for a filler, is strict restriction to the cone point followed by evaluation of
split fibres there. -/
lemma splitFiberCospanUp_comp_twoFibreProductStage_comp_mapDiagonal_fiber
    (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    splitFiberCospanUp B S hS 𝒳 𝒴 f E j ⋙
        Cat.twoFibreProductStage
          (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)
          (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E) j ⋙
        CategoricalPullback.mapDiagonal (Deformation.Artin.colimitComparison 𝒳.val.p E d)
          (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
          (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt)
          (Deformation.Artin.colimitComparison 𝒴.val.p E d)
          (canonicalTwoCell B S hS f E d) =
      splitFiberCospanRestrict B S hS 𝒳 𝒴 f E d j ⋙
        splitFiberCospanEval B S hS 𝒳 𝒴 f d.pt := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  have hι := Deformation.Artin.colimitComparison_ι 𝒳.val.p E d j.unop
  refine CategoryTheory.Functor.ext (fun P ↦ ?_) (fun P Q m ↦ ?_)
  · refine Cat.categoricalPullback_obj_ext
      (Functor.congr_obj hι ((splitFiberCospanUp B S hS 𝒳 𝒴 f E j).obj P).fst)
      (Functor.congr_obj hι ((splitFiberCospanUp B S hS 𝒳 𝒴 f E j).obj P).snd) ?_
    have hmid := Functor.congr_hom
      (Deformation.Artin.colimitComparison_ι 𝒴.val.p E d j.unop)
      ((splitFiberCospanUp B S hS 𝒳 𝒴 f E j).obj P).iso.hom
    simp only [Functor.comp_map] at hmid
    have hdown : AsSmall.down.map ((splitFiberCospanUp B S hS 𝒳 𝒴 f E j).obj P).iso.hom =
        P.iso.hom :=
      congrArg (fun m ↦ AsSmall.down.map m)
        (CategoricalPullback.asSmallMap_obj_iso_hom _ _)
    rw [hdown] at hmid
    have hlhs : ((splitFiberCospanUp B S hS 𝒳 𝒴 f E j ⋙
          Cat.twoFibreProductStage
            (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)
            (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E) j ⋙
          CategoricalPullback.mapDiagonal (Deformation.Artin.colimitComparison 𝒳.val.p E d)
            (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
            (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt)
            (Deformation.Artin.colimitComparison 𝒴.val.p E d)
            (canonicalTwoCell B S hS f E d)).obj P).iso.hom =
        (canonicalTwoCell B S hS f E d).hom.app
            ((Cat.twoFibreProductStage
              (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)
              (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E) j).obj
            ((splitFiberCospanUp B S hS 𝒳 𝒴 f E j).obj P)).fst ≫
          (Deformation.Artin.colimitComparison 𝒴.val.p E d).map
            ((Cat.twoFibreProductStage
              (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)
              (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E) j).obj
              ((splitFiberCospanUp B S hS 𝒳 𝒴 f E j).obj P)).iso.hom ≫
          (canonicalTwoCell B S hS f E d).inv.app
            ((Cat.twoFibreProductStage
              (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)
              (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E) j).obj
            ((splitFiberCospanUp B S hS 𝒳 𝒴 f E j).obj P)).snd := rfl
    have hrhs : ((splitFiberCospanRestrict B S hS 𝒳 𝒴 f E d j ⋙
          splitFiberCospanEval B S hS 𝒳 𝒴 f d.pt).obj P).iso.hom =
        (splitEvaluationIso B S hS f d.pt).hom.app
            ((splitFiberCospanRestrict B S hS 𝒳 𝒴 f E d j).obj P).fst ≫
          (Deformation.Artin.evaluateSplitFiber 𝒴.val.p d.pt).map
            ((splitFiberCospanRestrict B S hS 𝒳 𝒴 f E d j).obj P).iso.hom ≫
          (splitEvaluationIso B S hS f d.pt).inv.app
            ((splitFiberCospanRestrict B S hS 𝒳 𝒴 f E d j).obj P).snd := rfl
    rw [Cat.twoFibreProductStage_obj_iso_hom, Functor.map_comp, Functor.map_comp,
      hmid] at hlhs
    simp only [Cat.twoFibreProductStage_obj_fst, Cat.twoFibreProductStage_obj_snd,
      CategoricalPullback.map_obj_fst, CategoricalPullback.map_obj_snd,
      canonicalTwoCell_hom_app_ι B S hS 𝒳 𝒴 f E d j P.fst,
      canonicalTwoCell_inv_app_ι B S hS 𝒳 𝒴 f E d j P.snd,
      eqToHom_map] at hlhs
    simp only [CategoricalPullback.map_obj_fst, CategoricalPullback.map_obj_snd,
      CategoricalPullback.map_obj_iso_hom, Functor.map_comp] at hrhs
    refine hlhs.trans ?_
    rw [hrhs]
    simp only [eqToIso.inv, eqToHom_app, eqToHom_map, Category.assoc, eqToHom_trans]
    exact conj_chain₃_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · refine CategoricalPullback.Hom.ext ?_ ?_
    · simp only [Functor.comp_map, CategoricalPullback.mapDiagonal_map_fst,
        Cat.twoFibreProductStage_map_fst, CategoricalPullback.map_map_fst,
        CategoricalPullback.comp_fst, Cat.categoricalPullback_eqToHom_fst]
      exact Functor.congr_hom hι (AsSmall.up.map m.fst)
    · simp only [Functor.comp_map, CategoricalPullback.mapDiagonal_map_snd,
        Cat.twoFibreProductStage_map_snd, CategoricalPullback.map_map_snd,
        CategoricalPullback.comp_snd, Cat.categoricalPullback_eqToHom_snd]
      exact Functor.congr_hom hι (AsSmall.up.map m.snd)

/-- **The lower leg of Stacks 0CMW's diagonal square at a stage.** The universe-lifted form of
`AlgebraicGeometry.Stack.splitFiberCospanUp_comp_twoFibreProductStage_comp_mapDiagonal_fiber`,
in the universe lift of the cospan of fibres at the cone point. -/
lemma splitFiberCospanUp_comp_twoFibreProductStage_comp_mapDiagonal
    (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    splitFiberCospanUp B S hS 𝒳 𝒴 f E j ⋙
        Cat.twoFibreProductStage
          (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)
          (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E) j ⋙
        CategoricalPullback.mapDiagonal
          (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
          (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
          (AsSmall.down ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
            AsSmall.up)
          (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
          (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d) =
      splitFiberCospanRestrict B S hS 𝒳 𝒴 f E d j ⋙
        splitFiberCospanEval B S hS 𝒳 𝒴 f d.pt ⋙
        fiberCospanUp B S hS 𝒳 𝒴 f d.pt := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  have hstep : CategoricalPullback.mapDiagonal
        (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
        (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
        (AsSmall.down ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
          AsSmall.up)
        (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
        (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d) =
      CategoricalPullback.mapDiagonal (Deformation.Artin.colimitComparison 𝒳.val.p E d)
          (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
          (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt)
          (Deformation.Artin.colimitComparison 𝒴.val.p E d)
          (canonicalTwoCell B S hS f E d) ⋙
        fiberCospanUp B S hS 𝒳 𝒴 f d.pt :=
    CategoricalPullback.mapDiagonal_comp_asSmallMap _ _ _ _ (canonicalTwoCell B S hS f E d)
  exact (congrArg (fun G ↦ splitFiberCospanUp B S hS 𝒳 𝒴 f E j ⋙
      Cat.twoFibreProductStage
        (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)
        (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E) j ⋙ G) hstep).trans
    (congrArg (fun G ↦ G ⋙ fiberCospanUp B S hS 𝒳 𝒴 f d.pt)
      (splitFiberCospanUp_comp_twoFibreProductStage_comp_mapDiagonal_fiber B S hS 𝒳 𝒴 f E d j))

end AlgebraicGeometry.Stack

end
