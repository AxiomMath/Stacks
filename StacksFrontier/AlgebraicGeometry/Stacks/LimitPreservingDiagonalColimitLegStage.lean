module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonalColimitLeg
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CategoricalPullbackSquareDiagonal

/-!
# Universe lifts through diagonals of changes of cospan

The universe lift `CategoryTheory.AsSmall.up` passes through the diagonal of a change of cospan: a
diagonal whose three legs are universe lifts and whose filler is the lift of a 2-cell is the
unlifted diagonal followed by the universe lift of the whole cospan. We also compute the 2-cell `η`
of the square of Stacks 0CMR at an object of a stage of the colimit, before the universe lift.

## Main results

* `CategoryTheory.Limits.CategoricalPullback.asSmallMap_obj_iso_hom`: the filling isomorphism of
  the universe lift of a cospan is the lift of the filling isomorphism.
* `CategoryTheory.Limits.CategoricalPullback.mapDiagonal_comp_asSmallMap`: the universe lift
  passes through the diagonal of a change of cospan.
* `AlgebraicGeometry.Stack.canonicalTwoCell_hom_app_ι` and
  `AlgebraicGeometry.Stack.canonicalTwoCell_inv_app_ι`: the 2-cell `η` of the square of
  Stacks 0CMR at an object of a stage, before the universe lift.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 02XA](https://stacks.math.columbia.edu/tag/02XA)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] CategoryTheory.AsSmall CategoryTheory.AsSmall.up
  CategoryTheory.AsSmall.down

namespace CategoryTheory.Limits.CategoricalPullback

universe t uX uY vX vY

variable {X : Type uX} {Y : Type uY} [Category.{vX} X] [Category.{vY} Y]

/-- **The filling isomorphism of the universe lift of a cospan is the lift of the filling
isomorphism.** -/
lemma asSmallMap_obj_iso_hom (FF : X ⥤ Y) (P : CategoricalPullback FF FF) :
    ((map FF FF AsSmall.up.{vX, uX, t} AsSmall.up.{vX, uX, t} AsSmall.up.{vY, uY, t}
        (AsSmall.down ⋙ FF ⋙ AsSmall.up.{vY, uY, t})
        (AsSmall.down ⋙ FF ⋙ AsSmall.up.{vY, uY, t})
        (eqToIso (rfl : AsSmall.up.{vX, uX, t} ⋙
          (AsSmall.down ⋙ FF ⋙ AsSmall.up.{vY, uY, t}) =
          AsSmall.up.{vX, uX, t} ⋙ (AsSmall.down ⋙ FF ⋙ AsSmall.up.{vY, uY, t})))
        (eqToIso (rfl : FF ⋙ AsSmall.up.{vY, uY, t} =
          FF ⋙ AsSmall.up.{vY, uY, t}))).obj P).iso.hom =
      AsSmall.up.{vY, uY, t}.map P.iso.hom := by
  rw [map_obj_iso_hom, eqToIso_rfl_inv_app, eqToIso_rfl_inv_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- **The universe lift passes through the diagonal of a change of cospan.** Changing the cospan
of a diagonal by functors that are themselves universe lifts, with the lift of a 2-cell for a
filler, is the unlifted change of cospan followed by the universe lift of the whole cospan. -/
lemma mapDiagonal_comp_asSmallMap {C' : Type*} {D' : Type*} [Category C'] [Category D']
    (a₀ : C' ⥤ X) (u : C' ⥤ D') (FF : X ⥤ Y) (b₀ : D' ⥤ Y) (α₀ : a₀ ⋙ FF ≅ u ⋙ b₀) :
    mapDiagonal (a₀ ⋙ AsSmall.up.{vX, uX, t}) u
        (AsSmall.down ⋙ FF ⋙ AsSmall.up.{vY, uY, t}) (b₀ ⋙ AsSmall.up.{vY, uY, t})
        (Functor.isoWhiskerRight α₀ AsSmall.up.{vY, uY, t}) =
      mapDiagonal a₀ u FF b₀ α₀ ⋙
        map FF FF AsSmall.up.{vX, uX, t} AsSmall.up.{vX, uX, t} AsSmall.up.{vY, uY, t}
          (AsSmall.down ⋙ FF ⋙ AsSmall.up.{vY, uY, t})
          (AsSmall.down ⋙ FF ⋙ AsSmall.up.{vY, uY, t})
          (eqToIso (rfl : AsSmall.up.{vX, uX, t} ⋙
            (AsSmall.down ⋙ FF ⋙ AsSmall.up.{vY, uY, t}) =
            AsSmall.up.{vX, uX, t} ⋙ (AsSmall.down ⋙ FF ⋙ AsSmall.up.{vY, uY, t})))
          (eqToIso (rfl : FF ⋙ AsSmall.up.{vY, uY, t} = FF ⋙ AsSmall.up.{vY, uY, t})) := by
  refine CategoryTheory.Functor.ext
    (fun T => Cat.categoricalPullback_obj_ext rfl rfl ?_) (fun T T' m => ?_)
  · refine Cat.eq_eqToHom_conj _ _ _ _ (heq_of_eq ?_)
    change AsSmall.up.{vY, uY, t}.map (α₀.hom.app T.fst) ≫
          AsSmall.up.{vY, uY, t}.map (b₀.map T.iso.hom) ≫
          AsSmall.up.{vY, uY, t}.map (α₀.inv.app T.snd) =
        𝟙 _ ≫ AsSmall.up.{vY, uY, t}.map (α₀.hom.app T.fst ≫ b₀.map T.iso.hom ≫
          α₀.inv.app T.snd) ≫ 𝟙 _
    simp
  · refine CategoricalPullback.Hom.ext ?_ ?_ <;>
    · simp only [Functor.comp_map, mapDiagonal_map_fst, mapDiagonal_map_snd, map_map_fst,
        map_map_snd, comp_fst, comp_snd, Cat.categoricalPullback_eqToHom_fst,
        Cat.categoricalPullback_eqToHom_snd]
      exact Cat.eq_eqToHom_conj _ _ _ _ HEq.rfl

end CategoryTheory.Limits.CategoricalPullback

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS))
  (f : 𝒳 ⟶ 𝒴) {I : Type v} [Category.{w} I]

/-- **The 2-cell `η` of the square of Stacks 0CMR at an object of a stage, before the universe
lift.** Its universe lift is `AlgebraicGeometry.Stack.canonicalTwoCellUp_hom_app_ι`. -/
lemma canonicalTwoCell_hom_app_ι (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ)
    (x : 𝒳.val.p.SplitFiber (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (canonicalTwoCell B S hS f E d).hom.app
        ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
          (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj x)) =
      eqToHom (congrArg (Deformation.Artin.evaluateSplitFiber 𝒳.val.p d.pt ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt).obj
          (Deformation.Artin.colimitDesc_ι_down_obj 𝒳.val.p E d j x)) ≫
        (splitEvaluationIso B S hS f d.pt).hom.app
          ((Functor.SplitFiber.restrict 𝒳.val.p (d.π.app j.unop)).obj x) ≫
        eqToHom (congrArg (splitFiberMap B S hS f d.pt ⋙
            Deformation.Artin.evaluateSplitFiber 𝒴.val.p d.pt).obj
          (Deformation.Artin.colimitDesc_ι_down_obj 𝒳.val.p E d j x)).symm ≫
        eqToHom (Functor.congr_obj (colimitComparison_comp_splitFiberMap B S hS f E d)
          ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
            (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj x))) :=
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  congrArg (fun m => AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w}.map m)
    (canonicalTwoCellUp_hom_app_ι.{u, v, w, max (u + 1) v w, max u v} B S hS f E d j x)

/-- **The 2-cell `η` of the square of Stacks 0CMR at an object of a stage, before the universe
lift, inverse side.** -/
lemma canonicalTwoCell_inv_app_ι (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ)
    (x : 𝒳.val.p.SplitFiber (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (canonicalTwoCell B S hS f E d).inv.app
        ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
          (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj x)) =
      eqToHom (Functor.congr_obj (colimitComparison_comp_splitFiberMap B S hS f E d)
          ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) j).toFunctor.obj
            (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj x))).symm ≫
        eqToHom (congrArg (splitFiberMap B S hS f d.pt ⋙
            Deformation.Artin.evaluateSplitFiber 𝒴.val.p d.pt).obj
          (Deformation.Artin.colimitDesc_ι_down_obj 𝒳.val.p E d j x)) ≫
        (splitEvaluationIso B S hS f d.pt).inv.app
          ((Functor.SplitFiber.restrict 𝒳.val.p (d.π.app j.unop)).obj x) ≫
        eqToHom (congrArg (Deformation.Artin.evaluateSplitFiber 𝒳.val.p d.pt ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt).obj
          (Deformation.Artin.colimitDesc_ι_down_obj 𝒳.val.p E d j x)).symm :=
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  congrArg (fun m => AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w}.map m)
    (canonicalTwoCellUp_inv_app_ι.{u, v, w, max (u + 1) v w, max u v} B S hS f E d j x)

end AlgebraicGeometry.Stack

end
