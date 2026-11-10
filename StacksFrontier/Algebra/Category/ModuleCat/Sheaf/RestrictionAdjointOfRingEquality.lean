module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactCocontinuous

/-!
# Restriction of modules is left adjoint to the direct image, for a ring equality

Let `w : X ⥤ Y` be a continuous and cocontinuous functor of sites, `O_Y` a sheaf of rings on `Y`
and `O_X` a sheaf of rings on `X` together with an equality `h : w^{-1}O_Y = O_X`, where
`w^{-1}O_Y` is the restriction of `O_Y` along `w`. The structure map `f^♯ : O_Y ⟶ {}_sw O_X` of the
ringed morphism of topoi is the transpose of `eqToHom h`, and the direct image of sheaves of
modules is `Stacks.SheafOfModules.pushforwardCocontinuous` over it. This file shows that it is
right adjoint to restriction of modules along `w`, read over `O_X` through `h`; the left adjoint
is exact.

This is the situation of a 1-morphism of algebraic stacks on the sites of Stacks 06TP, where
`h` is Stacks 06TW. A square of such functors `u' ⋙ v = v' ⋙ u` with `v`, `v'` inclusions of
subsites gives a second structure map, `Stacks.SheafOfModules.structureMapSquare`; it is again
the transpose of an equality of restricted sheaves of rings, so the same adjunction applies to
the restricted column.

## Main results

* `Stacks.SheafOfModules.RestrictRan.homEquiv_id_eq_sheafUnit`: the transpose of the identity of
  the restricted sheaf of rings is the unit structure map.
* `Stacks.SheafOfModules.RestrictRan.restrictionAdjunctionOfEq`: restriction of modules along
  `w`, read over `O_X` through `h`, is left adjoint to the direct image over the transpose of
  `eqToHom h`.
* `Stacks.SheafOfModules.structureMapSquare_homEquiv_eqToHom`: the structure map of the
  restricted column of a square is the transpose of an equality of restricted sheaves of rings
  when that of the unrestricted column is.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v r v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace Stacks.SheafOfModules

namespace RestrictRan

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (w : X ⥤ Y)
  (JX : GrothendieckTopology X) (JY : GrothendieckTopology Y)
  [w.IsContinuous JX JY] [w.IsCocontinuous JX JY] (OY : Sheaf JY RingCat.{r})
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]

/-- **The transpose of the identity is the unit structure map.** Under the adjunction between
restriction and the direct image of sheaves of rings along a continuous and cocontinuous functor,
the identity of the restricted sheaf of rings corresponds to
`Stacks.SheafOfModules.RestrictRan.sheafUnit`, the unit of the right-Kan-extension adjunction. -/
theorem homEquiv_id_eq_sheafUnit :
    (w.sheafAdjunctionCocontinuous RingCat.{r} JX JY).homEquiv OY (ringSheaf w JX JY OY)
        (𝟙 _) = sheafUnit w JX JY OY := by
  apply ObjectProperty.hom_ext
  rw [Functor.sheafAdjunctionCocontinuous_homEquiv_apply_hom]
  change ((w.op.ranAdjunction RingCat.{r}).homEquiv OY.obj (w.op ⋙ OY.obj)) (𝟙 _) =
    (w.op.ranAdjunction RingCat.{r}).unit.app OY.obj
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

variable [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]
  {OX : Sheaf JX RingCat.{r}}

/-- **Restriction of sheaves of modules is left adjoint to the direct image, for a ring
equality.** For a continuous and cocontinuous functor of sites `w` and an equality
`h : w^{-1}O_Y = O_X`, restriction of sheaves of `O_Y`-modules along `w`, read over `O_X` through
`h`, is left adjoint to `Stacks.SheafOfModules.pushforwardCocontinuous` over the transpose of
`eqToHom h`. After substituting `h` this is `Stacks.SheafOfModules.RestrictRan.sheafAdjunction`,
by `Stacks.SheafOfModules.RestrictRan.homEquiv_id_eq_sheafUnit`. -/
def restrictionAdjunctionOfEq (h : ringSheaf w JX JY OY = OX) :
    _root_.SheafOfModules.pushforward.{v} (F := w) (R := OY) (eqToHom h.symm) ⊣
      pushforwardCocontinuous.{v} w
        ((w.sheafAdjunctionCocontinuous RingCat.{r} JX JY).homEquiv OY OX (eqToHom h)) := by
  subst h
  rw [eqToHom_refl, homEquiv_id_eq_sheafUnit]
  exact sheafAdjunction.{v} w JX JY OY

end RestrictRan

section Square

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] {J' : GrothendieckTopology C'}
  {J : GrothendieckTopology C} {K' : GrothendieckTopology D'} {K : GrothendieckTopology D}
  {u' : C' ⥤ D'} {u : C ⥤ D} {v' : C' ⥤ C} {v : D' ⥤ D} [u.IsContinuous J K]
  [u.IsCocontinuous J K] [u'.IsContinuous J' K'] [u'.IsCocontinuous J' K']
  [v.IsContinuous K' K] [v.IsCocontinuous K' K] [v'.IsContinuous J' J] [v'.IsCocontinuous J' J]
  [∀ G : Cᵒᵖ ⥤ RingCat.{r}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ RingCat.{r}, u'.op.HasPointwiseRightKanExtension G]
  {OC : Sheaf J RingCat.{r}} {OD : Sheaf K RingCat.{r}}

omit [v.IsCocontinuous K' K] [v'.IsCocontinuous J' J] in
/-- **The structure map of the restricted column of a square is the transpose of an equality.**
Let `u' ⋙ v = v' ⋙ u` be a square of continuous and cocontinuous functors of sites and
`h : u^{-1}O_D = O_C`. Then the structure map `Stacks.SheafOfModules.structureMapSquare` built
from the transpose of `eqToHom h` is the transpose of `eqToHom h'`, for the equality
`h' : (u')^{-1}(v^{-1}O_D) = (v')^{-1}O_C` of restricted sheaves of rings. Both are checked on the
legs of the limit cones computing the right Kan extension along `u'`, where each is a restriction
map of `O_D` along an `eqToHom`. -/
theorem structureMapSquare_homEquiv_eqToHom (hsq : u' ⋙ v = v' ⋙ u)
    (h : inverseImageRing J K u OD = OC)
    (h' : inverseImageRing J' K' u' (inverseImageRing K' K v OD) = inverseImageRing J' J v' OC) :
    structureMapSquare (J' := J') (K' := K')
        ((u.sheafAdjunctionCocontinuous RingCat.{r} J K).homEquiv OD OC (eqToHom h)) hsq =
      (u'.sheafAdjunctionCocontinuous RingCat.{r} J' K').homEquiv _ _ (eqToHom h') := by
  subst h
  apply ObjectProperty.hom_ext
  rw [Functor.sheafAdjunctionCocontinuous_homEquiv_apply_hom]
  ext V' : 2
  refine ran_hom_ext u'.op _ (fun j => ?_)
  have e1 := structureBaseChange_π (J' := J') (OC := inverseImageRing J K u OD) hsq V' j
  have e2 := RestrictRan.homEquiv_app_comp_ranπ u'.op (G := (inverseImageRing K' K v OD).obj)
    (F := (inverseImageRing J' J v' (inverseImageRing J K u OD)).obj) (eqToHom h').hom V' j
  have e3 := RestrictRan.homEquiv_app_comp_ranπ u.op (G := OD.obj)
    (F := (inverseImageRing J K u OD).obj)
    (𝟙 (u.op ⋙ OD.obj)) (v.op.obj V') (squareIndex hsq j)
  have e4 : (eqToHom h').hom = eqToHom (congrArg (sheafToPresheaf J' RingCat.{r}).obj h') :=
    eqToHom_map (sheafToPresheaf J' RingCat.{r}) h'
  refine ((Category.assoc _ _ _).trans ((congrArg (fun t => _ ≫ t) e1).trans ?_)).trans e2.symm
  rw [eqToHom_refl, Functor.sheafAdjunctionCocontinuous_homEquiv_apply_hom]
  refine e3.trans ?_
  rw [e4, eqToHom_app]
  simp only [squareIndex, Stacks.Sites.CocontinuousExchange.twoSquare]
  simp only [StructuredArrow.mk_hom_eq_self, TwoSquare.op, Functor.map_comp]
  refine (Category.comp_id (obj := RingCat.{r}) _).trans ?_
  refine congrArg (fun t => OD.obj.map (v.op.map j.hom) ≫ t) ?_
  simp only [NatTrans.op_app, eqToHom_app, eqToHom_op, eqToHom_map]
  rfl

end Square

end Stacks.SheafOfModules
