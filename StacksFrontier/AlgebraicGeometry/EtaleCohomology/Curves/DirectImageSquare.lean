module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreFunctionField

/-!
# Direct images along a commutative square of schemes

Let `i' ≫ p = a ≫ i` be a commutative square of schemes, with `i : Y ⟶ X`, `i' : Y' ⟶ X'`,
`p : X' ⟶ X` and `a : Y' ⟶ Y`. For an étale `X`-scheme `U` there is a natural morphism of étale
`Y'`-schemes `(U ×_X X') ×_{X'} Y' ⟶ (U ×_X Y) ×_Y Y'`, and restriction along it gives, for every
abelian sheaf `F` on `Y'_ét`, a morphism of sheaves on `X_ét`

`i_* a_* F ⟶ p_* i'_* F`.

For `F = 𝐆_{m,Y'}`, preceded by the comparison `𝐆_{m,Y} ⟶ a_* 𝐆_{m,Y'}`, this is the morphism
`i_* 𝐆_{m,Y} ⟶ p_* i'_* 𝐆_{m,Y'}` restricting invertible functions; it is compatible with the
comparisons `𝐆_{m,X} ⟶ i_* 𝐆_{m,Y}` and `𝐆_{m,X'} ⟶ i'_* 𝐆_{m,Y'}`. Along the generic points of
two curves this is the first square of the morphism between their divisor sequences.

## Main definitions

* `smallEtaleBaseChangeSquare`: the natural isomorphism `(U ×_X X') ×_{X'} Y' ≅ (U ×_X Y) ×_Y Y'`.
* `etaleDirectImageSquareMap`: `i_* a_* F ⟶ p_* i'_* F`.
* `multiplicativeDirectImageSquareMap`: `i_* 𝐆_{m,Y} ⟶ p_* i'_* 𝐆_{m,Y'}`.
* `genericPointMap`: for a flat morphism `p : X' ⟶ X` of irreducible schemes, the morphism
  `Spec K(X') ⟶ Spec K(X)` of generic points, which with the two generic point inclusions forms a
  commutative square (`genericPointInclusion_comp_eq_genericPointMap_comp`).

## Main results

* `multiplicativeDirectImageComparison_comp_multiplicativeDirectImageSquareMap`: the square with
  the two comparison morphisms commutes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}} {i : Y ⟶ X} {i' : Y' ⟶ X'} {p : X' ⟶ X} {a : Y' ⟶ Y}
  (h : i' ≫ p = a ≫ i)

/-- **The natural isomorphism `(U ×_X X') ×_{X'} Y' ≅ (U ×_X Y) ×_Y Y'` of étale `Y'`-schemes**
attached to a commutative square `i' ≫ p = a ≫ i`: both are `U ×_X Y'`. -/
def smallEtaleBaseChangeSquare :
    smallEtaleBaseChange p ⋙ smallEtaleBaseChange i' ≅
      smallEtaleBaseChange i ⋙ smallEtaleBaseChange a :=
  (smallEtaleBaseChangeComp' i' p (i' ≫ p) rfl).symm ≪≫ smallEtaleBaseChangeComp' a i (i' ≫ p) h

/-- The underlying morphism of schemes of `Stacks.EtaleCohomology.smallEtaleBaseChangeSquare`. -/
abbrev smallEtaleBaseChangeSquareLeft (U : X.Etale) :
    ((smallEtaleBaseChange p ⋙ smallEtaleBaseChange i').obj U).left ⟶
      ((smallEtaleBaseChange i ⋙ smallEtaleBaseChange a).obj U).left :=
  ((smallEtaleBaseChangeSquare h).hom.app U).left

/-- **The square isomorphism lies over `U`**: followed by the projections to `U`, it is the
composite of the projections `(U ×_X X') ×_{X'} Y' ⟶ U ×_X X' ⟶ U`. -/
theorem smallEtaleBaseChangeSquareLeft_fst_fst (U : X.Etale) :
    smallEtaleBaseChangeSquareLeft h U ≫ pullback.fst _ _ ≫ pullback.fst U.hom i =
      pullback.fst ((smallEtaleBaseChange p).obj U).hom i' ≫ pullback.fst U.hom p := by
  have h1 := smallEtaleBaseChangeComp'_fst_fst a i (i' ≫ p) h U
  have h2 := smallEtaleBaseChangeComp'_fst_fst i' p (i' ≫ p) rfl U
  have h3 : ((smallEtaleBaseChangeComp' i' p (i' ≫ p) rfl).inv.app U).left ≫
      ((smallEtaleBaseChangeComp' i' p (i' ≫ p) rfl).hom.app U).left = 𝟙 _ :=
    congrArg (fun φ => φ.left) ((smallEtaleBaseChangeComp' i' p (i' ≫ p) rfl).inv_hom_id_app U)
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans ((congrArg (_ ≫ ·) h2.symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h3).trans (Category.id_comp _)))))

/-- **The morphism `i_* a_* F ⟶ p_* i'_* F`** attached to a commutative square `i' ≫ p = a ≫ i`:
on sections over an étale `X`-scheme `U` it is restriction along
`(U ×_X X') ×_{X'} Y' ⟶ (U ×_X Y) ×_Y Y'`. -/
def etaleDirectImageSquareMap (F : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianDirectImage.{u, v} i).obj ((etaleAbelianDirectImage.{u, v} a).obj F) ⟶
      (etaleAbelianDirectImage.{u, v} p).obj ((etaleAbelianDirectImage.{u, v} i').obj F) :=
  ⟨Functor.whiskerRight (NatTrans.op (smallEtaleBaseChangeSquare h).hom) F.obj⟩

/-- On sections over an étale `X`-scheme `U`, `etaleDirectImageSquareMap h F` is the restriction
map of `F` along `(smallEtaleBaseChangeSquare h).hom.app U`. -/
theorem etaleDirectImageSquareMap_hom_app
    (F : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (U : X.Etale) :
    (etaleDirectImageSquareMap.{u, v} h F).hom.app (op U) =
      F.obj.map ((smallEtaleBaseChangeSquare h).hom.app U).op :=
  rfl

/-- **The morphism `i_* 𝐆_{m,Y} ⟶ p_* i'_* 𝐆_{m,Y'}`** attached to a commutative square
`i' ≫ p = a ≫ i`: an invertible function on `U ×_X Y` is restricted to
`(U ×_X X') ×_{X'} Y'`. -/
def multiplicativeDirectImageSquareMap :
    (etaleAbelianDirectImage.{u, v} i).obj (Stacks.Kummer.multiplicativeSheaf.{u, v} Y) ⟶
      (etaleAbelianDirectImage.{u, v} p).obj
        ((etaleAbelianDirectImage.{u, v} i').obj (Stacks.Kummer.multiplicativeSheaf.{u, v} Y')) :=
  (etaleAbelianDirectImage.{u, v} i).map (multiplicativeDirectImageComparison.{u, v} a) ≫
    etaleDirectImageSquareMap.{u, v} h _

/-- **On sections the morphism `i_* 𝐆_{m,Y} ⟶ p_* i'_* 𝐆_{m,Y'}` is restriction** along the
composite `(U ×_X X') ×_{X'} Y' ⟶ U ×_X Y`. -/
theorem multiplicativeDirectImageSquareMap_app_ofUnit (U : X.Etale)
    (x : (Γ(((smallEtaleBaseChange i).obj U).left, ⊤))ˣ) :
    (multiplicativeDirectImageSquareMap.{u, v} h).hom.app (op U) (Stacks.Kummer.ofUnit x) =
      Stacks.Kummer.ofUnit (U := (smallEtaleBaseChange i').obj ((smallEtaleBaseChange p).obj U))
        (Units.map (smallEtaleBaseChangeSquareLeft h U ≫ pullback.fst _ _).appTop.hom.toMonoidHom
          x) :=
  rfl

/-- **The comparison morphisms commute with the square**: restricting an invertible function on
`U` first to `U ×_X X'` and then to `(U ×_X X') ×_{X'} Y'` is the same as restricting it first
to `U ×_X Y` and then along `(U ×_X X') ×_{X'} Y' ⟶ U ×_X Y`. -/
theorem multiplicativeDirectImageComparison_comp_multiplicativeDirectImageSquareMap :
    multiplicativeDirectImageComparison.{u, v} p ≫
        (etaleAbelianDirectImage.{u, v} p).map (multiplicativeDirectImageComparison.{u, v} i') =
      multiplicativeDirectImageComparison.{u, v} i ≫
        multiplicativeDirectImageSquareMap.{u, v} h := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  show globalUnitsAdditive.{u, v}.map (pullback.fst U.unop.hom p).op ≫
      globalUnitsAdditive.{u, v}.map
        (pullback.fst ((smallEtaleBaseChange p).obj U.unop).hom i').op =
    globalUnitsAdditive.{u, v}.map (pullback.fst U.unop.hom i).op ≫
      (globalUnitsAdditive.{u, v}.map
          (pullback.fst ((smallEtaleBaseChange i).obj U.unop).hom a).op ≫
        globalUnitsAdditive.{u, v}.map (smallEtaleBaseChangeSquareLeft h U.unop).op)
  have key := smallEtaleBaseChangeSquareLeft_fst_fst h U.unop
  have hop := congrArg Quiver.Hom.op (key.symm.trans (Category.assoc _ _ _).symm)
  exact ((globalUnitsAdditive.{u, v}.map_comp (pullback.fst U.unop.hom p).op
    (pullback.fst ((smallEtaleBaseChange p).obj U.unop).hom i').op).symm.trans
      (congrArg globalUnitsAdditive.{u, v}.map hop)).trans
    ((globalUnitsAdditive.{u, v}.map_comp (pullback.fst U.unop.hom i).op
      (smallEtaleBaseChangeSquareLeft h U.unop ≫
        pullback.fst ((smallEtaleBaseChange i).obj U.unop).hom a).op).trans
      (congrArg (globalUnitsAdditive.{u, v}.map (pullback.fst U.unop.hom i).op ≫ ·)
        (globalUnitsAdditive.{u, v}.map_comp
          (pullback.fst ((smallEtaleBaseChange i).obj U.unop).hom a).op
          (smallEtaleBaseChangeSquareLeft h U.unop).op)))

section GenericPoint

variable {X X' : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace X'] (p : X' ⟶ X) [Flat p]

/-- **The morphism of generic points of a flat morphism of irreducible schemes**,
`Spec K(X') ⟶ Spec K(X)`: the stalk map of `p` at the generic point of `X'`, which lies over the
generic point of `X`. -/
def genericPointMap : Spec X'.functionField ⟶ Spec X.functionField :=
  Spec.map (X.presheaf.stalkSpecializes
      (Inseparable.of_eq (base_genericPoint_eq_genericPoint_of_flat p)).specializes ≫
    p.stalkMap (genericPoint X'))

/-- **The generic point square commutes**: `j_{X'} ≫ p = (Spec K(X') ⟶ Spec K(X)) ≫ j_X`. -/
theorem genericPointInclusion_comp_eq_genericPointMap_comp :
    genericPointInclusion X' ≫ p = genericPointMap p ≫ genericPointInclusion X := by
  rw [genericPointMap, Spec.map_comp, Category.assoc, genericPointInclusion,
    genericPointInclusion, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

end GenericPoint

end Stacks.EtaleCohomology

end
