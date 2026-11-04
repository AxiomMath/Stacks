module

public import StacksFrontier.AlgebraicGeometry.PullbackTensor.StalkFormula
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits

/-!
# Pullback of a bilinear map of sheaves of modules

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `A`, `B`, `C` be sheaves of
`𝒪_Y`-modules.  A multiplication of local sections, `Stacks.BilinearMap A B C`, pulls back to a
multiplication of local sections of `f^*A`, `f^*B` and `f^*C`, compatibly with the unit of the
pullback adjunction.

This is a consequence of [Stacks, Tag 01CD], `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B`, and it is the only
route to such a multiplication: `RingedSpaceModuleAdjunction.modulePullback` is defined as
`(modulePushforward f).leftAdjoint` and has no description of its sections, so a bilinear map
on sections of pullbacks cannot be written down directly.  What Tag 01CD supplies is the
inverse comparison `f^*A ⊗ f^*B ⟶ f^*(A ⊗ B)`, and composing it with the pullback of the
morphism `A ⊗ B ⟶ C` that the bilinear map descends to gives a morphism of sheaves whose
sectionwise values are the pulled-back multiplication.

## Main definitions

* `Stacks.RingedSpace.ofBilinearSheaf`: a bilinear map on sections of two sheaves of modules,
  with values in a third, as a morphism `A ⊗ B ⟶ C` out of the tensor product sheaf.  This is
  `PresheafOfModules.ofBilinear` descended along the unit exhibiting the tensor product as a
  sheafification.
* `Stacks.RingedSpace.pullbackBilinearHom`: the morphism `f^*A ⊗ f^*B ⟶ f^*C` obtained from
  `ofBilinearSheaf` and the inverse of the Tag 01CD comparison.
* `Stacks.RingedSpace.pullbackBilinear`: the pulled-back bilinear map on sections, and
  `Stacks.RingedSpace.pullbackBilinearApp` its value on a pair of local sections.

## Main results

* `Stacks.RingedSpace.ofBilinearSheaf_unit_tmul`: `ofBilinearSheaf` sends the
  sheafification-unit image of a pure tensor of sections to the value of the bilinear map.
* `Stacks.RingedSpace.pullbackBilinear_pullbackUnit`: **the computation that identifies the
  pulled-back multiplication.**  On the pullback-unit images of two local sections it is the
  pullback-unit image of their product.

## Implementation notes

The invertibility of the comparison is taken from the instance
`Stacks.RingedSpace.isIso_comparison` of
`StacksFrontier/AlgebraicGeometry/PullbackTensor/StalkFormula.lean`, where Tag 01CD is stated
unconditionally, so nothing here carries a hypothesis.

This does **not** give a sheaf of graded algebras on `X` from one on `Y`.  The multiplication
is here, but `SheafOfModules.GradedAlgebra` also asks for associativity and the two unit laws
*on sections*, and those do not follow from `pullbackBilinear_pullbackUnit`: the sections of
`f^*A` over an open are not sums of pullback-unit images, only their germs are, so the laws
have to be checked after passing to stalks, using the stalk formula recorded in
`StacksFrontier/AlgebraicGeometry/PullbackTensor/Basic.lean`.

The linearity and naturality of `pullbackBilinearApp` follow from
`PresheafOfModules.toBilinear`, applied to the adjoint transpose of the pulled-back
morphism. The transpose retains the identity restriction of scalars in its codomain.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace PresheafOfModules Opposite
open scoped TensorProduct
universe u

namespace Stacks.RingedSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)

attribute [local implicit_reducible] TopCat.Sheaf TopCat.Presheaf.IsSheaf
  CategoryTheory.sheafCompose

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {A B C : SheafOfModules.{u} (structureRingSheaf Y)}

/-- The morphism `A ⊗ B ⟶ C` out of the tensor product sheaf induced by a bilinear map `β`
on sections of `A` and `B` with values in `C`. -/
noncomputable def ofBilinearSheaf (β : SheafOfModules.BilinearMap A B C) :
    ((sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B ⟶ C :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureRingSheaf Y).obj)).homEquiv
      (PresheafOfModules.tensorObj A.val B.val) C).symm (PresheafOfModules.ofBilinear β)

/-- `ofBilinearSheaf β` sends the sheafification-unit image of a pure tensor `x ⊗ₜ y` of
sections over `U` to `β.app U x y`. -/
lemma ofBilinearSheaf_unit_tmul (β : SheafOfModules.BilinearMap A B C)
    (U : (Opens Y.carrier)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    Hom.app (ofBilinearSheaf β).val U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
          (𝟙 (ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).unit.app
            (PresheafOfModules.tensorObj A.val B.val)) U (x ⊗ₜ y)) = β.app U x y :=
  (hom_congr_apply (PresheafOfModules.sheafificationAdjunction_unit_comp_homEquiv_symm
    (𝟙 (structureRingSheaf Y).obj) (PresheafOfModules.ofBilinear β)) U (x ⊗ₜ y)).trans
    (PresheafOfModules.ofBilinear_tmul β U x y)

/-- The morphism `f^*A ⊗ f^*B ⟶ f^*C` obtained by composing the inverse of the comparison
`comparison f A B` with the pullback of `ofBilinearSheaf β`. -/
noncomputable def pullbackBilinearHom (β : SheafOfModules.BilinearMap A B C) :
    ((sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj
      ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B) ⟶
      (pullbackFunctor f).obj C :=
  @inv _ _ _ _ (comparison f A B) (isIso_comparison f A B) ≫
    (pullbackFunctor f).map (ofBilinearSheaf β)

/-- The value of the pulled-back bilinear map on a pair of sections `x` of `f^*A` and `y` of
`f^*B` over `V`: the image of `x ⊗ₜ y` under `pullbackBilinearHom f β`. -/
noncomputable def pullbackBilinearApp (β : SheafOfModules.BilinearMap A B C)
    (V : (Opens X.carrier)ᵒᵖ) (x : ((pullbackFunctor f).obj A).val.obj V)
    (y : ((pullbackFunctor f).obj B).val.obj V) :
    ((pullbackFunctor f).obj C).val.obj V :=
  Hom.app (pullbackBilinearHom f β).val V
    (Hom.app ((PresheafOfModules.sheafificationAdjunction
      (R := ringSheaf ⟨X.presheaf, X.IsSheaf⟩)
      (𝟙 (ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj)).unit.app
        (PresheafOfModules.tensorObj ((pullbackFunctor f).obj A).val
          ((pullbackFunctor f).obj B).val)) V
      (x ⊗ₜ y))


/-- The bilinear map on sections of `f^*A` and `f^*B` with values in `f^*C` pulled back from
`β`. -/
noncomputable def pullbackBilinear (β : SheafOfModules.BilinearMap A B C) :
    SheafOfModules.BilinearMap ((pullbackFunctor f).obj A) ((pullbackFunctor f).obj B)
      ((pullbackFunctor f).obj C) :=
  PresheafOfModules.toBilinear (O := X.presheaf)
    ((PresheafOfModules.sheafificationAdjunction
      (R := ringSheaf ⟨X.presheaf, X.IsSheaf⟩)
      (𝟙 (ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj)).homEquiv _ _
        (pullbackBilinearHom f β))

section Props
variable (β : SheafOfModules.BilinearMap A B C) (V : (Opens X.carrier)ᵒᵖ)

/-- `pullbackBilinearApp f β V` is additive in its first argument. -/
lemma pullbackBilinearApp_add_left (x x' : ((pullbackFunctor f).obj A).val.obj V)
    (y : ((pullbackFunctor f).obj B).val.obj V) :
    pullbackBilinearApp f β V (x + x') y =
      pullbackBilinearApp f β V x y + pullbackBilinearApp f β V x' y :=
  congrArg (fun value => value y) (map_add ((pullbackBilinear f β).app V) x x')

/-- `pullbackBilinearApp f β V` is additive in its second argument. -/
lemma pullbackBilinearApp_add_right (x : ((pullbackFunctor f).obj A).val.obj V)
    (y y' : ((pullbackFunctor f).obj B).val.obj V) :
    pullbackBilinearApp f β V x (y + y') =
      pullbackBilinearApp f β V x y + pullbackBilinearApp f β V x y' :=
  map_add ((pullbackBilinear f β).app V x) y y'

/-- `pullbackBilinearApp f β V` is linear over sections of `𝒪_X` in its first argument. -/
lemma pullbackBilinearApp_smul_left (r : (structureRingSheaf X).obj.obj V)
    (x : ((pullbackFunctor f).obj A).val.obj V)
    (y : ((pullbackFunctor f).obj B).val.obj V) :
    pullbackBilinearApp f β V (r • x) y = r • pullbackBilinearApp f β V x y :=
  (pullbackBilinear f β).map_smul_left V r x y

/-- `pullbackBilinearApp f β V` is linear over sections of `𝒪_X` in its second argument. -/
lemma pullbackBilinearApp_smul_right (r : (structureRingSheaf X).obj.obj V)
    (x : ((pullbackFunctor f).obj A).val.obj V)
    (y : ((pullbackFunctor f).obj B).val.obj V) :
    pullbackBilinearApp f β V x (r • y) = r • pullbackBilinearApp f β V x y :=
  (pullbackBilinear f β).map_smul_right V r x y

end Props

section Nat
variable (β : SheafOfModules.BilinearMap A B C)

/-- `pullbackBilinearApp f β` commutes with restriction of sections along `g : V ⟶ W`. -/
lemma pullbackBilinearApp_naturality {V W : (Opens X.carrier)ᵒᵖ} (g : V ⟶ W)
    (x : ((pullbackFunctor f).obj A).val.obj V)
    (y : ((pullbackFunctor f).obj B).val.obj V) :
    ((pullbackFunctor f).obj C).val.restrictₛₗ g (pullbackBilinearApp f β V x y) =
      pullbackBilinearApp f β W (((pullbackFunctor f).obj A).val.restrictₛₗ g x)
        (((pullbackFunctor f).obj B).val.restrictₛₗ g y) :=
  (pullbackBilinear f β).naturality g x y

end Nat

/-- The sections of `pullbackBilinear f β` over `V` are given by `pullbackBilinearApp f β V`. -/
@[simp]
lemma pullbackBilinear_app (β : SheafOfModules.BilinearMap A B C)
    (V : (Opens X.carrier)ᵒᵖ) (x : ((pullbackFunctor f).obj A).val.obj V)
    (y : ((pullbackFunctor f).obj B).val.obj V) :
    (pullbackBilinear f β).app V x y = pullbackBilinearApp f β V x y := rfl

/-- On the pullback-unit images of sections `a` of `A` and `b` of `B` over `U`, the
pulled-back bilinear map is the pullback-unit image of `β.app U a b`. -/
lemma pullbackBilinear_pullbackUnit (β : SheafOfModules.BilinearMap A B C)
    (U : (Opens Y.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    (pullbackBilinear f β).app ((opensMap f).op.obj U)
        (pullbackUnit f A U a) (pullbackUnit f B U b) =
      pullbackUnit f C U (β.app U a b) := by
  let : IsIso (comparison f A B) := isIso_comparison f A B
  have hcomp : comparison f A B ≫ pullbackBilinearHom f β =
      (pullbackFunctor f).map (ofBilinearSheaf β) :=
    IsIso.hom_inv_id_assoc (comparison f A B) ((pullbackFunctor f).map (ofBilinearSheaf β))
  have key : ∀ t : ((pullbackFunctor f).obj (((sheafTensor.{u, u, u, u, u} ⟨Y.presheaf,
      Y.IsSheaf⟩).obj A).obj B)).val.obj
        ((opensMap f).op.obj U),
      Hom.app (pullbackBilinearHom f β).val ((opensMap f).op.obj U)
        (Hom.app (comparison f A B).val ((opensMap f).op.obj U) t) =
      Hom.app ((pullbackFunctor f).map (ofBilinearSheaf β)).val ((opensMap f).op.obj U) t :=
    fun t => hom_congr_apply
      (congrArg (SheafOfModules.forget (structureRingSheaf X)).map hcomp) _ t
  have hnat := pullbackUnit_naturality (f := f) (A := ((sheafTensor.{u, u, u, u, u} ⟨Y.presheaf,
      Y.IsSheaf⟩).obj A).obj B) (A' := C)
    (ofBilinearSheaf β) U (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
          (𝟙 (ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).unit.app
            (PresheafOfModules.tensorObj A.val B.val)) U (a ⊗ₜ b))
  exact (congrArg
    (fun value => Hom.app (pullbackBilinearHom f β).val ((opensMap f).op.obj U) value)
    (comparison_pullbackUnit_tmul f A B U a b).symm).trans
      ((key _).trans
        (hnat.trans (congrArg (pullbackUnit f C U) (ofBilinearSheaf_unit_tmul β U a b))))

end Stacks.RingedSpace

end
