module

public import
StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomEvaluationRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.TensorTransport

/-!
# The mate of Stacks 0E8H on local sections

Let `(C, O)` be a ringed site and `U` an object of `C`. The comparison
`A|_U ⊗_{O|_U} F|_U ⟶ (A ⊗_O F)|_U` of
`Stacks.SheafOfModules.ExtensionByZero.tensorRestrictionComparison` is defined as the mate of
Stacks 0E8H under the tensor--internal-Hom correspondence of Stacks 03EO on `C` and on `C/U`.
That definition says what the comparison *is* but not what it *does*; this file computes it on a
local section.

The answer is the one the name suggests: the comparison carries the image under the
sheafification unit of a pure tensor `x ⊗ₜ y` of two sections over an object `V ⟶ U` of `C/U` to
the image under the sheafification unit of the same pure tensor, read over `V` on `C`. The mate
is, on sections, the identity on pure tensors.

## Why the mate has a sections formula at all

Three facts, each already in the development:

* the mate of a 2-cell is characterised by one adjoint transpose,
  `CategoryTheory.unit_mateEquiv_symm`, so the transpose of the comparison is the restriction of
  the *unit* of Stacks 03EO followed by Stacks 0E8H;
* the correspondence of Stacks 03EO has a pure-tensor sections formula,
  `Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv_apply`, which both reads the transpose
  back off the comparison and evaluates the unit -- the unit being the correspondence at the
  identity;
* Stacks 0E8H contributes no computation, only a reindexing along the iterated-slice functor:
  `Stacks.SheafOfModules.InternalHom.internalHomOverIso_hom_app` is proved by `rfl`.

Nothing here takes the mate of both sides of anything, which would be circular, and nothing here
uses a monoidal structure.

## Main results

All names below are in the namespace `Stacks.SheafOfModules.ExtensionByZero`.

* `sheafTensor_obj_map_app_sheafifyUnit_tmul`: tensoring a pure tensor by a morphism in the
  *right-hand* factor, the companion of the existing `sheafTensor_map_app_sheafifyUnit_tmul` for
  the left-hand one.
* `sheafTensorHomEquiv_tensorRestrictionComparison`: the adjoint transpose of the mate, with no
  `mateEquiv` left: the restriction of the unit of Stacks 03EO followed by Stacks 0E8H.
* `sheafTensorRightHomAdjunction_unit_app_val_app_apply_app`: the unit of Stacks 03EO on a pure
  tensor.
* `tensorRestrictionComparison_natTrans_app_val_app_unit_tmul`: **the mate of Stacks 0E8H on a
  pure tensor** -- the restricted pure tensor.
* `transport_comp_tensorRestrictionComparison_val_app_unit_tmul` and its `_op`, `_of_eq`,
  `_of_eq_comp` and `_tensorTransportComp` forms: a transport of the two tensor factors along two
  morphisms `φ`, `ψ`, followed by the mate, on a pure tensor: the restricted pure tensor of the two
  transported sections. `_tensorTransportComp` is the form for the Tag 04IX transport, stated at
  the composite of its two named halves; the others take the transport as a variable with an
  equation, which at that transport is not dischargeable (see the section introduction).

## Implementation notes

The composite form is stated with the two transports as *variables* `φ` and `ψ`, and the
transport itself as a variable `T` together with an equation, rather than at the pullback along
a localization morphism of ringed topoi. That is not generality for its own sake. Written out at
`Stacks.SheafOfModules.localizationTensorTransport`'s own arguments, the *statement* --- before
any proof --- exhausts the elaborator's whole budget at `whnf`, because the two one-variable
actions of the curried tensor product and the pure tensor's module instances then have to be
forced against each other at those concrete terms. At variables the same statement elaborates in
a second and the concrete instance is one term application, with the crossing left at an
explicit argument. For the Tag 04IX transport the form to use is `..._tensorTransportComp`,
stated at the composite of that transport's two named halves; the `T`-plus-equation forms cannot
be discharged there, and neither can anything that writes the transport's own name, for the
reason recorded above that lemma.

Every proof whose two sides mix two spellings of the structure sheaf of rings is a term rather
than a tactic script, for the reason recorded in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/BilinearValueFormulas.lean`: the spellings agree
only at default transparency, which a term checks and the motive check of `rw` does not. The two
`rw`s that do occur rewrite a hypothesis by an equation whose left-hand side is syntactically
present in it.

Nothing here carries a `stacks` attribute: these are section-level computations of an existing
comparison and the source states none of them.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.SheafOfModules.InternalHom (internalHomSecondFunctor sheafTensorRightHomAdjunction
  sheafTensorHomEquiv internalHomOverIso)

namespace Stacks.SheafOfModules.ExtensionByZero

universe u

section SecondVariable

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  (O : Sheaf J CommRingCat.{u})

/-- **Tensoring a pure tensor by `ψ` in the right-hand factor.** The companion of
`Stacks.SheafOfModules.ExtensionByZero.sheafTensor_map_app_sheafifyUnit_tmul`, which does the
same for the left-hand factor: the one-variable action of the curried tensor product of
Stacks 0GMW in its second argument carries the sheafification-unit image of `y ⊗ₜ x` to that of
`y ⊗ₜ ψ x`. -/
theorem sheafTensor_obj_map_app_sheafifyUnit_tmul
    (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {G G' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (ψ : G ⟶ G')
    (W : C) (y : F.val.obj (op W)) (x : G.val.obj (op W)) :
    (((sheafTensor O).obj F).map ψ).val.app (op W)
        ((((_root_.PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit).app
            (((_root_.PresheafOfModules.tensorBifunctor.{u, u, u, u, u} O.obj).obj F.val).obj
              G.val)).app
          (op W) (y ⊗ₜ[O.obj.obj (op W)] x)) =
      (((_root_.PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit).app
          (((_root_.PresheafOfModules.tensorBifunctor.{u, u, u, u, u} O.obj).obj F.val).obj
            G'.val)).app
        (op W) (y ⊗ₜ[O.obj.obj (op W)] ψ.val.app (op W) x) := by
  let wl : ((_root_.PresheafOfModules.tensorBifunctor.{u, u, u, u, u} O.obj).obj F.val).obj G.val ⟶
      ((_root_.PresheafOfModules.tensorBifunctor.{u, u, u, u, u} O.obj).obj F.val).obj G'.val :=
    MonoidalCategory.whiskerLeft F.val ψ.val
  have h1 : ((sheafTensor O).obj F).map ψ =
      (_root_.PresheafOfModules.sheafification.{u}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map wl := rfl
  have h2 := (_root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.naturality wl
  rw [h1]
  exact (congrArg (fun k ↦ (ConcreteCategory.hom (k.app (op W)))
    (y ⊗ₜ[O.obj.obj (op W)] x)) h2).symm

/-- The sections formula of Stacks 03EO at the identity object of `C/W`: a morphism `b` out of the
sheafified tensor product, transposed, sends `x` and `y` to the value of `b` on the
sheafification-unit image of `x ⊗ₜ y`. -/
private theorem sheafTensorHomEquiv_apply_app_id {D : Type u} [Category.{u} D]
    {K : GrothendieckTopology D} [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify K AddCommGrpCat.{u}]
    (R : Sheaf K CommRingCat.{u})
    (F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (b : ((sheafTensor R).obj F).obj G ⟶ H) (W : D) (x : F.val.obj (op W))
    (y : G.val.obj (op W)) :
    (((((sheafTensorHomEquiv R F G H b).val.app (op W)).hom x).app
          (op (Over.mk (𝟙 W)))).hom y) =
      b.val.app (op W)
        (((_root_.PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).unit.app
            (F.val ⊗ G.val)).app (op W)
          (x ⊗ₜ[(R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op W)] y)) := by
  have hid : (F.val.restrictₛₗ (𝟙 W).op) x = x :=
    congrArg (fun φ ↦ (ConcreteCategory.hom φ) x) (F.val.map_id (op W))
  have hcomp : (Stacks.SheafOfModules.InternalHom.sheafifyForgetAdjunction R).homEquiv
        (F.val ⊗ G.val) H b =
      (_root_.PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).unit.app (F.val ⊗ G.val) ≫
        b.val :=
    (Stacks.SheafOfModules.InternalHom.sheafifyForgetAdjunction R).homEquiv_unit
      (F.val ⊗ G.val) H b
  have hkey := Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv_apply R F G H b W x (𝟙 W) y
  rw [hcomp, hid] at hkey
  exact hkey

end SecondVariable

section Sections

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F A : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The adjoint transpose of the mate of Stacks 0E8H**, with no `mateEquiv` left: it is the
restriction to `C/U` of the unit of Stacks 03EO followed by Stacks 0E8H.

This is `CategoryTheory.unit_mateEquiv_symm`, the characterisation of a mate by one adjoint
transpose, at the two correspondences of Stacks 03EO, together with
`CategoryTheory.Adjunction.homEquiv_unit`. It is what makes the comparison computable on
sections, since the correspondence of Stacks 03EO has a pure-tensor sections formula and its
unit is the correspondence at the identity. -/
theorem sheafTensorHomEquiv_tensorRestrictionComparison :
    sheafTensorHomEquiv (X.O.over U) (A.over U) (F.over U)
        ((((sheafTensor X.O).obj A).obj F).over U)
        ((tensorRestrictionComparison X U F).app A) =
      (_root_.SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
          ((sheafTensorRightHomAdjunction X.O F).unit.app A) ≫
        (internalHomRestrictionNatIso X U F).hom.app (((sheafTensor X.O).obj A).obj F) :=
  ((sheafTensorRightHomAdjunction.{u, u} (X.O.over U) (F.over U)).homEquiv_unit
      (A.over U) ((((sheafTensor X.O).obj A).obj F).over U)
      ((tensorRestrictionComparison X U F).app A)).trans
    (unit_mateEquiv_symm (sheafTensorRightHomAdjunction.{u, u} X.O F)
      (sheafTensorRightHomAdjunction.{u, u} (X.O.over U) (F.over U))
      (TwoSquare.mk _ _ _ _ (internalHomRestrictionNatIso X U F).hom) A).symm

/-- **The unit of Stacks 03EO on a pure tensor.** The unit `A ⟶ Hom_O(F, A ⊗_O F)` carries a
section `x` of `A` over `W` to the morphism `F|_W ⟶ (A ⊗_O F)|_W` whose value on a section `y`
over `W` itself is the sheafification-unit image of `x ⊗ₜ y`.

The unit is the correspondence of Stacks 03EO at the identity
(`CategoryTheory.Adjunction.homEquiv_id`), so this is
`Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv_apply` there, the restriction of `x`
along the identity removed by `PresheafOfModules.map_id`. -/
theorem sheafTensorRightHomAdjunction_unit_app_val_app_apply_app (W : X.C)
    (x : A.val.obj (op W)) (y : F.val.obj (op W)) :
    (((((sheafTensorRightHomAdjunction X.O F).unit.app A).val.app (op W)).hom x).app
          (op (Over.mk (𝟙 W)))).hom y =
      ((_root_.PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (A.val ⊗ F.val)).app (op W)
        (x ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op W)] y) := by
  have hunit : Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv X.O A F
        (((sheafTensor X.O).obj A).obj F) (𝟙 _) =
      (sheafTensorRightHomAdjunction X.O F).unit.app A :=
    (sheafTensorRightHomAdjunction X.O F).homEquiv_id A
  exact (congrArg
    (fun e : A ⟶ (Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor X.J X.O F).obj
        (((sheafTensor X.O).obj A).obj F) ↦
      (((e.val.app (op W)).hom x).app (op (Over.mk (𝟙 W)))).hom y) hunit).symm.trans
    (sheafTensorHomEquiv_apply_app_id X.O A F _ (𝟙 _) W x y)

/-- The adjoint transpose of the mate of Stacks 0E8H, evaluated on a section `x` of `A|_U` and a
section `y` of `F|_U` over the identity object of `(C/U)/V`, is the sheafification-unit image of
`x ⊗ₜ y` formed on `C` over `V`. -/
theorem sheafTensorHomEquiv_tensorRestrictionComparison_val_app_apply_app (V : Over U)
    (x : (A.over U).val.obj (op V)) (y : (F.over U).val.obj (op V)) :
    ((((Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv (X.O.over U) (A.over U)
            (F.over U) ((((sheafTensor X.O).obj A).obj F).over U)
            ((tensorRestrictionComparison X U F).app A)).val.app (op V)).hom x).app
          (op (Over.mk (𝟙 V)))).hom y =
      ((_root_.PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (A.val ⊗ F.val)).app (op V.left)
        (x ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op V.left)] y) :=
  (congrArg (fun e : (A.over U) ⟶
      (Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor (X.J.over U) (X.O.over U)
        (F.over U)).obj ((((sheafTensor X.O).obj A).obj F).over U) ↦
    (((e.val.app (op V)).hom x).app (op (Over.mk (𝟙 V)))).hom y)
    (sheafTensorHomEquiv_tensorRestrictionComparison X U F A)).trans
    (sheafTensorRightHomAdjunction_unit_app_val_app_apply_app X F A V.left x y)

/-- **The mate of Stacks 0E8H on a pure tensor: the restricted pure tensor.** The comparison
`A|_U ⊗_{O|_U} F|_U ⟶ (A ⊗_O F)|_U` carries the sheafification-unit image, formed on the slice
site `C/U`, of a pure tensor of two sections over an object `V ⟶ U` to the sheafification-unit
image of the same pure tensor formed on `C` over `V`.

The proof reads the comparison off its adjoint transpose by
`Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv_apply` on the slice site, identifies that
transpose by `sheafTensorHomEquiv_tensorRestrictionComparison`, and then evaluates its two
factors: Stacks 0E8H is a reindexing along the iterated-slice functor, which at the identity
object of `(C/U)/V` is the identity object of `C/V`, and the unit of Stacks 03EO is
`sheafTensorRightHomAdjunction_unit_app_val_app_apply_app`. Every step after the first two is
definitional. -/
theorem tensorRestrictionComparison_natTrans_app_val_app_unit_tmul (V : Over U)
    (x : (A.over U).val.obj (op V)) (y : (F.over U).val.obj (op V)) :
    ((tensorRestrictionComparison X U F).app A).val.app (op V)
        (((_root_.PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)).obj)).unit.app
            ((A.over U).val ⊗ (F.over U).val)).app (op V)
          (x ⊗ₜ[((X.O.over U).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op V)] y)) =
      ((_root_.PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (A.val ⊗ F.val)).app (op V.left)
        (x ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op V.left)] y) := by
  exact (sheafTensorHomEquiv_apply_app_id (X.O.over U) (A.over U) (F.over U) _
    ((tensorRestrictionComparison X U F).app A) V x y).symm.trans
    (sheafTensorHomEquiv_tensorRestrictionComparison_val_app_apply_app X U F A V x y)

/-- **A transport of the two tensor factors followed by the mate of Stacks 0E8H, on a pure
tensor.** For morphisms `φ : A' ⟶ A|_U` and `ψ : F' ⟶ F|_U` on the slice site, moving `φ` into
the first factor of `A' ⊗_{O|_U} F'` and then `ψ` into the second and then applying the mate of
Stacks 0E8H carries the sheafification-unit image of `a ⊗ₜ b` to the sheafification-unit image,
formed on `C` over `V`, of `φ a ⊗ₜ ψ b`.

Both transports are one-variable actions of the curried tensor product of Stacks 0GMW, which is
the spelling the mate is stated at; no crossing to the bifunctor of Stacks 03EL occurs. -/
theorem transport_comp_tensorRestrictionComparison_val_app_unit_tmul
    {A' F' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))}
    (φ : A' ⟶ A.over U) (ψ : F' ⟶ F.over U) (V : Over U)
    (a : A'.val.obj (op V)) (b : F'.val.obj (op V)) :
    ((((sheafTensor (X.O.over U)).map φ).app F' ≫
            ((sheafTensor (X.O.over U)).obj (A.over U)).map ψ) ≫
          (tensorRestrictionComparison X U F).app A).val.app (op V)
        (((_root_.PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)).obj)).unit.app
            (A'.val ⊗ F'.val)).app (op V)
          (a ⊗ₜ[((X.O.over U).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op V)] b)) =
      ((_root_.PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (A.val ⊗ F.val)).app (op V.left)
        (φ.val.app (op V) a ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op V.left)]
          ψ.val.app (op V) b) := by
  have s1 := sheafTensor_map_app_sheafifyUnit_tmul (X.J.over U) (X.O.over U) φ F' V a b
  have s2 := sheafTensor_obj_map_app_sheafifyUnit_tmul (X.J.over U) (X.O.over U) (A.over U) ψ V
    (φ.val.app (op V) a) b
  have s3 := tensorRestrictionComparison_natTrans_app_val_app_unit_tmul X U F A V
    (φ.val.app (op V) a) (ψ.val.app (op V) b)
  exact (congrArg (fun z ↦ ((tensorRestrictionComparison X U F).app A).val.app (op V)
      ((((sheafTensor (X.O.over U)).obj (A.over U)).map ψ).val.app (op V) z)) s1).trans
    ((congrArg (fun z ↦ ((tensorRestrictionComparison X U F).app A).val.app (op V) z)
      s2).trans s3)

/-- `transport_comp_tensorRestrictionComparison_val_app_unit_tmul` with the object of the slice
site written in the opposite category, which is the shape a consumer's goal carries it in. -/
theorem transport_comp_tensorRestrictionComparison_val_app_unit_tmul_op
    {A' F' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))}
    (φ : A' ⟶ A.over U) (ψ : F' ⟶ F.over U) (V : (Over U)ᵒᵖ)
    (a : A'.val.obj V) (b : F'.val.obj V) :
    ((((sheafTensor (X.O.over U)).map φ).app F' ≫
            ((sheafTensor (X.O.over U)).obj (A.over U)).map ψ) ≫
          (tensorRestrictionComparison X U F).app A).val.app V
        (((_root_.PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)).obj)).unit.app
            (A'.val ⊗ F'.val)).app V
          (a ⊗ₜ[((X.O.over U).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj V] b)) =
      ((_root_.PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (A.val ⊗ F.val)).app (op V.unop.left)
        (φ.val.app V a ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op V.unop.left)]
          ψ.val.app V b) :=
  transport_comp_tensorRestrictionComparison_val_app_unit_tmul X U F A φ ψ V.unop a b

/-- `transport_comp_tensorRestrictionComparison_val_app_unit_tmul_op` for a morphism `T` given
by name rather than by its formula: any morphism equal to the two one-variable actions of the
curried tensor product on `φ` and `ψ` has the same value on a pure tensor.

This is the form in which a goal stated with
`Stacks.SheafOfModules.localizationTensorTransport` is reduced: supply that transport as `T` and
`rfl` as `hT`, in the context where the transport's own type is already elaborated. Writing the
two actions out at the pullbacks inside a statement here instead costs the elaborator's whole
budget, which is the known hazard of forcing a crossing of tensor spellings into a
hand-written type rather than leaving it at an explicit argument. -/
theorem transport_comp_tensorRestrictionComparison_val_app_unit_tmul_of_eq
    {A' F' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))}
    (φ : A' ⟶ A.over U) (ψ : F' ⟶ F.over U)
    (T : ((sheafTensor (X.O.over U)).obj A').obj F' ⟶
      ((sheafTensor (X.O.over U)).obj (A.over U)).obj (F.over U))
    (hT : T = ((sheafTensor (X.O.over U)).map φ).app F' ≫
      ((sheafTensor (X.O.over U)).obj (A.over U)).map ψ)
    (V : (Over U)ᵒᵖ) (a : A'.val.obj V) (b : F'.val.obj V) :
    (T ≫ (tensorRestrictionComparison X U F).app A).val.app V
        (((_root_.PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)).obj)).unit.app
            (A'.val ⊗ F'.val)).app V
          (a ⊗ₜ[((X.O.over U).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj V] b)) =
      ((_root_.PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (A.val ⊗ F.val)).app (op V.unop.left)
        (φ.val.app V a ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op V.unop.left)]
          ψ.val.app V b) :=
  (congrArg (fun m ↦ (m ≫ (tensorRestrictionComparison X U F).app A).val.app V
      (((_root_.PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)).obj)).unit.app
          (A'.val ⊗ F'.val)).app V
        (a ⊗ₜ[((X.O.over U).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj V] b))) hT).trans
    (transport_comp_tensorRestrictionComparison_val_app_unit_tmul_op X U F A φ ψ V a b)

/-! ### The transport at its two named halves

`..._of_eq` above takes the transport as a variable `T` together with an equation identifying it
with a *written-out* composite of the two one-variable actions. That equation cannot be supplied
at `Stacks.SheafOfModules.localizationTensorTransport`, and the obstruction is not where one might
expect it. Three placements, each `(kernel) deterministic timeout` after 90-120 s:

* `hT := rfl` against the written-out composite;
* `hT := rfl` against a composite of the two one-variable actions given as *named* definitions;
* the same equation extracted as a theorem of its own in the transport's own module, with
  `localizationTensorTransport` *defined* as exactly that composite of the two names.

The *statement* of that equation, by contrast, elaborates and is kernel-checked in 2.5 s as a
`def ... : Prop`. So the cost is entirely in the kernel's conversion check between the transport's
name and its own unfolded body, and no restatement of the hypothesis removes it: the two halves
being names does not help, because the comparison itself is what is expensive.

The further measurement, which fixes what a consumer has to do: a declaration whose kernel check
requires converting `localizationTensorTransport X U A F` with its own unfolded body times out
*in either direction* -- as the right-hand side of an equation, and as the left-hand side of a
goal discharged by `..._tensorTransportComp` below, the lemma stated at the composite. One delta
step is all that separates the two terms, and the kernel does not take it here. By contrast the
*type* mentioning both of them is checked in 2.5 s, so it is specifically the conversion, not the
size of the terms.

So the name of the transport is a wall for the kernel, and the working conclusion is that a
statement about the Tag 04IX transport of a tensor product must be written at the composite
`tensorTransportFirst _ _ _ φ _ ≫ tensorTransportSecond _ _ _ _ ψ` throughout, with
`localizationTensorTransport` not appearing in it at all. That composite *is* the transport --
`Stacks.SheafOfModules.localizationTensorTransport` is defined as it -- so nothing is weakened by
writing it out; what is avoided is ever asking the kernel to identify the two spellings.
`..._tensorTransportComp` below is the mate's pure-tensor formula in that form.

The two halves are declared with the transport in
`StacksFrontier/CategoryTheory/Sites/Modules/LocalizationRingedSites/TensorTransport.lean`, not
here,
so that the transport's body and this file's statements are applications of the same two
constants.
-/

/-- `transport_comp_tensorRestrictionComparison_val_app_unit_tmul_op` for a morphism `T` given by
name, with the hypothesis on `T` stated against the two *named* halves `tensorTransportFirst` and
`tensorTransportSecond` instead of against a written-out composite of the two one-variable
actions.

`hT` is then an equation between two applications of named constants rather than between a name
and a written-out composite. This does not make it dischargeable at
`Stacks.SheafOfModules.localizationTensorTransport` -- see the section
introduction, and use `..._tensorTransportComp` instead on a goal carrying that transport. This
form remains the one to use for a transport that is genuinely a variable. -/
theorem transport_comp_tensorRestrictionComparison_val_app_unit_tmul_of_eq_comp
    {A' F' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))}
    (φ : A' ⟶ A.over U) (ψ : F' ⟶ F.over U)
    (T : ((sheafTensor (X.O.over U)).obj A').obj F' ⟶
      ((sheafTensor (X.O.over U)).obj (A.over U)).obj (F.over U))
    (hT : T = Stacks.SheafOfModules.tensorTransportFirst X U A φ F' ≫
      Stacks.SheafOfModules.tensorTransportSecond X U A F ψ)
    (V : (Over U)ᵒᵖ) (a : A'.val.obj V) (b : F'.val.obj V) :
    (T ≫ (tensorRestrictionComparison X U F).app A).val.app V
        (((_root_.PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)).obj)).unit.app
            (A'.val ⊗ F'.val)).app V
          (a ⊗ₜ[((X.O.over U).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj V] b)) =
      ((_root_.PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (A.val ⊗ F.val)).app (op V.unop.left)
        (φ.val.app V a ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op V.unop.left)]
          ψ.val.app V b) :=
  transport_comp_tensorRestrictionComparison_val_app_unit_tmul_of_eq X U F A φ ψ T hT V a b

/-- **The transport of the two tensor factors, followed by the mate of Stacks 0E8H, on a pure
tensor** -- stated at the composite of the two *named* halves
`Stacks.SheafOfModules.tensorTransportFirst` and `Stacks.SheafOfModules.tensorTransportSecond`.

`Stacks.SheafOfModules.localizationTensorTransport` is defined as that composite, so this is the
mate's pure-tensor formula for the Tag 04IX transport. It is usable only by a goal that is itself
written at the composite: a goal that writes the transport's name instead leaves the kernel one
delta step to take, and it does not take it. The section introduction records
this, and `..._of_eq` and `..._of_eq_comp` -- which take the transport as a variable with
an equation -- fail there for the same reason. -/
theorem transport_comp_tensorRestrictionComparison_val_app_unit_tmul_tensorTransportComp
    {A' F' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))}
    (φ : A' ⟶ A.over U) (ψ : F' ⟶ F.over U)
    (V : (Over U)ᵒᵖ) (a : A'.val.obj V) (b : F'.val.obj V) :
    ((Stacks.SheafOfModules.tensorTransportFirst X U A φ F' ≫
            Stacks.SheafOfModules.tensorTransportSecond X U A F ψ) ≫
          (tensorRestrictionComparison X U F).app A).val.app V
        (((_root_.PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)).obj)).unit.app
            (A'.val ⊗ F'.val)).app V
          (a ⊗ₜ[((X.O.over U).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj V] b)) =
      ((_root_.PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (A.val ⊗ F.val)).app (op V.unop.left)
        (φ.val.app V a ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op V.unop.left)]
          ψ.val.app V b) :=
  transport_comp_tensorRestrictionComparison_val_app_unit_tmul_of_eq_comp X U F A φ ψ _ rfl V a b

end Sections

end Stacks.SheafOfModules.ExtensionByZero

end
