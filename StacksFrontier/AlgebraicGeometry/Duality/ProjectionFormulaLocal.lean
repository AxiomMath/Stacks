module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaRestrictionSections

/-!
# The projection formula for an affine morphism

Let `h : T ⟶ S` be an affine morphism of schemes, `G` a quasi-coherent `𝒪_T`-module and `H` a
quasi-coherent `𝒪_S`-module. Then the projection-formula morphism

`h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)`

is invertible.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.ProjectionFormula`.

* `restrictSourceIso` and `restrictTargetIso`: the restriction to an open `V ⊆ S` of the source,
  respectively of the target, of the projection-formula morphism of `h`, identified with the
  source, respectively the target, of the projection-formula morphism of `h ∣_ V`.
* `restrictSourceIso_hom_restrictUnit_unit_tmul` and
  `restrictTargetIso_hom_restrictUnit_unit_tmul`: those two isomorphisms on local sections.
* `projectionFormulaMap_restrict`: the restriction of the projection-formula morphism is the
  projection-formula morphism of the restricted morphism.
* `isIso_projectionFormulaMap_restrict`: for an affine morphism `h`, quasi-coherent `G` and `H`
  and an affine open `V ⊆ S`, the restriction to `V` of the projection-formula morphism is
  invertible.
* `isIso_projectionFormulaMap`: for an affine morphism of schemes and quasi-coherent modules the
  projection-formula morphism `h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)` is invertible.
* `projectionFormulaIsoOfQuasicoherent`: the resulting isomorphism.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction PresheafOfModules Stacks.RingedSpace
open Stacks.AlgebraicGeometry.AffinePushforward
open Stacks.AlgebraicGeometry.RestrictionSections
open scoped TensorProduct
open scoped CategoryTheory.Prod

universe u

namespace Stacks.AlgebraicGeometry.ProjectionFormula

/-- A morphism whose conjugate by two isomorphisms is invertible is invertible. -/
lemma isIso_of_isIso_conj {C : Type*} [Category C] {W X Y Z : C} (a : X ≅ W) (b : Y ≅ Z)
    (f : X ⟶ Y) (hf : IsIso (a.inv ≫ f ≫ b.hom)) : IsIso f := by
  simpa using (inferInstance : IsIso (a.hom ≫ (a.inv ≫ f ≫ b.hom) ≫ b.inv))

/-- Applying a morphism of sheaves of modules and then a left inverse to it returns the section. -/
private lemma app_comp_eq_self {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (a : M ⟶ N) (b : N ⟶ M)
    (hab : a ≫ b = 𝟙 M) (U : Cᵒᵖ) (x : M.val.obj U) : (b.val.app U) (a.val.app U x) = x :=
  PresheafOfModules.hom_congr_apply' (congrArg (fun k => SheafOfModules.Hom.val k) hab) _ _

variable {T S : Scheme.{u}} (h : T ⟶ S) (V : S.Opens) (G : T.Modules) (H : S.Modules)

/-! ### The restriction of the source and of the target -/

/-- The restriction to `V` of the source `h_*G ⊗_{𝒪_S} H` of the projection-formula morphism is
`(h ∣_ V)_*(G|_{h⁻¹V}) ⊗_{𝒪_V} H|_V`, the source of the projection-formula morphism of
`h ∣_ V`. -/
def restrictSourceIso :
    (Scheme.Modules.restrictFunctor V.ι).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩)).obj
            ((Scheme.Modules.pushforward h).obj G, H)) ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨V.toScheme.toRingedSpace.presheaf, V.toScheme.toRingedSpace.IsSheaf⟩)).obj
        ((Scheme.Modules.pushforward (h ∣_ V)).obj
            ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G),
          (Scheme.Modules.restrictFunctor V.ι).obj H) :=
  restrictTensorIso V.ι ((Scheme.Modules.pushforward h).obj G) H ≪≫
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨V.toScheme.toRingedSpace.presheaf, V.toScheme.toRingedSpace.IsSheaf⟩)).mapIso
      (Iso.prod ((restrictPushforwardIso h V).app G) (Iso.refl _))

/-- The restriction to `V` of the target `h_*(G ⊗_{𝒪_T} h^*H)` of the projection-formula morphism
is `(h ∣_ V)_*(G|_{h⁻¹V} ⊗_{𝒪_{h⁻¹V}} (h ∣_ V)^*(H|_V))`, the target of the projection-formula
morphism of `h ∣_ V`. -/
def restrictTargetIso :
    (Scheme.Modules.restrictFunctor V.ι).obj
        ((Scheme.Modules.pushforward h).obj
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).obj
              (G, (Scheme.Modules.pullback h).obj H))) ≅
      (Scheme.Modules.pushforward (h ∣_ V)).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(h ⁻¹ᵁ V).toScheme.toRingedSpace.presheaf,
            (h ⁻¹ᵁ V).toScheme.toRingedSpace.IsSheaf⟩)).obj
          ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G,
            (Scheme.Modules.pullback (h ∣_ V)).obj
              ((Scheme.Modules.restrictFunctor V.ι).obj H))) :=
  (restrictPushforwardIso h V).app
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).obj
          (G, (Scheme.Modules.pullback h).obj H)) ≪≫
    (Scheme.Modules.pushforward (h ∣_ V)).mapIso
      (restrictTensorIso (h ⁻¹ᵁ V).ι G ((Scheme.Modules.pullback h).obj H) ≪≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(h ⁻¹ᵁ V).toScheme.toRingedSpace.presheaf,
            (h ⁻¹ᵁ V).toScheme.toRingedSpace.IsSheaf⟩)).mapIso
          (Iso.prod (Iso.refl _) ((pullbackRestrictIso h V).app H)))

/-- `restrictSourceIso` on local sections: it carries the restriction of the
sheafification-unit image of a pure tensor `x ⊗ y` to the sheafification-unit image of the
tensor of the restrictions, the first factor read through the restriction-direct-image
comparison. -/
lemma restrictSourceIso_hom_restrictUnit_unit_tmul (W : S.Opens)
    (x : ((Scheme.Modules.pushforward h).obj G).val.obj (op W)) (y : H.val.obj (op W)) :
    Hom.app (restrictSourceIso h V G H).hom.val (op (V.ι ⁻¹ᵁ W))
        (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩)).obj
                ((Scheme.Modules.pushforward h).obj G, H))).val
          (op W) (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf S.toRingedSpace)
              (𝟙 (Stacks.RingedSpace.structureRingSheaf S.toRingedSpace).obj)).unit.app
              (PresheafOfModules.tensorObj (O := S.toRingedSpace.presheaf)
              ((Scheme.Modules.pushforward h).obj G).val H.val)) (op W) (x ⊗ₜ y))) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf V.toScheme.toRingedSpace)
          (𝟙 (Stacks.RingedSpace.structureRingSheaf V.toScheme.toRingedSpace).obj)).unit.app
          (PresheafOfModules.tensorObj (O := V.toScheme.toRingedSpace.presheaf)
          (((Scheme.Modules.pushforward (h ∣_ V)).obj
            ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G))).val
                ((Scheme.Modules.restrictFunctor V.ι).obj H).val)) (op (V.ι ⁻¹ᵁ W))
        (Hom.app ((restrictPushforwardIso h V).hom.app G).val (op (V.ι ⁻¹ᵁ W))
            (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app
              ((Scheme.Modules.pushforward h).obj G)).val (op W) x) ⊗ₜ
          Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app H).val (op W) y) := by
  refine Eq.trans (PresheafOfModules.comp_app_apply
    (restrictTensorIso V.ι ((Scheme.Modules.pushforward h).obj G) H).hom.val
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨V.toScheme.toRingedSpace.presheaf, V.toScheme.toRingedSpace.IsSheaf⟩)).map
      (Iso.prod ((restrictPushforwardIso h V).app G)
        (Iso.refl ((Scheme.Modules.restrictFunctor V.ι).obj H))).hom).val _ _) ?_
  refine Eq.trans (congrArg (Hom.app ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨V.toScheme.toRingedSpace.presheaf,
      V.toScheme.toRingedSpace.IsSheaf⟩)).map
      (Iso.prod ((restrictPushforwardIso h V).app G)
        (Iso.refl ((Scheme.Modules.restrictFunctor V.ι).obj H))).hom).val (op (V.ι ⁻¹ᵁ W)))
    (restrictTensorIso_hom_restrictUnit_unit_tmul V.ι
      ((Scheme.Modules.pushforward h).obj G) H (op W) x y)) ?_
  exact tensorSheaf_map_unit_tmul V.toScheme.toRingedSpace
    ((restrictPushforwardIso h V).app G).hom
    (Iso.refl ((Scheme.Modules.restrictFunctor V.ι).obj H)).hom (op (V.ι ⁻¹ᵁ W)) _ _

/-- `restrictTargetIso` on local sections: it carries the restriction of the
sheafification-unit image of a pure tensor `x ⊗ b`, with `x` a section of `G` and `b` a section
of `h^*H` over `h⁻¹W`, to the sheafification-unit image of the tensor of their restrictions, the
second factor read through the restriction-inverse-image comparison. -/
lemma restrictTargetIso_hom_restrictUnit_unit_tmul (W : S.Opens) (x : G.val.obj (op (h ⁻¹ᵁ W)))
    (b : ((Scheme.Modules.pullback h).obj H).val.obj (op (h ⁻¹ᵁ W))) :
    Hom.app (restrictTargetIso h V G H).hom.val (op (V.ι ⁻¹ᵁ W))
        (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app
            ((Scheme.Modules.pushforward h).obj
              ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).obj
                  (G, (Scheme.Modules.pullback h).obj H)))).val
          (op W) (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf T.toRingedSpace)
              (𝟙 (Stacks.RingedSpace.structureRingSheaf T.toRingedSpace).obj)).unit.app
              (PresheafOfModules.tensorObj (O := T.toRingedSpace.presheaf) G.val
              ((Scheme.Modules.pullback h).obj H).val)) (op (h ⁻¹ᵁ W)) (x ⊗ₜ b))) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf ((h ⁻¹ᵁ V).toScheme.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf
          ((h ⁻¹ᵁ V).toScheme.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := ((h ⁻¹ᵁ V).toScheme.toRingedSpace).presheaf)
          ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G).val
          (((Scheme.Modules.pullback (h ∣_ V)).obj
            ((Scheme.Modules.restrictFunctor V.ι).obj H))).val))
          (op ((h ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)))
        (G.val.map (homOfLE (image_restrict_preimage_le h V W)).op x ⊗ₜ
          Hom.app ((pullbackRestrictIso h V).hom.app H).val (op ((h ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)))
            (((Scheme.Modules.pullback h).obj H).val.map
              (homOfLE (image_restrict_preimage_le h V W)).op b)) := by
  refine Eq.trans (PresheafOfModules.comp_app_apply
    ((restrictPushforwardIso h V).hom.app
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).obj
          (G, (Scheme.Modules.pullback h).obj H))).val
    ((Scheme.Modules.pushforward (h ∣_ V)).map
      (restrictTensorIso (h ⁻¹ᵁ V).ι G ((Scheme.Modules.pullback h).obj H) ≪≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(h ⁻¹ᵁ V).toScheme.toRingedSpace.presheaf,
            (h ⁻¹ᵁ V).toScheme.toRingedSpace.IsSheaf⟩)).mapIso
          (Iso.prod (Iso.refl ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G))
            ((pullbackRestrictIso h V).app H))).hom).val _ _) ?_
  refine Eq.trans (congrArg _ (restrictPushforwardIso_hom_restrictUnit h V
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).obj
        (G, (Scheme.Modules.pullback h).obj H)) W
    (Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.RingedSpace.structureRingSheaf T.toRingedSpace)
        (𝟙 (Stacks.RingedSpace.structureRingSheaf T.toRingedSpace).obj)).unit.app
        (PresheafOfModules.tensorObj (O := T.toRingedSpace.presheaf) G.val
        ((Scheme.Modules.pullback h).obj H).val)) (op (h ⁻¹ᵁ W)) (x ⊗ₜ b)))) ?_
  refine Eq.trans (congrArg _ (tensorSheafUnit_val_map G ((Scheme.Modules.pullback h).obj H)
    (homOfLE (image_restrict_preimage_le h V W)).op x b)) ?_
  refine Eq.trans (PresheafOfModules.comp_app_apply
    (restrictTensorIso (h ⁻¹ᵁ V).ι G ((Scheme.Modules.pullback h).obj H)).hom.val
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(h ⁻¹ᵁ V).toScheme.toRingedSpace.presheaf, (h ⁻¹ᵁ V).toScheme.toRingedSpace.IsSheaf⟩)).map
      (Iso.prod (Iso.refl ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G))
        ((pullbackRestrictIso h V).app H)).hom).val _ _) ?_
  refine Eq.trans (congrArg _ (restrictTensorIso_hom_unit_tmul (h ⁻¹ᵁ V).ι G
    ((Scheme.Modules.pullback h).obj H) ((h ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)) _ _)) ?_
  exact tensorSheaf_map_unit_tmul (h ⁻¹ᵁ V).toScheme.toRingedSpace
    (Iso.refl ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G)).hom
    ((pullbackRestrictIso h V).app H).hom (op ((h ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W))) _ _

/-- `restrictSourceIso` undone: its inverse carries the sheafification-unit image of the pure
tensor of two restricted sections back to the restriction of the sheafification-unit image of
the pure tensor upstairs. -/
lemma restrictSourceIso_inv_unit_tmul (W : S.Opens)
    (x : ((Scheme.Modules.pushforward h).obj G).val.obj (op W)) (y : H.val.obj (op W)) :
    Hom.app (restrictSourceIso h V G H).inv.val (op (V.ι ⁻¹ᵁ W))
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf V.toScheme.toRingedSpace)
            (𝟙 (Stacks.RingedSpace.structureRingSheaf V.toScheme.toRingedSpace).obj)).unit.app
            (PresheafOfModules.tensorObj (O := V.toScheme.toRingedSpace.presheaf)
            (((Scheme.Modules.pushforward (h ∣_ V)).obj
              ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G))).val
                  ((Scheme.Modules.restrictFunctor V.ι).obj H).val)) (op (V.ι ⁻¹ᵁ W))
          (Hom.app ((restrictPushforwardIso h V).hom.app G).val (op (V.ι ⁻¹ᵁ W))
              (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app
                ((Scheme.Modules.pushforward h).obj G)).val (op W) x) ⊗ₜ
            Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app H).val (op W) y)) =
      Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩)).obj
            ((Scheme.Modules.pushforward h).obj G, H))).val (op W)
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf S.toRingedSpace)
            (𝟙 (Stacks.RingedSpace.structureRingSheaf S.toRingedSpace).obj)).unit.app
            (PresheafOfModules.tensorObj (O := S.toRingedSpace.presheaf)
            ((Scheme.Modules.pushforward h).obj G).val H.val)) (op W) (x ⊗ₜ y)) := by
  refine Eq.trans (congrArg (Hom.app (restrictSourceIso h V G H).inv.val (op (V.ι ⁻¹ᵁ W)))
    (restrictSourceIso_hom_restrictUnit_unit_tmul h V G H W x y).symm) ?_
  exact app_comp_eq_self _ _ (restrictSourceIso h V G H).hom_inv_id _ _

/-- The restriction of the projection-formula morphism on the restriction of a
sheafification-unit image of a pure tensor `x ⊗ y`: it is the restriction of the
sheafification-unit image of `x ⊗ η(y)`, `η` being the unit of `h^* ⊣ h_*`. -/
lemma restrictFunctor_map_projectionFormulaMap_restrictUnit (W : S.Opens)
    (x : ((Scheme.Modules.pushforward h).obj G).val.obj (op W)) (y : H.val.obj (op W)) :
    Hom.app ((Scheme.Modules.restrictFunctor V.ι).map (projectionFormulaMap h G H)).val
        (op (V.ι ⁻¹ᵁ W))
        (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩)).obj
              ((Scheme.Modules.pushforward h).obj G, H))).val (op W)
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf S.toRingedSpace)
              (𝟙 (Stacks.RingedSpace.structureRingSheaf S.toRingedSpace).obj)).unit.app
              (PresheafOfModules.tensorObj (O := S.toRingedSpace.presheaf)
              ((Scheme.Modules.pushforward h).obj G).val H.val)) (op W) (x ⊗ₜ y))) =
      Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app
          ((Scheme.Modules.pushforward h).obj ((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).obj
            (G, (Scheme.Modules.pullback h).obj H)))).val (op W)
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf T.toRingedSpace)
            (𝟙 (Stacks.RingedSpace.structureRingSheaf T.toRingedSpace).obj)).unit.app
            (PresheafOfModules.tensorObj (O := T.toRingedSpace.presheaf) G.val
            ((Scheme.Modules.pullback h).obj H).val))
          (op (h ⁻¹ᵁ W)) (x ⊗ₜ pullbackUnit h.toLRSHom.toShHom H (op W) y)) := by
  refine Eq.trans (restrictUnit_naturality V.ι (projectionFormulaMap h G H) (op W) _) ?_
  exact congrArg (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app
      ((Scheme.Modules.pushforward h).obj ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.toRingedSpace.presheaf,
          T.toRingedSpace.IsSheaf⟩)).obj
        (G, (Scheme.Modules.pullback h).obj H)))).val (op W))
    (projectionFormulaMap_unit_tmul h G H (op W) x y)

/-- Every section of `(h ∣_ V)_*(G|_{h⁻¹V})` over the preimage in `V` of an open `W` of `S` is,
through the restriction-direct-image comparison, the restriction of a section of `h_*G` over
`W`, provided `W` lies in `V`. -/
lemma exists_restrictPushforwardIso_hom_restrictUnit_eq (W : S.Opens)
    (hW : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W)
    (x' : ((Scheme.Modules.pushforward (h ∣_ V)).obj
      ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G)).val.obj (op (V.ι ⁻¹ᵁ W))) :
    ∃ x : ((Scheme.Modules.pushforward h).obj G).val.obj (op W),
      Hom.app ((restrictPushforwardIso h V).hom.app G).val (op (V.ι ⁻¹ᵁ W))
        (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app
          ((Scheme.Modules.pushforward h).obj G)).val (op W) x) = x' := by
  refine (exists_restrictUnit_eq V.ι ((Scheme.Modules.pushforward h).obj G) W hW
    (Hom.app ((restrictPushforwardIso h V).inv.app G).val (op (V.ι ⁻¹ᵁ W)) x')).elim
    fun x hx => ⟨x, ?_⟩
  refine Eq.trans (congrArg (Hom.app ((restrictPushforwardIso h V).hom.app G).val
    (op (V.ι ⁻¹ᵁ W))) hx) ?_
  exact app_comp_eq_self _ _ ((restrictPushforwardIso h V).inv_hom_id_app G) _ _

/-! ### The restriction of the projection-formula morphism -/

/-- The conjugate of the restriction of `projectionFormulaMap h G H` by `restrictSourceIso` and
`restrictTargetIso` carries the sheafification-unit image of the pure tensor of two restricted
sections `x|_V ⊗ y|_V` to the sheafification-unit image of `x|_V ⊗ η(y|_V)`, `η` being the unit
of `(h ∣_ V)^* ⊣ (h ∣_ V)_*`. -/
lemma projectionFormulaMap_restrict_unit_tmul (W : S.Opens)
    (x : ((Scheme.Modules.pushforward h).obj G).val.obj (op W)) (y : H.val.obj (op W)) :
    Hom.app ((restrictSourceIso h V G H).inv ≫
          (Scheme.Modules.restrictFunctor V.ι).map (projectionFormulaMap h G H) ≫
            (restrictTargetIso h V G H).hom).val (op (V.ι ⁻¹ᵁ W))
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf V.toScheme.toRingedSpace)
            (𝟙 (Stacks.RingedSpace.structureRingSheaf V.toScheme.toRingedSpace).obj)).unit.app
            (PresheafOfModules.tensorObj (O := V.toScheme.toRingedSpace.presheaf)
            (((modulePushforward (h ∣_ V).toLRSHom.toShHom).obj
              ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G))).val
                  ((Scheme.Modules.restrictFunctor V.ι).obj H).val)) (op (V.ι ⁻¹ᵁ W))
          (Hom.app ((restrictPushforwardIso h V).hom.app G).val (op (V.ι ⁻¹ᵁ W))
              (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app
                ((Scheme.Modules.pushforward h).obj G)).val (op W) x) ⊗ₜ
            Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app H).val (op W) y)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf ((h ⁻¹ᵁ V).toScheme.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf
          ((h ⁻¹ᵁ V).toScheme.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := ((h ⁻¹ᵁ V).toScheme.toRingedSpace).presheaf)
          ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G).val
          (((modulePullback (h ∣_ V).toLRSHom.toShHom).obj
            ((Scheme.Modules.restrictFunctor V.ι).obj H))).val))
          ((opensMap (h ∣_ V).toLRSHom.toShHom).op.obj (op (V.ι ⁻¹ᵁ W)))
        (Hom.app ((restrictPushforwardIso h V).hom.app G).val (op (V.ι ⁻¹ᵁ W))
            (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app
              ((Scheme.Modules.pushforward h).obj G)).val (op W) x) ⊗ₜ
          pullbackUnit (h ∣_ V).toLRSHom.toShHom
            ((Scheme.Modules.restrictFunctor V.ι).obj H) (op (V.ι ⁻¹ᵁ W))
            (Hom.app ((Scheme.Modules.restrictAdjunction V.ι).unit.app H).val (op W) y)) := by
  refine Eq.trans (PresheafOfModules.comp_app_apply (restrictSourceIso h V G H).inv.val
    ((Scheme.Modules.restrictFunctor V.ι).map (projectionFormulaMap h G H) ≫
      (restrictTargetIso h V G H).hom).val (op (V.ι ⁻¹ᵁ W)) _) ?_
  refine Eq.trans (congrArg (Hom.app
      ((Scheme.Modules.restrictFunctor V.ι).map (projectionFormulaMap h G H) ≫
        (restrictTargetIso h V G H).hom).val (op (V.ι ⁻¹ᵁ W)))
    (restrictSourceIso_inv_unit_tmul h V G H W x y)) ?_
  refine Eq.trans (PresheafOfModules.comp_app_apply
    ((Scheme.Modules.restrictFunctor V.ι).map (projectionFormulaMap h G H)).val
    (restrictTargetIso h V G H).hom.val (op (V.ι ⁻¹ᵁ W)) _) ?_
  refine Eq.trans (congrArg (Hom.app (restrictTargetIso h V G H).hom.val (op (V.ι ⁻¹ᵁ W)))
    (restrictFunctor_map_projectionFormulaMap_restrictUnit h V G H W x y)) ?_
  refine Eq.trans (restrictTargetIso_hom_restrictUnit_unit_tmul h V G H W x
    (pullbackUnit h.toLRSHom.toShHom H (op W) y)) ?_
  exact congrArg₂ (fun p q => Hom.app ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.RingedSpace.structureRingSheaf ((h ⁻¹ᵁ V).toScheme.toRingedSpace))
      (𝟙 (Stacks.RingedSpace.structureRingSheaf ((h ⁻¹ᵁ V).toScheme.toRingedSpace)).obj)).unit.app
      (PresheafOfModules.tensorObj (O := ((h ⁻¹ᵁ V).toScheme.toRingedSpace).presheaf)
      ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G).val
      (((Scheme.Modules.pullback (h ∣_ V)).obj
        ((Scheme.Modules.restrictFunctor V.ι).obj H))).val))
      (op ((h ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W))) (p ⊗ₜ q))
    (restrictPushforwardIso_hom_restrictUnit h V G W x).symm
    (pullbackRestrictIso_hom_pullbackUnit h V H W y)

/-- `projectionFormulaMap_restrict_unit_tmul` for arbitrary sections of the two restrictions over
the preimage in `V` of an open `W` of `S` lying in `V`. -/
lemma projectionFormulaMap_restrict_app (W : S.Opens) (hW : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W)
    (x' : ((modulePushforward (h ∣_ V).toLRSHom.toShHom).obj
      ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G)).val.obj (op (V.ι ⁻¹ᵁ W)))
    (y' : ((Scheme.Modules.restrictFunctor V.ι).obj H).val.obj (op (V.ι ⁻¹ᵁ W))) :
    Hom.app ((restrictSourceIso h V G H).inv ≫
          (Scheme.Modules.restrictFunctor V.ι).map (projectionFormulaMap h G H) ≫
            (restrictTargetIso h V G H).hom).val (op (V.ι ⁻¹ᵁ W))
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf V.toScheme.toRingedSpace)
            (𝟙 (Stacks.RingedSpace.structureRingSheaf V.toScheme.toRingedSpace).obj)).unit.app
            (PresheafOfModules.tensorObj (O := V.toScheme.toRingedSpace.presheaf)
            (((modulePushforward (h ∣_ V).toLRSHom.toShHom).obj
              ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G))).val
                  ((Scheme.Modules.restrictFunctor V.ι).obj H).val)) (op (V.ι ⁻¹ᵁ W)) (x' ⊗ₜ y')) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf ((h ⁻¹ᵁ V).toScheme.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf
          ((h ⁻¹ᵁ V).toScheme.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := ((h ⁻¹ᵁ V).toScheme.toRingedSpace).presheaf)
          ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G).val
          (((modulePullback (h ∣_ V).toLRSHom.toShHom).obj
            ((Scheme.Modules.restrictFunctor V.ι).obj H))).val))
          ((opensMap (h ∣_ V).toLRSHom.toShHom).op.obj (op (V.ι ⁻¹ᵁ W)))
        (x' ⊗ₜ pullbackUnit (h ∣_ V).toLRSHom.toShHom
          ((Scheme.Modules.restrictFunctor V.ι).obj H) (op (V.ι ⁻¹ᵁ W)) y') := by
  refine (exists_restrictUnit_eq V.ι H W hW y').elim fun y hy => ?_
  refine (exists_restrictPushforwardIso_hom_restrictUnit_eq h V G W hW x').elim fun x hx => ?_
  subst hy hx
  exact projectionFormulaMap_restrict_unit_tmul h V G H W x y

/-- `projectionFormulaMap_restrict_app` over every open of `V`. -/
lemma projectionFormulaMap_restrict_hom_app :
    ∀ (W₁ : (Opens V.toScheme.toRingedSpace.carrier)ᵒᵖ)
      (x' : ((modulePushforward (h ∣_ V).toLRSHom.toShHom).obj
        ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G)).val.obj W₁)
      (y' : ((Scheme.Modules.restrictFunctor V.ι).obj H).val.obj W₁),
      Hom.app ((restrictSourceIso h V G H).inv ≫
            (Scheme.Modules.restrictFunctor V.ι).map (projectionFormulaMap h G H) ≫
              (restrictTargetIso h V G H).hom).val W₁
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf V.toScheme.toRingedSpace)
              (𝟙 (Stacks.RingedSpace.structureRingSheaf V.toScheme.toRingedSpace).obj)).unit.app
              (PresheafOfModules.tensorObj (O := V.toScheme.toRingedSpace.presheaf)
              (((modulePushforward (h ∣_ V).toLRSHom.toShHom).obj
              ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G))).val
                  ((Scheme.Modules.restrictFunctor V.ι).obj H).val)) W₁ (x' ⊗ₜ y')) =
        Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf ((h ⁻¹ᵁ V).toScheme.toRingedSpace))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf
            ((h ⁻¹ᵁ V).toScheme.toRingedSpace)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := ((h ⁻¹ᵁ V).toScheme.toRingedSpace).presheaf)
            ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G).val
            (((modulePullback (h ∣_ V).toLRSHom.toShHom).obj
              ((Scheme.Modules.restrictFunctor V.ι).obj H))).val))
            ((opensMap (h ∣_ V).toLRSHom.toShHom).op.obj W₁)
          (x' ⊗ₜ pullbackUnit (h ∣_ V).toLRSHom.toShHom
            ((Scheme.Modules.restrictFunctor V.ι).obj H) W₁ y') := by
  intro W₁ x' y'
  obtain ⟨W, hW, rfl⟩ : ∃ W : S.Opens, V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W ∧ W₁ = op (V.ι ⁻¹ᵁ W) :=
    ⟨V.ι ''ᵁ W₁.unop, image_preimage_image V.ι W₁.unop, by rw [V.ι.preimage_image_eq]⟩
  exact projectionFormulaMap_restrict_app h V G H W hW x' y'

/-- Conjugated by `restrictSourceIso` and `restrictTargetIso`, the restriction to an open
`V ⊆ S` of `projectionFormulaMap h G H` is `projectionFormulaMap (h ∣_ V) (G|_{h⁻¹V}) (H|_V)`. -/
theorem projectionFormulaMap_restrict :
    (restrictSourceIso h V G H).inv ≫
        (Scheme.Modules.restrictFunctor V.ι).map (projectionFormulaMap h G H) ≫
          (restrictTargetIso h V G H).hom =
      projectionFormulaMap (h ∣_ V) ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G)
        ((Scheme.Modules.restrictFunctor V.ι).obj H) :=
  projectionFormulaMap_unique (h ∣_ V) _ _ _ (projectionFormulaMap_restrict_hom_app h V G H)

/-! ### Stacks 0FZE -/

/-- The restriction to an affine open `V ⊆ S` of the projection-formula morphism of an affine
morphism with quasi-coherent arguments is invertible. -/
theorem isIso_projectionFormulaMap_restrict [IsAffineHom h] (hG : G.IsQuasicoherent)
    (hH : H.IsQuasicoherent) (hV : IsAffineOpen V) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map (projectionFormulaMap h G H)) := by
  have : IsAffine V.toScheme := hV
  have : G.IsQuasicoherent := hG
  have : H.IsQuasicoherent := hH
  have hrestrict : IsIso (projectionFormulaMap (h ∣_ V)
      ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ V).ι).obj G)
      ((Scheme.Modules.restrictFunctor V.ι).obj H)) :=
    isIso_projectionFormulaMap_of_isAffine (h ∣_ V)
      (Scheme.Modules.isQuasicoherent_restrictFunctor (h ⁻¹ᵁ V).ι G)
      (Scheme.Modules.isQuasicoherent_restrictFunctor V.ι H)
  have hsq : IsIso ((restrictSourceIso h V G H).inv ≫
      (Scheme.Modules.restrictFunctor V.ι).map (projectionFormulaMap h G H) ≫
        (restrictTargetIso h V G H).hom) := by
    rwa [projectionFormulaMap_restrict h V G H]
  exact isIso_of_isIso_conj (restrictSourceIso h V G H) (restrictTargetIso h V G H) _ hsq

/-- Let `h : T ⟶ S` be an affine morphism of schemes, `G` a quasi-coherent `𝒪_T`-module and `H` a
quasi-coherent `𝒪_S`-module. Then the canonical projection-formula morphism

`h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)`

is invertible. -/
@[stacks 0FZE]
theorem isIso_projectionFormulaMap [IsAffineHom h] (hG : G.IsQuasicoherent)
    (hH : H.IsQuasicoherent) : IsIso (projectionFormulaMap h G H) :=
  isIso_projectionFormulaMap_of_restrict_affineOpens h G H
    fun V => isIso_projectionFormulaMap_restrict h (V : S.Opens) G H hG hH V.2

/-- `isIso_projectionFormulaMap` as an isomorphism: for an affine morphism of schemes and
quasi-coherent modules, `h_*G ⊗_{𝒪_S} H ≅ h_*(G ⊗_{𝒪_T} h^*H)`, the forward map being the
canonical projection-formula morphism. -/
def projectionFormulaIsoOfQuasicoherent [IsAffineHom h] (hG : G.IsQuasicoherent)
    (hH : H.IsQuasicoherent) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩)).obj
        ((Scheme.Modules.pushforward h).obj G, H) ≅
      (Scheme.Modules.pushforward h).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).obj
            (G, (Scheme.Modules.pullback h).obj H)) :=
  haveI := isIso_projectionFormulaMap h G H hG hH
  projectionFormulaIso h G H

end Stacks.AlgebraicGeometry.ProjectionFormula

end
