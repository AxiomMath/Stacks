module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Triple
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction of sheaves of modules is left adjoint to the direct image

Let `w : X ⥤ Y` be a functor of sites which is both continuous and cocontinuous, and let `O_Y` be
a sheaf of rings on `Y`. Restriction along `w` is a morphism of topoi `g` whose inverse image
`g^{-1}` is restriction and whose direct image `g_*` is the right Kan extension `{}_s w`
(Stacks 00XO, 00XT). Read with the restricted sheaf of rings `O_X = g^{-1}O_Y` and its
tautological structure map `O_Y ⟶ g_*g^{-1}O_Y`, the inverse image of sheaves of modules
`g^* = g^{-1}` (Stacks 03D2) is left adjoint to the direct image of sheaves of modules
`Stacks.SheafOfModules.pushforwardCocontinuous` (Stacks 03D6 (1), 03D7).

The adjunction is the presheaf-level adjunction
`Stacks.SheafOfModules.pushforward₀RanPushforwardAdjunction` restricted to sheaves, both functors
carrying sheaves to sheaves. It needs no smallness at all, unlike the adjoint functor theorem
behind `Stacks.SheafOfModules.inverseImageCocontinuousAdjunction`.

When `w` is moreover fully faithful its counit is an isomorphism (Stacks 00XT), so every left
adjoint `g_!` of the inverse image has invertible unit: `g^{-1}g_! = id` (Stacks 0789, 0797).

## Main results

* `Stacks.SheafOfModules.inverseImagePushforwardCocontinuousTautologicalAdjunction`:
  `g^{-1} ⊣ g_*` for the
  tautological structure map.
* `Stacks.SheafOfModules.pushforwardPushforwardCocontinuousInverseImageRingAdjunction`: the same
  for a sheaf of
  rings on `X` equal to the restricted one, with the transposed structure map.
* `Stacks.SheafOfModules.isIso_counit_inverseImagePushforwardCocontinuousAdjunction`: its counit
  is invertible when `w` is fully faithful.
* `Stacks.SheafOfModules.isIso_unit_of_adjunction_inverseImage`: hence every left adjoint of the
  inverse image along a fully faithful functor has invertible unit.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v r v₁ u₁ v₂ u₂

namespace Stacks.SheafOfModules

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (w : X ⥤ Y)
  {JX : GrothendieckTopology X} {JY : GrothendieckTopology Y}
  [w.IsContinuous JX JY] [w.IsCocontinuous JX JY]
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]
  (OY : Sheaf JY RingCat.{r})

/-- Restriction of sheaves of modules, read on underlying presheaves of modules, is restriction of
presheaves of modules. -/
def forgetCompPushforward₀Iso :
    _root_.SheafOfModules.forget.{v} OY ⋙ PresheafOfModules.pushforward₀.{v} w OY.obj ≅
      inverseImage.{v} JX JY w OY ⋙
        _root_.SheafOfModules.forget.{v} (inverseImageRing JX JY w OY) :=
  NatIso.ofComponents
    (fun _M ↦
      { hom := PresheafOfModules.homMk (𝟙 _) (fun _ _ _ ↦ rfl)
        inv := PresheafOfModules.homMk (𝟙 _) (fun _ _ _ ↦ rfl)
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun _ ↦ rfl)

/-- The **tautological structure map** `O_Y ⟶ g_*g^{-1}O_Y` of sheaves of rings: the unit of the
right Kan extension adjunction on underlying presheaves of rings. -/
def tautologicalStructureMap :
    OY ⟶ (w.sheafPushforwardCocontinuous RingCat.{r} JX JY).obj (inverseImageRing JX JY w OY) :=
  ObjectProperty.homMk (ranUnitRing w OY.obj)

/-- The direct image of sheaves of modules for the tautological structure map, read on underlying
presheaves of modules, is the presheaf-level direct image for the tautological structure map. -/
def forgetCompRanPushforwardIso :
    _root_.SheafOfModules.forget.{v} (inverseImageRing JX JY w OY) ⋙
        ranPushforward.{v} w (ranUnitRing w OY.obj) ≅
      pushforwardCocontinuous.{v} w (tautologicalStructureMap w OY) ⋙
        _root_.SheafOfModules.forget.{v} OY :=
  Iso.refl _

/-- **Restriction of sheaves of modules along a continuous and cocontinuous functor is left
adjoint to the direct image** (Stacks 03D7 for the morphism of topoi of Stacks 00XO), for the
tautological structure map. -/
@[sga "4 III 2.4" "special case"]
def inverseImagePushforwardCocontinuousTautologicalAdjunction :
    inverseImage.{v} JX JY w OY ⊣ pushforwardCocontinuous.{v} w (tautologicalStructureMap w OY) :=
  (pushforward₀RanPushforwardAdjunction.{v} w OY.obj).restrictFullyFaithful
    (_root_.SheafOfModules.fullyFaithfulForget OY)
    (_root_.SheafOfModules.fullyFaithfulForget (inverseImageRing JX JY w OY))
    (forgetCompPushforward₀Iso w OY) (forgetCompRanPushforwardIso w OY)

omit [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F] in
/-- The transpose of the identity of the restricted sheaf of rings is the tautological structure
map. -/
lemma homEquiv_id_eq_tautologicalStructureMap :
    (w.sheafAdjunctionCocontinuous RingCat.{r} JX JY).homEquiv _ _
      (𝟙 (inverseImageRing JX JY w OY)) = tautologicalStructureMap w OY := by
  refine Sheaf.hom_ext ?_
  rw [Adjunction.homEquiv_unit]
  simp only [CategoryTheory.Functor.map_id]
  exact Functor.sheafAdjunctionCocontinuous_unit_app_hom w RingCat.{r} JX JY OY

omit [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F] in
/-- The legs of the transpose of an identification `g^{-1}O_Y = O_X`: at `(U, ψ : V ⟶ w(U))` the
transpose is restriction along `ψ` followed by the identification. -/
lemma homEquiv_eqToHom_app_ranπ {OX : Sheaf JX RingCat.{r}}
    (h : inverseImageRing JX JY w OY = OX) (V : Yᵒᵖ) (j : StructuredArrow V w.op) :
    ((w.sheafAdjunctionCocontinuous RingCat.{r} JX JY).homEquiv _ _ (eqToHom h)).hom.app V ≫
        ranπ w.op OX.obj V j =
      OY.obj.map j.hom ≫ (eqToHom h).hom.app j.right := by
  subst h
  rw [eqToHom_refl, homEquiv_id_eq_tautologicalStructureMap]
  exact ranAdjunction_unit_app_ranπ w.op OY.obj V j

/-- **Restriction of sheaves of modules is left adjoint to the direct image**, for a sheaf of rings
`O_X` on the source equal to the restriction of `O_Y`, the structure map `O_Y ⟶ w_*O_X` being the
transpose of that equality and restriction reading scalars through it. -/
def pushforwardPushforwardCocontinuousInverseImageRingAdjunction {OX : Sheaf JX RingCat.{r}}
    (h : inverseImageRing JX JY w OY = OX) :
    _root_.SheafOfModules.pushforward.{v} (F := w) (eqToHom h.symm) ⊣
      pushforwardCocontinuous.{v} w
        ((w.sheafAdjunctionCocontinuous RingCat.{r} JX JY).homEquiv _ _ (eqToHom h)) := by
  subst h
  rw [eqToHom_refl, homEquiv_id_eq_tautologicalStructureMap]
  exact inverseImagePushforwardCocontinuousTautologicalAdjunction w OY

section FullyFaithful

variable [w.Full] [w.Faithful]

/-- **The counit `g^{-1}g_* ⟶ id` is an isomorphism on sheaves of modules** when `w` is fully
faithful: on underlying presheaves of abelian groups it is the counit of the right Kan extension
along a fully faithful functor (Stacks 00XT). -/
theorem isIso_counit_inverseImagePushforwardCocontinuousAdjunction :
    IsIso (inverseImagePushforwardCocontinuousTautologicalAdjunction (JX := JX) w OY).counit := by
  have hpre : ∀ P : PresheafOfModules.{v} (inverseImageRing JX JY w OY).obj,
      IsIso ((pushforward₀RanPushforwardAdjunction.{v} w OY.obj).counit.app P) := fun P ↦ by
    have : IsIso ((PresheafOfModules.toPresheaf _).map
        ((pushforward₀RanPushforwardAdjunction.{v} w OY.obj).counit.app P)) := by
      change IsIso (w.op.ranCounit.app P.presheaf)
      infer_instance
    exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  have : ∀ N, IsIso ((inverseImagePushforwardCocontinuousTautologicalAdjunction (JX := JX) w
      OY).counit.app N) :=
    fun N ↦ by
      have : IsIso ((_root_.SheafOfModules.forget.{v} _).map
          ((inverseImagePushforwardCocontinuousTautologicalAdjunction (JX := JX) w OY).counit.app
              N)) := by
        have e := Adjunction.map_restrictFullyFaithful_counit_app
          (pushforward₀RanPushforwardAdjunction.{v} w OY.obj)
          (_root_.SheafOfModules.fullyFaithfulForget OY)
          (_root_.SheafOfModules.fullyFaithfulForget (inverseImageRing JX JY w OY))
          (forgetCompPushforward₀Iso w OY) (forgetCompRanPushforwardIso w OY) N
        refine (congrArg IsIso e).mpr ?_
        have := hpre ((_root_.SheafOfModules.forget (inverseImageRing JX JY w OY)).obj N)
        exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso'
          ((PresheafOfModules.pushforward₀ w OY.obj).mapIso
            ((forgetCompRanPushforwardIso w OY).app N).symm).isIso_hom inferInstance)
      exact isIso_of_reflects_iso _ (_root_.SheafOfModules.forget.{v} _)
  exact NatIso.isIso_of_isIso_app _

/-- **Every left adjoint `g_!` of the inverse image of sheaves of modules along a fully faithful,
continuous and cocontinuous functor has invertible unit**: `g^{-1}g_! = id` (Stacks 0797, 0789).
The inverse image is also a left adjoint, of the direct image, with invertible counit, and in an
adjoint triple the unit of the first adjunction is invertible exactly when the counit of the
second is. -/
theorem isIso_unit_of_adjunction_inverseImage
    {L : _root_.SheafOfModules.{v} (inverseImageRing JX JY w OY) ⥤ _root_.SheafOfModules.{v} OY}
    (adj : L ⊣ inverseImage.{v} JX JY w OY) : IsIso adj.unit :=
  (Adjunction.Triple.isIso_unit_iff_isIso_counit
    ⟨adj, inverseImagePushforwardCocontinuousTautologicalAdjunction w OY⟩).mpr
    (isIso_counit_inverseImagePushforwardCocontinuousAdjunction w OY)

end FullyFaithful

end Stacks.SheafOfModules

end
