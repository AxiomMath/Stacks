module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderProjectionFormulaMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence

/-!
# Inserting a global section into a tensor product of sheaves of modules

Let `X` be a scheme, let `N` be a sheaf of `𝒪_X`-modules and let `s` be a section of `N` over
the whole of `X`.  Multiplication by `s` is a morphism `𝒪_X ⟶ N` of sheaves of modules, and
tensoring it on the right of a sheaf `F` gives the morphism `F ⟶ F ⊗_{𝒪_X} N`, `x ↦ x ⊗ s`,
by which a formula on pure tensors with a *fixed* second factor is read as an identity of
morphisms of sheaves.

This is the device by which
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionSheafIntegrable.lean` states the
extension rule `∇(x ⊗ ω) = ∇(x) ∧ ω + x ⊗ d ω` of [Stacks, Section 60.15, Tag 07J5] at the level
of sheaves: `x ⊗ ω` is `Crystalline.insertHom` applied to `x`, and the two terms on the right
are morphisms of sheaves applied to `x`.

## Main definitions

* `Crystalline.restrFromTop` — the restriction of a global section of a sheaf of modules to an
  open.
* `Crystalline.unitHom` — **a global section of `N` read as a morphism `𝒪_X ⟶ N`**, `r ↦ r s`.
* `Crystalline.insertHom` — **`F ⟶ F ⊗_{𝒪_X} N`, `x ↦ x ⊗ s`**, the right unitor followed by
  `F` tensored with `Crystalline.unitHom`.

## Main results

* `Crystalline.unitHom_val_app_top_one` — the morphism `𝒪_X ⟶ N` carries `1` to `s`.
* `Crystalline.leftUnitorInv_val_app` and `Crystalline.rightUnitorInv_val_app` — the inverses of
  the two unitors on local sections: `x ↦ 1 ⊗ x` and `x ↦ x ⊗ 1`, and
  `Crystalline.leftUnitor_val_app` — the left unitor itself, `r ⊗ x ↦ r x`.
* `Crystalline.insertHom_val_app` — **`Crystalline.insertHom` carries a local section `x` to the
  pure tensor `x ⊗ s|_W`**, so it really is "tensoring with `s`".
* `Crystalline.insertHom_comp_braiding` — composing it with the symmetry constraint gives
  `(λ_ F)⁻¹` followed by `Crystalline.unitHom` whiskered on the right.  This is what lets a
  computation with `x ⊗ s` be carried out with the two factors in the other order, where the
  symmetry constraint has cancelled and only right whiskering is left.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules braidedCategorySchemeModules

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose TopCat.Sheaf AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Presheaf.IsSheaf

variable (X : Scheme.{u}) (N : X.Modules)

/-! ### Restricting a global section -/

/-- Restriction along an identity does nothing, on the sections of a sheaf of modules on a
scheme. -/
theorem pmap_id_apply (W : (Opens ↑X)ᵒᵖ) (x : N.val.obj W) : N.val.map (𝟙 W) x = x := by
  rw [← PresheafOfModules.presheaf_map_apply_coe, N.val.presheaf.map_id]
  rfl

/-- **The restriction of a global section of a sheaf of modules to an open.** -/
def restrFromTop (W : (Opens ↑X)ᵒᵖ) (s : Γ(N, ⊤)) : N.val.obj W :=
  N.val.map (homOfLE (le_top : W.unop ≤ ⊤)).op s

@[simp]
theorem restrFromTop_top (s : Γ(N, ⊤)) : restrFromTop X N (op ⊤) s = s :=
  pmap_id_apply X N (op ⊤) s

theorem restrFromTop_map {W V : (Opens ↑X)ᵒᵖ} (g : W ⟶ V) (s : Γ(N, ⊤)) :
    N.val.map g (restrFromTop X N W s) = restrFromTop X N V s :=
  (N.val.map_comp_apply (homOfLE (le_top : W.unop ≤ ⊤)).op g s).symm

/-! ### A global section as a morphism out of the structure sheaf -/

/-- **A global section `s` of a sheaf of `𝒪_X`-modules `N`, read as a morphism `𝒪_X ⟶ N`** of
sheaves of modules: over an open `W` it is `r ↦ r · s|_W`. -/
def unitHom (s : Γ(N, ⊤)) : schemeUnitModule X ⟶ N :=
  ⟨{ app W := ModuleCat.ofHom
       (LinearMap.toSpanSingleton ↑(X.ringCatSheaf.obj.obj W) ↑(N.val.obj W)
         (restrFromTop X N W s))
     naturality := fun {W V} g => ModuleCat.hom_ext (LinearMap.ext
       fun r : ↑(X.ringCatSheaf.obj.obj W) => by
         have h1 : N.val.map g (r • restrFromTop X N W s) =
             (X.ringCatSheaf.obj.map g).hom r • N.val.map g (restrFromTop X N W s) :=
           map_smulₛₗ (N.val.restrictₛₗ g) r (restrFromTop X N W s)
         show (X.ringCatSheaf.obj.map g).hom r • restrFromTop X N V s =
           N.val.map g (r • restrFromTop X N W s)
         rw [h1, restrFromTop_map]
         rfl) }⟩

theorem unitHom_val_app (s : Γ(N, ⊤)) (W : (Opens ↑X)ᵒᵖ)
    (r : ↑(X.ringCatSheaf.obj.obj W)) :
    (unitHom X N s).val.app W r = r • restrFromTop X N W s := rfl

/-- **The morphism `𝒪_X ⟶ N` of a global section carries `1` to that section.** -/
theorem unitHom_val_app_top_one (s : Γ(N, ⊤)) :
    (unitHom X N s).val.app (op ⊤) (1 : ↑(X.ringCatSheaf.obj.obj (op ⊤))) = s :=
  (one_smul _ (restrFromTop X N (op ⊤) s)).trans (restrFromTop_top X N s)

/-! ### The inverses of the two unitors on local sections -/

variable (F : X.Modules)

/-- The left unitor of `X.Modules` is the left unit isomorphism of the sheaf tensor product. -/
private theorem leftUnitor_eq_tensorSheafUnitLeftIso :
    (λ_ F) = Stacks.RingedSpace.tensorSheafUnitLeftIso X.toRingedSpace F :=
  Iso.ext (Stacks.RingedSpace.leftUnitor_sheafTensor_eq X.toRingedSpace F)

/-- **The inverse of the left unitor carries a local section `x` to the pure tensor `1 ⊗ x`.** -/
theorem leftUnitorInv_val_app (W : (Opens ↑X)ᵒᵖ) (x : F.val.obj W) :
    (λ_ F).inv.val.app W x =
      Stacks.PullbackTensorCoherence.tmul X.toRingedSpace (schemeUnitModule X) F W
        (1 : ↑(X.ringCatSheaf.obj.obj W)) x := by
  rw [leftUnitor_eq_tensorSheafUnitLeftIso]
  exact Stacks.RingedSpace.tensorSheafUnitLeftIso_inv_app_tensorSheafUnit X.toRingedSpace F W x

/-- **The left unitor carries the pure tensor `r ⊗ x` to `r · x`.** -/
theorem leftUnitor_val_app (W : (Opens ↑X)ᵒᵖ) (r : ↑(X.ringCatSheaf.obj.obj W))
    (x : F.val.obj W) :
    (λ_ F).hom.val.app W
        (Stacks.PullbackTensorCoherence.tmul X.toRingedSpace (schemeUnitModule X) F W r x) =
      r • x := by
  rw [leftUnitor_eq_tensorSheafUnitLeftIso]
  exact Stacks.RingedSpace.tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul X.toRingedSpace F W r x

/-- **The inverse of the right unitor carries a local section `x` to the pure tensor
`x ⊗ 1`.** -/
theorem rightUnitorInv_val_app (W : (Opens ↑X)ᵒᵖ) (x : F.val.obj W) :
    (ρ_ F).inv.val.app W x =
      Stacks.PullbackTensorCoherence.tmul X.toRingedSpace F (schemeUnitModule X) W x
        (1 : ↑(X.ringCatSheaf.obj.obj W)) := by
  have h : (ρ_ F) = Stacks.RingedSpace.tensorSheafUnitRightIso X.toRingedSpace F :=
    Iso.ext (Stacks.RingedSpace.rightUnitor_sheafTensor_eq X.toRingedSpace F)
  refine (congrArg (fun k : F ⊗ (schemeUnitModule X) ≅ F => k.inv.val.app W x) h).trans ?_
  exact Stacks.RingedSpace.tensorSheafUnitRightIso_inv_app_tensorSheafUnit X.toRingedSpace F W x

/-! ### Tensoring with a global section -/

/-- **`F ⟶ F ⊗_{𝒪_X} N`, `x ↦ x ⊗ s`**, for `s` a global section of `N`: the inverse of the
right unitor followed by `F` tensored with `Crystalline.unitHom`. -/
def insertHom (s : Γ(N, ⊤)) : F ⟶ F ⊗ N :=
  (ρ_ F).inv ≫ (F ◁ unitHom X N s)

/-- **`Crystalline.insertHom` carries a local section `x` to the pure tensor `x ⊗ s|_W`.** -/
theorem insertHom_val_app (s : Γ(N, ⊤)) (W : (Opens ↑X)ᵒᵖ) (x : F.val.obj W) :
    (insertHom X N F s).val.app W x =
      Stacks.PullbackTensorCoherence.tmul X.toRingedSpace F N W x (restrFromTop X N W s) := by
  have h1 : (insertHom X N F s).val.app W x =
      (F ◁ unitHom X N s).val.app W ((ρ_ F).inv.val.app W x) :=
    Stacks.SheafOfModules.comp_val_app_apply _ _ W x
  rw [h1, rightUnitorInv_val_app]
  have h2 := Stacks.RingedSpace.tensorSheaf_map_unit_tmul X.toRingedSpace (𝟙 F)
    (unitHom X N s) W x (1 : ↑(X.ringCatSheaf.obj.obj W))
  have h3 : (unitHom X N s).val.app W (1 : ↑(X.ringCatSheaf.obj.obj W)) =
      restrFromTop X N W s :=
    (unitHom_val_app X N s W 1).trans (one_smul _ _)
  have h4 : Stacks.PullbackTensorCoherence.tmul X.toRingedSpace F N W x
        ((unitHom X N s).val.app W (1 : ↑(X.ringCatSheaf.obj.obj W))) =
      Stacks.PullbackTensorCoherence.tmul X.toRingedSpace F N W x (restrFromTop X N W s) :=
    congrArg (Stacks.PullbackTensorCoherence.tmul X.toRingedSpace F N W x) h3
  exact Eq.trans (PresheafOfModules.hom_congr_apply
    (congrArg (fun k => SheafOfModules.Hom.val k)
      ((Stacks.SheafOfModules.Tensor.sheafTensor_obj_map X.toRingedSpace.sheaf F
          (unitHom X N s)).trans
        (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.toRingedSpace.sheaf (𝟙 F)
          (unitHom X N s)).symm)) W _) (h2.trans h4)

/-- **Tensoring with a global section, read through the symmetry constraint.**  Composing
`Crystalline.insertHom` with the symmetry constraint gives the inverse of the *left* unitor
followed by right whiskering of `Crystalline.unitHom`.

This is the shape in which a computation with `x ⊗ s` is carried out: on the right-hand side the
symmetry constraint has disappeared, and only right whiskering is left, which has a formula on
local pure tensors. -/
theorem insertHom_comp_braiding (s : Γ(N, ⊤)) :
    insertHom X N F s ≫ (β_ F N).hom = (λ_ F).inv ≫ (unitHom X N s ▷ F) := by
  have h1 : (F ◁ unitHom X N s) ≫ (β_ F N).hom =
      (β_ F (schemeUnitModule X)).hom ≫ (unitHom X N s ▷ F) :=
    BraidedCategory.braiding_naturality_right F (unitHom X N s)
  have h2 : (ρ_ F).inv ≫ (β_ F (schemeUnitModule X)).hom = (λ_ F).inv := by
    rw [Iso.inv_comp_eq]
    exact (Iso.eq_comp_inv _).2 (braiding_leftUnitor F)
  rw [insertHom, Category.assoc, h1, ← Category.assoc, h2]

end Crystalline

end

end
