module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonReading
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonUnitor

/-!
# Tensoring with a global section

For `𝒪_X`-modules `F` and `G` on a scheme `X` and a global section `s` of `G`, we construct the
morphism of `𝒪_X`-modules `F ⟶ F ⊗_{𝒪_X} G`, `x ↦ x ⊗ s`. Its restriction to an open `V` is
the morphism `tensorLocalSection` attached to the restriction `s|_V`, composing it with `𝟙 ⊗ φ`
for a morphism `φ : G ⟶ G'` gives the morphism attached to `φ(s)`, and for `G = 𝒪_X` and `s = 1`
it is the inverse of the right unitor.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.globalRestrict`: the restriction of a global
  section to an open.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorGlobalSection`: **the morphism
  `F ⟶ F ⊗_{𝒪_X} G`, `x ↦ x ⊗ s`, for a global section `s` of `G`.**

## Main results

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `tensorGlobalSection_app_apply`: the morphism on sections is `x ↦ x ⊗ s|_W`.
* `tensorGlobalSection_restrictFunctor`: **its restriction to an open `V` is
  `tensorLocalSection` at the restriction of the section.**
* `tensorGlobalSection_naturality`: **composing with `𝟙 ⊗ φ` moves the global section along
  `φ`.**
* `tensorGlobalSection_unit`: at `G = 𝒪_X` and `s = 1` it is the inverse right unitor.
* `isIso_tensorGlobalSection_unit`: at `G = 𝒪_X` and `s = 1` it is an isomorphism.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

attribute [local instance] moduleOfPresheafRing
attribute [local instance] moduleOfTensorSections

variable {X : Scheme.{u}} (F G : X.Modules)

/-- **The restriction of a global section to an open.** -/
def globalRestrict (s : Γ(G, ⊤)) (W : X.Opens) : Γ(G, W) :=
  G.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s

/-- Restricting a global section twice is restricting it once. -/
theorem globalRestrict_map {W W' : X.Opens} (h : W' ≤ W) (s : Γ(G, ⊤)) :
    G.presheaf.map (homOfLE h).op (globalRestrict G s W) = globalRestrict G s W' :=
  presheaf_map_homOfLE_comp G h (le_top : W ≤ ⊤) s

/-- The component over an open of the morphism `x ↦ x ⊗ s`. -/
def tensorGlobalSectionApp (s : Γ(G, ⊤)) (W : (Opens X.carrier)ᵒᵖ) :
    F.val.obj W ⟶ ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G)).val.obj W :=
  show ModuleCat.of ↑(X.presheaf.obj W) ↑(F.val.obj W) ⟶
      ModuleCat.of ↑(X.presheaf.obj W)
        ↑(((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G)).val.obj W) from
    ModuleCat.ofHom (tensorSectionLinear X F G W (globalRestrict G s W.unop))

/-- **The morphism `F ⟶ F ⊗_{𝒪_X} G`, `x ↦ x ⊗ s`, for a global section `s` of `G`.** -/
def tensorGlobalSection (s : Γ(G, ⊤)) :
    F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G) where
  val :=
    { app := tensorGlobalSectionApp F G s
      naturality := by
        intro W W' i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change toTensorSheafSection X.toRingedSpace F G W'
            ((F.val.map i) x ⊗ₜ[X.presheaf.obj W'] (globalRestrict G s W'.unop)) =
          (((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G)).val.map i)
            (toTensorSheafSection X.toRingedSpace F G W
              (x ⊗ₜ[X.presheaf.obj W] (globalRestrict G s W.unop)))
        rw [show globalRestrict G s W'.unop =
            G.presheaf.map i (globalRestrict G s W.unop) from
          (Eq.trans (congrArg (fun j => G.presheaf.map j (globalRestrict G s W.unop))
              (Subsingleton.elim i (homOfLE (leOfHom i.unop)).op))
            (globalRestrict_map G (leOfHom i.unop) s)).symm]
        exact PresheafOfModules.naturality_apply
          (sheafifyUnit X.toRingedSpace
            ((PresheafOfModules.tensorObj (O := X.toRingedSpace.presheaf) F.val G.val))) i
          (x ⊗ₜ[X.presheaf.obj W] (globalRestrict G s W.unop)) }

/-- **The morphism `x ↦ x ⊗ s` on sections.** -/
theorem tensorGlobalSection_app_apply (s : Γ(G, ⊤)) (W : X.Opens) (x : Γ(F, W)) :
    Scheme.Modules.Hom.app (tensorGlobalSection F G s) W x =
      toTensorSheafSection X.toRingedSpace F G (op W)
        (x ⊗ₜ[X.presheaf.obj (op W)] (globalRestrict G s W)) := rfl

/-- **The restriction of `x ↦ x ⊗ s` to an open is `x ↦ x ⊗ s|_V`.** -/
theorem tensorGlobalSection_restrictFunctor (s : Γ(G, ⊤)) (V : X.Opens) :
    (Scheme.Modules.restrictFunctor V.ι).map (tensorGlobalSection F G s) =
      tensorLocalSection X F G V (globalRestrict G s V) := by
  refine Scheme.Modules.hom_ext _ _ fun S => ?_
  ext x
  rw [restrictFunctor_map_app V (tensorGlobalSection F G s) S x]
  refine (tensorGlobalSection_app_apply F G s _ x).trans ?_
  rw [← ModuleLimits.imageSections_rfl_app (tensorLocalSection X F G V (globalRestrict G s V)) S x,
    imageSections_tensorLocalSection F G (globalRestrict G s V) rfl (V.ι_image_le S) x,
    globalRestrict_map G (V.ι_image_le S) s]
  rfl

/-- **Composing `x ↦ x ⊗ s` with a morphism in the second factor moves the global section
along it.** -/
theorem tensorGlobalSection_naturality {G' : X.Modules} (φ : G ⟶ G') (s : Γ(G, ⊤)) :
    tensorGlobalSection F G s ≫ (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).map φ) =
      tensorGlobalSection F G' (Scheme.Modules.Hom.app φ ⊤ s) := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext x
  change (((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).map φ)).val.app (op W)).hom
      (toTensorSheafSection X.toRingedSpace F G (op W)
        (x ⊗ₜ[X.presheaf.obj (op W)] (globalRestrict G s W))) = _
  rw [sheafTensor_obj_map_toTensorSheafSection F φ (op W) x (globalRestrict G s W)]
  refine congrArg (toTensorSheafSection X.toRingedSpace F G' (op W)) ?_
  refine congrArg (fun y : Γ(G', W) => x ⊗ₜ[X.presheaf.obj (op W)] y) ?_
  exact (ModuleLimits.Hom_app_presheaf_map φ (le_top : W ≤ ⊤) s).symm

/-- **At `G = 𝒪_X` and `s = 1` the morphism is the inverse right unitor.** -/
theorem tensorGlobalSection_unit :
    tensorGlobalSection F (Scheme.unitModule X) (1 : ↑(X.presheaf.obj (op ⊤))) =
      tensorUnitInv F := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext x
  change toTensorSheafSection X.toRingedSpace F (Scheme.unitModule X) (op W)
      (x ⊗ₜ[X.presheaf.obj (op W)]
        (globalRestrict (Scheme.unitModule X) (1 : ↑(X.presheaf.obj (op ⊤))) W)) = _
  refine Eq.trans ?_ (tensorUnitInv_app_apply F (op W) x).symm
  refine congrArg (toTensorSheafSection X.toRingedSpace F (Scheme.unitModule X) (op W)) ?_
  exact congrArg (fun y : (Scheme.unitModule X).val.obj (op W) =>
      x ⊗ₜ[X.presheaf.obj (op W)] y)
    (PresheafOfModules.unit_map_one X.ringCatSheaf.obj (homOfLE (le_top : W ≤ ⊤)).op)

/-- At `G = 𝒪_X` and `s = 1` the morphism `x ↦ x ⊗ s` is an isomorphism. -/
instance isIso_tensorGlobalSection_unit :
    IsIso (tensorGlobalSection F (Scheme.unitModule X) (1 : ↑(X.presheaf.obj (op ⊤)))) := by
  rw [tensorGlobalSection_unit]
  infer_instance

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
