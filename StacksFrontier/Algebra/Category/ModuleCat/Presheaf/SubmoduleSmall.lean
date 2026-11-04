module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.CategoryTheory.EssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEssentiallySmall

/-!
# Submodules and subobjects over an essentially small site form a small set

Let `C` be a category which is essentially small at a universe `w` and let `M` be a presheaf of
modules on `C` whose sections lie in `Type w`. A submodule of `M` — a family of submodules of the
sections stable under restriction — is determined by its values on a set of representatives of the
isomorphism classes of objects, because along an isomorphism `e : X ≅ Y` the submodule over `X` is
the preimage of the one over `Y`. So the submodules of `M` form a `w`-small set, and so do the
subobjects of a sheaf of modules, which embed in the submodules of the underlying presheaf
(`SheafOfModules.subobjectSubmodule`).

## Main results

* `PresheafOfModules.Submodule.restrictSmallModel_injective`: two submodules agreeing on the
  objects of a small model agree.
* `PresheafOfModules.small_submodule`: the submodules form a small set.
* `SheafOfModules.small_subobject`: the subobjects of a sheaf of modules form a small set.
-/

@[expose] public noncomputable section

universe w v₁ u₁ u v

open CategoryTheory Opposite

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{w} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  (M : PresheafOfModules.{w} R)

omit [EssentiallySmall.{w} C] in
/-- Along an isomorphism of objects, the submodule over the source is the preimage of the one over
the target. -/
theorem Submodule.mem_obj_iff_of_iso (N : M.Submodule) {X Y : Cᵒᵖ} (e : X ≅ Y) (x : M.obj X) :
    x ∈ N.obj X ↔ M.map e.hom x ∈ N.obj Y := by
  refine ⟨fun hx => N.map_mem e.hom hx, fun hx => ?_⟩
  have h := N.map_mem e.inv hx
  rwa [← M.map_comp_apply, M.congr_map_apply e.hom_inv_id, M.map_id] at h

/-- The restriction of a submodule to the objects of a small model of `C`. -/
def Submodule.restrictSmallModel (N : M.Submodule) :
    ∀ X : SmallModel.{w} C, _root_.Submodule (R.obj (op ((equivSmallModel C).inverse.obj X)))
      (M.obj (op ((equivSmallModel C).inverse.obj X))) :=
  fun X => N.obj (op ((equivSmallModel C).inverse.obj X))

/-- **A submodule is determined by its values on the objects of a small model.** -/
theorem Submodule.restrictSmallModel_injective :
    Function.Injective (Submodule.restrictSmallModel M) := by
  intro N₁ N₂ h
  ext X x
  let e : X ≅ op ((equivSmallModel C).inverse.obj ((equivSmallModel C).functor.obj X.unop)) :=
    (((equivSmallModel C).unitIso.app X.unop).op).symm
  rw [Submodule.mem_obj_iff_of_iso M N₁ e, Submodule.mem_obj_iff_of_iso M N₂ e,
    show N₁.obj _ = N₂.obj _ from congrFun h ((equivSmallModel C).functor.obj X.unop)]

/-- **The submodules of a presheaf of modules on an essentially small category form a small
set.** -/
instance small_submodule : Small.{w} M.Submodule :=
  small_of_injective (Submodule.restrictSmallModel_injective M)

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- **The subobjects of a sheaf of modules on an essentially small site form a small set**: they
embed in the submodules of the underlying presheaf of modules. -/
instance small_subobject (M : SheafOfModules.{w} R) : Small.{w} (Subobject M) :=
  small_of_injective (subobjectSubmodule M).injective

end SheafOfModules

end
