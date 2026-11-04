module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Restriction of a submodule of a sheaf of modules to a slice site

Let `(C, J)` be a site, `R` a sheaf of rings on it, `M` a sheaf of `R`-modules and `U : C`.
Restriction to the slice site is `SheafOfModules.over`, the pushforward along `Over.forget U`
with no change of scalars. This file restricts a `SheafOfModules.Submodule M` along it:
`N.over U` has for its sections over `V : C/U` the sections of `N` over `V.left`, and the
associated sheaf of modules is the restriction of the associated sheaf of modules.

## Main definitions

* `SheafOfModules.Submodule.over`: the restriction of a submodule of a sheaf of modules to a
  slice site.
* `SheafOfModules.Submodule.overIso`: the sheaf of modules of the restricted submodule is
  isomorphic to the restriction of the sheaf of modules of the submodule.

## Main results

* `SheafOfModules.Submodule.over_toSheafOfModules`: the sheaf of modules of the restricted
  submodule is equal to the restriction of the sheaf of modules of the submodule.
* `SheafOfModules.Submodule.overIso_hom_ι`: `overIso` is compatible with the two inclusions.
* `SheafOfModules.Submodule.over_mono`: restriction is monotone.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M : SheafOfModules.{v} R} (N : M.Submodule) (U : C)

/-- The restriction of a submodule of a sheaf of modules to a slice site: its sections over an
object `V` of `C/U` are the sections of `N` over `V.left`. -/
noncomputable def over : (M.over U).Submodule where
  obj V := N.toSubmodule.obj (op (unop V).left)
  map f := N.toSubmodule.map (Quiver.Hom.op (Over.Hom.left f.unop))
  isSheaf {_} s hs := N.isSheaf s
    (J.superset_covering (fun _ f hf ↦ (Sieve.overEquiv_iff _ f).mp hf) ((J.mem_over_iff _).mp hs))

/-- The sections of `N.over U` over `V` are the sections of `N` over `V.left`. -/
@[simp]
lemma over_toSubmodule_obj (V : (Over U)ᵒᵖ) :
    (N.over U).toSubmodule.obj V = N.toSubmodule.obj (op (unop V).left) :=
  rfl

/-- A section lies in `N.over U` over `V` if and only if it lies in `N` over `V.left`. -/
lemma mem_over_obj_iff {V : (Over U)ᵒᵖ} (s : (M.over U).val.obj V) :
    s ∈ (N.over U).toSubmodule.obj V ↔ s ∈ N.toSubmodule.obj (op (unop V).left) :=
  Iff.rfl

/-- The sheaf of modules of a restricted submodule is equal to the restriction of the sheaf of
modules of the submodule. -/
theorem over_toSheafOfModules :
    (N.over U).toSheafOfModules = N.toSheafOfModules.over U :=
  rfl

/-- `SheafOfModules.Submodule.over_toSheafOfModules` as an isomorphism. -/
noncomputable def overIso :
    (N.over U).toSheafOfModules ≅ N.toSheafOfModules.over U :=
  eqToIso (over_toSheafOfModules N U)

/-- `overIso` carries the inclusion of the restricted submodule to the restricted inclusion. -/
@[simp]
lemma overIso_hom_ι : (overIso N U).hom ≫ N.ι.over U = (N.over U).ι :=
  rfl

/-- The inverse of `overIso` carries the restricted inclusion to the inclusion of the restricted
submodule. -/
@[simp]
lemma overIso_inv_ι : (overIso N U).inv ≫ (N.over U).ι = N.ι.over U :=
  rfl

/-- Restriction of submodules to a slice site is monotone. -/
lemma over_mono {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) : N₁.over U ≤ N₂.over U :=
  fun V ↦ h (op (unop V).left)

end SheafOfModules.Submodule

end
