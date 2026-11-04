module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Restriction of sheaves of modules to the slice at a terminal object

For a sheaf of rings `R` on a site `C` and a terminal object `X` of `C`, the restriction
`CategoryTheory.SheafOfModules.overFunctor R X` from `R`-modules to `R.over X`-modules is fully
faithful: every object of the slice `Over X` is, up to the unique structure morphism, an object
of `C`, and the sections of `M.over X` over it are those of `M`.

## Main definitions

* `Stacks.SheafOfModules.C1573.overFunctorPreimageOfIsTerminal`: a morphism of the restrictions
  to the slice at a terminal object, read as a morphism of the original modules.
* `Stacks.SheafOfModules.C1573.overFunctorFullyFaithfulOfIsTerminal`: the restriction to the
  slice at a terminal object is fully faithful.
-/

namespace Stacks.SheafOfModules.C1573
end Stacks.SheafOfModules.C1573

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v v₁ u₁ u

namespace Stacks.SheafOfModules

open _root_.Stacks.SheafOfModules.C1573
variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  {X : C} (hX : IsTerminal X)

/-- A morphism of the restrictions of two sheaves of modules to the slice at a terminal object
`X`, read as a morphism of the sheaves of modules themselves: over `U` it is the component at the
object `U ⟶ X` of the slice. -/
def C1573.overFunctorPreimageOfIsTerminal {M N : SheafOfModules.{v} R} (f : M.over X ⟶ N.over X) :
    M ⟶ N where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun m => (f.val.app (op (Over.mk (hX.from U.unop)))).hom m
          map_add' := fun a b => (f.val.app (op (Over.mk (hX.from U.unop)))).hom.map_add a b
          map_smul' := fun r m => (f.val.app (op (Over.mk (hX.from U.unop)))).hom.map_smul r m }
      naturality := fun {U V} g => by
        ext m
        exact (PresheafOfModules.naturality_apply f.val
          (Over.homMk (U := Over.mk (hX.from V.unop)) (V := Over.mk (hX.from U.unop)) g.unop
            (hX.hom_ext _ _)).op m) }

/-- The component of `overFunctorPreimageOfIsTerminal R hX f` at `U` sends a section `m` to its
image under the component of `f` at the object `U ⟶ X` of the slice. -/
theorem C1573.overFunctorPreimageOfIsTerminal_val_app_apply {M N : SheafOfModules.{v} R}
    (f : M.over X ⟶ N.over X) (U : Cᵒᵖ) (m : M.val.obj U) :
    (overFunctorPreimageOfIsTerminal R hX f).val.app U m =
      (f.val.app (op (Over.mk (hX.from U.unop)))).hom m := rfl

/-- **The restriction of sheaves of modules to the slice at a terminal object is fully
faithful.** -/
def C1573.overFunctorFullyFaithfulOfIsTerminal :
    (_root_.SheafOfModules.overFunctor.{v} R X).FullyFaithful where
  preimage f := overFunctorPreimageOfIsTerminal R hX f
  map_preimage {M N} f := by
    refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
    obtain ⟨⟨Y, ⟨⟨⟩⟩, h⟩⟩ := U
    obtain rfl : h = hX.from Y := hX.hom_ext _ _
    rfl
  preimage_map φ := rfl

end Stacks.SheafOfModules

end
