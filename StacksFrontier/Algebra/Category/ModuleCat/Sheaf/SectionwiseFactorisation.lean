module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Factoring a morphism of sheaves of modules through a sectionwise injective one

Let `incl : I ⟶ M` be a morphism of sheaves of modules which is injective on sections over
every object of the site, and let `g : N ⟶ M` be a morphism all of whose local sections are in
the image of `incl`. Then `g` factors through `incl`, uniquely.

This is the sheaf-of-modules form of "a map into the ambient object whose values lie in a
submodule factors through the submodule". It is stated for a morphism `incl` presented together
with its sectionwise injectivity and sectionwise image, rather than for a chosen kernel or
subobject, because that is the shape in which a defining ideal of a thickening of ringed topoi
(Stacks 08M7) is available: naming the kernel of a structure map as an object would require
sheafification hypotheses on the site merely to state the factorisation.

## Main results

* `Stacks.SheafOfModules.existsUnique_factorThrough`: the unique factorisation.

## Implementation notes

The factorisation is built sectionwise, each value being the section of `I` that the hypothesis
`hg` provides. Additivity, linearity and naturality of the resulting family all follow by
applying `incl` and using its injectivity, since `incl` and `g` are themselves additive, linear
and natural. No sheaf condition and no property of the site is used, so the same argument would
work for presheaves of modules; the sheaf version is stated because that is what the consumers
need.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.SheafOfModules

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {I M N : SheafOfModules.{w} R} (incl : I ⟶ M)
  (hinj : ∀ U : Cᵒᵖ, Function.Injective (incl.val.app U))
  (g : N ⟶ M)
  (hg : ∀ (U : Cᵒᵖ) (z : N.val.obj U), ∃ b : I.val.obj U,
    incl.val.app U b = g.val.app U z)

include hinj hg in
/-- **A morphism of sheaves of modules whose local sections lie in the image of a sectionwise
injective morphism factors through it, uniquely.**

The lift is the section of `I` provided by `hg`, and it is additive, linear and natural because
`incl` is injective and both `incl` and `g` are. Uniqueness is immediate from injectivity. -/
theorem existsUnique_factorThrough : ∃! l : N ⟶ I, l ≫ incl = g := by
  set t : ∀ (U : Cᵒᵖ), N.val.obj U → I.val.obj U := fun U z ↦ (hg U z).choose
  have hti : ∀ (U : Cᵒᵖ) (z : N.val.obj U), incl.val.app U (t U z) = g.val.app U z :=
    fun U z ↦ (hg U z).choose_spec
  let lapp : ∀ U : Cᵒᵖ, N.val.obj U →ₗ[R.obj.obj U] I.val.obj U := fun U ↦
    { toFun := t U
      map_add' := fun z z' ↦ hinj U (by simp only [map_add, hti])
      map_smul' := fun r z ↦ hinj U (by simp only [map_smul, hti, RingHom.id_apply]) }
  have hnat : ∀ {U V : Cᵒᵖ} (p : U ⟶ V), N.val.map p ≫
      (ModuleCat.restrictScalars (R.obj.map p).hom).map (ModuleCat.ofHom (lapp V)) =
        ModuleCat.ofHom (lapp U) ≫ I.val.map p := fun {U V} p ↦
    ModuleCat.hom_ext (LinearMap.ext fun z ↦ hinj V (by
      show (incl.val.app V) (t V (N.val.map p z)) = (incl.val.app V) (I.val.map p (t U z))
      exact (hti V (N.val.map p z)).trans
        ((PresheafOfModules.naturality_apply g.val p z).trans
          ((congrArg (fun x ↦ M.val.map p x) (hti U z).symm).trans
            (PresheafOfModules.naturality_apply incl.val p (t U z)).symm))))
  refine ⟨⟨{ app := fun U ↦ ModuleCat.ofHom (lapp U), naturality := hnat }⟩, ?_, ?_⟩
  · exact SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
      ModuleCat.hom_ext (LinearMap.ext fun z ↦ hti U z))
  · exact fun l hl ↦ SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
      ModuleCat.hom_ext (LinearMap.ext fun z ↦
        hinj U ((congrArg (fun m : N ⟶ M ↦ m.val.app U z) hl).trans (hti U z).symm)))

end Stacks.SheafOfModules

end
