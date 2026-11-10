module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover

/-!
# Sections of the kernel of a morphism of sheaves of modules

Let `R` be a sheaf of rings on a site and let `α : M ⟶ N` be a morphism of sheaves of
`R`-modules. The categorical kernel of `α` is computed sectionwise: evaluation at an object of
the site preserves finite limits, so the sections of `kernel α` over an object `V` are the
kernel of the map `α` induces on sections over `V`.

This file records that computation in the form its consumers need: the inclusion
`kernel.ι α` is injective on sections, its composite with `α` vanishes, and every section of
`M` over `V` annihilated by `α` is the image of a (unique) section of `kernel α` over `V`.

## Main results

* `Stacks.SheafOfModules.kernelSectionsIso`: the sections of `kernel α` over `V` are the
  kernel submodule of the map on sections over `V`.
* `Stacks.SheafOfModules.injective_kernel_ι_app`: `kernel.ι α` is injective on sections.
* `Stacks.SheafOfModules.app_kernel_ι_app`: a section of `kernel α` is annihilated by `α`.

The converse — that a section of `M` annihilated by `α` comes from a section of `kernel α` — is
`Stacks.SheafOfModules.exists_kernel_section`, which lives in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover` and is stated there for an
arbitrary morphism of sheaves of modules. It is re-exported by the import above rather than restated
here.

## Implementation notes

`SheafOfModules.evaluation R V` is a `def` rather than an abbreviation, so neither its
additivity nor the preservation of zero morphisms it implies is found by instance resolution;
`Stacks.SheafOfModules.evaluation_additive` re-exposes it, and it is needed because
`CategoryTheory.Limits.PreservesKernel.iso` is stated for functors preserving zero morphisms.

The three section-level statements are deliberately phrased with `α.val.app V` and
`(kernel.ι α).val.app V` rather than with the image of `α` under the evaluation functor: the
two are definitionally equal, but only the former spelling matches what a consumer writes.
Each is therefore proved by `exact`, never by `rw` through the evaluation functor, since the
`PresheafOfModules` restriction-of-scalars coercions make the rewritten goals fail to be
type-correct at `implicit` transparency.

## References

* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {M N : SheafOfModules.{w} R} (α : M ⟶ N) (V : Cᵒᵖ)

/-- Evaluation of a sheaf of modules at an object of the site is an additive functor. This is
`SheafOfModules.evaluation` written as the composite it is defined to be, so that the instances
of the two factors apply. -/
instance evaluation_additive : (_root_.SheafOfModules.evaluation.{w} R V).Additive :=
  inferInstanceAs (Functor.Additive
    (_root_.SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj V))

/-- **The sections of a kernel are the kernel of the sections.** Evaluation at `V` preserves
finite limits, so it takes `kernel α` to a kernel of the map `α` induces on sections over `V`,
which in `ModuleCat` is the kernel submodule. -/
def kernelSectionsIso :
    (_root_.SheafOfModules.evaluation.{w} R V).obj (kernel α) ≅
      ModuleCat.of (R.obj.obj V)
        (LinearMap.ker ((_root_.SheafOfModules.evaluation.{w} R V).map α).hom) :=
  PreservesKernel.iso (_root_.SheafOfModules.evaluation.{w} R V) α ≪≫ ModuleCat.kernelIsoKer _

/-- The identification of `Stacks.SheafOfModules.kernelSectionsIso` is compatible with the
inclusion of the kernel: it sends an element of the kernel submodule to the section of
`kernel α` that `kernel.ι α` carries back to it. -/
lemma kernelSectionsIso_inv_ι
    (x : LinearMap.ker ((_root_.SheafOfModules.evaluation.{w} R V).map α).hom) :
    (_root_.SheafOfModules.evaluation.{w} R V).map (kernel.ι α)
        ((kernelSectionsIso α V).inv x) = x.1 := by
  rw [kernelSectionsIso, Iso.trans_inv, ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    PreservesKernel.iso_inv_ι]
  exact ModuleCat.kernelIsoKer_inv_kernel_ι_apply _ x

/-- The inclusion of the kernel is a monomorphism on sections over any object of the site. -/
lemma mono_evaluation_map_kernel_ι :
    Mono ((_root_.SheafOfModules.evaluation.{w} R V).map (kernel.ι α)) := by
  have h : (_root_.SheafOfModules.evaluation.{w} R V).map (kernel.ι α) =
      (PreservesKernel.iso (_root_.SheafOfModules.evaluation.{w} R V) α).hom ≫
        kernel.ι ((_root_.SheafOfModules.evaluation.{w} R V).map α) := by
    rw [← PreservesKernel.iso_inv_ι, Iso.hom_inv_id_assoc]
  rw [h]
  infer_instance

/-- **The inclusion of the kernel is injective on sections.** -/
lemma injective_kernel_ι_app : Function.Injective ((kernel.ι α).val.app V) :=
  (ModuleCat.mono_iff_injective _).1 (mono_evaluation_map_kernel_ι α V)

/-- **A section of the kernel is annihilated by `α`.** -/
lemma app_kernel_ι_app (y : (kernel α).val.obj V) :
    (α.val.app V) ((kernel.ι α).val.app V y) = 0 := by
  have h := congrArg (fun (f : kernel α ⟶ N) =>
    (_root_.SheafOfModules.evaluation.{w} R V).map f) (kernel.condition α)
  simp only [Functor.map_comp, Functor.map_zero] at h
  exact ConcreteCategory.congr_hom h y

end Stacks.SheafOfModules

end
