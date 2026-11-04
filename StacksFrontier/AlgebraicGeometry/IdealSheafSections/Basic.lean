module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Locality
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Sections of a kernel of sheaves of modules, and of an ideal sheaf

A kernel of sheaves of modules is computed section by section: evaluation at an object of the
site preserves finite limits (`SheafOfModules.evaluationPreservesFiniteLimits`),
so the sections of `CategoryTheory.Limits.kernel g` over an object are the kernel of the map
`g` induces on sections there.

Half of that statement was already available: the inclusion of a kernel is a monomorphism,
hence injective on sections, which for an ideal sheaf is
`Stacks.Conormal.Locality.idealSheaf_section_injective`. This file supplies the other half,
surjectivity onto the sectionwise kernel, which is what *produces* a section of an ideal
sheaf from an element of the structure sheaf that the comorphism kills.

## Main results

* `Stacks.ModuleKernelSections.exists_section_of_app_eq_zero`: a section of `N` over `X` that the
  map `g : N ⟶ P` kills is the image of a section of `kernel g` over `X`.
* `Stacks.ClosedImmersion.exists_idealSheaf_section`: the same statement for the ideal sheaf
  of a morphism of schemes, in the vocabulary that
  `Stacks.ClosedImmersion.idealSheaf` is written in — the ideal sheaf is by definition the
  kernel of `SheafOfModules.unitToPushforwardObjUnit`, so a section of the
  structure sheaf of the target annihilated by the comorphism names a section of the ideal
  sheaf, and by `idealSheaf_section_injective` it names exactly one.

## Implementation notes

`CategoryTheory.Limits.PreservesKernel.iso` needs its functor to preserve zero morphisms, and
Mathlib records additivity for `SheafOfModules.forget` and for
`CategoryTheory.PresheafOfModules.evaluation` but not for their composite
`SheafOfModules.evaluation`, which is a plain definition and so is not seen
through by instance search. `evaluation_preservesZeroMorphisms` records it; the proof is
`rfl`, evaluation being the identity on the underlying map of sections.

The sectionwise kernel is reached in two steps rather than one: `PreservesKernel.iso`
transports to `kernel` of the evaluated map inside `ModuleCat`, and
`ModuleCat.kernelIsoKer` identifies that with the `LinearMap.ker`, which is where an element
can be exhibited. Only `PreservesKernel.iso_inv_ι` and
`ModuleCat.kernelIsoKer_inv_kernel_ι` are needed to carry the formula across, so the witness
is explicit and no choice is made.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe v v₁ u₁ u

namespace Stacks.ModuleKernelSections

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Evaluation of sheaves of modules at an object of the site preserves zero morphisms: it is
the identity on the underlying map of sections. Instance search does not find this through
the additivity of the two functors `SheafOfModules.evaluation` is the
composite of, because that composite is a plain definition. -/
instance evaluation_preservesZeroMorphisms (X : Cᵒᵖ) :
    (SheafOfModules.evaluation.{v} R X).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

/-- **Sections of a kernel of sheaves of modules are the sectionwise kernel.** A section of
`N` over `X` that `g` sends to zero is the image under `CategoryTheory.Limits.kernel.ι g` of a
section of `kernel g` over `X`.

Together with injectivity of `kernel.ι g` on sections — it is a monomorphism — this says the
sections of `kernel g` over `X` are exactly the kernel of the map on sections. -/
theorem exists_section_of_app_eq_zero {N P : _root_.SheafOfModules.{v} R} (g : N ⟶ P)
    [HasKernel g] (X : Cᵒᵖ)
    [PreservesLimit (parallelPair g 0) (SheafOfModules.evaluation.{v} R X)]
    (y : N.val.obj X) (hy : ((g.val.app X)).hom y = 0) :
    ∃ x : (kernel g).val.obj X, ((kernel.ι g : kernel g ⟶ N).val.app X).hom x = y := by
  let E := SheafOfModules.evaluation.{v} R X
  refine ⟨(PreservesKernel.iso E g).inv.hom ((ModuleCat.kernelIsoKer (E.map g)).inv.hom ⟨y, hy⟩),
    ?_⟩
  have hz := ConcreteCategory.congr_hom (ModuleCat.kernelIsoKer_inv_kernel_ι (E.map g)) ⟨y, hy⟩
  rwa [← PreservesKernel.iso_inv_ι E g] at hz

end Stacks.ModuleKernelSections

namespace Stacks.ClosedImmersion

universe u'

variable {Z U : Scheme.{u'}}

/-- **A section of the structure sheaf killed by the comorphism names a section of the ideal
sheaf.** The ideal sheaf of `k : Z ⟶ U` is the kernel of
`SheafOfModules.unitToPushforwardObjUnit` at the comorphism of `k`, and that
kernel is computed on sections, so a section of the unit module over an open `W` of `U` whose
image under the comorphism vanishes is the image of a section of the ideal sheaf over `W`.

`Stacks.Conormal.Locality.idealSheaf_section_injective` says that section is unique, so the
two together describe the sections of the ideal sheaf over `W` exactly.

This is what makes the hypothesis of a generator formula for the conormal sheaf — a named
section `x` of the ideal sheaf whose image in the structure sheaf is a prescribed element —
satisfiable rather than an assumption: it has to be checked only that the comorphism kills
the prescribed element. -/
theorem exists_idealSheaf_section (k : Z ⟶ U) (W : U.Opens)
    (y : (SheafOfModules.unit
      (structureSheafRing U.toLocallyRingedSpace.toRingedSpace)).val.obj (.op W))
    (hy : ((SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom k.toLRSHom.toShHom)).val.app (.op W)).hom y = 0) :
    ∃ x : (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom).val.obj (.op W),
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom k.toLRSHom.toShHom))).val.app (.op W)).hom x = y :=
  Stacks.ModuleKernelSections.exists_section_of_app_eq_zero _ _ y hy

end Stacks.ClosedImmersion

end
