module

public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Preadditive.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Kernels are monomorphisms, cokernels are epimorphisms

For a morphism `f : x ⟶ y` in a preadditive category: every kernel of `f` is a monomorphism,
every cokernel of `f` is an epimorphism, the coimage `x ⟶ Coker(Ker f → x)` is an epimorphism
and the image `Ker(y → Coker f) ⟶ y` is a monomorphism.

## Main results

* `CategoryTheory.Limits.kernel_mono_and_cokernel_epi_and_coimage_epi_and_image_mono`:
  the four statements together.
-/

@[expose] public section

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Let `f : x ⟶ y` be a morphism in a preadditive category. (1) Every kernel of `f` (a kernel
fork that is a limit) is a monomorphism; (2) every cokernel of `f` (a cokernel cofork that is a
colimit) is an epimorphism; (3) if a kernel of `f` and the coimage `Coker(Ker f → x)` exist, the
coimage map `x ⟶ Coim f` is an epimorphism; (4) if a cokernel of `f` and the image
`Ker(y → Coker f)` exist, the image map `Im f ⟶ y` is a monomorphism. -/
@[stacks 0E43 "all four parts; kernels and cokernels are arbitrary limit (co)forks"]
theorem kernel_mono_and_cokernel_epi_and_coimage_epi_and_image_mono {x y : C} (f : x ⟶ y) :
    (∀ (c : KernelFork f), IsLimit c → Mono c.ι) ∧
      (∀ (c : CokernelCofork f), IsColimit c → Epi c.π) ∧
      (∀ [HasKernel f] [HasCokernel (kernel.ι f)], Epi (Abelian.coimage.π f)) ∧
      (∀ [HasCokernel f] [HasKernel (cokernel.π f)], Mono (Abelian.image.ι f)) :=
  ⟨fun _ hc => mono_of_isLimit_fork hc, fun _ hc => epi_of_isColimit_cofork hc,
    fun {_ _} => inferInstance, fun {_ _} => inferInstance⟩

end CategoryTheory.Limits
