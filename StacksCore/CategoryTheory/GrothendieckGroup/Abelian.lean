module

import StacksCore.Algebra.Homology.ShortComplex.ShortExact
public import StacksCore.CategoryTheory.GrothendieckGroup.Basic

/-! # Kernels, images, cokernels and homology in the Grothendieck group

In an abelian category `A`, the classes in `K₀(A)` of the objects attached to a morphism
`f : X ⟶ Y` or to a short complex satisfy the following identities.

* `of_eq_of_kernel_add_of_coimage`: `[X] = [Ker f] + [Coim f]`, from the short exact sequence
  `0 → Ker f → X → Coim f → 0`; this one holds more generally in a preadditive category with
  homology.
* `of_eq_of_kernel_add_of_image`: `[X] = [Ker f] + [Im f]`, from the short exact sequence
  `0 → Ker f → X → Im f → 0`.
* `of_eq_of_image_add_of_cokernel`: `[Y] = [Im f] + [Coker f]`, from the short exact sequence
  `0 → Im f → Y → Coker f → 0`; this one also holds in a preadditive category with homology.
* `of_sub_of_eq_of_kernel_sub_of_cokernel`: `[X] - [Y] = [Ker f] - [Coker f]`.
* `of_homology`: `[H(S)] = [Ker S.g] - [Im S.f]` for a short complex `S`.
* `of_homology_sub_of_homology`: `[Ker ψ / Im φ] - [Ker φ / Im ψ] = [N] - [M]` for
  `φ : M ⟶ N` and `ψ : N ⟶ M` with `φ ≫ ψ = 0` and `ψ ≫ φ = 0`.
* `of_homology_eq_of_homology`: the homology objects `H⁰ = Ker ψ / Im φ` and
  `H¹ = Ker φ / Im ψ` of a 2-periodic complex `M --φ--> M --ψ--> M` (Stacks 02MW) have the
  same class.

Here `Im f` is `Abelian.image f`, the kernel of the cokernel of `f`, `Coim f` is
`Abelian.coimage f`, the cokernel of the kernel of `f`, and the homology of a short complex `S`
is `S.homology`. For the 2-periodic complex, `H⁰` is
`(ShortComplex.mk φ ψ _).homology` and `H¹` is `(ShortComplex.mk ψ φ _).homology`.

These identities are used as follows.

* Stacks 02MX (1): if the kernel and the cokernel of `f : X ⟶ Y` satisfy a Serre class
  `P : ObjectProperty A`, then `[X] - [Y]` lies in the image of `K₀(P.FullSubcategory) → K₀(A)`,
  by `of_sub_of_eq_of_kernel_sub_of_cokernel`.
* Stacks 02MX (2): the class `[H⁰] - [H¹]` of a 2-periodic complex is zero in `K₀(A)`, by
  `of_homology_eq_of_homology`.
* Stacks 0BDW: in its proof, the differential `d_r` gives maps `φ : E_r^even → E_r^odd` and
  `ψ : E_r^odd → E_r^even` whose composites vanish, and the step from `E_r` to `E_{r+1}`,
  `[E_{r+1}^odd] - [E_{r+1}^even] = [E_r^odd] - [E_r^even]`, is `of_homology_sub_of_homology`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.GrothendieckGroup

open Limits

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The class of the source of `f : X ⟶ Y` is the sum of the classes of its kernel and of its
coimage, by the short exact sequence `0 → Ker f → X → Coim f → 0`. This holds in any
preadditive category with homology in which `f` has a kernel and `kernel.ι f` has a
cokernel. -/
lemma of_eq_of_kernel_add_of_coimage {C : Type u} [Category.{v} C] [Preadditive C]
    [CategoryWithHomology C] {X Y : C} (f : X ⟶ Y) [HasKernel f] [HasCokernel (kernel.ι f)] :
    of X = of (kernel f) + of (Abelian.coimage f) :=
  additivity (ShortComplex.shortExact_mk_cokernel_π (kernel.ι f))

/-- The class of the source of `f : X ⟶ Y` is the sum of the classes of its kernel and of its
image, by the short exact sequence `0 → Ker f → X → Im f → 0`. -/
lemma of_eq_of_kernel_add_of_image {X Y : A} (f : X ⟶ Y) :
    of X = of (kernel f) + of (Abelian.image f) := by
  rw [← of_eq_of_iso (Abelian.coimageIsoImage f), of_eq_of_kernel_add_of_coimage f]

/-- The class of the target of `f : X ⟶ Y` is the sum of the classes of its image and of its
cokernel, by the short exact sequence `0 → Im f → Y → Coker f → 0`. This holds in any
preadditive category with homology in which `f` has a cokernel and `cokernel.π f` has a
kernel. -/
lemma of_eq_of_image_add_of_cokernel {C : Type u} [Category.{v} C] [Preadditive C]
    [CategoryWithHomology C] {X Y : C} (f : X ⟶ Y) [HasCokernel f] [HasKernel (cokernel.π f)] :
    of Y = of (Abelian.image f) + of (cokernel f) :=
  additivity (ShortComplex.shortExact_mk_kernel_ι (cokernel.π f))

/-- For `f : X ⟶ Y`, `[X] - [Y] = [Ker f] - [Coker f]`. In Stacks 02MX (1) this shows that
`[X] - [Y]` comes from `K₀(P.FullSubcategory)` when the kernel and the cokernel of `f` satisfy a
Serre class `P`. -/
lemma of_sub_of_eq_of_kernel_sub_of_cokernel {X Y : A} (f : X ⟶ Y) :
    of X - of Y = of (kernel f) - of (cokernel f) := by
  rw [of_eq_of_kernel_add_of_image f, of_eq_of_image_add_of_cokernel f]
  abel

/-- The class of the homology of a short complex `S` is `[Ker S.g] - [Im S.f]`. -/
lemma of_homology (S : ShortComplex A) :
    of S.homology = of (kernel S.g) - of (Abelian.image S.f) := by
  let γ := kernel.ι S.g ≫ cokernel.π S.f
  have e : Abelian.image S.f ≅ kernel γ :=
    IsLimit.conePointUniqueUpToIso S.abelianImageToKernelIsKernel (limit.isLimit _)
  rw [of_eq_of_kernel_add_of_coimage γ, of_eq_of_iso e, add_sub_cancel_left,
    of_eq_of_iso (ShortComplex.LeftHomologyData.ofAbelian S).homologyIso,
    ShortComplex.LeftHomologyData.ofAbelian_H]

/-- For `φ : M ⟶ N` and `ψ : N ⟶ M` with `φ ≫ ψ = 0` and `ψ ≫ φ = 0`, the homology
`Ker ψ / Im φ` at `N` and the homology `Ker φ / Im ψ` at `M` satisfy
`[Ker ψ / Im φ] - [Ker φ / Im ψ] = [N] - [M]`. This is the computation in the proof of
Stacks 0BDW. -/
lemma of_homology_sub_of_homology {M N : A} (φ : M ⟶ N) (ψ : N ⟶ M) (hφψ : φ ≫ ψ = 0)
    (hψφ : ψ ≫ φ = 0) :
    of (ShortComplex.mk φ ψ hφψ).homology - of (ShortComplex.mk ψ φ hψφ).homology =
      of N - of M := by
  rw [of_homology, of_homology, of_eq_of_kernel_add_of_image φ, of_eq_of_kernel_add_of_image ψ]
  abel

/-- The homology objects `H⁰ = Ker ψ / Im φ` and `H¹ = Ker φ / Im ψ` of a 2-periodic complex
`M --φ--> M --ψ--> M` (Stacks 02MW) have the same class in `K₀(A)`. In Stacks 02MX (2) this
shows that `[H⁰] - [H¹]` lies in the kernel of `K₀(P.FullSubcategory) → K₀(A)` when `H⁰` and
`H¹` satisfy a Serre class `P`. -/
lemma of_homology_eq_of_homology {M : A} (φ ψ : M ⟶ M) (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0) :
    of (ShortComplex.mk φ ψ hφψ).homology = of (ShortComplex.mk ψ φ hψφ).homology :=
  sub_eq_zero.1 ((of_homology_sub_of_homology φ ψ hφψ hψφ).trans (sub_self _))

end CategoryTheory.GrothendieckGroup
