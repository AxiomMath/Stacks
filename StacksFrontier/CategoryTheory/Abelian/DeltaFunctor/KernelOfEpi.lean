module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# The image of the subobject of a short exact sequence as a kernel

Let `F` be a cohomological `δ`-functor between abelian categories and `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` a
short exact sequence. If `Fⁿ(X₂) ⟶ Fⁿ(X₃)` is an epimorphism, then the connecting morphism
`δ : Fⁿ(X₃) ⟶ Fⁿ⁺¹(X₁)` vanishes, so `Fⁿ⁺¹(X₁) ⟶ Fⁿ⁺¹(X₂)` is a monomorphism and
`Fⁿ⁺¹(X₁)` is the kernel of `Fⁿ⁺¹(X₂) ⟶ Fⁿ⁺¹(X₃)`. In degree `0` the same holds with no
hypothesis.

This is how the Artin–Schreier sequence `0 ⟶ 𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0` computes the higher direct
images of `𝐙/p𝐙` as the kernels of `F - 1` on those of `𝐆_a` once `F - 1` is surjective on the
latter.

## Main results

* `CategoryTheory.DeltaFunctor.δ_eq_zero_of_epi_map_g`: the connecting morphism vanishes.
* `CategoryTheory.DeltaFunctor.mono_map_f_succ_of_epi_map_g`: the next map is a monomorphism.
* `CategoryTheory.DeltaFunctor.isLimitMapFOfEpi`: `Fⁿ(X₁)` is the kernel of `Fⁿ(X₂) ⟶ Fⁿ(X₃)`
  as soon as `n = 0` or the previous map `Fⁿ⁻¹(X₂) ⟶ Fⁿ⁻¹(X₃)` is an epimorphism.
-/

@[expose] public noncomputable section

universe v v' u u'

namespace CategoryTheory.DeltaFunctor

open Limits

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]
  (F : DeltaFunctor A B) {S : ShortComplex A}

/-- If `Fⁿ(X₂) ⟶ Fⁿ(X₃)` is an epimorphism, the connecting morphism `δ : Fⁿ(X₃) ⟶ Fⁿ⁺¹(X₁)`
vanishes. -/
theorem δ_eq_zero_of_epi_map_g (hS : S.ShortExact) (n : ℕ) (h : Epi ((F.functor n).map S.g)) :
    F.δ hS n = 0 :=
  (F.exact_δ₁ hS n).epi_f_iff.1 h

/-- If `Fⁿ(X₂) ⟶ Fⁿ(X₃)` is an epimorphism, then `Fⁿ⁺¹(X₁) ⟶ Fⁿ⁺¹(X₂)` is a monomorphism. -/
theorem mono_map_f_succ_of_epi_map_g (hS : S.ShortExact) (n : ℕ)
    (h : Epi ((F.functor n).map S.g)) :
    Mono ((F.functor (n + 1)).map S.f) :=
  (F.exact_δ₂ hS n).mono_g (F.δ_eq_zero_of_epi_map_g hS n h)

/-- **`Fⁿ(X₁)` is the kernel of `Fⁿ(X₂) ⟶ Fⁿ(X₃)`** when `n = 0` or `Fⁿ⁻¹(X₂) ⟶ Fⁿ⁻¹(X₃)` is
an epimorphism. -/
def isLimitMapFOfEpi (hS : S.ShortExact) (n : ℕ)
    (h : ∀ m : ℕ, n = m + 1 → Epi ((F.functor m).map S.g)) :
    IsLimit (KernelFork.ofι ((F.functor n).map S.f) (F.map_f_comp_map_g n)) := by
  have : Mono ((F.functor n).map S.f) := by
    rcases n with _ | m
    · exact F.mono_map_f hS
    · exact F.mono_map_f_succ_of_epi_map_g hS m (h m rfl)
  haveI : Mono (S.map (F.functor n)).f := this
  exact (F.exact_map hS n).fIsKernel

/-- **`Fⁿ(X₁) ≅ Ker(Fⁿ(X₂) ⟶ Fⁿ(X₃))`** when `n = 0` or `Fⁿ⁻¹(X₂) ⟶ Fⁿ⁻¹(X₃)` is an
epimorphism, the isomorphism being compatible with the inclusions into `Fⁿ(X₂)`. -/
def isoKernelMapG (hS : S.ShortExact) (n : ℕ)
    (h : ∀ m : ℕ, n = m + 1 → Epi ((F.functor m).map S.g)) :
    (F.functor n).obj S.X₁ ≅ kernel ((F.functor n).map S.g) :=
  IsLimit.conePointUniqueUpToIso (F.isLimitMapFOfEpi hS n h) (limit.isLimit _)

/-- The isomorphism `isoKernelMapG` is compatible with the inclusions into `Fⁿ(X₂)`. -/
@[reassoc (attr := simp)]
theorem isoKernelMapG_hom_ι (hS : S.ShortExact) (n : ℕ)
    (h : ∀ m : ℕ, n = m + 1 → Epi ((F.functor m).map S.g)) :
    (F.isoKernelMapG hS n h).hom ≫ kernel.ι _ = (F.functor n).map S.f :=
  IsLimit.conePointUniqueUpToIso_hom_comp (F.isLimitMapFOfEpi hS n h) (limit.isLimit _)
    WalkingParallelPair.zero

end CategoryTheory.DeltaFunctor

end
