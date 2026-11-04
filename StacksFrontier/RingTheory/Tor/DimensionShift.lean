module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import StacksFrontier.RingTheory.Tor.LongExactSequence
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u

/-!
# The dimension shift `Tor₂(B, B) ≅ Tor₁(B, J) ≅ ker (J ⊗ J → A)`

Let `A` be a commutative ring, let `J` be an ideal of `A` and let `B = A ⧸ J`. Two shifts along
the short exact sequence `0 → J → A → B → 0` compute the second Tor of `B` with itself: the
sequence of `Tor_•(B, -)` in the underived variable gives `Tor₂(B, B) ≅ Tor₁(B, J)`, because
`Tor_i(B, A) = 0` for `i > 0` as `A` is flat, and the sequence of `Tor_•(-, J)` in the derived
variable gives `Tor₁(B, J) ≅ ker (J ⊗_A J → A ⊗_A J)`, because `Tor₁(A, J) = 0` as `A` is
projective. Composing `A ⊗_A J ≅ J ⊆ A` identifies the second map with multiplication
`Submodule.mulMap J J`.

## Main results

* `Stacks.Tor.DimensionShift.torTwoSelfIsoTorOneIdeal`: `Tor₂(B, B) ≅ Tor₁(B, J)`.
* `Stacks.Tor.DimensionShift.torOneIdealIsoKerMulMap`: `Tor₁(B, J) ≅ ker (Submodule.mulMap J J)`.
* `Stacks.Tor.DimensionShift.torTwoSelfIsoKerMulMap` and
  `Stacks.Tor.DimensionShift.torTwoSelfLinearEquivKerMulMap`: the composite
  `Tor₂(B, B) ≅ ker (Submodule.mulMap J J)`, as an isomorphism of `ModuleCat A` and as an
  `A`-linear equivalence.

## Implementation notes

Both shifts come from the long exact sequences of `StacksFrontier/RingTheory/Tor/LongExactSequence`,
whose connecting morphisms are named rather than existentially quantified; this is what makes the
two isomorphisms definitions with real content rather than mere existence statements. The second
shift is at the bottom of its sequence, where the degree zero terms are the tensor products
themselves, and identifies `Tor₁(B, J)` with a kernel: the connecting morphism is a monomorphism
and the sequence is exact at `J ⊗ J`, so it *is* a kernel of `J ⊗ J → A ⊗ J`.

The target is spelled `LinearMap.ker (Submodule.mulMap J J)`, the kernel of the multiplication
map `J ⊗_A J →ₗ[A] A`, which agrees with the kernel of `J ⊗_A J → A ⊗_A J` because
`A ⊗_A J ≅ J` and the inclusion of `J` in `A` are injective.
-/

open CategoryTheory MonoidalCategory Limits
open scoped TensorProduct

namespace Stacks.Tor.DimensionShift

variable {A : Type u} [CommRing A] (J : Ideal A)

/-- The short exact sequence `0 → J → A → A ⧸ J → 0` of `A`-modules. -/
noncomputable def quotientShortComplex : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk (ModuleCat.ofHom J.subtype) (ModuleCat.ofHom J.mkQ) (by
    ext x
    simp [Ideal.Quotient.eq_zero_iff_mem])

/-- The sequence `0 → J → A → A ⧸ J → 0` is short exact. -/
theorem shortExact_quotientShortComplex : (quotientShortComplex J).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ J) J.injective_subtype
    (Submodule.mkQ_surjective J)

/-- **First dimension shift.** For `B = A ⧸ J` the connecting morphism of the long exact sequence
of `Tor_•(B, -)` is an isomorphism `Tor₂(B, B) ≅ Tor₁(B, J)`: the sequence `0 → J → A → B → 0`
has flat middle term, so `Tor₂(B, A)` and `Tor₁(B, A)` both vanish. -/
@[ega "III 7.6.11" "The case P_0=A"]
noncomputable def torTwoSelfIsoTorOneIdeal :
    ((Tor' (ModuleCat.{u} A) 2).obj (ModuleCat.of A (A ⧸ J))).obj (ModuleCat.of A (A ⧸ J)) ≅
      ((Tor' (ModuleCat.{u} A) 1).obj (ModuleCat.of A (A ⧸ J))).obj (ModuleCat.of A J) :=
  Tor'δSecondIso (shortExact_quotientShortComplex J) (ModuleCat.of A (A ⧸ J)) 1
    (isZero_Tor'_succ_obj_of_flat _ (ModuleCat.of A A) 1)
    (isZero_Tor'_succ_obj_of_flat _ (ModuleCat.of A A) 0)

/-- The kernel of `J ⊗_A J → A ⊗_A J` is the kernel of the multiplication map
`Submodule.mulMap J J : J ⊗_A J →ₗ[A] A`. -/
theorem ker_rTensor_subtype_eq_ker_mulMap :
    LinearMap.ker (J.subtype.rTensor J) = LinearMap.ker (Submodule.mulMap J J) := by
  have hcomp : (J.subtype ∘ₗ (TensorProduct.lid A J).toLinearMap) ∘ₗ
      J.subtype.rTensor J = Submodule.mulMap J J := by
    apply TensorProduct.ext'
    intro x y
    simp
  have hker : LinearMap.ker (J.subtype ∘ₗ (TensorProduct.lid A J).toLinearMap) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (J.injective_subtype.comp (TensorProduct.lid A J).injective)
  rw [← hcomp, LinearMap.ker_comp, hker, Submodule.comap_bot]

/-- The categorical kernel of `J ⊗ J → A ⊗ J` as the submodule `ker (Submodule.mulMap J J)`. -/
noncomputable def kernelIsoKerMulMap :
    kernel ((quotientShortComplex J).f ▷ ModuleCat.of A J) ≅
      ModuleCat.of A (LinearMap.ker (Submodule.mulMap J J)) :=
  ModuleCat.kernelIsoKer _ ≪≫
    (LinearEquiv.ofEq _ _ (ker_rTensor_subtype_eq_ker_mulMap J)).toModuleIso

/-- The two term exact sequence `Tor₁(B, J) → J ⊗ J → A ⊗ J` at the bottom of the long exact
sequence of `Tor_•(-, J)`, for `B = A ⧸ J`. -/
noncomputable def bottomShortComplex : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk (Tor'δFirstZero (shortExact_quotientShortComplex J) (ModuleCat.of A J))
    ((quotientShortComplex J).f ▷ ModuleCat.of A J)
    ((Tor'_composableArrows_exact_first_zero (shortExact_quotientShortComplex J)
      (ModuleCat.of A J)).toIsComplex.zero 2)

/-- The sequence `Tor₁(B, J) → J ⊗ J → A ⊗ J` is exact. -/
theorem exact_bottomShortComplex : (bottomShortComplex J).Exact :=
  (Tor'_composableArrows_exact_first_zero (shortExact_quotientShortComplex J)
    (ModuleCat.of A J)).exact' 2 3 4

/-- `Tor₁(B, J) → J ⊗ J` is injective, since `A` is projective and so `Tor₁(A, J) = 0`. -/
instance mono_bottomShortComplex_f : Mono (bottomShortComplex J).f :=
  mono_Tor'δFirstZero (shortExact_quotientShortComplex J) (ModuleCat.of A J)
    (isZero_Tor'_succ_of_projective (ModuleCat.{u} A) (ModuleCat.of A A) (ModuleCat.of A J) 0)

/-- **Second dimension shift.** For `B = A ⧸ J` the connecting morphism at the bottom of the long
exact sequence of `Tor_•(-, J)` is a monomorphism with image the kernel of multiplication, so
`Tor₁(B, J) ≅ ker (Submodule.mulMap J J)`: the sequence `0 → J → A → B → 0` has projective
middle term, so `Tor₁(A, J)` vanishes. -/
noncomputable def torOneIdealIsoKerMulMap :
    ((Tor' (ModuleCat.{u} A) 1).obj (ModuleCat.of A (A ⧸ J))).obj (ModuleCat.of A J) ≅
      ModuleCat.of A (LinearMap.ker (Submodule.mulMap J J)) :=
  ((exact_bottomShortComplex J).fIsKernel.conePointUniqueUpToIso (kernelIsKernel _)) ≪≫
    kernelIsoKerMulMap J

/-- **The dimension shift.** For a commutative ring `A`, an ideal `J` and `B = A ⧸ J`, the second
Tor of `B` with itself is the kernel of the multiplication map `J ⊗_A J →ₗ[A] A`. -/
noncomputable def torTwoSelfIsoKerMulMap :
    ((Tor' (ModuleCat.{u} A) 2).obj (ModuleCat.of A (A ⧸ J))).obj (ModuleCat.of A (A ⧸ J)) ≅
      ModuleCat.of A (LinearMap.ker (Submodule.mulMap J J)) :=
  torTwoSelfIsoTorOneIdeal J ≪≫ torOneIdealIsoKerMulMap J

/-- The dimension shift `Tor₂(A ⧸ J, A ⧸ J) ≅ ker (Submodule.mulMap J J)` as an `A`-linear
equivalence. -/
noncomputable def torTwoSelfLinearEquivKerMulMap :
    ((Tor' (ModuleCat.{u} A) 2).obj (ModuleCat.of A (A ⧸ J))).obj (ModuleCat.of A (A ⧸ J)) ≃ₗ[A]
      LinearMap.ker (Submodule.mulMap J J) :=
  (torTwoSelfIsoKerMulMap J).toLinearEquiv

end Stacks.Tor.DimensionShift

end
