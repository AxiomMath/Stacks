module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Finite products of localizations at different submonoids

`Mathlib`'s `IsLocalizedModule.pi` says that a finite product of localizations of modules at one
fixed submonoid is again a localization at that submonoid. This file proves the variant in which
the submonoids *differ* from factor to factor, under the hypothesis that the product of the
corresponding localizations of the base ring is itself a localization of the base ring: if
`B i` is a localization of `A` at `S i`, `N i` is a localization of `M` at `S i`, and
`∏ B i` is a localization of `A` at `S`, then `∏ N i` is a localization of `M` at `S`.

The instance to have in mind is a ring `A` with finitely many minimal primes `𝔮 i` all of whose
zerodivisors lie in a minimal prime: there `∏ A_{𝔮 i}` is the total ring of fractions `Q(A)`,
and the conclusion is `Q(A) ⊗_A M = ∏ M_{𝔮 i}`.

## Main results

* `isBaseChange_pi_of_forall_isBaseChange`: a finite product of base changes along *different*
  `A`-algebras `B i` is the base change along `∏ B i`. This is the variant of
  `IsBaseChange.pi` in which the target algebra varies with the index.
* `isLocalizedModule_pi_of_isLocalization_pi`: the localization statement obtained from it.

## Implementation notes

The proof is the identification `(∏ B i) ⊗_A M = ∏ (B i ⊗_A M)`, valid because the index type
is finite. It is assembled out of `TensorProduct.comm` and `Mathlib`'s `TensorProduct.piRight`,
which puts the product in the *second* tensor factor; the two commutativity isomorphisms move it
to the first, where `IsBaseChange` needs it.

Only `A`-linearity of that isomorphism has to be supplied, not `∏ B i`-linearity, because
`IsBaseChange S f` unfolds to `IsTensorProduct` of the `A`-bilinear map `(s, m) ↦ s • f m`, and
`IsTensorProduct.of_equiv` asks for an isomorphism over the base ring. Going through
`IsBaseChange.of_equiv` instead would require an isomorphism linear over `∏ B i`, which is more
than is available from the componentwise data.
-/

@[expose] public section

open TensorProduct

universe u v w

variable {A : Type u} [CommRing A] {ι : Type v}
  {B : ι → Type w} [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
  {M : Type*} [AddCommGroup M] [Module A M]
  {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)]
  [∀ i, Module (B i) (N i)] [∀ i, IsScalarTower A (B i) (N i)]

/-- A finite product of base changes along varying `A`-algebras is the base change along the
product algebra: `(∏ B i) ⊗_A M = ∏ (B i ⊗_A M)`.

This is the variant of `IsBaseChange.pi` in which the algebra, rather than the module, varies
with the index. -/
theorem isBaseChange_pi_of_forall_isBaseChange [Finite ι] (f : ∀ i, M →ₗ[A] N i)
    (hf : ∀ i, IsBaseChange (B i) (f i)) :
    IsBaseChange (∀ i, B i) (LinearMap.pi f) := by
  classical
  cases nonempty_fintype ι
  refine IsTensorProduct.of_equiv (f := _)
    ((TensorProduct.comm A (∀ i, B i) M) ≪≫ₗ
      (TensorProduct.piRight A A M (fun i ↦ B i)) ≪≫ₗ
        LinearEquiv.piCongrRight
          (fun i ↦ (TensorProduct.comm A M (B i)) ≪≫ₗ ((hf i).equiv.restrictScalars A))) ?_
  intro b m
  funext i
  simp

/-- A finite product of localizations of a module at **different** submonoids is a localization
of that module, at any submonoid at which the product of the corresponding localizations of the
base ring is a localization of the base ring.

With one fixed submonoid throughout this is `IsLocalizedModule.pi`. -/
theorem isLocalizedModule_pi_of_isLocalization_pi [Finite ι] (S : Submonoid A)
    (Sb : ι → Submonoid A) [∀ i, IsLocalization (Sb i) (B i)]
    (hS : IsLocalization S (∀ i, B i))
    (f : ∀ i, M →ₗ[A] N i) [∀ i, IsLocalizedModule (Sb i) (f i)] :
    IsLocalizedModule S (LinearMap.pi f) := by
  have := hS
  rw [isLocalizedModule_iff_isBaseChange S (∀ i, B i)]
  exact isBaseChange_pi_of_forall_isBaseChange f
    fun i ↦ (isLocalizedModule_iff_isBaseChange (Sb i) (B i) (f i)).mp inferInstance
