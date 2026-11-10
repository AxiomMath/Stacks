module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Two presentations of one quotient

Two surjective additive maps out of one abelian group with the same kernel present the same
quotient, so their targets are canonically isomorphic.

## Main definitions

* `Stacks.addEquivOfSurjectiveKerEq`: the isomorphism of the two targets.

## Main results

* `Stacks.addEquivOfSurjectiveKerEq_apply`: the isomorphism carries the image of an element
  under the first map to its image under the second.

## Implementation notes

The isomorphism factors both maps through `M ⧸ ker` and transports along the equality of
kernels, so no preimages are chosen.
-/

@[expose] public noncomputable section

namespace Stacks

/-- Two additive maps with the same vanishing locus have the same kernel. -/
theorem ker_eq_ker_of_eq_zero_iff {M A B : Type*} [AddCommGroup M] [AddCommGroup A]
    [AddCommGroup B] (f : M →+ A) (g : M →+ B) (hker : ∀ x, f x = 0 ↔ g x = 0) :
    f.ker = g.ker := by
  ext x
  simpa only [AddMonoidHom.mem_ker] using hker x

/-- **Two surjective additive maps out of one group with the same kernel identify their
targets.** -/
def addEquivOfSurjectiveKerEq {M A B : Type*} [AddCommGroup M] [AddCommGroup A]
    [AddCommGroup B] (f : M →+ A) (g : M →+ B) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hker : ∀ x, f x = 0 ↔ g x = 0) : A ≃+ B :=
  (QuotientAddGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (ker_eq_ker_of_eq_zero_iff f g hker)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective g hg))

/-- The identification carries the image of an element under the first map to its image under
the second. -/
theorem addEquivOfSurjectiveKerEq_apply {M A B : Type*} [AddCommGroup M] [AddCommGroup A]
    [AddCommGroup B] (f : M →+ A) (g : M →+ B) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hker : ∀ x, f x = 0 ↔ g x = 0) (x : M) :
    addEquivOfSurjectiveKerEq f g hf hg hker (f x) = g x := by
  have h1 : (QuotientAddGroup.quotientKerEquivOfSurjective f hf).symm (f x) =
      (QuotientAddGroup.mk x : M ⧸ f.ker) :=
    (QuotientAddGroup.quotientKerEquivOfSurjective f hf).symm_apply_eq.mpr rfl
  change (QuotientAddGroup.quotientKerEquivOfSurjective g hg)
      ((QuotientAddGroup.quotientAddEquivOfEq (ker_eq_ker_of_eq_zero_iff f g hker))
        ((QuotientAddGroup.quotientKerEquivOfSurjective f hf).symm (f x))) = g x
  rw [h1]
  rfl

end Stacks

end
