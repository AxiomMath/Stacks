module

public import Mathlib.RingTheory.Flat.Localization
public import StacksCore.Tactic.StacksAttribute

/-!
# Flatness over a base ring is inherited by localizations of the module

Let `R → A` be a ring map and let `M` be an `A`-module which is flat over `R`. This file shows
that every localization of `M` at a multiplicative subset of `A` is again flat over `R`.

## Main results

* `Module.Flat.of_isLocalizedModule_of_tower`: if `M` is an `A`-module flat over a base ring `R`
  and `g : M → M'` exhibits `M'` as the localization of `M` at a multiplicative subset of `A`,
  then `M'` is flat over `R`.
* `Module.Flat.localizedModule_of_tower`: the same for `LocalizedModule S M`, as an instance.
* `Module.Flat.localizedModule_atPrime_of_tower`: the same at a prime of `A`.

## Implementation notes

Mathlib's `Module.Flat.of_isLocalizedModule` is a different statement: there the multiplicative
subset lives in the base ring and the conclusion is flatness over the localized base ring, whereas
here the base ring is untouched and the multiplicative subset lives in `A`.

The restriction of scalars along `R → A` is expressed by `[Module R M] [IsScalarTower R A M]`.

## References

* [Stacks Project, Tag 05UA](https://stacks.math.columbia.edu/tag/05UA)
-/

@[expose] public section

open TensorProduct

namespace Module.Flat

variable {R A M M' : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']

/-- If an `A`-module `M` is flat over a base ring `R` and `g : M → M'` exhibits `M'` as the
localization of `M` at a multiplicative subset `S` of `A`, then `M'` is flat over `R`. -/
theorem of_isLocalizedModule_of_tower (S : Submonoid A) (g : M →ₗ[A] M')
    [IsLocalizedModule S g] [Module.Flat R M] : Module.Flat R M' := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ Q
  have hinj : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor A M Q.subtype) := by
    rw [TensorProduct.AlgebraTensorModule.coe_lTensor]
    exact Module.Flat.iff_lTensor_injectiveₛ.1 ‹Module.Flat R M› Q
  have := IsLocalizedModule.map_injective
    (f := TensorProduct.AlgebraTensorModule.rTensor R (↥Q) g)
    (g := TensorProduct.AlgebraTensorModule.rTensor R P g) S _ hinj
  rw [IsLocalizedModule.map_lTensor A S Q.subtype g] at this
  rwa [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := A)]

/-- A localization of a module flat over a base ring is flat over that base ring. -/
instance localizedModule_of_tower (S : Submonoid A) [Module.Flat R M] :
    Module.Flat R (LocalizedModule S M) :=
  of_isLocalizedModule_of_tower S (LocalizedModule.mkLinearMap S M)

/-- The localization of a module flat over a base ring at a prime of the top ring is flat over
that base ring. -/
instance localizedModule_atPrime_of_tower (q : Ideal A) [q.IsPrime] [Module.Flat R M] :
    Module.Flat R (LocalizedModule q.primeCompl M) :=
  localizedModule_of_tower q.primeCompl

end Module.Flat

end
