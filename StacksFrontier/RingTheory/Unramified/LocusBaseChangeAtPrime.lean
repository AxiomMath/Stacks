module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Unramified.Locus
public import StacksFrontier.RingTheory.Support.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The unramified locus under base change, at a single prime

Let `R → A` be of finite type, let `R → R'` be an arbitrary ring map and let `A'` be the base
change `R' ⊗_R A`. Let `q'` be a prime of `A'` lying over the prime `q` of `A`. This file proves
that `A` is unramified over `R` at `q` if and only if `A'` is unramified over `R'` at `q'`, with
no flatness hypothesis on either side.

## Main results

* `Algebra.isUnramifiedAt_iff_isUnramifiedAt_of_isPushout`: unramifiedness at a prime is
  insensitive to base change, at any prime lying over it.

## Implementation notes

Unramifiedness at a prime is the vanishing of the module of differentials there
(`Algebra.unramifiedLocus_eq_compl_support`), the differentials of a base change are the base
change of the differentials (`KaehlerDifferential.tensorKaehlerEquiv`), and the support of the
base change of a finite module is the inverse image of the support
(`IsBaseChange.support_eq_preimage_comap`). The finite type hypothesis enters only through the
finiteness of `Ω[A⁄R]` as an `A`-module. No flatness is needed on either side, in contrast with
the smooth locus: the inclusion of supports that is faithful flatness in the flat case is
Nakayama's lemma over the residue field extension here.

The base change is the abstract one, `Algebra.IsPushout R A R' A'`, rather than the model
`R' ⊗_R A`; the model is a witness by `TensorProduct.isPushout`, and stating the hypothesis lets
a consumer apply the result to the base change already in hand. The correspondence of primes is
`Ideal.LiesOver`.

## References

* [Stacks Project, Tag 0475](https://stacks.math.columbia.edu/tag/0475)
* [Stacks Project, Tag 0BUR](https://stacks.math.columbia.edu/tag/0BUR)
-/

@[expose] public section

open TensorProduct

namespace Algebra

/-- The support of the base change of a finite module is the inverse image of its support. This
is `IsBaseChange.support_eq_preimage_comap` for the model base change `A' ⊗[A] M`. -/
@[ega "0 1.7.5" "partial"]
private theorem support_tensorProduct_eq_preimage_comap (A A' : Type*) [CommRing A]
    [CommRing A'] [Algebra A A'] (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Module.support A' (A' ⊗[A] M) =
      PrimeSpectrum.comap (algebraMap A A') ⁻¹' Module.support A M :=
  (IsBaseChange.of_equiv (LinearEquiv.refl A' (A' ⊗[A] M))
    (f := TensorProduct.mk A A' M 1) fun _ ↦ rfl).support_eq_preimage_comap

/-- **The unramified locus commutes with base change, at a prime.** Let `R → A` be of finite
type, let `A'` be the base change of `A` along an arbitrary `R → R'` and let `q'` be a prime of
`A'` lying over `q ⊆ A`. Then `A` is unramified over `R` at `q` if and only if `A'` is unramified
over `R'` at `q'`.

This is the commutative algebra underlying the base change of the unramified locus of a morphism
of schemes. -/
@[ega "IV 17.7.2" "(i), affine case"]
theorem isUnramifiedAt_iff_isUnramifiedAt_of_isPushout (R A R' A' : Type*) [CommRing R]
    [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra A A']
    [Algebra R' A'] [Algebra R A'] [IsScalarTower R R' A'] [IsScalarTower R A A']
    [Algebra.IsPushout R A R' A'] [Algebra.FiniteType R A]
    (q : Ideal A) (q' : Ideal A') [q.IsPrime] [q'.IsPrime] [q'.LiesOver q] :
    Algebra.IsUnramifiedAt R q ↔ Algebra.IsUnramifiedAt R' q' := by
  have hsymm : Algebra.IsPushout R R' A A' := .symm inferInstance
  have hfin : Module.Finite A Ω[A⁄R] := inferInstance
  have hsupp : Module.support A' Ω[A'⁄R'] =
      PrimeSpectrum.comap (algebraMap A A') ⁻¹' Module.support A Ω[A⁄R] := by
    rw [← (KaehlerDifferential.tensorKaehlerEquiv R R' A A').support_eq]
    exact support_tensorProduct_eq_preimage_comap A A' Ω[A⁄R]
  have hcomap : PrimeSpectrum.comap (algebraMap A A') ⟨q', ‹q'.IsPrime›⟩
      = ⟨q, ‹q.IsPrime›⟩ := PrimeSpectrum.ext (q'.over_def q).symm
  have hmem : (⟨q', ‹q'.IsPrime›⟩ : PrimeSpectrum A') ∈ Algebra.unramifiedLocus R' A' ↔
      (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum A) ∈ Algebra.unramifiedLocus R A := by
    rw [Algebra.unramifiedLocus_eq_compl_support, Algebra.unramifiedLocus_eq_compl_support,
      Set.mem_compl_iff, Set.mem_compl_iff, hsupp, Set.mem_preimage, hcomap]
  exact hmem.symm

end Algebra

end
