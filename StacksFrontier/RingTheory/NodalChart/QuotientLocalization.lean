module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Localizing a hypersurface quotient at a prime

Let `A` be a commutative ring, `f : A`, and let `q` be a prime of `A ⧸ (f)` whose contraction to
`A` is a prime `p`. The localization of `A ⧸ (f)` at `q` is then the quotient of the localization
of `A` at `p` by the image of `(f)`: localizing and cutting by `f` commute, because the
multiplicative set defining `q` is the image of the one defining `p`.

The statement is recorded as an `IsLocalization` property of that quotient rather than as a ring
equivalence, which is the form the regularity arguments for the standard nodal model consume: it
lets `IsLocalization.algEquiv` produce the comparison map with `Localization.AtPrime q`.

## Main results

* `Stacks.isLocalization_quotient_atPrime_of_mem_iff` — the quotient
  `Localization.AtPrime p ⧸ (f)` is a localization of `A ⧸ (f)` at `q`, under the hypothesis that
  membership in `q` of the class of `r : A` is equivalent to membership of `r` in `p`.

## Implementation notes

This is the public form of a helper that is private to
`StacksFrontier/RingTheory/NodalChart/Regularity.lean`, where it was introduced to serve the two
directions of the hypersurface regularity criterion; it could not be made public there, so the
statement and its proof are reproduced here for use by consumers outside that file.

## References

* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
* [Stacks Project, Tag 07PF](https://stacks.math.columbia.edu/tag/07PF)
-/

@[expose] public noncomputable section

universe u

namespace Stacks

/-- **The localization of `A ⧸ (f)` at a prime `q` is the quotient of the localization of `A` at
the contraction of `q` by the image of `(f)`.** The hypothesis `hpq` says that `p` is that
contraction: a class `Ideal.Quotient.mk (Ideal.span {f}) r` lies in `q` exactly when `r` lies in
`p`. -/
public theorem isLocalization_quotient_atPrime_of_mem_iff
    {A : Type u} [CommRing A] (f : A) {p : Ideal A} [p.IsPrime]
    {q : Ideal (A ⧸ Ideal.span {f})} [q.IsPrime]
    (hpq : ∀ r : A, Ideal.Quotient.mk (Ideal.span {f}) r ∈ q ↔ r ∈ p) :
    IsLocalization q.primeCompl
      (Localization.AtPrime p ⧸
        (Ideal.span {f}).map (algebraMap A (Localization.AtPrime p))) := by
  have hloc : IsLocalization
      (Algebra.algebraMapSubmonoid (A ⧸ Ideal.span {f}) p.primeCompl)
      (Localization.AtPrime p ⧸
        (Ideal.span {f}).map (algebraMap A (Localization.AtPrime p))) :=
    IsLocalization.of_surjective p.primeCompl (Localization.AtPrime p)
      (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
      (fun a ha ↦ by rw [Ideal.mk_ker] at ha ⊢; assumption)
  have hsub : Algebra.algebraMapSubmonoid (A ⧸ Ideal.span {f}) p.primeCompl = q.primeCompl := by
    ext y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨?_, fun hr ↦ ⟨r, fun hrp ↦ hr ((hpq r).mpr hrp), rfl⟩⟩
    rintro ⟨s, hs, heq⟩ hqr
    refine hs ((hpq s).mp ?_)
    change algebraMap A (A ⧸ Ideal.span {f}) s ∈ q
    rwa [heq]
  rwa [hsub] at hloc

end Stacks

end
