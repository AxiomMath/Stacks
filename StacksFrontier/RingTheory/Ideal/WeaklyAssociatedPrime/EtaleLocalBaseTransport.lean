module

public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.EtaleBaseChange

/-!
# Weak association transported along an étale local base change

Let `R → R'` be an étale ring map, let `p'` be a prime of `R'` lying over a prime `p` of `R`,
and let `X` be an `R`-module.  This file records that the maximal ideal of the local ring
`R'_{p'}` is weakly associated to `R'_{p'} ⊗[R] X` exactly when `p` is weakly associated
to `X`.

The proof chains two known equivalences.  Étale base change
(`Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_tensorProduct_iff_of_etale`, the
ring-theoretic form of [Stacks, Tag 05FP]) identifies weak association of `p'` to `R' ⊗[R] X`
with weak association of its contraction to `X`, and that contraction is `p` because `p'` lies
over `p`.  Localization at `p'`, which is insensitive for weak association by
`Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_tensor_comap_iff_of_isLocalization`,
then moves the statement from `p'` to the maximal ideal of `R'_{p'}`;  the relevant
localization map is the base change of `R' → R'_{p'}` tensored with the identity of `X`.

## Main results

* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_tensorProduct_localization_iff_of_etale`:
  weak association of the maximal ideal of `R'_{p'}` to `R'_{p'} ⊗[R] X` is weak association
  of `p` to `X`.

## References

* [Stacks Project, Tag 05FP](https://stacks.math.columbia.edu/tag/05FP)
* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Stacks.WeaklyAssociatedPrimes

/-- For an étale ring map `R → R'`, a prime `p'` of `R'` lying over a prime `p` of `R` and an
`R`-module `X`, the maximal ideal of the local ring `R'_{p'}` is weakly associated to
`R'_{p'} ⊗[R] X` if and only if `p` is weakly associated to `X`. -/
public theorem isWeaklyAssociatedPrime_tensorProduct_localization_iff_of_etale
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (p : Ideal R) [p.IsPrime] (p' : Ideal R') [p'.IsPrime] [p'.LiesOver p]
    (X : Type u) [AddCommGroup X] [Module R X] :
    IsWeaklyAssociatedPrime (Localization.AtPrime p')
        (Localization.AtPrime p' ⊗[R] X)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p')) ↔
      IsWeaklyAssociatedPrime R X p := by
  have hloc := isWeaklyAssociatedPrime_tensor_comap_iff_of_isLocalization
    (R := R) (A := R') (A' := Localization.AtPrime p') (P := R')
    (P' := Localization.AtPrime p') (X := X) p'.primeCompl
    (Algebra.linearMap R' (Localization.AtPrime p'))
    (IsLocalRing.maximalIdeal (Localization.AtPrime p')) inferInstance
  have hmp : (IsLocalRing.maximalIdeal (Localization.AtPrime p')).comap
      (algebraMap R' (Localization.AtPrime p')) = p' :=
    IsLocalization.AtPrime.under_maximalIdeal (S := Localization.AtPrime p') (I := p')
  rw [hmp] at hloc
  rw [hloc, isWeaklyAssociatedPrime_tensorProduct_iff_of_etale, ← Ideal.under_def R p',
    ← p'.over_def p]

end Stacks.WeaklyAssociatedPrimes

end
