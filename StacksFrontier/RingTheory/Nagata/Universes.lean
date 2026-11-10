module

public import StacksFrontier.RingTheory.Nagata.FiniteType

/-!
# Finite type algebras over a Nagata ring, at two independent universes

`IsNagataRing R` tests `R` against the finite field extensions of the fraction fields of its
prime quotients that live in **`R`'s own universe**. The transport lemmas that move the condition
across a universe boundary are stated where the condition itself is: `IsJapaneseRing.of_ringEquiv`
and `module_finite_integralClosure_of_isJapaneseRing` in
`StacksFrontier.RingTheory.Nagata.Japanese`,
`MonogenicN1.isNagataRing_of_ringEquiv` in `StacksFrontier.RingTheory.Nagata.MonogenicN1`, resting
on `StacksFrontier.RingTheory.Nagata.Shrink`.

What is left for this module is the two consequences that genuinely live downstream, because they
consume `isNagataRing_tfae` (Tag 0334) and `isNagata_of_isLocalization` (Tag 032U): a finite type,
or essentially finite type, algebra over a Nagata ring is Nagata, with **no constraint relating
the two universes**. The same-universe form is item (2) of `isNagataRing_tfae`; the coupling comes
off by presenting the algebra as a quotient of `MvPolynomial (Fin n) A`, which lives in the base's
universe, and transporting along the resulting isomorphism.

## Main results

* `IsNagataRing.of_finiteType`: a finite type algebra over a Nagata ring is Nagata, at two
  independent universes.
* `IsNagataRing.of_essFiniteType`: the same for an algebra essentially of finite type.

## References

* [Stacks Project, Tag 0334](https://stacks.math.columbia.edu/tag/0334)
* [Stacks Project, Tag 032U](https://stacks.math.columbia.edu/tag/032U)
-/

@[expose] public section

universe u v

/-- **A finite type algebra over a Nagata ring is Nagata, at two independent universes.**

Item (2) of `isNagataRing_tfae` (Tag 0334) with the universe coupling removed. The algebra is
presented as a quotient of `MvPolynomial (Fin n) A`, which lives in `A`'s universe, so the
same-universe form applies to that quotient; `MonogenicN1.isNagataRing_of_ringEquiv` then carries
the conclusion across the universe boundary. -/
theorem IsNagataRing.of_finiteType {A : Type u} {S : Type v} [CommRing A] [CommRing S]
    [Algebra A S] [Algebra.FiniteType A S] (hA : IsNagataRing A) : IsNagataRing S := by
  have hfinite : ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra.FiniteType A T],
      IsNagataRing T := ((isNagataRing_tfae (R := A)).out 1 2).mp hA
  obtain ⟨n, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := S)).mp inferInstance
  exact MonogenicN1.isNagataRing_of_ringEquiv
    (Ideal.quotientKerAlgEquivOfSurjective hf).toRingEquiv (hfinite _)

/-- **An algebra essentially of finite type over a Nagata ring is Nagata, at two independent
universes.**

`Algebra.EssFiniteType.subalgebra A B` is of finite type over `A` and `B` is its localization at
`Algebra.EssFiniteType.submonoid A B`. Only the first step crosses a universe boundary — the
subalgebra already lives in `B`'s universe — so the localization step is the existing
same-universe Tag 032U. -/
theorem IsNagataRing.of_essFiniteType {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.EssFiniteType A B] (hA : IsNagataRing A) : IsNagataRing B := by
  have hC : IsNagataRing (Algebra.EssFiniteType.subalgebra A B) :=
    IsNagataRing.of_finiteType hA
  exact isNagata_of_isLocalization (Algebra.EssFiniteType.subalgebra A B)
    (Algebra.EssFiniteType.submonoid A B) B hC

end
