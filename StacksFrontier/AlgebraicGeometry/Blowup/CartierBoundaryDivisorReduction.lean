module

public import StacksFrontier.AlgebraicGeometry.Blowup.DominatedByBlowup

/-!
# The reduction to a divisor of Remark 38.30.1

After a single `U`-admissible blowup of a quasi-compact and quasi-separated scheme, a
quasi-compact open `U` is the complement of an effective Cartier divisor supported on the
boundary, and is then scheme theoretically dense.

## Main results

* `AlgebraicGeometry.CartierBoundaryDivisorReduction`: the full conclusion of the "reduction to a
  divisor" paragraph of [Stacks, Tag 080Y].
* `AlgebraicGeometry.cartierBoundaryDivisorReduction`: [Stacks, Tag 080Y], that paragraph in full.

## Implementation notes

The centre is the one of `AlgebraicGeometry.cartierBoundaryReduction`, whose exceptional locus is
the boundary. The two further assertions are for the exceptional ideal of that same blowup: it is
an effective Cartier divisor ([Stacks, Tag 02OS] part (2),
`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal`), and the complement of an effective
Cartier divisor is scheme theoretically dense ([Stacks, Tag 07ZU],
`Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor`).

## References

* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The full conclusion of the "reduction to a divisor" paragraph of [Stacks, Tag 080Y]: a
`U`-admissible blowup of `S` on which the boundary is cut out by an *effective Cartier divisor*
whose complement is exactly the inverse image of `U`, and on which that inverse image is
*scheme theoretically dense*.

This is the whole of the third paragraph of Remark 38.30.1, where
`AlgebraicGeometry.CartierBoundaryReduction` records only the identification of the exceptional
locus with the boundary.

It is therefore **not** a duplicate of `AlgebraicGeometry.CartierBoundaryReduction`, and must not
be replaced by an alias of it: this predicate asserts strictly more, namely the existence of an
effective Cartier divisor `D` with that support together with the scheme theoretic density of the
inverse image of `U`. Aliasing would weaken every consumer. A statement-text duplicate scan pairs
the two because their conclusions begin alike; the bodies differ from the third conjunct on. -/
public def CartierBoundaryDivisorReduction (S : Scheme.{u}) (U : S.Opens) : Prop :=
  ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
    Disjoint (U : Set S) (I.support : Set S) ∧
      ∃ D : (blowUp I).IdealSheafData,
        Stacks.Divisors.IsEffectiveCartierDivisor D ∧
          D.support.compl = (blowUpToBase I ⁻¹ᵁ U : (blowUp I).Opens) ∧
            Scheme.Opens.IsSchemeTheoreticallyDense (blowUpToBase I ⁻¹ᵁ U : (blowUp I).Opens)

/-- **Stacks Project, Tag 080Y**, the reduction to a divisor of Remark 38.30.1 in full. On a
quasi-compact and quasi-separated scheme `S` a quasi-compact open `U` becomes, after a single
`U`-admissible blowup, the complement of an effective Cartier divisor `D` supported on the
boundary; and then `U` is scheme theoretically dense.

The centre is the one of `AlgebraicGeometry.cartierBoundaryReduction`, and `D` is the
exceptional divisor of its blowup: an effective Cartier divisor by [Stacks, Tag 02OS] part (2)
(`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal`), whose support is the boundary by
that theorem. The density is then [Stacks, Tag 07ZU]
(`Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor`): the
complement of an effective Cartier divisor is scheme theoretically dense. -/
@[stacks 080Y "the reduction to a divisor: after one U-admissible blowup the boundary is an \
effective Cartier divisor whose complement is the inverse image of U, and that inverse image is \
scheme theoretically dense"]
public theorem cartierBoundaryDivisorReduction [CompactSpace S] [QuasiSeparatedSpace S]
    (U : S.Opens) (hU : IsCompact (U : Set S)) : CartierBoundaryDivisorReduction S U := by
  obtain ⟨I, hIfp, hIU, hIboundary⟩ := cartierBoundaryReduction U hU
  have hcompl : ((exceptionalIdeal I).support.compl : (blowUp I).Opens) =
      (blowUpToBase I ⁻¹ᵁ U : (blowUp I).Opens) := by
    refine TopologicalSpace.Opens.ext ?_
    rw [show (((exceptionalIdeal I).support.compl : (blowUp I).Opens) : Set (blowUp I)) =
      ((exceptionalIdeal I).support : Set (blowUp I))ᶜ from rfl, hIboundary, compl_compl]
  refine ⟨I, hIfp, hIU, exceptionalIdeal I,
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I, hcompl, ?_⟩
  exact hcompl ▸ Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor
    (exceptionalIdeal I) (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I)

end AlgebraicGeometry

end
