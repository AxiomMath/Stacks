module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpCompletionNormal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CompletionDefinesRationalSingularity

/-!
# Both clauses of Tag 0BG7 over carried hypotheses

Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two defining a rational singularity
whose completion `A^` along `𝔪` is a normal domain. Assuming [Stacks, Tag 0B4Z], [Stacks, Tag 081S]
and the descent of the vanishing of `H¹` along `A ⟶ A^`, the ring `A^` defines a rational
singularity, and the completion of the local ring of the blowup of `Spec(A)` in `𝔪` at every
closed point is a normal domain.

## Main results

* `isNormalDomain_adicCompletion_stalk_blowUp_maximalIdeal_of_definesRationalSingularity`:
  clause (2) of [Stacks, Tag 0BG7] over the carried hypotheses.
* `definesRationalSingularity_and_isNormalDomain_stalk_blowUp_maximalIdeal`: both clauses of
  [Stacks, Tag 0BG7] over the carried hypotheses.

## Implementation notes

The carried hypotheses are:

* `h0B4Z`, [Stacks, Tag 0B4Z]: the blowup of the spectrum of a local normal Nagata domain of
  dimension two defining a rational singularity, in its maximal ideal, is normal.
* `h081S`, [Stacks, Tag 081S]: for every modification `Y ⟶ Spec(A^)` there is a blowup of
  `Spec(A^)`, admissible for the punctured spectrum, along which the strict transform of `Y` is an
  open subscheme of the blowup.
* `hdescend`, `AlgebraicGeometry.CompletionVanishingDescends`: flat base change for `H¹` along
  `A ⟶ A^` ([Stacks, Tag 02KH]) followed by the first conclusion of [Stacks, Tag 0AXF].

The statement of [Stacks, Tag 0BG7] with no carried hypotheses is
`AlgebraicGeometry.definesRationalSingularity_adicCompletion_and_isNormalDomain_stalk_blowUp`.

## References

* [Stacks Project, Tag 0BG7](https://stacks.math.columbia.edu/tag/0BG7)
* [Stacks Project, Tag 0B4Z](https://stacks.math.columbia.edu/tag/0B4Z)
* [Stacks Project, Tag 081S](https://stacks.math.columbia.edu/tag/081S)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- For a local normal Nagata domain `A` of dimension two defining a rational singularity whose
completion `A^` is a normal domain, assuming [Stacks, Tag 0B4Z] (`h0B4Z`), [Stacks, Tag 081S]
(`h081S`) and `CompletionVanishingDescends A` (`hdescend`), the completion of the local ring of the
blowup of `Spec(A)` in the maximal ideal at a closed point is a normal domain. -/
public theorem isNormalDomain_adicCompletion_stalk_blowUp_maximalIdeal_of_definesRationalSingularity
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    [IsNormalDomain (AdicCompletion (maximalIdeal A) A)]
    (hNagata : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hrat : DefinesRationalSingularity A)
    (h081S : ∀ ⦃Y : Scheme.{u}⦄ (q : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))),
      IsModification q →
        StrictTransformOpenImmersion q
          (Stacks.puncturedSpectrum (AdicCompletion (maximalIdeal A) A)))
    (hdescend : CompletionVanishingDescends.{u} A)
    (h0B4Z : BlowUpMaximalIdealIsNormal.{u})
    (x : blowUp (maximalIdealSheaf A))
    (hx : IsClosed ({x} : Set (blowUp (maximalIdealSheaf A)))) :
    IsNormalDomain (AdicCompletion
      (maximalIdeal ((blowUp (maximalIdealSheaf A)).presheaf.stalk x))
      ((blowUp (maximalIdealSheaf A)).presheaf.stalk x)) :=
  isNormalDomain_adicCompletion_stalk_blowUp_maximalIdeal_of_rationalSingularity A hNagata hdim
    hrat inferInstance h0B4Z
    (definesRationalSingularity_adicCompletion_maximalIdeal A hNagata hdim hrat h081S hdescend)
    x hx

/-- For a local normal Nagata domain `A` of dimension two defining a rational singularity whose
completion `A^` is a normal domain, assuming [Stacks, Tag 0B4Z] (`h0B4Z`), [Stacks, Tag 081S]
(`h081S`) and `CompletionVanishingDescends A` (`hdescend`): `A^` defines a rational singularity,
and the completion of the local ring of the blowup of `Spec(A)` in the maximal ideal at every
closed point is a normal domain. -/
public theorem definesRationalSingularity_and_isNormalDomain_stalk_blowUp_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    [IsNormalDomain (AdicCompletion (maximalIdeal A) A)]
    (hNagata : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hrat : DefinesRationalSingularity A)
    (h081S : ∀ ⦃Y : Scheme.{u}⦄ (q : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))),
      IsModification q →
        StrictTransformOpenImmersion q
          (Stacks.puncturedSpectrum (AdicCompletion (maximalIdeal A) A)))
    (hdescend : CompletionVanishingDescends.{u} A)
    (h0B4Z : BlowUpMaximalIdealIsNormal.{u}) :
    DefinesRationalSingularity (AdicCompletion (maximalIdeal A) A) ∧
      ∀ x : blowUp (maximalIdealSheaf A), IsClosed ({x} : Set (blowUp (maximalIdealSheaf A))) →
        IsNormalDomain (AdicCompletion
          (maximalIdeal ((blowUp (maximalIdealSheaf A)).presheaf.stalk x))
          ((blowUp (maximalIdealSheaf A)).presheaf.stalk x)) :=
  ⟨definesRationalSingularity_adicCompletion_maximalIdeal A hNagata hdim hrat h081S hdescend,
    fun x hx =>
      isNormalDomain_adicCompletion_stalk_blowUp_maximalIdeal_of_definesRationalSingularity A
        hNagata hdim hrat h081S hdescend h0B4Z x hx⟩

end AlgebraicGeometry

end
