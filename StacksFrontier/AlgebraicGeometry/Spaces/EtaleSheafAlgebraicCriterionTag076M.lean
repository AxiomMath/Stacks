module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafAlgebraicCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional

/-!
# Stacks 076M: an étale sheaf with an étale presentation is an algebraic space

Let `S` be a scheme contained in a chosen big fppf site `B`. A presheaf of sets on the big fppf
category over `S` which is a sheaf for the chosen *étale* topology, whose diagonal is
representable and which admits a surjective étale atlas by a scheme is an algebraic space over
`S`. This is Stacks 076M, with no further hypothesis.

`StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafAlgebraicCriterion` carries out the whole
comparison of quotients that the source's proof performs, but leaves two things standing in its
statements: the clause `hquot`, that a section of the fppf quotient sheaf of an étale
equivalence relation lifts on a covering sieve of the étale topology, and the instance
assumption that set-valued presheaves on the site admit sheafification. Both are now theorems
of this development, so this file substitutes them and the tag follows.

* `hquot` is obtained from Stacks 02WW. The quotient map `U ⟶ U/R` of an étale equivalence
  relation is surjective and étale after every representable base change —
  `AlgebraicGeometry.Space.quotientMap_surjective_unconditional` and
  `AlgebraicGeometry.Space.quotientMap_etale_unconditional`, which assume nothing beyond the
  relation being an étale equivalence relation — and a map out of a represented presheaf with
  those two properties is locally surjective for the étale topology by
  `AlgebraicGeometry.Space.isLocallySurjective_etaleTopology_of_presheaf`. This is exactly the
  step the source takes: it is because `U ⟶ U/R` is surjective étale that `T ×_{U/R} U → T` is
  an étale covering of any `T` carrying a section of `U/R`.
* `CategoryTheory.HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u)` is
  `AlgebraicGeometry.hasSheafify_bigFppfOver`, the big fppf category over `S` being essentially
  small. It is not an open mathematical assumption but the choice of universe in which the
  quotient presheaf is sheafified, and the conclusion `AlgebraicGeometry.IsAlgebraicSpace` does
  not mention it; it is discharged here so that the statement below has the source's three
  hypotheses and nothing else.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isSheaf_etale`: **Stacks 076M.**

## Implementation notes

The comparison itself is not repeated. The proof is the composite of
`AlgebraicGeometry.Space.isAlgebraicSpace_of_isSheaf_etale_of_isLocallySurjective_quotientMap`,
which is the sharper of the two conditional forms, with the three unconditional results listed
above. In particular the kernel-pair clause, the coequalizer comparison and the universe
bookkeeping around `CategoryTheory.coequalizer_of_surjection` all stay where they are.

## References

* [Stacks Project, Tag 076M](https://stacks.math.columbia.edu/tag/076M)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 076M.** A presheaf of sets on the big fppf category over `S` which is a sheaf for
the chosen étale topology, whose diagonal is representable and which admits a surjective étale
atlas by a scheme is an algebraic space over `S`.

Only the fppf sheaf condition is at issue, and it comes from a comparison with the fppf
quotient sheaf `U/R` of the étale equivalence relation `R = U ×_F U`: the atlas and the
quotient map are both locally surjective for the étale topology and have the same kernel pair,
so `F` and `U/R` are the same coequalizer of `h_R ⇉ h_U` in étale sheaves, and `F` inherits the
fppf sheaf condition from `U/R`. The comparison is
`AlgebraicGeometry.Space.isAlgebraicSpace_of_isSheaf_etale_of_isLocallySurjective_quotientMap`;
the étale-local surjectivity of the quotient map is Stacks 02WW. -/
@[stacks 076M]
theorem isAlgebraicSpace_of_isSheaf_etale (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F)
    (hdiag : yoneda.relativelyRepresentable (diag F))
    (hatlas : ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsAlgebraicSpace B S hS F := by
  let _ : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  refine isAlgebraicSpace_of_isSheaf_etale_of_isLocallySurjective_quotientMap B S hS F hF hdiag
    hatlas fun {R U} s t hj ↦ ?_
  have := hj
  exact isLocallySurjective_etaleTopology_of_presheaf B S hS (quotientMap B S hS s t)
    (quotientMap_surjective_unconditional B S hS s t)
    (quotientMap_etale_unconditional B S hS s t)

end AlgebraicGeometry.Space

end
