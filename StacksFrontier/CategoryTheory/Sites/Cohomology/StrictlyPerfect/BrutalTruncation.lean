module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TruncatingApproximations
import StacksCore.Tactic.StacksAttribute

/-!
# The brutal truncation of a strictly perfect complex is strictly perfect

Let `(C, O)` be a ringed site and let `e` be an embedding of complex shapes into
`ComplexShape.up ℤ`. Mathlib's brutal truncation `HomologicalComplex.stupidTrunc K e` keeps the
terms of `K` in the image of `e` and replaces the others by zero, so every one of its terms is
either a term of `K` or a zero object. Both clauses of strict perfection (Stacks 08FL) are
therefore inherited: only finitely many terms are nonzero, and each is a direct summand of a
finite free `O`-module.

The use this is made for is the embedding `ComplexShape.embeddingUpIntGE n`, whose brutal
truncation `σ^{≥n}P` is the complex the proof of Stacks 08G7 substitutes for a strictly perfect
approximation `P` in order to make it concentrated in degrees `≥ n`: the hypotheses of
`Stacks.SheafOfModules.DerivedTensorProduct.exists_iso_truncGE_and_isFlat_opcycles` ask for
`CochainComplex.IsStrictlyGE`, which `P` itself does not satisfy. That `σ^{≥n}P` is
`CochainComplex.IsStrictlyGE n` and stays `CochainComplex.IsStrictlyLE b` is already in Mathlib,
as instances; what is not is that it stays strictly perfect, which is this file.

## Main results

* `Stacks.SheafOfModules.isStrictlyPerfect_stupidTrunc`: the brutal truncation of a strictly
  perfect complex of `O`-modules along any embedding of complex shapes is strictly perfect.

## Implementation notes

The statement is about an arbitrary embedding `e` rather than about
`ComplexShape.embeddingUpIntGE n`: the argument uses nothing about `e` beyond the dichotomy
"`i` is in the image of `e`, or it is not", which is exactly what
`HomologicalComplex.stupidTruncXIso` and `HomologicalComplex.isZero_stupidTrunc_X` record.

The sections of the structure sheaf and of the modules live in `Type`, as everywhere in the
ringed-site perfectness development; see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/TruncatingApproximations.lean`.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{0})
  [HasSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- **The brutal truncation of a strictly perfect complex is strictly perfect.** Each term of
`K.stupidTrunc e` is either the corresponding term of `K`, when its degree is in the image of
`e`, or a zero object; so the nonzero terms are among those of `K` and each term is a direct
summand of a finite free `O`-module.

With `e = ComplexShape.embeddingUpIntGE n` this is what lets a strictly perfect approximation be
replaced by one concentrated in degrees `≥ n` in the proof of Stacks 08G7. -/
theorem isStrictlyPerfect_stupidTrunc {ι : Type*} {c : ComplexShape ι}
    (e : c.Embedding (ComplexShape.up ℤ)) [e.IsRelIff]
    {P : CochainComplex (SheafOfModules.{0} R) ℤ} (hP : IsStrictlyPerfect R P) :
    IsStrictlyPerfect R (P.stupidTrunc e) where
  bounded := by
    refine hP.bounded.subset ?_
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi ⊢
    intro hz
    refine hi ?_
    by_cases h : ∃ j, e.f j = i
    · obtain ⟨j, hj⟩ := h
      exact hz.of_iso (P.stupidTruncXIso e hj)
    · exact P.isZero_stupidTrunc_X e i (by simpa using h)
  termDirectSummand i := by
    by_cases h : ∃ j, e.f j = i
    · obtain ⟨j, hj⟩ := h
      exact IsDirectSummandOfFiniteFree.of_iso R (P.stupidTruncXIso e hj)
        (hP.termDirectSummand i)
    · exact IsDirectSummandOfFiniteFree.of_isZero R
        (P.isZero_stupidTrunc_X e i (by simpa using h))

end Stacks.SheafOfModules

end
