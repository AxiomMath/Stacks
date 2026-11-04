module

public import StacksFrontier.Algebra.Homology.Embedding.StupidTruncHomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.CanonicalTruncation

/-!
# Strictly perfect approximations with no terms below the degree they approximate from

An `m`-pseudo-coherent complex of `𝒪_X`-modules admits, near every point, an approximation by a
strictly perfect complex in degrees at least `m`. This file upgrades that approximation to one
whose source has no terms below degree `m`, over the same open set: one replaces the strictly
perfect complex `P` by its stupid truncation `σ^{≥m}P` and precomposes with the inclusion
`σ^{≥m}P ⟶ P`, which is an isomorphism on cohomology above `m` and surjective in degree `m` and
therefore preserves both halves of the approximation condition.

The upgrade is what makes the strictly perfect source eligible for Stacks 08C8
(`Stacks.PseudoCoherence.DerivedCharacterization.exists_local_lift_homotopy`), whose hypothesis is
  exactly the vanishing of the
source below the degree from which the target map is an isomorphism on cohomology. Stacks
performs it inside the proof of 08CD as "we may replace `K` by `σ_{≥m+1}K`"; the statement below
is at a general degree, so that reading is the case `m := m + 1`.

## Main results

* `StrictlyPerfect.isStrictlyPerfect_stupidTrunc`: the stupid truncation of a strictly perfect
  complex along any embedding of complex shapes is strictly perfect.
* `AlgebraicGeometry.RingedSpace.exists_isZero_X_below_approximation`: the approximation of an
  `m`-pseudo-coherent complex near a point can be taken with no terms below degree `m`.

## Implementation notes

The truncation does not move the open set, so the second statement is the defining property of
`AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom` with one conjunct added, not a weaker
statement over a smaller neighbourhood. Both halves of its conclusion come from
`HomologicalComplex.homologyMap_comp`: above `m` an isomorphism composed with an isomorphism, and
in degree `m` an epimorphism composed with an epimorphism.

Strict perfection of the truncation needs no hypothesis — every term of the truncation is either
a term of the complex or zero — and the proof uses nothing about the embedding beyond
`stupidTruncXIso`, so it is stated for an arbitrary embedding rather than only for
`ComplexShape.embeddingUpIntGE`.

## References

* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08CD](https://stacks.math.columbia.edu/tag/08CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace StrictlyPerfect

universe u

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- Each term of a stupid truncation is either zero or isomorphic to the same term of the
complex. -/
private theorem isZero_or_nonempty_iso_stupidTrunc_X {ι : Type*} {c : ComplexShape ι}
    (E : CochainComplex (OXMod.{u} X) ℤ) (e : c.Embedding (ComplexShape.up ℤ)) [e.IsRelIff]
    (i : ℤ) : IsZero ((E.stupidTrunc e).X i) ∨ Nonempty ((E.stupidTrunc e).X i ≅ E.X i) := by
  by_cases him : ∃ j, e.f j = i
  · obtain ⟨j, hji⟩ := him
    exact Or.inr ⟨E.stupidTruncXIso e hji⟩
  · exact Or.inl (E.isZero_stupidTrunc_X e i (by simpa using him))

/-- **The stupid truncation of a strictly perfect complex is strictly perfect.** Each of its
terms is either a term of the complex, through `HomologicalComplex.stupidTruncXIso`, or zero, so
both the finiteness of the nonzero terms and the direct-summand condition are inherited. -/
theorem isStrictlyPerfect_stupidTrunc {ι : Type*} {c : ComplexShape ι}
    (E : CochainComplex (OXMod.{u} X) ℤ) (hE : IsStrictlyPerfect E)
    (e : c.Embedding (ComplexShape.up ℤ)) [e.IsRelIff] :
    IsStrictlyPerfect (E.stupidTrunc e) where
  bounded := by
    refine hE.bounded.subset fun i hi hEi => hi ?_
    obtain h | h := isZero_or_nonempty_iso_stupidTrunc_X E e i
    · exact h
    · exact hEi.of_iso h.some
  directSummand i := by
    rcases isZero_or_nonempty_iso_stupidTrunc_X E e i with h | h
    · exact Stacks.Cohomology.PerfectCanonicalTruncation.isDirectSummandOfFiniteFree_of_isZero h
    · exact isDirectSummandOfFiniteFree_of_iso h.some (hE.directSummand i)

end StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

open StrictlyPerfect

universe u

variable {X : RingedSpace.{u, u}}

/-- **An `m`-pseudo-coherent complex is approximated near every point by a strictly perfect
complex with no terms below degree `m`.** The approximation provided by `m`-pseudo-coherence is
composed with the inclusion of the stupid truncation `σ^{≥m}P ⟶ P`, which is an isomorphism on
cohomology above `m` and surjective in degree `m`, so the two conditions on cohomology survive;
the open set is the one `m`-pseudo-coherence already provides. -/
theorem exists_isZero_X_below_approximation
    (E : CochainComplex (OXMod.{u, u} X) ℤ) (m : ℤ)
    (hE : IsPseudoCoherentComplexFrom (X := X) E m) (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧ (∀ j : ℤ, j < m → IsZero (P.X j)) ∧
        ∃ α : P ⟶ restrictComplex E U,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
          Epi (HomologicalComplex.homologyMap α m) := by
  obtain ⟨U, hxU, P, hP, α, hgt, hepi⟩ := hE x
  refine ⟨U, hxU, P.stupidTrunc (ComplexShape.embeddingUpIntGE m),
    isStrictlyPerfect_stupidTrunc P hP _,
    fun j hj => P.isZero_X_stupidTrunc_embeddingUpIntGE m j hj,
    P.ιStupidTrunc (ComplexShape.embeddingUpIntGE m) ≫ α, ?_, ?_⟩
  · intro j hj
    rw [HomologicalComplex.homologyMap_comp]
    have := P.isIso_homologyMap_ιStupidTrunc_embeddingUpIntGE m j hj
    have := hgt j hj
    infer_instance
  · rw [HomologicalComplex.homologyMap_comp]
    exact epi_comp' (P.epi_homologyMap_ιStupidTrunc_embeddingUpIntGE m) hepi

end AlgebraicGeometry.RingedSpace

end
