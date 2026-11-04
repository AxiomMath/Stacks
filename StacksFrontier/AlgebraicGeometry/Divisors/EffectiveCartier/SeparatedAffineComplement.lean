module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.AffineComplement

/-!
# The complement of a dense affine open in a separated Noetherian scheme

Let `X` be a Noetherian separated scheme and let `U ⊆ X` be a dense affine open.  If `𝒪_{X,x}`
is a unique factorization domain for every `x ∈ X ∖ U`, then there is an effective Cartier
divisor `D ⊆ X` with `U = X ∖ D`.

## Main results

* `AlgebraicGeometry.exists_effectiveCartierDivisor_compl_affineOpen_of_isSeparated`:
  **Stacks Tag 0BCW.**
* `AlgebraicGeometry.exists_effectiveCartierDivisor_compl_affineOpen_of_preirreducible`: on an
  irreducible such scheme every nonempty affine open is the complement of an effective Cartier
  divisor, density being automatic.

## The argument

A separated scheme has affine diagonal: its structure morphism to the terminal scheme is
separated, the diagonal of a separated morphism is a closed immersion, and a closed immersion is
affine — the three steps recorded for Tag 0BDX in
`StacksFrontier/AlgebraicGeometry/Cohomology/Coherent/AffineDiagonal.lean`.  The statement for a
scheme with affine diagonal is Tag 0EGJ,
`AlgebraicGeometry.exists_effectiveCartierDivisor_compl_affineOpen`.  The source deduces that
tag from this one by covering `X` with affine opens, on each of which the open is affine because
the diagonal is; here the implication runs the other way, affineness of the diagonal being the
weaker hypothesis.

The support of the divisor is `X ∖ U` on the nose, so the conclusion `U = X ∖ D` of the source is
the complement of that equality.

## References

* [Stacks Project, Tag 0BCW](https://stacks.math.columbia.edu/tag/0BCW)
* [Stacks Project, Tag 0EGJ](https://stacks.math.columbia.edu/tag/0EGJ)
* [Stacks Project, Tag 0BDX](https://stacks.math.columbia.edu/tag/0BDX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0BCW.** Let `X` be a Noetherian separated scheme and `U ⊆ X` a dense
affine open whose complement meets only points with factorial local rings.  Then there is an
effective Cartier divisor `D ⊆ X` with `U = X ∖ D`. -/
@[stacks 0BCW]
theorem exists_effectiveCartierDivisor_compl_affineOpen_of_isSeparated
    (X : Scheme.{u}) [IsNoetherian X] [Scheme.IsSeparated X]
    (U : X.Opens) (hU : IsAffineOpen U) (hdense : Dense (U : Set X))
    (hUFD : ∀ x : X, x ∉ U → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ I : X.IdealSheafData,
      IsEffectiveCartierDivisor I ∧ (U : Set X) = (I.support : Set X)ᶜ := by
  obtain ⟨I, hI, hsupp⟩ :=
    exists_effectiveCartierDivisor_compl_affineOpen X U hU hdense hUFD
  exact ⟨I, hI, by rw [hsupp, compl_compl]⟩

/-- On an irreducible Noetherian separated scheme with factorial local rings every nonempty
affine open is the complement of an effective Cartier divisor: a nonempty open subset of an
irreducible space is dense, so no density hypothesis is needed. -/
theorem exists_effectiveCartierDivisor_compl_affineOpen_of_preirreducible
    (X : Scheme.{u}) [IsNoetherian X] [Scheme.IsSeparated X] [PreirreducibleSpace X]
    (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty)
    (hUFD : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ I : X.IdealSheafData,
      IsEffectiveCartierDivisor I ∧ (U : Set X) = (I.support : Set X)ᶜ :=
  exists_effectiveCartierDivisor_compl_affineOpen_of_isSeparated X U hU (U.2.dense hne)
    fun x _ => hUFD x

end AlgebraicGeometry

end
