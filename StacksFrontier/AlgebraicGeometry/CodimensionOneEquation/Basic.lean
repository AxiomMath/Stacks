module

public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.EmbeddedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.CodimensionOneDivisor.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Ideal.UFD

/-!
# Equations for codimension-one subschemes of projective space

Tag 0BXL asserts that a closed subscheme `Z` of projective space over a Noetherian unique
factorization domain `R`, having no embedded points and with every irreducible component of
codimension one, has a principal homogeneous ideal.

This file states that assertion over the library's own vocabulary for its two dependencies —
the homogeneous ideal of a closed subscheme (Tag 0BXK) and the absence of embedded points
(Tag 05AK) — and proves it modulo a single ring-theoretic input, carried as the hypothesis
`hassoc` of each theorem below.

## Main results

* `isPrincipal_of_codimension_one_of_associatedPrimes_height_eq_one`: the statement of Tag
  0BXL with one added hypothesis, that every associated prime of the homogeneous ideal of `Z`
  has height one.
* `isPrincipal_of_codimension_one_of_isUnmixed_of_minimalPrimes_height_eq_one`: the same with
  that hypothesis split into the two halves the geometry is meant to supply, namely that every
  associated prime of the ideal is minimal over it (no embedded primes) and that every minimal
  prime has height one (components of codimension one).

## Route

The polynomial `Proj` model of projective space (Tag 01NF) is used, so that the canonical
homogeneous ideal of Tag 0BXK applies to `i` directly. The algebraic engine is
`Stacks.RingTheory.PrincipalCodimOne.isPrincipal_of_forall_associatedPrimes_height_eq_one`: in
a Noetherian unique factorization domain, an ideal all of whose associated primes have height
one is principal, which specializes Mathlib's
`UniqueFactorizationMonoid.isPrincipal_of_height_eq_one` from a prime to an unmixed ideal by a
primary decomposition. The three ring hypotheses pass from `R` to
`MvPolynomial (Fin (n + 1)) R`, which is what makes that engine applicable to a projective
coordinate ring at all.

The notion of associated prime used is `Submodule.associatedPrimes I`, the primes of the form
`√(I : x)`, which is the set of associated primes of the quotient by `I` and hence the
algebraic counterpart of the associated points of `Z`.

## What is not done

The hypothesis `hassoc` is the entire geometric content of Tag 0BXL and is not proved here;
the tag's two geometric hypotheses are what should imply it, and are accordingly not consumed
by these proofs. Written out, the missing statement is

```
∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
  (n : ℕ) {Z : Scheme.{u}}
  (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsClosedImmersion i],
  HasNoEmbeddedPoints Z →
  (∀ W ∈ irreducibleComponents Z, ∀ x : Z, IsGenericPoint x W →
    codimension (IrreducibleCloseds.closureSingleton (i x)) = 1) →
  ∀ p ∈ Submodule.associatedPrimes
      (idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i),
    p.height = 1
```

Deriving it needs three comparisons. The third is supplied by
`Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_one_iff`: the
codimension of the closure of a point of a scheme is the Krull dimension of its local ring.
The other two are absent from both Mathlib and this repository, as searched:

* the correspondence between closed subschemes of `Proj 𝒮` and *saturated* homogeneous ideals
  of `𝒮`, which is the unproved half of Tag 0BXK — its `"saturated ideals"` clause,
  `isIdealOfClosedSubscheme_iff_saturated`. Without it nothing
  relates `idealOfClosedSubscheme 𝒮 i` to the topology of `Z`, so neither the minimal primes
  nor their heights can be read off the components of `Z`. Mathlib has only the topological
  Galois connection `ProjectiveSpectrum.gc_homogeneousIdeal` between homogeneous ideals and
  closed subsets of `ProjectiveSpectrum`, which says nothing about closed subschemes;
* the identification of the associated points of a scheme with the associated primes of its
  rings of functions. Nothing relates
  `Stacks.AlgebraicGeometry.AssociatedPointsMono.IsAssociatedPoint` to any ring-level notion of
  associated prime, so `HasNoEmbeddedPoints` cannot yet be turned into the unmixedness of the
  ideal.

Also not done is the refinement that the generator may be taken homogeneous, the form in which
Tag 0BXL is usually read as "cut out by one equation". The conclusion stated here is
`IsPrincipal`. The upgrade now has its first ingredient, since
`idealOfClosedSubscheme_isHomogeneous` is available, but still needs the additivity of lowest
and highest degree in a graded domain, which this repository does not have.

## References

* [Stacks Project, Tag 0BXL](https://stacks.math.columbia.edu/tag/0BXL)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 05AK](https://stacks.math.columbia.edu/tag/05AK)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.EmbeddedPoints
open Stacks.AlgebraicGeometry.IdealOfClosedSubscheme

namespace Stacks.AlgebraicGeometry.CodimensionOneEquation

universe u

-- The grading of a polynomial ring by homogeneous degree is a definition in Mathlib rather
-- than an instance, so it is supplied here exactly as Tag 0BXL's own statement supplies it.
attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Stacks 0BXL, with one added hypothesis.** A closed subscheme of projective space over a
Noetherian unique factorization domain, with no embedded points and with every irreducible
component of codimension one, has a principal homogeneous ideal — *provided* every associated
prime of that ideal has height one.

`hassoc` is the whole geometric content of the tag and is not proved; see the "what is not
done" section of the module docstring for its exact statement and for what is missing. The
tag's two geometric hypotheses are therefore not used by this proof and appear with underscored
names. -/
public theorem isPrincipal_of_codimension_one_of_associatedPrimes_height_eq_one
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [UniqueFactorizationMonoid R] (n : ℕ) {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion i] (_hno : HasNoEmbeddedPoints Z)
    (_hcodim : ∀ W ∈ irreducibleComponents Z, ∀ x : Z,
      IsGenericPoint x W → codimension (IrreducibleCloseds.closureSingleton (i x)) = 1)
    (hassoc : ∀ p ∈ Submodule.associatedPrimes
        (idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i),
      p.height = 1) :
    (idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i).IsPrincipal :=
  Stacks.RingTheory.PrincipalCodimOne.isPrincipal_of_forall_associatedPrimes_height_eq_one
    hassoc

/-- The same conclusion with the added hypothesis split into the two halves the geometry is
meant to supply: that every associated prime of the ideal is minimal over it, which is the
ring-theoretic reading of "no embedded points", and that every minimal prime has height one,
which is the reading of "every irreducible component has codimension one". -/
public theorem isPrincipal_of_codimension_one_of_isUnmixed_of_minimalPrimes_height_eq_one
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [UniqueFactorizationMonoid R] (n : ℕ) {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion i] (_hno : HasNoEmbeddedPoints Z)
    (_hcodim : ∀ W ∈ irreducibleComponents Z, ∀ x : Z,
      IsGenericPoint x W → codimension (IrreducibleCloseds.closureSingleton (i x)) = 1)
    (hunmixed : ∀ p ∈ Submodule.associatedPrimes
        (idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i),
      p ∈ (idealOfClosedSubscheme
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i).minimalPrimes)
    (hheight : ∀ p ∈ (idealOfClosedSubscheme
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i).minimalPrimes, p.height = 1) :
    (idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i).IsPrincipal :=
  Stacks.RingTheory.PrincipalCodimOne.isPrincipal_of_forall_associatedPrimes_height_eq_one
    fun p hp => hheight p (hunmixed p hp)

/-- The homogeneous ideal of Tag 0BXL is homogeneous for the grading of the polynomial ring by
degree, so a generator produced by the theorems above generates a homogeneous ideal. This is
the first ingredient of the usual reading of the tag, that `Z` is cut out by one *homogeneous*
equation. -/
public theorem idealOfClosedSubscheme_isHomogeneous_mvPolynomial
    (R : Type u) [CommRing R] (n : ℕ) {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion i] :
    (idealOfClosedSubscheme
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) :=
  idealOfClosedSubscheme_isHomogeneous _ i

end Stacks.AlgebraicGeometry.CodimensionOneEquation

end
