module

public import StacksFrontier.RingTheory.FormallySmooth.Presentation

/-!
# Formal smoothness of a field is the vanishing of `H¹` of its cotangent complex

A field `K` which is an algebra over a commutative ring `R` is formally smooth over `R` if and only
if `H¹(L_{K/R}) = 0`, that is, if and only if `Algebra.H1Cotangent R K` is a subsingleton. For a
general `R`-algebra `S`, formal smoothness is equivalent to the conjunction of projectivity of
`Ω[S⁄R]` as an `S`-module and the vanishing of `H¹(L_{S/R})`; over a field `K` the first condition
holds automatically, since `Ω[K⁄R]` is a `K`-vector space.

## Main results

* `Stacks.FormallySmooth.CotangentVanishing.solution`: a field `K` is formally smooth over `R` if
  and only if `H¹(L_{K/R}) = 0`.
* `Algebra.formallySmooth_iff_subsingleton_h1Cotangent`: the same statement.

## References

* [StacksProject 031Z](https://stacks.math.columbia.edu/tag/031Z)
* [StacksProject 031J](https://stacks.math.columbia.edu/tag/031J)

## Tags

formally smooth, field extension, cotangent complex, naive cotangent complex, Kähler differentials
-/

@[expose] public section

@[expose] public section

namespace Stacks.FormallySmooth.CotangentVanishing

/-- A field `K` which is an algebra over a commutative ring `R` is formally smooth over `R` if and
only if `H¹(L_{K/R}) = 0`. -/
public theorem solution
    (R K : Type*) [CommRing R] [Field K] [Algebra R K] :
    Algebra.FormallySmooth R K ↔ Subsingleton (Algebra.H1Cotangent R K) :=
  ((Algebra.FormallySmooth.tfae_of_surjective
      (Algebra.Generators.self R K).algebraMap_surjective).out 1 4).trans
    (and_iff_right Module.Projective.of_free)

end Stacks.FormallySmooth.CotangentVanishing

end

@[expose] public section

/-- A field `K` which is an algebra over a commutative ring `R` is formally smooth over `R` if and
only if `H¹(L_{K/R}) = 0`. -/
@[stacks 031Z "Stated for a field `K` over an arbitrary commutative base ring `R`; the source's
base field `k` is the case `R := k`, and no hypothesis on the base is used. `H_1(L_{K/k}) = 0` is
`Subsingleton (Algebra.H1Cotangent R K)`. See the module docstring."]
public theorem Algebra.formallySmooth_iff_subsingleton_h1Cotangent
    (R K : Type*) [CommRing R] [Field K] [Algebra R K] :
    Algebra.FormallySmooth R K ↔ Subsingleton (Algebra.H1Cotangent R K) :=
  Stacks.FormallySmooth.CotangentVanishing.solution R K

end
