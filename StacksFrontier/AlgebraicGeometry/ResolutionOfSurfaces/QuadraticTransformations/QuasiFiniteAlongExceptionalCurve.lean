module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.PullbackVanishingQuasiFinite
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.SquareToTriangle

/-!
# The morphism is quasi-finite along the exceptional curve

This file completes the step of [Stacks, Tag 0C5R] (Resolution of Surfaces, Lemma 54.17.1) that
the other files of this directory build up, and delivers what the next step of the source
consumes.

The situation is the one of `SquareToTriangle.lean`: a morphism `f' : X' ⟶ Y'` locally of finite
type, an exceptional curve of the first kind `E ⊆ X'`, a second one `E' ⊆ Y'` with a compatible
presentation as `𝐏¹_k`, a morphism `g : E ⟶ E'` and an immersion `j : E ⟶ Y'` equal both to
`i ≫ f'` and to `g ≫ i'`. There it was shown that a nonzero conormal comparison map forces
`i^* Ω_{X'/Y'} = 0`. Here that vanishing is converted into quasi-finiteness of `f'` at every
point of `E`, by
`Stacks.UnramifiedAlongImmersion.quasiFiniteAt_of_isZero_pullback_relativeDifferentials`:
Nakayama turns the vanishing of the pullback into the vanishing of the differentials stalk at
each point of `E`, which is unramifiedness there by [Stacks, Tag 02GF], and an unramified point
of a morphism locally of finite type is a quasi-finite point.

In [Stacks, Tag 0C5R] this is what makes item (4) of [Stacks, Tag 0BFP] applicable on `Y'`, which
is the next step of the source's argument.

## Main results

* `Stacks.ResolutionOfSurfaces.quasiFiniteAt_of_exceptionalCurvePair` — **`f'` is quasi-finite at
  every point of the exceptional curve**, given a nonzero conormal comparison map for the square
  of two exceptional curves of the first kind.
* `Stacks.ResolutionOfSurfaces.quasiFiniteAt_of_isZero_pullback_relativeDifferentials_subscheme`
  — the same conversion with the vanishing of `i^* Ω_{X'/Y'}` taken as the hypothesis, for an
  arbitrary closed subscheme of `X'` rather than an exceptional curve.

## What is and is not proved

Proved: the conversion of the vanishing into quasi-finiteness, and its combination with the
results of the other files of this directory.

Carried, exactly as in the other files of this directory:
`Stacks.ResolutionOfSurfaces.ConormalSequenceSecondArrow`, the second arrow of
[Stacks, Tag 067L] together with the two clauses of that tag which this library does not prove —
that the composite of the two arrows of the conormal sequence vanishes and that the second arrow
is an epimorphism. It is quantified over every triangle of immersions of schemes and mentions
none of the objects of the conclusion, so it is in particular not a disguised form of it.

**No `@[stacks 0C5R]` attribute is placed here**: this is a step of the proof of that tag, not a
clause of its statement. The contradiction that the source draws from quasi-finiteness —
[Stacks, Tag 0BFP] item (4) on `Y'`, then item (2) on `Y`, then the factorisation of
[Stacks, Tag 0C5J] — is not carried out here.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
* [Stacks Project, Tag 02V5](https://stacks.math.columbia.edu/tag/02V5)
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace Stacks.ResolutionOfSurfaces

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **From the vanishing of `i^* Ω_{X'/Y'}` to quasi-finiteness along a closed subscheme.** For a
closed subscheme `D ⊆ X'` and a morphism `f' : X' ⟶ Y'` locally of finite type, vanishing of the
pullback of the relative differentials to `D` makes `f'` quasi-finite at every point of `D`. -/
public theorem quasiFiniteAt_of_isZero_pullback_relativeDifferentials_subscheme
    {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') [LocallyOfFiniteType f'] (D : X'.IdealSheafData)
    (hzero : IsZero ((Scheme.Modules.pullback D.subschemeι).obj
      (Scheme.Hom.relativeDifferentials f')))
    (z : D.subscheme) : f'.QuasiFiniteAt (D.subschemeι.base z) :=
  Stacks.UnramifiedAlongImmersion.quasiFiniteAt_of_isZero_pullback_relativeDifferentials
    D.subschemeι f' hzero z

/-- **`f'` is quasi-finite at every point of the exceptional curve.** Let `E ⊆ X'` and `E' ⊆ Y'`
be exceptional curves of the first kind with compatible presentations `e : 𝐏¹_k ≅ E` and
`e' : 𝐏¹_k ≅ E'`, let `g : E ⟶ E'` satisfy `e ≫ g = e'`, let `j : E ⟶ Y'` be an immersion equal
to `g ≫ i'` and to `i ≫ f'`, and suppose the conormal comparison map
`g^* 𝒞_{E'/Y'} ⟶ 𝒞_{E/X'}` of [Stacks, Tag 01R4] is nonzero. If `f'` is locally of finite type
then it is quasi-finite at every point of `E`.

This is the step of [Stacks, Tag 0C5R] that makes item (4) of [Stacks, Tag 0BFP] applicable: the
conormal comparison is an isomorphism because both modules are invertible of degree one on
`𝐏¹_k`, so `i^* Ω_{X'/Y'} = 0`, so `f'` is unramified along `E`, so it is quasi-finite there. -/
public theorem quasiFiniteAt_of_exceptionalCurvePair (k : Type u) [Field k]
    (hsec : ConormalSequenceSecondArrow.{u})
    {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') [LocallyOfFiniteType f']
    {D : X'.IdealSheafData} {D' : Y'.IdealSheafData}
    {e : projectiveLineProj k ≅ D.subscheme} {e' : projectiveLineProj k ≅ D'.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e) (hE' : D'.IsExceptionalCurveOfFirstKind k e')
    (g : D.subscheme ⟶ D'.subscheme) (he : e.hom ≫ g = e'.hom)
    (j : D.subscheme ⟶ Y') [IsImmersion j] (hj : g ≫ D'.subschemeι = j)
    (h : D.subschemeι ≫ f' = j)
    (hne : Stacks.Immersion.immersionConormalSheafMap D.subschemeι D'.subschemeι g f'
      (Stacks.Immersion.toShHom_square (h.trans hj.symm)) ≠ 0)
    (z : D.subscheme) : f'.QuasiFiniteAt (D.subschemeι.base z) :=
  quasiFiniteAt_of_isZero_pullback_relativeDifferentials_subscheme f' D
    (isZero_pullback_relativeDifferentials_of_exceptionalCurvePair k hsec f' hE hE' g he j hj h
      hne) z

end Stacks.ResolutionOfSurfaces

end
