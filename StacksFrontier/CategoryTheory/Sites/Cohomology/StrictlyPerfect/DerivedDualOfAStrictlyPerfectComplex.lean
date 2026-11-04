module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexIntoASingleComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
import StacksCore.Tactic.StacksAttribute

/-!
# The derived dual of a strictly perfect complex, as an ordinary Hom complex

Let `(𝒞, 𝒪)` be a ringed site and let `E` be a strictly perfect complex of `𝒪`-modules
([Stacks, Tag 08FL]). The derived dual `E^∨ = R𝑆heafHom_𝒪(E, 𝒪)` of [Stacks, Tag 08JD],
`AlgebraicGeometry.RingedSite.derivedDual`, is then represented by the *ordinary* internal Hom
complex `𝑆heafHom_𝒪(E, 𝒪[0])` of [Stacks, Tag 0A8Z]. This file packages that identification as
an isomorphism of `D(𝒪)`.

The content is entirely [Stacks, Tag 08JH], which the library already has as the invertibility of
a comparison *morphism*,
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso`. What was missing is the
isomorphism itself at the structure sheaf, where the comparison's target is the derived dual; it
is used anonymously inside the proof of [Stacks, Tag 08JJ] in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals`, at the universe pin
`RingedSite.{0, 0, 0}` of the perfectness cluster there, and so is unavailable to a consumer at
the diagonal universes of the derived-internal-Hom cluster.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedDualIsoSheafHomComplex`: `E^∨ ≅ 𝑆heafHom_𝒪(E, 𝒪[0])` in
  `D(𝒪)`, for `E` bounded with termwise finite-free-summand terms.
* `AlgebraicGeometry.RingedSite.derivedDualIsoSheafHomComplexOfIsStrictlyPerfect`: the same under
  the hypothesis `IsStrictlyPerfect` itself.

## Implementation notes

The strict perfectness of `E` is spelled, as in
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso`, by bounded support together
with `AlgebraicGeometry.RingedSite.IsFiniteFreeSummand` of every term; the variant phrased by
`IsStrictlyPerfect` passes through the bridge
`AlgebraicGeometry.RingedSite.IsDirectSummandOfFiniteFree.isFiniteFreeSummand`, which is why it
carries one further sheaf-composition hypothesis.

**What this does *not* give.** `AlgebraicGeometry.RingedSite.sheafHomComplex` is `@[no_expose]`:
its terms are named by
`AlgebraicGeometry.RingedSite.homStructureSheafDegreeIso` — the degree-`n` term is
`𝑆heafHom_𝒪(E^{-n}, 𝒪)` — but its *differentials* are not available to a consumer. So this
isomorphism identifies the derived dual with a complex whose terms are the duals of the terms of
`E` in the reflected degrees, and no more; it does not identify that complex with any
independently constructed termwise dual, such as the `dualComplex` of [Stacks, Tag 0FPR] in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.DualComplexOfModules`. Matching the two
differentials is exactly what the dual of a Koszul complex would need, and it is not done
anywhere in this library.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **[Stacks, Tag 08JH] at the structure sheaf, as an isomorphism.** For a bounded complex `E`
of `𝒪`-modules each of whose terms is a summand of a finite free `𝒪`-module, the derived dual
`E^∨ = R𝑆heafHom_𝒪(E, 𝒪)` of [Stacks, Tag 08JD] is represented by the ordinary internal Hom
complex `𝑆heafHom_𝒪(E, 𝒪[0])` of [Stacks, Tag 0A8Z].

The isomorphism is the comparison morphism
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`, which [Stacks, Tag 08JH]
(`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso`) says is invertible, at the
internal-Hom datum `AlgebraicGeometry.RingedSite.derivedInternalHomOfBifunctor` carried by the
explicit bifunctor over which `derivedDual` is defined. -/
def derivedDualIsoSheafHomComplex
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i : ℤ, IsFiniteFreeSummand X (E.X i)) :
    derivedDual X (DerivedCategory.Q.obj E) ≅
      DerivedCategory.Q.obj (sheafHomComplex X E (structureSheafComplex X)).obj :=
  letI := strictlyPerfectHomComparison_isIso X (derivedInternalHomOfBifunctor X) E
    (structureSheafComplex X) hbdd hterm
  (asIso (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) E
    (structureSheafComplex X))).symm

/-- **[Stacks, Tag 08JH] at the structure sheaf, under the hypothesis `IsStrictlyPerfect`.** For
`E` strictly perfect in the sense of [Stacks, Tag 08FL] the derived dual `E^∨` is represented by
the ordinary internal Hom complex `𝑆heafHom_𝒪(E, 𝒪[0])`. -/
def derivedDualIsoSheafHomComplexOfIsStrictlyPerfect
    [HasWeakSheafify X.J AddCommGrpCat.{u}]
    [X.J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) E) :
    derivedDual X (DerivedCategory.Q.obj E) ≅
      DerivedCategory.Q.obj (sheafHomComplex X E (structureSheafComplex X)).obj :=
  derivedDualIsoSheafHomComplex X E hE.bounded
    fun i ↦ IsDirectSummandOfFiniteFree.isFiniteFreeSummand X (hE.termDirectSummand i)

end AlgebraicGeometry.RingedSite

end
