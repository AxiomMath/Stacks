module

public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.CohomologyAgainstPerfect
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.PseudoCoherentByPerfectTwists
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeAbsolute
public import StacksCore.Tactic.StacksAttribute

/-!
# The object of Grothendieck's existence theorem is pseudo-coherent

In Situation [Stacks, Tag 0DIB] let `K = DQ_X(R lim Kₙ)` be the object of [Stacks, Tag 0DIC]. Then
`K` is pseudo-coherent on `X` ([Stacks, Tag 0DIE]).

## The proof

The source's. By [Stacks, Tag 0DID] the complex `RΓ(X, K ⊗^𝐋 E)` is pseudo-coherent in `D(A)` for
every perfect object `E` of `D(𝒪_X)`. As `K` lies in `D_QCoh(𝒪_X)` ([Stacks, Tag 0DIC]),
[Stacks, Tag 0CSH] extends this to every pseudo-coherent `E`, and then [Stacks, Tag 0CSL] makes
`K` pseudo-coherent relative to `A`, the scheme `X` being separated and of finite presentation
over `A`; these two steps are assembled in the library as [Stacks, Tag 0GES]
(`AlgebraicGeometry.isPseudoCoherent_of_derivedGlobalSectionsOver_tensor_isPerfect`). Since `X`
is flat and of finite presentation over `A`, relative pseudo-coherence is pseudo-coherence on `X`
([Stacks, Tag 09UU], in its form for schemes, [Stacks, Tag 0DII]:
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherent_iff_of_flat_of_locallyOfFinitePresentation`).

## Main results

* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.isPseudoCoherent_limitObject`:
  **[Stacks, Tag 0DIE]**.

## Implementation notes

`K` is `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.limitObject`, the object
of [Stacks, Tag 0DIC] at the standard model of `D(𝒪_X)`, which is the model at which the objects
`Kₙ` of the situation are given; pseudo-coherence is the sheaf-level notion
`AlgebraicGeometry.RingedSpace.IsPseudoCoherent` of [Stacks, Tag 08CB]. The derived categories of
the different spellings of `𝒪_X`-modules met in the proof are each fixed to the standard model by
a `letI`. [Stacks, Tag 0DID] is stated for the derived tensor product
`AlgebraicGeometry.LerayOver.tensor` of the projection formula and [Stacks, Tag 0GES] for
`Stacks.SheafOfModules.derivedTensor`, with the factors in the other order; the two are
identified by `AlgebraicGeometry.RingedSite.derivedTensorObjIso` and
`AlgebraicGeometry.derivedTensorBraidingIso`.

## References

* [Stacks Project, Tag 0DIE](https://stacks.math.columbia.edu/tag/0DIE)
* [Stacks Project, Tag 0DID](https://stacks.math.columbia.edu/tag/0DID)
* [Stacks Project, Tag 0DIC](https://stacks.math.columbia.edu/tag/0DIC)
* [Stacks Project, Tag 0CSH](https://stacks.math.columbia.edu/tag/0CSH)
* [Stacks Project, Tag 0CSL](https://stacks.math.columbia.edu/tag/0CSL)
* [Stacks Project, Tag 0GES](https://stacks.math.columbia.edu/tag/0GES)
* [Stacks Project, Tag 09UU](https://stacks.math.columbia.edu/tag/09UU)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

/-- **Stacks Project, Tag 0DIE.** In Situation [Stacks, Tag 0DIB] let `K` be as in
[Stacks, Tag 0DIC]. Then `K` is pseudo-coherent on `X`.

Here `K = DQ_X(R lim Kₙ)` is
`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.limitObject`, an object of
`D(𝒪_X)` at the model at which the `Kₙ` are given. By [Stacks, Tag 0DID] (its first assertion,
`DerivedExistenceSituation.isPseudoCoherent_cohomology_and_isIso`)
`RΓ(X, K ⊗^𝐋 E)` is pseudo-coherent for every perfect `E`; [Stacks, Tag 0GES] (which is
[Stacks, Tags 0CSH and 0CSL] together, `X` being separated and of finite presentation over `A`
and `K` lying in `D_QCoh(𝒪_X)` by [Stacks, Tag 0DIC]) makes `K` pseudo-coherent relative to `A`,
and [Stacks, Tag 09UU] (for schemes, [Stacks, Tag 0DII]) turns that into pseudo-coherence on `X`,
`X` being flat and of finite presentation over `A`. -/
@[stacks 0DIE]
theorem isPseudoCoherent_limitObject (S : DerivedExistenceSituation.{u}) :
    letI := HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u, u} S.X.left.toRingedSpace)
    RingedSpace.IsPseudoCoherent (X := S.X.left.toRingedSpace) S.limitObject := by
  let := HasDerivedCategory.standard (StructureSheafModules S.X.left.sheaf)
  let := HasDerivedCategory.standard S.X.left.Modules
  let := HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u, u} S.X.left.toRingedSpace)
  let := HasDerivedCategory.standard (RingedSite.Modules (ringedSite S.X.left.sheaf))
  let := HasDerivedCategory.standard
    (ModuleCat.{u} (CategoryTheory.Limits.limit S.system : CommRingCat.{u}))
  have := S.proper
  have := S.flat
  have := S.finitePresentation.locallyOfFinitePresentation
  refine (Scheme.Hom.isPseudoCoherent_iff_of_flat_of_locallyOfFinitePresentation S.X.hom
    S.limitObject).1 ?_
  refine isPseudoCoherent_of_derivedGlobalSectionsOver_tensor_isPerfect S.X.hom S.limitObject
    S.isQuasicoherent_homology_limitObject fun E hE => ?_
  have h := (S.isPseudoCoherent_cohomology_and_isIso E hE).1.of_iso
    ((derivedGlobalSectionsOver S.X.hom).mapIso
      (RingedSite.derivedTensorObjIso (ringedSite S.X.left.sheaf) _ E)).symm
  exact h.of_iso ((derivedGlobalSectionsOver S.X.hom).mapIso
    (derivedTensorBraidingIso S.limitObject E))

end AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

end
