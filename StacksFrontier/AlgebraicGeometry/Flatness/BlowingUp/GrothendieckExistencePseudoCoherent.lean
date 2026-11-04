module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistencePerfectTensor
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceProperSupport
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.PseudoCoherentByPerfectTwists
public import StacksFrontier.Homology.Perfect.Saturation

/-!
# The derived limit of Situation 0CTC is pseudo-coherent relative to the base

In Situation [Stacks, Tag 0CTC], let
`K = R lim_{D_QCoh(𝒪_X)} (iₙ,* ℱₙ) = DQ_X(R lim_{D(𝒪_X)} iₙ,* ℱₙ)` be the object of
[Stacks, Tag 0CTD]. Then `K` is pseudo-coherent relative to `A = lim Aₙ` ([Stacks, Tag 0CTF]).

## Main results

* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.DerivedLimitQCoh.isPseudoCoherent`:
  [Stacks, Tag 0CTF].

## Implementation notes

`K` is identified by
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.DerivedLimitQCoh`: a derived limit `L`
of the system in `D(𝒪_X)` and a universal arrow `K ⟶ L` from `D_QCoh(𝒪_X)`, which pins `K` down as
`DQ_X(L)` up to unique isomorphism; so the statement, quantified over that data, is about *the*
`K` of Tag 0CTD.

The derived category of `𝒪_X`-modules is `HasDerivedCategory.standard`, scoped to the one
declaration below. This is forced: relative pseudo-coherence
(`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherent`, [Stacks, Tag 09UI]), [Stacks, Tag 0CSH],
[Stacks, Tag 0CSL] and [Stacks, Tag 0GES] are all defined or stated only at that model.

The hypothesis `LocallyOfFiniteType` that the definition of relative pseudo-coherence carries is
supplied from the finite presentation of `X` over `A` recorded in the situation, through the
instance `ExistenceSituation.instLocallyOfFinitePresentationXHom`.

## References

* [Stacks Project, Tag 0CTF](https://stacks.math.columbia.edu/tag/0CTF)
* [Stacks Project, Tag 0CTC](https://stacks.math.columbia.edu/tag/0CTC)
* [Stacks Project, Tag 0CTD](https://stacks.math.columbia.edu/tag/0CTD)
* [Stacks Project, Tag 0CTE](https://stacks.math.columbia.edu/tag/0CTE)
* [Stacks Project, Tag 0CSH](https://stacks.math.columbia.edu/tag/0CSH)
* [Stacks Project, Tag 0CSL](https://stacks.math.columbia.edu/tag/0CSL)
* [Stacks Project, Tag 0GES](https://stacks.math.columbia.edu/tag/0GES)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

variable {S : ExistenceSituation.{u}}

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 0CTF].** In Situation [Stacks, Tag 0CTC], let `K` be as in
[Stacks, Tag 0CTD], i.e. `K = DQ_X(R lim_{D(𝒪_X)} iₙ,* ℱₙ)`. Then `K` is pseudo-coherent relative
to `A = lim Aₙ`: relatively pseudo-coherent ([Stacks, Tag 09UI]) for the structure morphism
`X ⟶ Spec A`. Stated at the standard model. -/
@[stacks 0CTF]
theorem DerivedLimitQCoh.isPseudoCoherent (d : S.DerivedLimitQCoh) :
    S.X.hom.IsPseudoCoherent d.K :=
  have : QuasiCompact S.X.hom := S.finitePresentation.2.1
  have : IsSeparated S.X.hom := S.separated
  isPseudoCoherent_of_derivedGlobalSectionsOver_tensor_isPerfect S.X.hom d.K d.quasicoherent
    fun E hE => (StacksDraft.Perfect.isPseudoCoherent_of_isPerfect _
      (DerivedLimitQCoh.isPerfect_globalSectionsTensor S d E hE)).of_iso
      ((derivedGlobalSectionsOver S.X.hom).mapIso
        (RingedSite.derivedTensorObjIso (Stacks.SheafOfModules.ringedSite S.X.left.sheaf) E d.K ≪≫
          (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
            S.X.left.sheaf).braidingIso
            (Stacks.RingedSpace.toRingedSite S.X.left.toRingedSpace) E d.K)).symm

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

end
