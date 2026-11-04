module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalNatureAnySite
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian

/-!
# Perfectness is local on the small étale site of an algebraic space

Let `F` be an algebraic space over a scheme `S` and let `E` be an object of `D(𝒪_F)`. If every
object `U` of the small étale site of `F` admits a covering `{V → U}` over each member of which
the restriction of `E` is perfect on the localized ringed site, then `E` is perfect.

## Main results

* `AlgebraicGeometry.Space.isPerfect_of_locally`: perfectness of an object of `D(𝒪_F)` descends
  along a covering of the small étale site.

## Implementation notes

The small étale ringed site `AlgebraicGeometry.Space.smallEtaleRingedSite` of an algebraic space
is an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`: its objects are étale morphisms to the
space, one universe above the morphisms between them, and the sections of the structure sheaf
are in the universe of the schemes. The result is the instance at this site of
`AlgebraicGeometry.RingedSite.isPerfect_of_locally_anySite`, in which these three universes are
independent.

Nothing is assumed beyond the two derived categories. All six sheafification hypotheses —
on the site, on its slices, and on the slices of its slices — are instances for this site, from
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify`,
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_over` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_over_over` together with their
`WEqualsLocallyBijective` companions.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

variable [HasDerivedCategory.{d} (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))]
variable [∀ U : (smallEtaleRingedSite B S hS F hF).C, HasDerivedCategory.{d}
  (SheafOfModules.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over U))]

/-! ### The instances of the localized site that the statement is phrased through

The hypothesis of the descent statement speaks of the slice `(F_étale)/V` as a ringed site in
its own right, `AlgebraicGeometry.RingedSite.over`, whose projections instance search does not
unfold. These local instances provide the sheafification, restriction and derived-category
instances of the slices. Among them, `AlgebraicGeometry.RingedSite.iterHasSheafifyAll` and
`iterWEqAll` derive sheafification on a slice of a slice from sheafification on a slice, through
`CategoryTheory.Over.iteratedSliceEquiv`, so no iterated hypothesis has to be supplied.
-/

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.iterHasSheafifyAll RingedSite.iterWEqAll
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  RingedSite.locallyOverRingSheafHasDerivedCategory RingedSite.ovHasDerived

/-- **Perfectness of an object of `D(𝒪_F)` descends along a covering of the small étale site of
the algebraic space `F`.** If every object `U` of the site admits a covering `{V → U}` over each
member of which the restriction of `E` is perfect on the localized ringed site, then `E` is
perfect. -/
theorem isPerfect_of_locally
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
    (h : ∀ U : (smallEtaleRingedSite B S hS F hF).C,
      ∃ P : Presieve U, Sieve.generate P ∈ (smallEtaleRingedSite B S hS F hF).J U ∧
        ∀ ⦃V : (smallEtaleRingedSite B S hS F hF).C⦄ (f : V ⟶ U), P f →
          ((smallEtaleRingedSite B S hS F hF).over V).IsPerfect
            ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS F hF).O) V).mapDerivedCategory.obj E)) :
    (smallEtaleRingedSite B S hS F hF).IsPerfect E :=
  RingedSite.isPerfect_of_locally_anySite (smallEtaleRingedSite B S hS F hF) E h

end AlgebraicGeometry.Space

end
