module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject

/-!
# Relative perfectness at the degenerate certificate

Relative perfectness of Stacks 0DI0, `AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo`, takes the
derived tensor product on the inverse-image ringed space as a family `D` of certificates, one on
each open subspace. The `tensor` field of a
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` is free data, and
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection` inhabits the
bundle with the first projection `(ℰ, ℱ) ↦ ℰ`, which is exact and so is its own total left derived
functor.

This file reads relative perfectness at that family. The Tor conjunct collapses: it says only that
the cohomology of `E` vanishes outside an interval on each member of some open covering, with no
tensor product and no flatness anywhere in it. So relative perfectness **at an unpinned family of
certificates** is pseudo-coherence together with local boundedness.

The consequence, and the reason the file exists: a statement that takes relative perfectness as a
*hypothesis* and quantifies the family universally is asserting its conclusion under local
boundedness alone, which for any base other than a field is strictly weaker than finite Tor
dimension. Such a statement is therefore not the source's, and in general not true. The pinning
`AlgebraicGeometry.Scheme.Hom.IsGenuineRelativeTensorFamily` is what a hypothesis of relative
perfectness has to carry.

## Main definitions

* `AlgebraicGeometry.RingedSpace.firstProjectionFamily`: the family of first-projection
  certificates, one on each open subspace.
* `AlgebraicGeometry.RingedSpace.LocallyBoundedCohomology`: the cohomology of `E` restricted to
  each member of some open covering vanishes outside an interval depending on the member.

## Main results

* `AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_firstProjectionFamily_iff`: at the
  first-projection family, locally finite Tor dimension is local boundedness of the cohomology.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_firstProjectionFamily_iff`: at the
  first-projection family, relative perfectness is pseudo-coherence together with local
  boundedness of the cohomology of the derived restriction of scalars.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_firstProjectionFamily_of_locallyBounded`: the
  direction that matters for reading a hypothesis — a pseudo-coherent object with locally bounded
  cohomology is relatively perfect at the degenerate family, whatever its Tor amplitude.

## Implementation notes

`AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_firstProjection_iff` of
`StacksFrontier.AlgebraicGeometry.Perfect.TorDimension` does the work; everything here carries it
through the open covering of part (3) of Stacks 08CG and then through the conjunction of
Stacks 0DI0.

Flatness and local finite presentation of `f` are instance arguments of
`AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo` and are carried unused, as they are there.

## References

* [Stacks Project, Definition 36.35.1 (0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Definition 20.48.1 (08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]
  [∀ U : Opens X.carrier,
    HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]

/-- **The family of degenerate certificates.** On each open subspace of `X`, the certificate
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection` built from the
first projection `(ℰ, ℱ) ↦ ℰ`.

This is the family a statement quantified over families of certificates must also hold for. -/
public def firstProjectionFamily :
    ∀ U : Opens X.carrier,
      CertifiedDerivedSheafTensoring.{d', u} (X.restrict U.isOpenEmbedding) :=
  fun U => certifiedDerivedSheafTensoringOfFirstProjection.{d', u} (X.restrict U.isOpenEmbedding)

/-- **Local boundedness of the cohomology.** There is an open covering of `X` on each member of
which the cohomology of the restriction of `E` vanishes outside an interval depending on the
member.

No tensor product occurs in this condition. On a space whose sheaf of rings is a field in every
stalk it coincides with locally finite Tor dimension; in general it is strictly weaker. -/
public def LocallyBoundedCohomology (E : DerivedCategory (OXMod.{u, u} X)) : Prop :=
  ∃ (I : Type u) (U : I → Opens X.carrier), iSup U = ⊤ ∧
    ∀ i : I, ∃ a b : ℤ, ∀ j : ℤ, j ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor
        (OXMod.{u, u} (X.restrict (U i).isOpenEmbedding)) j).obj
          ((derivedRestrictModules X (U i)).obj E))

/-- **At the degenerate family, locally finite Tor dimension is local boundedness.** Part (3) of
Stacks 08CG asks for finite Tor dimension on each member of an open covering; at the
first-projection certificate finite Tor dimension is the vanishing of cohomology outside an
interval, by `hasTorAmplitudeIn_firstProjection_iff`. -/
public theorem locallyHasFiniteTorDimension_firstProjectionFamily_iff
    (E : DerivedCategory (OXMod.{u, u} X)) :
    LocallyHasFiniteTorDimension X (firstProjectionFamily.{d', u} X) E ↔
      LocallyBoundedCohomology X E := by
  constructor <;> rintro ⟨I, U, hsup, h⟩ <;> refine ⟨I, U, hsup, fun i => ?_⟩ <;>
    obtain ⟨a, b, hab⟩ := h i
  · exact ⟨a, b, (hasTorAmplitudeIn_firstProjection_iff _ _ a b).mp hab⟩
  · exact ⟨a, b, (hasTorAmplitudeIn_firstProjection_iff _ _ a b).mpr hab⟩

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
  [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [∀ U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    HasDerivedCategory.{d'}
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding))]

/-- **Relative perfectness at the degenerate family is pseudo-coherence plus local boundedness.**
Reading Stacks 0DI0 at `AlgebraicGeometry.RingedSpace.firstProjectionFamily`, the Tor conjunct
mentions no tensor product: it says that the cohomology of `E` read over `f^{-1}𝒪_S` vanishes
outside an interval on each member of some open covering.

So a statement whose hypothesis is relative perfectness for an arbitrary family of certificates is
a statement whose hypothesis is this. -/
public theorem isPerfectRelativeTo_firstProjectionFamily_iff [Flat f]
    [LocallyOfFinitePresentation f] (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    f.IsPerfectRelativeTo
        (RingedSpace.firstProjectionFamily.{d', u}
          (RingedSpace.inverseImage S.toRingedSpace f.base)) E ↔
      RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E ∧
        RingedSpace.LocallyBoundedCohomology
          (RingedSpace.inverseImage S.toRingedSpace f.base)
          ((derivedScalarRestriction f).obj E) :=
  and_congr_right fun _ =>
    RingedSpace.locallyHasFiniteTorDimension_firstProjectionFamily_iff _ _

/-- **A pseudo-coherent object with locally bounded cohomology is relatively perfect at the
degenerate family.** The direction of
`isPerfectRelativeTo_firstProjectionFamily_iff` that reads a hypothesis: no Tor-amplitude
information at all is needed to satisfy relative perfectness once the family of certificates is
left free. -/
public theorem isPerfectRelativeTo_firstProjectionFamily_of_locallyBounded [Flat f]
    [LocallyOfFinitePresentation f] (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hbdd : RingedSpace.LocallyBoundedCohomology
      (RingedSpace.inverseImage S.toRingedSpace f.base)
      ((derivedScalarRestriction f).obj E)) :
    f.IsPerfectRelativeTo
      (RingedSpace.firstProjectionFamily.{d', u}
        (RingedSpace.inverseImage S.toRingedSpace f.base)) E :=
  (isPerfectRelativeTo_firstProjectionFamily_iff f E).mpr ⟨hE, hbdd⟩

end AlgebraicGeometry.Scheme.Hom

end
