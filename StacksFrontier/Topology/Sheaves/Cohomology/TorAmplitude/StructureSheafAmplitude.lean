module

public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.Restriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatTransport
public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate

/-!
# The Tor amplitude of the structure sheaf

Let `(X, 𝒪_X)` be a ringed space. The structure sheaf, viewed as a module over itself and placed
in degree zero, has Tor amplitude in `[0, 0]`: it is the unit of the tensor product, so tensoring
with it is the identity functor. In particular it has finite Tor dimension, and it locally has
finite Tor dimension in the sense of part (3) of Stacks 08CG.

These are the cheapest *positive* instances of the three predicates of Stacks 08CG at the genuine
derived tensor product of Stacks 06YU, and that is what they are for: a statement quantified over
objects of locally finite Tor dimension is non-vacuous, and non-vacuous at a nonzero object rather
than only at the zero object.

## Main results

All in the namespace `Stacks.Cohomology.TorAmplitude`:

* `hasTorAmplitude_single_structureSheafModule`: the structure sheaf in degree zero has Tor
  amplitude in `[0, 0]`.
* `locallyHasFiniteTorDimension_single_structureSheafModule`: it locally has finite Tor
  dimension.
* `locallyHasFiniteTorDimension_canonical_single_structureSheafModule`: the same, read at the
  certificate-carrying predicate of `AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension`
  and the canonical certificate family.

## Implementation notes

The proof is the easy direction of Stacks 08CI: a complex of flat `𝒪_X`-modules concentrated in
`[a, b]` has Tor amplitude in `[a, b]`, which is
`Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative`. The one-term
complex `𝒪_X[0]` is such a complex: its degree-zero term is the structure sheaf, flat by
`Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_structureSheafModule`, and its
other terms are zero, flat by `AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero`. Nothing here
unfolds the derived tensor product.

The covering witnessing the local statement is the one-member covering by `⊤`, and the
restriction of the hypothesis to it is
`Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_restrictModules`; the last statement is
then the first read through
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iff`, which is
`Iff.rfl`, so the certificate predicate at the canonical family and the pinned predicate are the
same proposition.

No attribute is attached. Stacks 08CG is a definition, and its three predicates are already
registered at `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.HasTorAmplitudeIn`,
`HasFiniteTorDimension` and `AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension`; the
results below are instances of those predicates, not clauses of the definition.

## References

* [Stacks Project, Definition 20.48.1 (08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Lemma 20.48.3 (08CI)](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open AlgebraicGeometry

namespace Stacks.Cohomology.TorAmplitude

universe d u

attribute [local instance] restrictModules_preservesFiniteLimits
  restrictModules_preservesFiniteColimits

/-- **The structure sheaf in degree zero has Tor amplitude in `[0, 0]`.** The one-term complex
`𝒪_X[0]` is a complex of flat `𝒪_X`-modules concentrated in degree `0`, so the easy direction of
Stacks 08CI gives the bound. -/
public theorem hasTorAmplitude_single_structureSheafModule (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u} X)] :
    HasTorAmplitude X (DerivedCategory.Q.obj
      ((HomologicalComplex.single (OXMod.{u} X) (ComplexShape.up ℤ) 0).obj
        (BoundedFlatRepresentative.structureSheafModule X))) 0 0 :=
  Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative _ 0 0 _
    (fun i => by
      by_cases hi : i = 0
      · subst hi
        exact BoundedFlatRepresentative.isFlat_of_iso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm
          (BoundedFlatRepresentative.isFlat_structureSheafModule X)
      · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero _
          (HomologicalComplex.isZero_single_obj_X _ 0 _ i hi))
    (fun i hi => HomologicalComplex.isZero_single_obj_X _ 0 _ i (by
      simp only [Set.mem_Icc] at hi; omega))
    (Iso.refl _)

/-- **The structure sheaf in degree zero locally has finite Tor dimension.** The one-member
covering by `⊤` works, the bound of
`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_single_structureSheafModule` surviving
restriction.

This is a positive instance of part (3) of Stacks 08CG at the genuine derived tensor product and
at a *nonzero* object, so it witnesses that the predicate is not satisfied only by the zero
object. -/
public theorem locallyHasFiniteTorDimension_single_structureSheafModule (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u} X)]
    [∀ U : Opens X.carrier, HasDerivedCategory.{d} (OXMod.{u} (X.restrict U.isOpenEmbedding))] :
    LocallyHasFiniteTorDimension X (DerivedCategory.Q.obj
      ((HomologicalComplex.single (OXMod.{u} X) (ComplexShape.up ℤ) 0).obj
        (BoundedFlatRepresentative.structureSheafModule X))) :=
  ⟨PUnit, fun _ => ⊤, by simp,
    fun _ => hasFiniteTorDimension_restrictModules ⊤ _
      ⟨0, 0, hasTorAmplitude_single_structureSheafModule X⟩⟩

/-- **The same, at the certificate-carrying predicate and the canonical certificate family.**
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iff` identifies
the two predicates at that family, so this is the previous statement read for the genuine derived
tensor product rather than for an arbitrary certificate — in particular not for the degenerate
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection`. -/
public theorem locallyHasFiniteTorDimension_canonical_single_structureSheafModule
    (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u} X)]
    [∀ U : Opens X.carrier, HasDerivedCategory.{d} (OXMod.{u} (X.restrict U.isOpenEmbedding))] :
    RingedSpace.LocallyHasFiniteTorDimension X
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily X)
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single (OXMod.{u} X) (ComplexShape.up ℤ) 0).obj
          (BoundedFlatRepresentative.structureSheafModule X))) :=
  (RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iff X _).2
    (locallyHasFiniteTorDimension_single_structureSheafModule X)

end Stacks.Cohomology.TorAmplitude

end
