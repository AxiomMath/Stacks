module

public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksFrontier.Homology.Tor.Presentation
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedTensorStalk

/-!
# Base change of relative perfectness

Let `f : X ⟶ S` be flat and locally of finite presentation, let `g : S' ⟶ S` be arbitrary, set
`X' = S' ×_S X` and let `g' : X' ⟶ X` be the projection. Stacks 0DI5 asserts that the derived
pullback `L(g')^*K` of an `S`-perfect object `K` of `D(𝒪_X)` is `S'`-perfect. Relative
perfectness (Stacks 0DI0) is the conjunction of pseudo-coherence and locally finite Tor dimension
over `f^{-1}𝒪_S`; this file proves the first conjunct and assembles the vocabulary the second one
is stated in.

The pseudo-coherence conjunct is Stacks 09U7 read degree-free, which is
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherent_derivedPullback`: the source states that derived
pullback preserves `m`-pseudo-coherence for a fixed `m`, whereas Stacks 08CB (3) asks for a
*single* representing complex which is `m`-pseudo-coherent for every `m`, and Stacks 08CC (2)
reconciles the two. All that is left here is to feed it the first component of relative
perfectness.

For the Tor conjunct, Stacks 0C0V transfers Tor amplitude over the base across a Tor-independent
cartesian square, and `AlgebraicGeometry.TorIndependent` is automatic when `f` is flat, by
`AlgebraicGeometry.torIndependent_of_flat`. The
statement of Stacks 08CG on the inverse-image ringed space and the stalkwise predicate
`AlgebraicGeometry.HasTorAmplitudeOver` that Stacks 0C0V concludes at are compared by Stacks 09U9,
and the two halves of that comparison speak different Tor-amplitude vocabularies: Stacks 09U9
lands at `CategoryTheory.DerivedCategory.HasTorAmplitudeIn` for the canonical derived tensor
product of Stacks 0BYI over each stalk ring, while the ring-level base-change machinery is stated
at `StacksDraft.TorAmplitude.HasTorAmplitudeCanonical` and its `ULift`. The bridges between those
are proved below.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherent_derivedPullback_of_isPerfectRelativeTo`: the
  pseudo-coherence conjunct of Stacks 0DI5.
* `StacksDraft.TorAmplitude.hasTorAmplitudeIn_canonicalDerivedTensorProduct_iff`: Tor amplitude
  at the canonical derived tensor product of Stacks 0BYI, read through
  `CategoryTheory.DerivedCategory.HasTorAmplitudeIn`, is
  `StacksDraft.TorAmplitude.HasTorAmplitudeCanonical`.
* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_lift`: Tor amplitude over a ring is
  unchanged by lifting the module universe.
* `Stacks.SheafOfModules.DerivedTensorStalk.hasTorAmplitudeCanonical_forall_stalk_iff` and
  `...hasTorAmplitudeCanonicalLift_forall_stalk_iff`: **Stacks 09U9 in the ring-level
  vocabulary** — Tor amplitude of an object of `D(𝒪)` for the derived tensor product of
  Stacks 06YU is the canonical Tor amplitude of each of its stalks over the stalk ring.

## Implementation notes

`AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo` is parameterised by a family of derived tensor
products on the open subspaces of the inverse-image ringed space, because part (3) of Stacks 08CG
restricts to an open covering. Quantified over arbitrary certificates, Stacks 0DI5 is false: at
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection` the Tor clause
degenerates to local boundedness of cohomology, which derived pullback does not preserve — take
`S = X = Spec k[ε]`, `f = id`, `K = k[0]` and `g : Spec k ⟶ Spec k[ε]`. The family to read the
definition at is therefore
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoring`, whose derived operation
is the derived tensor product of Stacks 06YU. The pseudo-coherence conjunct proved here does not
mention the family at all, so it is stated for an arbitrary one.

`StacksDraft.TorAmplitude.HasTorAmplitudeCanonical` and
`CategoryTheory.DerivedCategory.HasTorAmplitudeIn` at
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` have character-identical bodies, but
the former is not exposed to importers, so the identification is not available as `Iff.rfl` here;
it is routed through the flat-representative criterion of Stacks 0654 instead, which both sides
have.

`StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift` is Tor amplitude of the lift of the
object to the next module universe, and that is the form in which the ring-level transfer across
a Tor-independent square of local rings is stated. The forward implication holds for an arbitrary
object; the converse is available only for an object of the form `DerivedCategory.Q.obj K`, so the
equivalence below passes through the canonical representative
`DerivedCategory.Q.objPreimage`.

## References

* [Stacks Project, Lemma 36.35.6 (Tag 0DI5)](https://stacks.math.columbia.edu/tag/0DI5)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 36.22.8 (Tag 0C0V)](https://stacks.math.columbia.edu/tag/0C0V)
* [Stacks Project, Lemma 20.47.3 (Tag 09U7)](https://stacks.math.columbia.edu/tag/09U7)
* [Stacks Project, Lemma 20.48.8 (Tag 09U9)](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Definition 20.47.1 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Lemma 20.47.4 (Tag 08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 0654](https://stacks.math.columbia.edu/tag/0654)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The pseudo-coherence conjunct of Stacks 0DI5 -/

namespace AlgebraicGeometry.Scheme.Hom

/-- **The pseudo-coherence conjunct of Stacks 0DI5.** For `f : X ⟶ S` flat and locally of finite
presentation, `g : S' ⟶ S` arbitrary, `X' = S' ×_S X` with projection `g' : X' ⟶ X`, and `K` an
`S`-perfect object of `D(𝒪_X)`, the derived pullback `L(g')^*K` is pseudo-coherent.

Only the pseudo-coherence conjunct of `AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo` is used,
so the family of derived tensor products on the inverse-image ringed space plays no role and is
left arbitrary. -/
@[stacks 0DI5 "the pseudo-coherence conjunct of the conclusion"]
public theorem isPseudoCoherent_derivedPullback_of_isPerfectRelativeTo
    {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    [Flat f] [LocallyOfFinitePresentation f] (_hpb : IsPullback g' f' f g)
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hK : f.IsPerfectRelativeTo D K) :
    RingedSpace.IsPseudoCoherent (X := X'.toRingedSpace)
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        g'.toLRSHom.toShHom).obj K) :=
  isPseudoCoherent_derivedPullback g' K hK.1

end AlgebraicGeometry.Scheme.Hom

/-! ### Tor amplitude at the canonical derived tensor product of a ring -/

namespace StacksDraft.TorAmplitude

/-- **Tor amplitude at the canonical derived tensor product, in the two vocabularies.** The
predicate `CategoryTheory.DerivedCategory.HasTorAmplitudeIn` applied to the derived tensor
product of Stacks 0BYI is `StacksDraft.TorAmplitude.HasTorAmplitudeCanonical`.

Both sides are equivalent to having a representative by flat modules concentrated in `[a, b]`,
which is Stacks 0654. -/
public theorem hasTorAmplitudeIn_canonicalDerivedTensorProduct_iff (R : Type u) [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    CategoryTheory.DerivedCategory.HasTorAmplitudeIn
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor K a b ↔
      HasTorAmplitudeCanonical R K a b := by
  rw [hasTorAmplitudeCanonical_iff_hasFlatRepresentative]
  exact hasTorAmplitude_iff_hasFlatRepresentative (canonicalTensorComparison R)
    (canonicalTensorIsLeftDerived R) K a b

/-- **Tor amplitude over a ring is unchanged by lifting the module universe.** An object of
`D(R)` has canonical Tor amplitude in `[a, b]` exactly when its image in the module category one
universe up does.

The forward implication is `hasTorAmplitudeCanonical_moduleLift`, which holds for an arbitrary
object; the converse is available for an object of the form `DerivedCategory.Q.obj K`, and the
canonical representative `DerivedCategory.Q.objPreimage` supplies one. -/
public theorem hasTorAmplitudeCanonical_iff_lift (R : Type u) [CommRing R]
    (E : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    HasTorAmplitudeCanonical R E a b ↔ HasTorAmplitudeCanonicalLift.{u, u, u} E a b := by
  refine ⟨AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_moduleLift E a b,
    fun h => ?_⟩
  have e := DerivedCategory.Q.objObjPreimageIso E
  have h' : HasTorAmplitudeCanonicalLift.{u, u, u}
      (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage E)) a b :=
    AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      ((moduleLift.{u, u, u} R).mapDerivedCategory.mapIso e.symm) a b h
  exact AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b
    (AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_moduleLift _ a b h')

end StacksDraft.TorAmplitude

/-! ### Stacks 09U9 in the ring-level vocabulary -/

namespace Stacks.SheafOfModules.DerivedTensorStalk

open StacksDraft.TorAmplitude

variable {X : TopCat.{u}}
  (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology X) CommRingCat.{u})

/-- **Stacks 09U9 in the ring-level vocabulary.** An object of `D(𝒪)` has Tor amplitude in
`[a, b]` for the derived tensor product of Stacks 06YU exactly when each of its stalks has
canonical Tor amplitude in `[a, b]` over the stalk ring.

This is `Stacks.SheafOfModules.DerivedTensorStalk.hasTorAmplitudeIn_canonical_iff_forall_stalk`
with the stalk side rewritten from
`CategoryTheory.DerivedCategory.HasTorAmplitudeIn` at the canonical derived tensor product of
Stacks 0BYI into `StacksDraft.TorAmplitude.HasTorAmplitudeCanonical`, which is the form the
ring-level results are stated at. A ringed space is read through `X.sheaf`, at which the left
side is Tor amplitude at
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoring`. -/
public theorem hasTorAmplitudeCanonical_forall_stalk_iff
    (E : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R)) (a b : ℤ) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      inferInstance
    letI := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
    letI := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
    letI := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
    CategoryTheory.DerivedCategory.HasTorAmplitudeIn
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).tensor E a b ↔
      ∀ y : X, HasTorAmplitudeCanonical
        (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj y)
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y).mapDerivedCategory.obj E)
        a b := by
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  let := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
  let := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
  let := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
  rw [hasTorAmplitudeIn_canonical_iff_forall_stalk R E a b]
  exact forall_congr' fun y => hasTorAmplitudeIn_canonicalDerivedTensorProduct_iff _ _ a b

/-- **Stacks 09U9 in the universe-lifted ring-level vocabulary.** The same equivalence with the
stalk condition read after lifting the module universe, which is the form in which Tor amplitude
over a base is recorded by `AlgebraicGeometry.HasTorAmplitudeOver`. -/
public theorem hasTorAmplitudeCanonicalLift_forall_stalk_iff
    (E : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R)) (a b : ℤ) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      inferInstance
    letI := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
    letI := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
    letI := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
    CategoryTheory.DerivedCategory.HasTorAmplitudeIn
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).tensor E a b ↔
      ∀ y : X, HasTorAmplitudeCanonicalLift.{u, u, u}
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y).mapDerivedCategory.obj E)
        a b := by
  exact (hasTorAmplitudeCanonical_forall_stalk_iff R E a b).trans
    (forall_congr' fun y => hasTorAmplitudeCanonical_iff_lift _ _ a b)

end Stacks.SheafOfModules.DerivedTensorStalk

end
