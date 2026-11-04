module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTriangulated
public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherentPullback
public import StacksFrontier.Geometry.RingedSpace.GlueMorphisms
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles

/-!
# Stacks 0DI3 at the genuine derived tensor product

Let `f : X ⟶ S` be a morphism of schemes which is flat and locally of finite presentation. The
`S`-perfect objects of `D(𝒪_X)` form a strictly full, saturated, triangulated subcategory. Two of
the three closure properties — strict fullness and saturation — hold for an arbitrary family of
Stacks 08CG certificates and are proved in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTriangulated`. The third,
triangulatedness, is proved there for every certificate family whose operations `- ⊗^{L} ℱ[0]`
commute with the shift and are exact and along which finite Tor dimension over a larger open
gives finite Tor dimension over a smaller one. The derived tensor product of Stacks 06YU has all
three properties, which is proved here, and so Stacks 0DI3 holds for every flat morphism locally
of finite presentation.

## Main definitions

* `AlgebraicGeometry.RingedSpace.resLE`: for opens `U ≤ V` of a ringed space `X`, the morphism of
  ringed spaces `X|_U ⟶ X|_V` whose underlying map is the inclusion and whose map on sections is
  restriction.
* `AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoOfLE`: restricting to `V` and then
  pulling back along that morphism is restricting to `U`.

## Main results

* `AlgebraicGeometry.RingedSpace.commShift_canonicalCertificate` and
  `AlgebraicGeometry.RingedSpace.isTriangulated_canonicalCertificate`: at the canonical
  certificate each `- ⊗^{L} ℱ[0]` commutes with the shift and is exact.
* `AlgebraicGeometry.RingedSpace.finiteTorDimensionRestricts_canonicalFamily`: the canonical
  certificate family satisfies `AlgebraicGeometry.RingedSpace.FiniteTorDimensionRestricts`.
* `AlgebraicGeometry.Scheme.Hom.isTriangulated_isPerfectRelativeTo_canonical` (Stacks 0DI3): for
  `f` flat and locally of finite presentation, the `S`-perfect objects of `D(𝒪_X)`, read at the
  derived tensor product of Stacks 06YU, form a triangulated subcategory.
* `AlgebraicGeometry.Scheme.Hom.isClosedUnderIsomorphisms_isPerfectRelativeTo_canonical` and
  `AlgebraicGeometry.Scheme.Hom.isSaturated_isPerfectRelativeTo_canonical`: the other two
  closure properties of Stacks 0DI3 at the same certificate family.
* `AlgebraicGeometry.Scheme.Hom.isSaturated_and_isTriangulated_isPerfectRelativeTo_canonical`
  (Stacks 0DI3): the whole statement, the `S`-perfect objects forming a strictly full, saturated,
  triangulated subcategory.

## Implementation notes

**Shift compatibility and exactness are fields of the derived tensor product.**
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` has fields `commShift₂` and `exact_left`,
so at `AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoring`, whose
`derivedTensor` field *is* `(derTensor X).tensor`, both properties are field projections. The
four instances the statement of `Stacks.Cohomology.TorAmplitude.derTensor` needs — additivity
of `sheafTensor` in each variable, existence of the total complexes, and `HasDerivedCategory` at
the spelling `Stacks.DerivedTensor.RingedSite.Modules X.sheaf` — are seated here as local
instances, exactly as `StacksFrontier/AlgebraicGeometry/Perfect/TorDimensionCanonicalCertificate.lean`
seats them.

**Locality of finite Tor dimension is Tag 09U8 at the inclusion of one open in another.** The
property `AlgebraicGeometry.RingedSpace.FiniteTorDimensionRestricts` compares the restriction
of one object of `D(𝒪_X)` to two nested opens, and the two restriction functors are not related
by a definitional equation. They are related by a morphism of ringed spaces: derived restriction
to an open is derived pullback along its inclusion
(`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback`), the derived pullbacks
along two composable morphisms compose
(`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`, Tag 0D5S, which holds for
arbitrary morphisms of ringed spaces), and derived pullback preserves Tor amplitude in a fixed
interval (`Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback`, Tag 09U8).
So the whole content is the factorisation `X|_U ⟶ X|_V ⟶ X` of the inclusion of `U`, which is
`AlgebraicGeometry.PresheafedSpace.resLE_comp_ofRestrict` transported along the fully faithful
functor forgetting the sheaf condition.

The interval is not widened and `a ≤ b` is not required: Tag 09U8 is stated for an arbitrary
interval, so the interval witnessing finite Tor dimension over `V` witnesses it over `U`.

**Everything about the inverse-image ringed space is read in the standard derived category**,
which is the model Tag 09U8 and the derived pullback are built in. The derived category of
`𝒪_X`-modules keeps its universe parameter, since no result about the derived pullback is applied
there.

## References

* [Stacks Project, Lemma 36.35.4 (Tag 0DI3)](https://stacks.math.columbia.edu/tag/0DI3)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Definition 13.6.1 (Tag 05RB)](https://stacks.math.columbia.edu/tag/05RB)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Section 20.26 (Tag 06YU)](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Lemma 36.60.4 (Tag 09U8)](https://stacks.math.columbia.edu/tag/09U8)
* [Stacks Project, Lemma 20.28.2 (Tag 0D5S)](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
  StrictlyPerfect AlgebraicGeometry
open Stacks.Cohomology.TorAmplitude Stacks.SheafOfModules.Tensor
open Stacks.DerivedTensor.RingedSite

universe d u

namespace AlgebraicGeometry.RingedSpace

/-! ### Shift compatibility and exactness at the canonical certificate -/

section OneSpace

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]

-- The four instances the statement of `Stacks.Cohomology.TorAmplitude.derTensor` needs. They
-- are `local instance`s of
-- `StacksFrontier/AlgebraicGeometry/Perfect/TorDimensionCanonicalCertificate.lean`, reseated here
-- rather than restated.
attribute [local instance] hasDerivedCategoryModules
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  hasMapBifunctorSheafTensor

/-- **`- ⊗^{L} ℱ[0]` commutes with the shift, at the canonical certificate.** The derived
tensor product of Stacks 06YU carries this as the `commShift₂` field of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, read in its left variable. -/
@[instance_reducible]
def commShift_canonicalCertificate (F : OXMod.{u, u} X) :
    ((canonicalCertifiedDerivedSheafTensoring.{d, u} X).derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)).CommShift ℤ :=
  (derTensor X).commShift_left _

/-- **`- ⊗^{L} ℱ[0]` is exact, at the canonical certificate.** This is the `exact_left` field of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`.

Together with `AlgebraicGeometry.RingedSpace.commShift_canonicalCertificate` this is the
exactness that `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` does not record and
that the triangulated clause of Stacks 0DI3 uses. -/
theorem isTriangulated_canonicalCertificate (F : OXMod.{u, u} X) :
    letI := commShift_canonicalCertificate X F
    ((canonicalCertifiedDerivedSheafTensoring.{d, u} X).derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)).IsTriangulated :=
  (derTensor X).exact_left _

end OneSpace

/-! ### The inclusion of one open subspace in another -/

/-- **The inclusion of one open subspace of a ringed space in a larger one.** For opens `U ≤ V`
of `X`, the morphism of ringed spaces `X|_U ⟶ X|_V` whose underlying map is the inclusion and
whose map on sections is restriction.

This is `AlgebraicGeometry.PresheafedSpace.resLE` carried along the fully faithful functor that
forgets the sheaf condition. -/
def resLE (X : RingedSpace.{u, u}) {U V : Opens X.carrier} (h : U ≤ V) :
    X.restrict U.isOpenEmbedding ⟶ X.restrict V.isOpenEmbedding :=
  SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage (X.toPresheafedSpace.resLE h)

/-- **The inclusion of `U` factors through the inclusion of `V`**, for `U ≤ V`. -/
theorem resLE_comp_ofRestrict (X : RingedSpace.{u, u}) {U V : Opens X.carrier} (h : U ≤ V) :
    resLE X h ≫ X.ofRestrict V.isOpenEmbedding = X.ofRestrict U.isOpenEmbedding :=
  SheafedSpace.forgetToPresheafedSpace.map_injective
    (X.toPresheafedSpace.resLE_comp_ofRestrict h)

/-! ### Locality of finite Tor dimension at the canonical certificate family -/

section Local

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-- **Restricting to `V` and then to `U ≤ V` is restricting to `U`**, on derived categories.
Derived restriction to an open is the derived pullback along its inclusion, the derived pullbacks
along two composable morphisms of ringed spaces compose (Tag 0D5S), and the inclusion of `U`
factors through the inclusion of `V`. -/
def derivedRestrictModulesIsoOfLE (X : RingedSpace.{u, u}) {U V : Opens X.carrier} (h : U ≤ V) :
    derivedRestrictModules X V ⋙ derivedPullback (resLE X h) ≅ derivedRestrictModules X U :=
  Functor.isoWhiskerRight (derivedRestrictModulesIsoDerivedPullback X V)
      (derivedPullback (resLE X h)) ≪≫
    Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical (resLE X h)
      (X.ofRestrict V.isOpenEmbedding) ≪≫
    eqToIso (congrArg (fun φ : X.restrict U.isOpenEmbedding ⟶ X => derivedPullback φ)
      (resLE_comp_ofRestrict X h)) ≪≫
    (derivedRestrictModulesIsoDerivedPullback X U).symm

/-- **`AlgebraicGeometry.RingedSpace.FiniteTorDimensionRestricts` holds at the genuine derived
tensor product**: the canonical certificate on every open subspace of `X` at once has the
property that finite Tor dimension of `E|_V` forces finite Tor dimension of `E|_U` for `U ≤ V`.

At the canonical certificate the predicate is the pinned Tor amplitude of
`Stacks.Cohomology.TorAmplitude`, `E|_U` is the derived pullback of `E|_V` along
`AlgebraicGeometry.RingedSpace.resLE`, and Tag 09U8 says derived pullback preserves Tor amplitude
in a fixed interval. The same interval therefore works. -/
theorem finiteTorDimensionRestricts_canonicalFamily (X : RingedSpace.{u, u}) :
    FiniteTorDimensionRestricts X (canonicalCertifiedDerivedSheafTensoringFamily X) := by
  intro U V hUV E hE
  obtain ⟨a, b, hab⟩ := hE
  refine ⟨a, b, (hasTorAmplitudeIn_canonicalCertificate_iff (X.restrict U.isOpenEmbedding)
    ((derivedRestrictModules X U).obj E) a b).2 ?_⟩
  refine Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso
    (X := X.restrict U.isOpenEmbedding) ?_ ((derivedRestrictModulesIsoOfLE X hUV).app E).symm
  exact Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback (resLE X hUV)
    ((derivedRestrictModules X V).obj E) a b
    ((hasTorAmplitudeIn_canonicalCertificate_iff (X.restrict V.isOpenEmbedding)
      ((derivedRestrictModules X V).obj E) a b).1 hab)

end Local

end AlgebraicGeometry.RingedSpace

/-! ### Stacks 0DI3 at the derived tensor product of Stacks 06YU -/

namespace AlgebraicGeometry.Scheme.Hom

section Canonical

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
  [Flat f] [LocallyOfFinitePresentation f]

/-- **Stacks 0DI3.** Strict fullness of the `S`-perfect objects, at the derived tensor product
of Stacks 06YU.

This is `AlgebraicGeometry.Scheme.Hom.isClosedUnderIsomorphisms_isPerfectRelativeTo`, which
holds for an arbitrary certificate family, read at the canonical one. -/
@[stacks 0DI3 "the strict fullness clause, at the genuine derived tensor product"]
public theorem isClosedUnderIsomorphisms_isPerfectRelativeTo_canonical :
    (isPerfectRelativeTo f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base))).IsClosedUnderIsomorphisms :=
  isClosedUnderIsomorphisms_isPerfectRelativeTo f _

/-- **Stacks 0DI3.** Saturation of the `S`-perfect objects, at the derived tensor product of
Stacks 06YU: a direct summand of an `S`-perfect object is `S`-perfect.

This is `AlgebraicGeometry.Scheme.Hom.isSaturated_isPerfectRelativeTo`, which holds for an
arbitrary certificate family, read at the canonical one. -/
@[stacks 0DI3 "the saturation clause, at the genuine derived tensor product"]
public theorem isSaturated_isPerfectRelativeTo_canonical :
    (isPerfectRelativeTo f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base))).IsSaturated :=
  isSaturated_isPerfectRelativeTo f _

/-- **Stacks 0DI3.** For a flat, locally finitely presented morphism `f : X ⟶ S` of schemes, the
`S`-perfect objects of `D(𝒪_X)` — read at the derived tensor product of Stacks 06YU on each open
subspace of `(X, f^{-1}𝒪_S)`, which is
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily` — form a
*triangulated* subcategory: the property contains the zero object, is stable under all shifts,
and is closed under extensions.

This is `AlgebraicGeometry.Scheme.Hom.isTriangulated_isPerfectRelativeTo` at the canonical
family: there each `- ⊗^{L} ℱ[0]` commutes with the shift and is exact, these being fields of the
derived tensor product, and finite Tor dimension restricts to smaller opens by Tag 09U8 at the
inclusion of one open subspace in another.

The other two assertions of Stacks 0DI3 — strict fullness and saturation — hold for an arbitrary
certificate family, and are
`AlgebraicGeometry.Scheme.Hom.isClosedUnderIsomorphisms_isPerfectRelativeTo` and
`AlgebraicGeometry.Scheme.Hom.isSaturated_isPerfectRelativeTo`; at the canonical family they are
`AlgebraicGeometry.Scheme.Hom.isClosedUnderIsomorphisms_isPerfectRelativeTo_canonical` and
`AlgebraicGeometry.Scheme.Hom.isSaturated_isPerfectRelativeTo_canonical`. -/
@[stacks 0DI3 "the triangulated clause, at the genuine derived tensor product"]
public theorem isTriangulated_isPerfectRelativeTo_canonical :
    (isPerfectRelativeTo f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base))).IsTriangulated :=
  isTriangulated_isPerfectRelativeTo f _
    (fun _ F => RingedSpace.commShift_canonicalCertificate _ F)
    (fun _ F => RingedSpace.isTriangulated_canonicalCertificate _ F)
    (RingedSpace.finiteTorDimensionRestricts_canonicalFamily _)

/-- **Stacks 0DI3.** Let `f : X ⟶ S` be a morphism of schemes which is flat and locally of finite
presentation. The `S`-perfect objects of `D(𝒪_X)`, read at the derived tensor product of
Stacks 06YU on each open subspace of `(X, f^{-1}𝒪_S)`, form a strictly full, saturated,
triangulated subcategory of `D(𝒪_X)`. -/
@[stacks 0DI3 "the whole statement: for f flat and locally of finite presentation, the S-perfect
objects of D(O_X) form a strictly full, saturated, triangulated subcategory"]
public theorem isSaturated_and_isTriangulated_isPerfectRelativeTo_canonical :
    (isPerfectRelativeTo f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace f.base))).IsClosedUnderIsomorphisms ∧
      (isPerfectRelativeTo f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace f.base))).IsSaturated ∧
      (isPerfectRelativeTo f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace f.base))).IsTriangulated :=
  ⟨isClosedUnderIsomorphisms_isPerfectRelativeTo_canonical f,
    isSaturated_isPerfectRelativeTo_canonical f, isTriangulated_isPerfectRelativeTo_canonical f⟩

end Canonical

end AlgebraicGeometry.Scheme.Hom

end
