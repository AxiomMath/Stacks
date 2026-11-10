module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTorDimensionLocality
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTriangulatedCanonical
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.NestedRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# Locally finite Tor dimension is inherited by an open subspace

Let `X` be a ringed space, `U ⊆ X` open and `E` an object of `D(𝒪_X)` which locally has finite
Tor dimension in the sense of part (3) of Stacks 08CG. Then `E|_U` locally has finite Tor
dimension on `X|_U`.

With it the implication (1) ⟹ (2) of the Tor-dimension clause of Stacks 0DI2 is three lines;
both are proved here.

## Main definitions

* `AlgebraicGeometry.RingedSpace.derivedRestrictModulesNestedIso`: restricting to `U` and then to
  an open `W` of `X|_U` is restricting to the image of `W` in `X` followed by the derived
  pullback along `AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedOpenIso`.

## Main results

* `AlgebraicGeometry.RingedSpace.hasTorAmplitude_derivedRestrictModules_nested`: Tor amplitude in
  `[a, b]` of the restriction of `E` to the image of `W` gives Tor amplitude in `[a, b]` of the
  twice-restricted object.
* `Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_derivedRestrictModules`:
  **locally finite Tor dimension is inherited by the restriction to an open subspace.**
* `AlgebraicGeometry.Scheme.Hom.chartHasFiniteTorDimension_of_locallyHasFiniteTorDimension`:
  **the implication (1) ⟹ (2) of the Tor-dimension clause of Stacks 0DI2**, at the canonical
  certificate family.

## Implementation notes

**Why the nesting needs a transport at all.** Both halves of the argument were already available:
`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_restrictModules` restricts Tor amplitude to an
open subspace, and `locallyHasFiniteTorDimension_iff_hasFiniteTorDimension` of
`AlgebraicGeometry.AffineRelativeTorAmplitude` collapses the local condition to the global one
on a quasi-compact space. They do not compose,
because `AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension` on `X|_U` quantifies over
the opens of `X|_U`, so its members are open subspaces of an open subspace, while everything
else in the development is stated for an open subspace of the ambient space. The transport across
that nesting is what this file supplies.

**It is built from derived pullbacks, not from the module-level nested identification.** The
comparison `AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedRestrictionModulesIso` identifies
the two restriction functors on modules, but Tor amplitude is a condition on a derived tensor
product, and no statement transports it along that identification. What does transport it is Tag
09U8, `Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback`, which preserves
Tor amplitude in a fixed interval along an *arbitrary* morphism of ringed spaces. So the
comparison is made at the level of derived pullbacks: derived restriction to an open is the
derived pullback along its inclusion
(`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback`), derived pullbacks
compose (Tag 0D5S,
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`), and
`AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedOpenIso_hom_fac` says the two routes from the
twice-restricted space to `X` agree. This is the same pattern as
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoOfLE`, with the inclusion of one open in
a larger one replaced by the nested comparison isomorphism.

**No shrinking of the covering is needed beyond intersecting with `U`.** The covering of `X|_U`
is the preimage of the given covering of `X`; the image in `X` of its `i`-th member is `U ⊓ V i`,
which is contained in `V i`, and finite Tor dimension passes to a smaller open by
`AlgebraicGeometry.RingedSpace.finiteTorDimensionRestricts_canonicalFamily`. The interval is not
reassembled anywhere in this file: part (3) of Stacks 08CG quantifies it existentially on each
member of the covering, so each member keeps its own.

**The spelling of derived restriction.** The statements below are at
`AlgebraicGeometry.RingedSpace.derivedRestrictModules`, the canonical name; it is equal to
`(AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U).mapDerivedCategory`, the
spelling inside `Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension`, by
`AlgebraicGeometry.RingedSpace.derivedRestrictModules_eq_mapDerivedCategory`, which is `rfl`.

**The derived categories are the standard ones.** Every ingredient — the affine-locality collapse,
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoOfLE` and
`AlgebraicGeometry.RingedSpace.finiteTorDimensionRestricts_canonicalFamily` — is stated at
`HasDerivedCategory.standard`, so these are too. A version with the hom universe left a parameter
would not be able to call any of them.

## References

* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Lemma 20.57.5 (Tag 09U8)](https://stacks.math.columbia.edu/tag/09U8)
* [Stacks Project, Lemma 20.28.9 (Tag 0D5S)](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 36.35.3 (Tag 0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

namespace AlgebraicGeometry.RingedSpace

universe u

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.TorAmplitude
open AlgebraicGeometry.RingedSpace.PseudoCoherence (nestedOpenIso nestedOpenIso_hom_fac)

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)
  (W : Opens (X.restrict U.isOpenEmbedding).carrier)

/-- **Nested derived restriction is derived restriction to the image, pulled back.** Restricting
to `U` and then to an open `W` of `X|_U` is restricting to the image of `W` in `X` followed by
the derived pullback along `AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedOpenIso`.

Each derived restriction is the derived pullback along the inclusion of its open, derived
pullbacks along composable morphisms compose by Tag 0D5S, and the two routes from the
twice-restricted space to `X` agree by
`AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedOpenIso_hom_fac`. -/
def derivedRestrictModulesNestedIso :
    derivedRestrictModules X (U.isOpenEmbedding.functor.obj W) ⋙
        derivedPullback (nestedOpenIso X U W).hom ≅
      derivedRestrictModules X U ⋙
        derivedRestrictModules (X.restrict U.isOpenEmbedding) W :=
  Functor.isoWhiskerRight
      (derivedRestrictModulesIsoDerivedPullback X (U.isOpenEmbedding.functor.obj W))
      (derivedPullback (nestedOpenIso X U W).hom) ≪≫
    Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (nestedOpenIso X U W).hom
      (X.ofRestrict (U.isOpenEmbedding.functor.obj W).isOpenEmbedding) ≪≫
    eqToIso (congrArg
      (fun φ : (X.restrict U.isOpenEmbedding).restrict W.isOpenEmbedding ⟶ X =>
        derivedPullback φ) (nestedOpenIso_hom_fac X U W)) ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      ((X.restrict U.isOpenEmbedding).ofRestrict W.isOpenEmbedding)
      (X.ofRestrict U.isOpenEmbedding)).symm ≪≫
    Functor.isoWhiskerRight (derivedRestrictModulesIsoDerivedPullback X U).symm
      (derivedPullback ((X.restrict U.isOpenEmbedding).ofRestrict W.isOpenEmbedding)) ≪≫
    Functor.isoWhiskerLeft (derivedRestrictModules X U)
      (derivedRestrictModulesIsoDerivedPullback (X.restrict U.isOpenEmbedding) W).symm

/-- **Tor amplitude passes across the nesting.** If the restriction of `E` to the image of `W` in
`X` has Tor amplitude in `[a, b]`, then so does the restriction of `E|_U` to `W`.

Tag 09U8 preserves Tor amplitude in a fixed interval along the nested comparison isomorphism, and
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesNestedIso` identifies the resulting object
with the twice-restricted one. -/
theorem hasTorAmplitude_derivedRestrictModules_nested
    (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ)
    (h : HasTorAmplitude
      (X.restrict (U.isOpenEmbedding.functor.obj W).isOpenEmbedding)
      ((derivedRestrictModules X (U.isOpenEmbedding.functor.obj W)).obj E) a b) :
    HasTorAmplitude ((X.restrict U.isOpenEmbedding).restrict W.isOpenEmbedding)
      ((derivedRestrictModules (X.restrict U.isOpenEmbedding) W).obj
        ((derivedRestrictModules X U).obj E)) a b :=
  FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1}
    (Pullback.hasTorAmplitude_derivedPullback (nestedOpenIso X U W).hom _ a b h)
    ((derivedRestrictModulesNestedIso X U W).app E).symm

/-- **Finite Tor dimension passes across the nesting.** The interval is carried unchanged. -/
theorem hasFiniteTorDimension_derivedRestrictModules_nested
    (E : DerivedCategory (OXMod.{u, u} X))
    (h : HasFiniteTorDimension
      (X.restrict (U.isOpenEmbedding.functor.obj W).isOpenEmbedding)
      ((derivedRestrictModules X (U.isOpenEmbedding.functor.obj W)).obj E)) :
    HasFiniteTorDimension ((X.restrict U.isOpenEmbedding).restrict W.isOpenEmbedding)
      ((derivedRestrictModules (X.restrict U.isOpenEmbedding) W).obj
        ((derivedRestrictModules X U).obj E)) := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨a, b, hasTorAmplitude_derivedRestrictModules_nested X U W E a b hab⟩

end AlgebraicGeometry.RingedSpace

namespace Stacks.Cohomology.TorAmplitude

universe u

attribute [local instance] HasDerivedCategory.standard

open _root_.Stacks.AlgebraicGeometry AlgebraicGeometry.RingedSpace

/-- **Locally finite Tor dimension is inherited by the restriction to an open subspace.** If an
object `E` of `D(𝒪_X)` locally has finite Tor dimension — part (3) of Stacks 08CG — then so does
its restriction to any open subspace `X|_U`.

The covering of `X|_U` is the preimage of a covering of `X` witnessing the hypothesis. The image
in `X` of its `i`-th member is contained in the `i`-th member `V i` of the given covering, so
finite Tor dimension of `E|_{V i}` gives finite Tor dimension of `E` restricted to that image
(`AlgebraicGeometry.RingedSpace.finiteTorDimensionRestricts_canonicalFamily`), and
`AlgebraicGeometry.RingedSpace.hasFiniteTorDimension_derivedRestrictModules_nested` carries it
across the nesting to the member of the covering of `X|_U`. No interval is widened: the predicate
quantifies the interval existentially on each member.

This is the ingredient of the implication (1) ⟹ (2) of the Tor-dimension clause of
Stacks 0DI2 that restricts the covering. -/
theorem locallyHasFiniteTorDimension_derivedRestrictModules
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    (U : TopologicalSpace.Opens X.carrier) (E : DerivedCategory (OXMod.{u, u} X))
    (h : LocallyHasFiniteTorDimension X E) :
    LocallyHasFiniteTorDimension (X.restrict U.isOpenEmbedding)
      ((derivedRestrictModules X U).obj E) := by
  obtain ⟨I, V, hV, hfin⟩ := h
  refine ⟨I, fun i => (Opens.map (Opens.inclusion' U)).obj (V i), ?_, fun i => ?_⟩
  · refine le_antisymm le_top fun y _ => ?_
    have hy : (Opens.inclusion' U).hom y ∈ iSup V := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · have hle : U.isOpenEmbedding.functor.obj ((Opens.map (Opens.inclusion' U)).obj (V i)) ≤
        V i := leOfHom (U.isOpenEmbedding.isOpenMap.adjunction.counit.app (V i))
    refine hasFiniteTorDimension_derivedRestrictModules_nested X U _ E ?_
    refine (hasFiniteTorDimension_canonicalCertificate_iff
      (X.restrict (U.isOpenEmbedding.functor.obj
        ((TopologicalSpace.Opens.map (TopologicalSpace.Opens.inclusion' U)).obj
          (V i))).isOpenEmbedding)
      ((derivedRestrictModules X (U.isOpenEmbedding.functor.obj
        ((TopologicalSpace.Opens.map (TopologicalSpace.Opens.inclusion' U)).obj
          (V i)))).obj E)).mp ?_
    exact finiteTorDimensionRestricts_canonicalFamily X hle E
      ((hasFiniteTorDimension_canonicalCertificate_iff (X.restrict (V i).isOpenEmbedding)
        ((derivedRestrictModules X (V i)).obj E)).mpr (hfin i))

end Stacks.Cohomology.TorAmplitude

namespace AlgebraicGeometry.Scheme.Hom

universe u

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.TorAmplitude
open AlgebraicGeometry.AffineRelativeTorAmplitude
  (locallyHasFiniteTorDimension_iff_hasFiniteTorDimension)

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The implication (1) ⟹ (2) of the Tor-dimension clause of Stacks 0DI2.** If `E` locally has
finite Tor dimension over `f⁻¹𝒪_S`, then for every affine open `U ⊆ X` the restriction `E|_U` has
finite Tor dimension over `f⁻¹𝒪_S`.

The three steps are: the certificate-carrying predicate at the canonical family is the pinned one
(`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iff`, which is
`Iff.rfl`); locally finite Tor dimension is inherited by `X|_U`
(`Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_derivedRestrictModules`); and on
`X|_U`, which is quasi-compact because `U` is affine, locally finite Tor dimension is finite Tor
dimension (`locallyHasFiniteTorDimension_iff_hasFiniteTorDimension` of
`AlgebraicGeometry.AffineRelativeTorAmplitude`).

**The certificate family is named, not quantified.** Unlike the two implications *into* condition
(1) of `AlgebraicGeometry.Scheme.Hom.locallyHasFiniteTorDimension_of_forall_chart` and
`AlgebraicGeometry.Scheme.Hom.locallyHasFiniteTorDimension_of_exists_affineCovering`, this
implication is not available for an arbitrary family: the premise is tested against the
certificates at the members of some covering and the conclusion against the certificate at `U`,
and a family carries no relation between its members, so at an arbitrary family the two sides
measure Tor amplitude against unrelated operations. It is stated at the genuine derived tensor
product of Stacks 06YU, which is what the source means; a consumer holding another family with
the same underived halves may use
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_iff_of_tensor_eq`.

**Affineness is used only through quasi-compactness**, so the statement holds verbatim for a
quasi-compact open; it is stated for an affine open because that is the chart condition of the
source. The affine open `V ⊆ S` that clause (2) asks the chart to map into does not appear,
because the sheaf-side condition does not refer to it; its module-side counterpart
`AlgebraicGeometry.Scheme.Hom.SectionsRelativelyPerfect` does. -/
@[stacks 0DI2 "the Tor-dimension clause, the implication (1) implies (2): if E locally has finite \
Tor dimension over f^{-1}O_S then its restriction to every affine open U of X has finite Tor \
dimension over f^{-1}O_S, for the derived tensor product of Stacks 06YU. The whole three-way \
equivalence, at the source's module-side conditions, is \
AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_tfae"]
theorem chartHasFiniteTorDimension_of_locallyHasFiniteTorDimension
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace f.base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base))
      ((derivedScalarRestriction f).obj E))
    (U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
    (hU : IsAffineOpen (X := X) U) :
    ChartHasFiniteTorDimension f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) E U := by
  have hcpt : CompactSpace
      ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding).carrier :=
    isCompact_iff_compactSpace.mp hU.isCompact
  have hres : LocallyHasFiniteTorDimension
      ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding)
      ((RingedSpace.derivedRestrictModules
        (RingedSpace.inverseImage S.toRingedSpace f.base) U).obj
          ((derivedScalarRestriction f).obj E)) :=
    locallyHasFiniteTorDimension_derivedRestrictModules
      (RingedSpace.inverseImage S.toRingedSpace f.base) U _
      ((RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iff
        (RingedSpace.inverseImage S.toRingedSpace f.base)
        ((derivedScalarRestriction f).obj E)).mp h)
  exact (RingedSpace.hasFiniteTorDimension_canonicalCertificate_iff
    ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding)
    ((RingedSpace.derivedRestrictModules
      (RingedSpace.inverseImage S.toRingedSpace f.base) U).obj
        ((derivedScalarRestriction f).obj E))).mpr
    ((locallyHasFiniteTorDimension_iff_hasFiniteTorDimension _).mp hres)

end AlgebraicGeometry.Scheme.Hom

end
