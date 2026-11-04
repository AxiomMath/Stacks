module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TriangleAdditivityQuasiCompact
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern classes of a perfect object over a quasi-compact base are defined

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `E` be a perfect object of `D(𝒪_X)`. Clause (4) of
[Stacks, Tag 0GUE] is that `X` be quasi-compact. Since the base of the Chow situation is
locally Noetherian and `X` is locally of finite type over it, such an `X` is Noetherian, hence
quasi-separated, so [Stacks, Tag 0GTU] supplies an envelope `f : Y ⟶ X` whose source carries an
ample family of invertible modules; `Y` is Noetherian, being the source of a proper morphism
with Noetherian target, has the resolution property by the Noetherian case of
[Stacks, Tag 0GMM] (`Stacks.Chow.hasResolutionProperty_of_isAmpleFamily_of_isNoetherian`) and
affine diagonal by the Noetherian case of [Stacks, Tag 0F8C]
(`AlgebraicGeometry.isAffineHom_diagonal_of_hasResolutionProperty_of_isNoetherian`). On such a
`Y` the perfect object `Lf^*E` is isomorphic to a bounded complex of finite locally free
`𝒪_Y`-modules by [Stacks, Tag 0F8F], which is clause (1) of the source.

This is the object-level counterpart of
`Stacks.Chow.triangleChernAdditive_of_compactSpace`, which is [Stacks, Tag 0F9F] under
condition (4) of that source: there the input of [Stacks, Tag 0F8I] needed is its fullness, so
that a *map* of perfect objects is represented by a map of bounded complexes; here only its
essential surjectivity, [Stacks, Tag 0F8F], is needed, and in the form
`Stacks.Perfect.BoundedLocallyFreeComplexes.exists_boundedFiniteLocallyFree_iso_of_affineDiagonal`
stated for a scheme with affine diagonal, which asks for nothing beyond the hypotheses displayed
below.

## Main results

* `Stacks.Chow.hasDefinedChernClasses_of_resolutionProperty_envelope` — the object-level rung:
  an envelope onto a quasi-compact, quasi-separated, semi-separated scheme with the resolution
  property makes the Chern classes of a perfect object defined.
* `Stacks.Chow.hasDefinedChernClasses_of_compactSpace` — **[Stacks, Tag 0GUE] clause (4)**: the
  Chern classes of a perfect object on a quasi-compact `X` locally of finite type over the base
  of the Chow situation are defined.

## Implementation notes

Clause (3) of the source — the irreducible components of `X` are quasi-compact — does not
reduce to clause (4): the envelope the source builds for it is the disjoint union `∐ X'ᵢ` over
the irreducible components, which is not quasi-compact when the components are infinite in
number. It is proved in
`StacksFrontier/AlgebraicGeometry/Chow/ChernClassDerived/CriteriaComponents.lean`
(`Stacks.Chow.hasDefinedChernClasses_of_isCompact_irreducibleComponents`), over the envelope
built in `StacksFrontier/AlgebraicGeometry/Chow/ChernClassDerived/ComponentEnvelope.lean`
(`Stacks.Chow.exists_isEnvelope_sigma_of_isCompact_irreducibleComponents`), whose summands are
Noetherian, carry the resolution property and have affine diagonal, so [Stacks, Tag 0F8F]
applies to each summand and `Lf^*E` is represented summand by summand. The derived algebra over
such a source needs no identification of `D(𝒪_{∐ X'ᵢ})` with the product of the `D(𝒪_{X'ᵢ})`,
which is not available: degreewise restriction to the summands is an equivalence on *complexes*
(`AlgebraicGeometry.sigmaComplexEquivalence`), so the summands' representatives assemble, and
the isomorphism in `D(𝒪_{∐ X'ᵢ})` is built from the summands' isomorphisms read as roofs of
actual complexes.

## References

* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0GTU](https://stacks.math.columbia.edu/tag/0GTU)
* [Stacks Project, Tag 0GMM](https://stacks.math.columbia.edu/tag/0GMM)
* [Stacks Project, Tag 0F8C](https://stacks.math.columbia.edu/tag/0F8C)
* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The Chern classes of a perfect object are defined from an envelope onto a scheme with the
resolution property.** If there is an envelope `f : Y ⟶ X` with `Y` quasi-compact,
quasi-separated, semi-separated and carrying the resolution property, then the Chern classes of
every perfect object `E` of `D(𝒪_X)` are defined.

The derived pullback `Lf^*E` is perfect by [Stacks, Tag 09UA], so it is isomorphic to a bounded
complex of finite locally free `𝒪_Y`-modules by [Stacks, Tag 0F8F]; a bounded complex is
locally bounded, so that is clause (1) of [Stacks, Tag 0GUE].

This is the object-level counterpart of
`Stacks.Chow.triangleChernAdditive_of_resolutionProperty_envelope`, which needs fullness of the
comparison of [Stacks, Tag 0F8I] as well, a map of perfect objects having to be represented. -/
theorem hasDefinedChernClasses_of_resolutionProperty_envelope {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsEnvelope f) [CompactSpace Y] [QuasiSeparatedSpace Y] [HasResolutionProperty Y]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (E : DerivedCategory X.Modules) (hE : IsPerfect (X := X.toRingedSpace) E) :
    HasDefinedChernClasses E := by
  obtain ⟨P, hP, ⟨i⟩⟩ := exists_boundedFiniteLocallyFree_iso_of_affineDiagonal Y _
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      f.toLRSHom.toShHom E hE)
  exact hasDefinedChernClasses_of_envelope f hf E P
    (isLocallyBoundedFiniteLocallyFree_of_boundedFiniteLocallyFreeComplex hP) ⟨i.symm⟩

/-- **[Stacks, Tag 0GUE] clause (4).** Let `(S, δ)` be the base situation of chapter 42, let `X`
be locally of finite type over `S` and quasi-compact, and let `E` be a perfect object of
`D(𝒪_X)`. Then the Chern classes of `E` are defined: there is an envelope `f : Y ⟶ X` such that
`Lf^*E` is isomorphic in `D(𝒪_Y)` to a locally bounded complex of finite locally free
`𝒪_Y`-modules.

`X` is Noetherian, the base being locally Noetherian, hence quasi-separated, so
[Stacks, Tag 0GTU] gives an envelope `f : Y ⟶ X` with `Y` carrying an ample family of invertible
modules; `Y` is Noetherian because `f` is proper, has the resolution property by
`Stacks.Chow.hasResolutionProperty_of_isAmpleFamily_of_isNoetherian`, and therefore has affine
diagonal by the Noetherian case of [Stacks, Tag 0F8C]. Then
`Stacks.Chow.hasDefinedChernClasses_of_resolutionProperty_envelope` applies.

Every hypothesis is a hypothesis of the source: the Chow situation, `X` locally of finite type
over its base, perfectness of `E`, and quasi-compactness of `X`. Quasi-separatedness,
Noetherianity, the envelope, the ample family, the resolution property and the affine diagonal
are all derived. -/
@[stacks 0GUE "clause (4): X is quasi-compact.  The conclusion is the full one: the Chern \
classes of E are defined, i.e. there is an envelope f : Y ⟶ X with Lf^*E isomorphic in D(O_Y) \
to a locally bounded complex of finite locally free O_Y-modules, which is Tag 0F9E (1).  The \
hypotheses are exactly the source's: the base situation of Tag 02QL, X locally of finite type \
over its base, E perfect, and X quasi-compact"]
theorem hasDefinedChernClasses_of_compactSpace
    (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    [CompactSpace X] (E : DerivedCategory X.Modules)
    (hE : IsPerfect (X := X.toRingedSpace) E) :
    HasDefinedChernClasses E := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNoetherian X := ⟨⟩
  have : QuasiSeparatedSpace X := inferInstance
  obtain ⟨Y, f, _hfp, hproper, hcd, _J, N, hN⟩ :=
    Stacks.BlowupAmpleFamily.exists_finitePresentation_proper_completelyDecomposed_isAmpleFamily X
  have : IsProper f := hproper
  have : IsNoetherian Y := AlgebraicGeometry.isNoetherian_source_of_isProper f
  have : CompactSpace Y := hN.compactSpace
  have : QuasiSeparatedSpace Y := hN.quasiSeparatedSpace
  have : HasResolutionProperty Y :=
    hasResolutionProperty_of_isAmpleFamily_of_isNoetherian hN
  have : IsAffineHom (pullback.diagonal (terminal.from Y)) :=
    AlgebraicGeometry.isAffineHom_diagonal_of_hasResolutionProperty_of_isNoetherian Y
  exact hasDefinedChernClasses_of_resolutionProperty_envelope f ⟨hproper, hcd⟩ E hE

end Stacks.Chow

end
