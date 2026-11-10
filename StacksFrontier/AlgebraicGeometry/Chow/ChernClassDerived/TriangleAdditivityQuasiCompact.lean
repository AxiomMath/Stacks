module

public import StacksFrontier.AlgebraicGeometry.BlowupAmpleFamily.Noetherian
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TriangleAdditivityResolution
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CompletelyDecomposedCover
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmpleFamilyIdealCovering
public import StacksFrontier.AlgebraicGeometry.Perfect.SectionImageIdeal
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealCoveringResolutionNoetherian

/-!
# Additivity across a triangle over a quasi-compact base

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished triangle in `D(𝒪_X)`
with `E₁` and `E₂` perfect. Condition (4) of [Stacks, Tag 0F9F] is that `X` be quasi-compact.
Since the base of the Chow situation is locally Noetherian and `X` is locally of finite type
over it, such an `X` is Noetherian, hence quasi-separated, so [Stacks, Tag 0GTU] supplies an
envelope `f : Y ⟶ X` whose source carries an ample family of invertible modules; `Y` is
Noetherian, being the source of a proper morphism with Noetherian target. On such a `Y` the
resolution property follows from the Noetherian case of the substantial direction of
[Stacks, Tag 0F89], which this development proves
(`AlgebraicGeometry.hasResolutionProperty_of_epi_idealPow_of_isNoetherian`), and the affine
diagonal then follows from the Noetherian case of [Stacks, Tag 0F8C], which this development
also proves (`AlgebraicGeometry.isAffineHom_diagonal_of_hasResolutionProperty_of_isNoetherian`).
`Stacks.Chow.triangleChernAdditive_of_resolutionProperty_envelope` then gives the conclusion of
Stacks 0F9F.

The last input of [Stacks, Tag 0GMM] that this rung needs, the sheaf of ideals cut out by a
global section of an invertible module, is `AlgebraicGeometry.existsSectionImageIdeal`
(`StacksFrontier/AlgebraicGeometry/Perfect/SectionImageIdeal.lean`). So both statements below stand
on their own hypotheses, and **Stacks 0F9F is registered here under condition (4) of the
source**, alongside its conditions (1) and (2) in
`StacksFrontier/AlgebraicGeometry/Chow/ChernClassDerived/TriangleAdditivity.lean`.

## Main results

* `Stacks.Chow.hasResolutionProperty_of_isAmpleFamily_of_isNoetherian` — the Noetherian case of
  [Stacks, Tag 0GMM]: a Noetherian scheme with an ample family of invertible modules has the
  resolution property. Unlike
  `AlgebraicGeometry.hasResolutionProperty_of_isAmpleFamily`, which is stated for every scheme
  and therefore needs the substantial direction of [Stacks, Tag 0F89] for every scheme, this one
  needs only the Noetherian case of that direction, which is proved here.
* `Stacks.Chow.triangleChernAdditive_of_compactSpace` — **[Stacks, Tag 0F9F] under condition (4)
  of the source**: a quasi-compact `X` locally of finite type over the base of the Chow
  situation.

## Implementation notes

The ideals, affine opens and finite locally free quotients that
`AlgebraicGeometry.hasResolutionProperty_of_epi_idealPow_of_isNoetherian` asks for are exactly
what `AlgebraicGeometry.existsSectionImageIdeal` produces at the sections of the finite affine
covering by nonvanishing loci that
`AlgebraicGeometry.Scheme.exists_finite_affine_nonvanishing_cover` extracts from the ample
family. Its finite-type conclusion is not used here: the Noetherian form of
[Stacks, Tag 0F89] does not ask for it, finite type of a sheaf of ideals being automatic on a
locally Noetherian scheme.

Condition (3) of the source — the irreducible components of `X` are quasi-compact — does not
reduce to condition (4): the envelope the source builds for it is the disjoint union `∐ X'ᵢ`
over the irreducible components, which is not quasi-compact when the components are infinite in
number. It is registered separately, at
`Stacks.Chow.triangleChernAdditive_of_isCompact_irreducibleComponents` in
`StacksFrontier/AlgebraicGeometry/Chow/ChernClassDerived/TriangleAdditivityComponents.lean`, over
that envelope (`Stacks.Chow.exists_isEnvelope_sigma_of_isCompact_irreducibleComponents`, in
`StacksFrontier/AlgebraicGeometry/Chow/ChernClassDerived/ComponentEnvelope.lean`). The derived
algebra over such a source assembles a cochain complex of sheaves of modules on a coproduct of
schemes out of complexes on the summands, which is the equivalence
`AlgebraicGeometry.sigmaComplexEquivalence`, and builds the commuting square of
`D(𝒪_{∐ X'ᵢ})` out of the summands' squares, which is faithfulness of the derived pullbacks to
the summands (`AlgebraicGeometry.eq_of_forall_derivedPullback_sigmaι_map_eq`).

## References

* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
* [Stacks Project, Tag 0GTU](https://stacks.math.columbia.edu/tag/0GTU)
* [Stacks Project, Tag 0GMM](https://stacks.math.columbia.edu/tag/0GMM)
* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
* [Stacks Project, Tag 0F8C](https://stacks.math.columbia.edu/tag/0F8C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u v

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The Noetherian case of [Stacks, Tag 0GMM].** A Noetherian scheme carrying an ample family
of invertible modules has the resolution property.

The ample family supplies a finite covering by affine nonvanishing loci of global sections of
invertible modules, `AlgebraicGeometry.existsSectionImageIdeal` turns each of those sections into
a sheaf of ideals cutting out the complement of its locus and presented as a quotient of a
finite locally free module, and the Noetherian case of the substantial direction of
[Stacks, Tag 0F89] (`AlgebraicGeometry.hasResolutionProperty_of_epi_idealPow_of_isNoetherian`)
concludes.

Unlike `AlgebraicGeometry.hasResolutionProperty_of_isAmpleFamily`, which is stated for every
scheme and so needs the substantial direction of [Stacks, Tag 0F89] for every scheme, this one
needs only its Noetherian case, which this development proves. -/
theorem hasResolutionProperty_of_isAmpleFamily_of_isNoetherian
    {ι : Type v} {X : Scheme.{u}}
    [IsNoetherian X] {L : ι → X.Modules} (hL : X.IsAmpleFamily L) :
    HasResolutionProperty X := by
  obtain ⟨m, i, n, U, s, hcover, hdata⟩ :=
    AlgebraicGeometry.Scheme.exists_finite_affine_nonvanishing_cover X L hL
  choose J hJsupport _hJft hJquot using fun k : Fin m =>
    AlgebraicGeometry.existsSectionImageIdeal X (X.tensorPow (L (i k)) (n k))
      (hL.isInvertibleModule_tensorPow (i k) (n k)) (s k)
  choose E hE q hq using hJquot
  refine AlgebraicGeometry.hasResolutionProperty_of_epi_idealPow_of_isNoetherian U J
    (fun k => (hdata k).2.1) hcover.iSup_eq_top (fun k => ?_) E hE q hq
  refine TopologicalSpace.Opens.ext ?_
  change ((J k).support : Set X)ᶜ = (U k : Set X)
  rw [hJsupport k, compl_compl, (hdata k).2.2]

/-- **[Stacks, Tag 0F9F] under condition (4) of the source.** Let `T` be a
distinguished triangle of `D(𝒪_X)` whose first two objects are perfect and let `X`, which is
locally of finite type over the base of the Chow situation, be quasi-compact. Then the Chern
classes of `E₁`, `E₂`, `E₃` are defined and

  `c(E₂) = c(E₁) c(E₃)`,  `ch_p(E₂) = ch_p(E₁) + ch_p(E₃)`,  `P_p(E₂) = P_p(E₁) + P_p(E₃)`.

`X` is Noetherian, the base being locally Noetherian, hence quasi-separated, so
[Stacks, Tag 0GTU] gives an envelope `f : Y ⟶ X` with `Y` carrying an ample family of invertible
modules; `Y` is Noetherian because `f` is proper, has the resolution property by
`Stacks.Chow.hasResolutionProperty_of_isAmpleFamily_of_isNoetherian`, and therefore has affine
diagonal by the Noetherian case of [Stacks, Tag 0F8C]. That is condition (1) of the source, in
the shape `Stacks.Chow.triangleChernAdditive_of_resolutionProperty_envelope` asks for.

Every hypothesis is a hypothesis of the source: the Chow situation, `X` locally of finite type
over its base, the distinguished triangle, perfectness of `E₁` and `E₂`, and quasi-compactness
of `X`. Quasi-separatedness, Noetherianity, the envelope, the ample family, the resolution
property and the affine diagonal are all derived. Perfectness of `E₃` is a standing hypothesis
of the source that no step of this proof uses, so it is omitted. -/
@[stacks 0F9F "condition (4): X is quasi-compact.  The conclusion is the whole one: the Chern \
classes of E_1, E_2 and E_3 are defined, c(E_2) = c(E_1)c(E_3), ch(E_2) = ch(E_1) + ch(E_3) and \
P_p(E_2) = P_p(E_1) + P_p(E_3), the last two read componentwise in A^p(X) tensor Q and in \
A^p(X) as the source reads them.  Perfectness of E_3 is a standing hypothesis of the source \
that no step of this proof uses, so it is omitted, exactly as for conditions (1) and (2)"]
theorem triangleChernAdditive_of_compactSpace
    (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    [CompactSpace X]
    (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distTriang (DerivedCategory X.Modules))
    (h₁ : IsPerfect (X := X.toRingedSpace) T.obj₁)
    (h₂ : IsPerfect (X := X.toRingedSpace) T.obj₂) :
    TriangleChernAdditive C sX T := by
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
  exact triangleChernAdditive_of_resolutionProperty_envelope C sX T hT f ⟨hproper, hcd⟩ h₁ h₂

end Stacks.Chow

end
