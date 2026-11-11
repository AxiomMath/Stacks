module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCentreEnlargedByDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCompositeCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupDivisorPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartAlphaBaseCase
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSummands
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsUnion
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion

/-!
# Enlarging the centre of a blowup by an effective Cartier divisor, from a presentation

Let `S` be a scheme, let `𝔅` be an algebraic space over `S`, let `Z ⊆ 𝔅` be a closed subspace
and let `D ⊆ 𝔅` be an effective Cartier divisor.  Let `Z' = Z + D` be the closed subspace cut
out by the product `𝓘_Z 𝓘_D` of the two defining ideals, Stacks 083U.  Stacks 0867 part (1)
says that the blowup of `𝔅` in `Z'` is the blowup of `𝔅` in `Z`, and part (2) that for a
morphism `f : X ⟶ 𝔅` and an `𝒪_X`-module `F` with no nonzero sections supported on `|f^{-1}D|`
the strict transform of `F` is the same for the centre `Z` and for the centre `Z'`.

`StacksFrontier.AlgebraicGeometry.Spaces.BlowupCentreEnlargedByDivisor` proves part (1) for an
arbitrary morphism which is the blowup of `𝔅` in `Z`, with the two inputs `h0809` and `h083V`.
This file discharges both and proves part (2).

## Main results

* `AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces_of_presentation` is part (1): a
  morphism which is the blowup of `𝔅` in `Z` is also the blowup of `𝔅` in `Z + D`, stated with
  the construction data of Stacks 085Q for `𝔅`.
  `AlgebraicGeometry.Space.exists_iso_blowup_sumClosedSubspaces_of_presentation` is the source's
  phrasing of it: every blowup of `𝔅` in `Z + D` is isomorphic over `𝔅` to the blowup of `𝔅` in
  `Z`.
* `AlgebraicGeometry.Space.strictTransformSheaf_preimage_sumClosedSubspaces` is part (2), and
  `AlgebraicGeometry.Space.exceptionalPreimageSet_preimage_sumClosedSubspaces` is the point-set
  identity it rests on: the exceptional preimage of the enlarged centre is the exceptional
  preimage of `Z` together with the inverse image of `|D|`.

Stacks 0867 itself, both parts with no construction data, is
`AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces_and_strictTransformSheaf_eq` in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupCentreEnlargedByDivisorUnconditional.lean`, where the
construction data is supplied for every algebraic space and every centre.

## Implementation notes

The input `h083V` of `AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces` is
`AlgebraicGeometry.Space.isPullbackDefined_sumClosedSubspaces_iff` of
`StacksFrontier.AlgebraicGeometry.Spaces.BlowupCompositeCentre`.  The input `h0809` — that the
inverse image of `D` along `b` is an effective Cartier divisor — is Stacks 085X, the
algebraic-space counterpart of Stacks 0809,
`AlgebraicGeometry.Space.isPullbackDefined_of_isBlowupAlong` of
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupDivisorPullback.lean`.  That proof goes through the
blowup constructed in Stacks 085Q, so it takes the construction data of that tag: an étale
presentation of `𝔅` and the three size conditions on the relative `Proj`s which
`AlgebraicGeometry.Space.relativeProjChartOfSituation` already asks for.  None of it appears in
the conclusion.

For part (2) the two blowups are, by part (1), the *same* morphism `b`, so the two strict
transforms live on the same `X ×_𝔅 B'` and are the quotients of the same module `pr_X^*F` by its
sections supported on `|pr_{B'}^{-1}(b^{-1}Z)|`, respectively on
`|pr_{B'}^{-1}(b^{-1}(Z + D))|` (`AlgebraicGeometry.Space.strictTransformSheaf`).  The second
set is the first together with the inverse image of `|f^{-1}D|`, because `|Z + D| = |Z| ∪ |D|`
(`AlgebraicGeometry.Space.subspacePointSet_sumClosedSubspaces`), and enlarging the supported set
by it changes the supported sections not at all
(`AlgebraicGeometry.Space.supportedSectionsSubmodule_union_eq`), so the two quotients are equal
on the nose and not merely isomorphic.

The hypothesis analogous to the source's `hW` — that `pr_X^*F` has no nonzero sections supported
on the inverse image of `|f^{-1}D|` over étale charts of `X ×_𝔅 B'` whose points avoid the
exceptional preimage — is derived from the hypothesis on `F` rather than assumed.  The derivation
has one geometric input: away from the exceptional locus the projection `pr_X` of the base change
is an isomorphism onto an open subspace of `X`, hence an open immersion and in particular étale.
This is part (1) of Stacks 085T, `AlgebraicGeometry.Space.isIso_fromPreimage_openComplement`,
applied to the open complement of `Z` in `𝔅` and transported across the pullback square defining
the base change by `CategoryTheory.Subfunctor.isIso_fromPreimage_of_isPullback`.  With that, a
chart of `X ×_𝔅 B'` avoiding the exceptional preimage factors through this open subspace, and
`AlgebraicGeometry.Space.sectionSupportedIn_etaleModulePullback_iff`, applied once to the
inclusion of the open subspace and once to its composite with `pr_X`, transports the vanishing of
sections of `F` supported on `|f^{-1}D|` to the chart.

## References

* [Stacks Project, Tag 0867](https://stacks.math.columbia.edu/tag/0867)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 085X](https://stacks.math.columbia.edu/tag/085X)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
* [Stacks Project, Tag 0809](https://stacks.math.columbia.edu/tag/0809)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Part (1) from the construction data of Stacks 085Q -/

section Constructed

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **Stacks 0867, part (1), from a presentation.** Let `Z ⊆ 𝔅` and `D ⊆ 𝔅` be closed
subspaces of an algebraic space over `S` with `D` an effective Cartier divisor, and let `Z + D`
be the closed subspace cut out by the product of their defining ideals.  A morphism
`b : B' ⟶ 𝔅` which is the blowup of `𝔅` in `Z` is also the blowup of `𝔅` in `Z + D`.

The input `h0809` of
`AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces` — that the inverse image of `D` along
`b` is an effective Cartier divisor — is Stacks 085X, the algebraic-space counterpart of Stacks
0809, `AlgebraicGeometry.Space.isPullbackDefined_of_isBlowupAlong`.  Its
proof goes through the blowup constructed in Stacks 085Q, so the construction data of that
tag — an étale presentation `P` of `𝔅` and the three size conditions on the relative `Proj`s —
is carried here; it does not appear in the conclusion.  The same statement without it is
`AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces_of_isEffectiveCartierDivisor`. -/
theorem isBlowupAlong_sumClosedSubspaces_of_presentation {𝔅 B' : AlgebraicSpaces B S hS}
    (Z D : ClosedSubspaces B S hS 𝔅.obj)
    (hD : IsEffectiveCartierDivisor B S hS 𝔅 D)
    (P : Presentation B S hS 𝔅.obj 𝔅.property)
    (hcU : B.Contains (reesChartSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
    (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
    (hcRR : B.Contains (reesDoubleSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
    {b : B' ⟶ 𝔅} (hb : IsBlowupAlong B S hS Z b) :
    IsBlowupAlong B S hS (sumClosedSubspaces B S hS 𝔅 Z D) b :=
  isBlowupAlong_sumClosedSubspaces B S hS Z D hD hb
    (isPullbackDefined_of_isBlowupAlong Z P hcU hcR hcRR hb D hD)
    (fun g => isPullbackDefined_sumClosedSubspaces_iff g Z D)

/-- **Stacks 0867, part (1), in the source's phrasing, from a presentation.**  Every blowup of
`𝔅` in `Z + D` is isomorphic over `𝔅` to a blowup `b : B' ⟶ 𝔅` of `𝔅` in `Z`.

This is `AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces_of_presentation` together with
the uniqueness of blowups, `AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`. -/
theorem exists_iso_blowup_sumClosedSubspaces_of_presentation {𝔅 B' : AlgebraicSpaces B S hS}
    (Z D : ClosedSubspaces B S hS 𝔅.obj)
    (hD : IsEffectiveCartierDivisor B S hS 𝔅 D)
    (P : Presentation B S hS 𝔅.obj 𝔅.property)
    (hcU : B.Contains (reesChartSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
    (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
    (hcRR : B.Contains (reesDoubleSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
    {b : B' ⟶ 𝔅} (hb : IsBlowupAlong B S hS Z b) :
    ∀ (B'' : AlgebraicSpaces B S hS) (b'' : B'' ⟶ 𝔅),
      IsBlowupAlong B S hS (sumClosedSubspaces B S hS 𝔅 Z D) b'' →
        ∃ e : B' ≅ B'', e.hom ≫ b'' = b :=
  fun _ _ hb'' =>
    (isBlowupAlong_sumClosedSubspaces_of_presentation B S hS Z D hD P hcU hcR hcRR hb).exists_iso
      hb''

end Constructed

/-! ### Part (2): the strict transform does not change -/

section StrictTransform

attribute [local instance] pointTopology

variable {𝔅 B' X : AlgebraicSpaces B S hS}

/-- The exceptional preimage of the preimage of `C` is the inverse image of `|C|` along
`pr_X ≫ f = pr_{B'} ≫ b`. -/
private theorem exceptionalPreimageSet_preimageClosedSubspace
    (C : ClosedSubspaces B S hS 𝔅.1) (b : B' ⟶ 𝔅) (f : X ⟶ 𝔅) :
    exceptionalPreimageSet B S hS f b (preimageClosedSubspace b C).1 =
      pointsMap B S hS (strictTransformPullback B S hS f b).1
          (strictTransformPullbackToSource B S hS f b).hom ⁻¹'
        (pointsMap B S hS X.1 f.hom ⁻¹' subspacePointSet B S hS 𝔅.1 C.1) := by
  have hw : (strictTransformPullbackToBlowUp B S hS f b).hom ≫ b.hom =
      (strictTransformPullbackToSource B S hS f b).hom ≫ f.hom :=
    congrArg (fun k : strictTransformPullback B S hS f b ⟶ 𝔅 => k.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).w.symm
  rw [exceptionalPreimageSet_eq_preimage]
  erw [range_pointsMap_preimage_ι B S hS b.hom C.1]
  rw [← Set.preimage_comp, ← Set.preimage_comp, ← pointsMap_comp, ← pointsMap_comp, hw]

/-- **The exceptional preimage of the enlarged centre is the exceptional preimage of `Z` together
with the inverse image of `|D|`.**

The point set of `Z + D` is the union of those of `Z` and of `D`
(`AlgebraicGeometry.Space.subspacePointSet_sumClosedSubspaces`), the points of an inverse image
are the inverse image of the points (Stacks 03H4) and `pr_{B'} ≫ b = pr_X ≫ f`, so the three
sets on the two sides are the inverse images along those morphisms of `|Z|` and of `|D|`. -/
theorem exceptionalPreimageSet_preimage_sumClosedSubspaces
    (Z D : ClosedSubspaces B S hS 𝔅.1) (b : B' ⟶ 𝔅) (f : X ⟶ 𝔅) :
    exceptionalPreimageSet B S hS f b
        (preimageClosedSubspace b (sumClosedSubspaces B S hS 𝔅 Z D)).1 =
      exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1 ∪
        pointsMap B S hS (strictTransformPullback B S hS f b).1
            (strictTransformPullbackToSource B S hS f b).hom ⁻¹'
          (pointsMap B S hS X.1 f.hom ⁻¹' subspacePointSet B S hS 𝔅.1 D.1) := by
  rw [exceptionalPreimageSet_preimageClosedSubspace, subspacePointSet_sumClosedSubspaces,
    Set.preimage_union, Set.preimage_union, exceptionalPreimageSet_preimageClosedSubspace]

/-- **Stacks 0867, part (2).** Let `Z, D ⊆ 𝔅` be closed subspaces with `D` an effective Cartier
divisor, let `b : B' ⟶ 𝔅` be the blowup of `𝔅` in `Z` — hence also the blowup of `𝔅` in `Z + D`,
by part (1) — let `f : X ⟶ 𝔅` be an algebraic space over `𝔅` and let `F` be an `𝒪_X`-module whose
subsheaf of sections supported on `|f^{-1}D|` is zero.  Then the strict transform of `F` with
respect to the blowup of `𝔅` in `Z` and the strict transform of `F` with respect to the blowup of
`𝔅` in `Z + D` agree.

Both strict transforms live on the same `X ×_𝔅 B'`, the two blowups being the same morphism `b`,
and both are the quotient of `pr_X^*F` by its sections supported on the respective exceptional
preimage.  Those two sets of points differ by the inverse image of `|D|`
(`AlgebraicGeometry.Space.exceptionalPreimageSet_preimage_sumClosedSubspaces`), and enlarging the
supported set by it changes the supported sections not at all,
`AlgebraicGeometry.Space.supportedSectionsSubmodule_union_eq`.

The hypothesis `hW` of `AlgebraicGeometry.Space.supportedSectionsSubmodule_union_eq`, that
`pr_X^*F` has no nonzero sections
supported on the inverse image of `|f^{-1}D|` over étale charts of `X ×_𝔅 B'` avoiding the
exceptional preimage, is derived here from the hypothesis on `F` rather than assumed.  Away from
the exceptional preimage the projection `pr_X : X ×_𝔅 B' ⟶ X` restricts to an isomorphism onto an
open subspace `P` of `X ×_𝔅 B'`, by Stacks 085T part (1)
(`AlgebraicGeometry.Space.isIso_fromPreimage_openComplement`) applied to the open complement of
`Z` in `𝔅` and transported across the pullback square defining the base change
(`CategoryTheory.Subfunctor.isIso_fromPreimage_of_isPullback`); in particular the inclusion of `P`
is étale.  A chart of `X ×_𝔅 B'` whose points avoid the exceptional preimage then factors through
`P`, and `AlgebraicGeometry.Space.sectionSupportedIn_etaleModulePullback_iff`, applied once to the
inclusion of `P` and once to its composite with `pr_X`, transports the vanishing of sections of
`F` supported on `|f^{-1}D|` to that chart. -/
theorem strictTransformSheaf_preimage_sumClosedSubspaces
    (Z D : ClosedSubspaces B S hS 𝔅.1)
    (_hD : IsEffectiveCartierDivisor B S hS 𝔅 D)
    {b : B' ⟶ 𝔅} (hb : IsBlowupAlong B S hS Z b) (f : X ⟶ 𝔅)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : HasNoSectionsSupportedIn B S hS X
      (pointsMap B S hS X.1 f.hom ⁻¹' subspacePointSet B S hS 𝔅.1 D.1) F) :
    strictTransformSheaf B S hS f b
        (preimageClosedSubspace b (sumClosedSubspaces B S hS 𝔅 Z D)).1 F =
      strictTransformSheaf B S hS f b (preimageClosedSubspace b Z).1 F := by
  set T := strictTransformPullback B S hS f b with hTdef
  set pX := strictTransformPullbackToSource B S hS f b with hpXdef
  set pB := strictTransformPullbackToBlowUp B S hS f b with hpBdef
  have sq : IsPullback pX.hom pB.hom f.hom b.hom := IsPullback.of_hasPullback f.hom b.hom
  -- Stage A: the open subspace `P` of `T := X ×_𝔅 B'` away from the exceptional preimage, on
  -- which `pX` restricts to an isomorphism onto an open subspace of `X`, hence is étale.
  set W0 := openComplementOfClosedSubspace B S hS 𝔅 Z with hW0def
  have hWiso : IsIso (W0.1.fromPreimage b.hom) := isIso_fromPreimage_openComplement hb
  set U'' : Subfunctor X.1 := W0.1.preimage f.hom with hU''def
  have hU''open : IsOpenSubspace B S hS U'' :=
    isOpenSubspace_preimage B S hS f.hom W0.1 𝔅.2 X.2 W0.2
  have hιPiso : IsIso (U''.fromPreimage pX.hom) :=
    CategoryTheory.Subfunctor.isIso_fromPreimage_of_isPullback sq W0.1 hWiso
  set P : Subfunctor T.1 := U''.preimage pX.hom with hPdef
  have hPopen : IsOpenSubspace B S hS P :=
    isOpenSubspace_preimage B S hS pX.hom U'' X.2 T.2 hU''open
  have hPιEt : IsEtale B S hS P.ι := isEtale_of_isOpenImmersion B S hS hPopen.2
  have hρ'Et : IsEtale B S hS (P.ι ≫ pX.hom) := by
    have heq : U''.fromPreimage pX.hom ≫ U''.ι = P.ι ≫ pX.hom :=
      Subfunctor.fromPreimage_ι U'' pX.hom
    rw [← heq]
    have := hιPiso
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS (U''.fromPreimage pX.hom))
      (isEtale_of_isOpenImmersion B S hS hU''open.2)
  -- The point set of `U''` is the complement of the inverse image of `Z`, and that of `P` the
  -- complement of the exceptional preimage.
  have hU''pts : subspacePointSet B S hS X.1 U'' =
      (pointsMap B S hS X.1 f.hom ⁻¹' subspacePointSet B S hS 𝔅.1 Z.1)ᶜ := by
    have e1 : subspacePointSet B S hS X.1 U'' =
        pointsMap B S hS X.1 f.hom ⁻¹' subspacePointSet B S hS 𝔅.1 W0.1 :=
      range_pointsMap_preimage_ι B S hS f.hom W0.1
    rw [e1, subspacePointSet_openComplement, Set.preimage_compl]
  have hEPeq : exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1 =
      pointsMap B S hS T.1 pX.hom ⁻¹'
        (pointsMap B S hS X.1 f.hom ⁻¹' subspacePointSet B S hS 𝔅.1 Z.1) :=
    exceptionalPreimageSet_preimageClosedSubspace B S hS Z b f
  have hEP : subspacePointSet B S hS T.1 P =
      (exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1)ᶜ := by
    have e4 : subspacePointSet B S hS T.1 P =
        pointsMap B S hS T.1 pX.hom ⁻¹' subspacePointSet B S hS X.1 U'' :=
      range_pointsMap_preimage_ι B S hS pX.hom U''
    rw [e4, hU''pts, Set.preimage_compl, hEPeq]
  -- `AlgebraicSpaces`-level bundling of `P`, and the two étale structure morphisms out of it.
  set Psp : AlgebraicSpaces B S hS := ⟨P.toFunctor, hPopen.1⟩ with hPspdef
  set Pισp : Psp ⟶ T := ObjectProperty.homMk P.ι with hPισpdef
  set ρ'sp : Psp ⟶ X := ObjectProperty.homMk (P.ι ≫ pX.hom) with hρ'spdef
  -- Stage B: derive `hW` from `hF`, chart by chart.
  have hW : ∀ V : SmallEtale B S hS T.1,
      Disjoint (Set.range (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS T.1).obj V))
          V.1.hom))
        (exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1) →
      ∀ s : ((modulePullback B S hS pX).obj F).val.obj (op V),
        SectionSupportedIn B S hS T.1 T.2
            (pointsMap B S hS T.1 pX.hom ⁻¹'
              (pointsMap B S hS X.1 f.hom ⁻¹' subspacePointSet B S hS 𝔅.1 D.1))
            ((modulePullback B S hS pX).obj F) V s →
          s = 0 := by
    intro V hVdisj s hs
    have hVsub : Set.range (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS T.1).obj V))
        V.1.hom) ⊆ subspacePointSet B S hS T.1 P := by
      rw [hEP]
      intro p hp
      by_contra hpP
      exact Set.disjoint_left.mp hVdisj hp (not_not.mp hpP)
    obtain ⟨hfact, hfactcomp⟩ :=
      exists_factorization_of_range_pointsMap_subset B S hS V.1.hom hPopen hVsub
    have hVEt : IsEtale B S hS V.1.hom := (isEtale_iff_presheaf_of_yoneda B S hS V.1.hom).mpr V.2
    have hfactEt : IsEtale B S hS hfact :=
      isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS V.1.left) hPopen.1 T.2
        hfact V.1.hom P.ι hVEt hPιEt hfactcomp
    set VP : SmallEtale B S hS Psp.1 :=
      ⟨CostructuredArrow.mk hfact, (isEtale_iff_presheaf_of_yoneda B S hS hfact).mp hfactEt⟩
      with hVPdef
    have hVeq : (smallEtalePostcomp B S hS Pισp hPιEt).obj VP = V := by
      refine ObjectProperty.FullSubcategory.ext ?_
      change CostructuredArrow.mk (hfact ≫ P.ι) = V.1
      rw [hfactcomp]
      exact (CostructuredArrow.eq_mk V.1).symm
    -- Two small helpers for transporting a `SectionSupportedIn` fact, resp. the vanishing of a
    -- section, across an equality of charts of `T` — avoiding `subst`, which fails here because
    -- `VP`'s value depends on data (`hfact`) built from `V`.
    have transport : ∀ {W1 W2 : SmallEtale B S hS T.1} (e : W1 = W2)
        (t1 : ((modulePullback B S hS pX).obj F).val.obj (op W1)),
        SectionSupportedIn B S hS T.1 T.2
            (pointsMap B S hS T.1 pX.hom ⁻¹'
              (pointsMap B S hS X.1 f.hom ⁻¹' subspacePointSet B S hS 𝔅.1 D.1))
            ((modulePullback B S hS pX).obj F) W1 t1 →
          SectionSupportedIn B S hS T.1 T.2
            (pointsMap B S hS T.1 pX.hom ⁻¹'
              (pointsMap B S hS X.1 f.hom ⁻¹' subspacePointSet B S hS 𝔅.1 D.1))
            ((modulePullback B S hS pX).obj F) W2 (e ▸ t1) := by
      intro W1 W2 e t1 ht1
      cases e
      exact ht1
    have final : ∀ {W1 W2 : SmallEtale B S hS T.1} (e : W1 = W2)
        (t1 : ((modulePullback B S hS pX).obj F).val.obj (op W1)),
        e ▸ t1 = 0 → t1 = 0 := by
      intro W1 W2 e t1 ht
      cases e
      exact ht
    -- `s1` is `s` read, via the equality of charts, as a section over `VP`'s postcomposite chart.
    set s1 : ((modulePullback B S hS pX).obj F).val.obj
        (op ((smallEtalePostcomp B S hS Pισp hPιEt).obj VP)) := hVeq.symm ▸ s with hs1def
    have hs0 : SectionSupportedIn B S hS T.1 T.2
        (pointsMap B S hS T.1 pX.hom ⁻¹'
          (pointsMap B S hS X.1 f.hom ⁻¹' subspacePointSet B S hS 𝔅.1 D.1))
        ((modulePullback B S hS pX).obj F) ((smallEtalePostcomp B S hS Pισp hPιEt).obj VP) s1 :=
      transport hVeq.symm s hs
    set Tset := pointsMap B S hS X.1 f.hom ⁻¹' subspacePointSet B S hS 𝔅.1 D.1 with hTsetdef
    have hiff1 := sectionSupportedIn_etaleModulePullback_iff B S hS Pισp hPιEt
      (pointsMap B S hS T.1 pX.hom ⁻¹' Tset) ((modulePullback B S hS pX).obj F) VP s1
    have hs1' : SectionSupportedIn B S hS Psp.1 Psp.2
        (pointsMap B S hS Psp.1 Pισp.hom ⁻¹' (pointsMap B S hS T.1 pX.hom ⁻¹' Tset))
        ((etaleModulePullback B S hS Pισp hPιEt).obj ((modulePullback B S hS pX).obj F)) VP s1 :=
      hiff1.mpr hs0
    -- Transport `s1` across the comparison of the pullback of `F` through `P.ι ≫ pX` with the
    -- étale pullback of `pX^*F` through `P.ι`, to a section of the étale pullback of `F` along
    -- `P.ι ≫ pX` itself.
    set Φ : (etaleModulePullback B S hS Pισp hPιEt).obj ((modulePullback B S hS pX).obj F) ≅
        (etaleModulePullback B S hS ρ'sp hρ'Et).obj F :=
      (modulePullbackIsoEtaleModulePullback B S hS Pισp hPιEt).symm.app
          ((modulePullback B S hS pX).obj F) ≪≫
        (modulePullbackCompIso B S hS Pισp pX).app F ≪≫
        (modulePullbackIsoEtaleModulePullback B S hS ρ'sp hρ'Et).app F with hΦdef
    have hPισppX : Pισp.hom ≫ pX.hom = ρ'sp.hom := rfl
    have hs2 : SectionSupportedIn B S hS Psp.1 Psp.2
        (pointsMap B S hS Psp.1 ρ'sp.hom ⁻¹' Tset)
        ((etaleModulePullback B S hS ρ'sp hρ'Et).obj F) VP (Φ.hom.val.app (op VP) s1) := by
      have heq : pointsMap B S hS Psp.1 Pισp.hom ⁻¹' (pointsMap B S hS T.1 pX.hom ⁻¹' Tset) =
          pointsMap B S hS Psp.1 ρ'sp.hom ⁻¹' Tset := by
        rw [← Set.preimage_comp, ← pointsMap_comp, hPισppX]
      rw [← heq]
      exact SectionSupportedIn.map B S hS Psp.1 Psp.2
        (pointsMap B S hS Psp.1 Pισp.hom ⁻¹' (pointsMap B S hS T.1 pX.hom ⁻¹' Tset))
        Φ.hom VP s1 hs1'
    have hiff2 := sectionSupportedIn_etaleModulePullback_iff B S hS ρ'sp hρ'Et Tset F VP
      (Φ.hom.val.app (op VP) s1)
    have hs3 : SectionSupportedIn B S hS X.1 X.2 Tset F
        ((smallEtalePostcomp B S hS ρ'sp hρ'Et).obj VP) (Φ.hom.val.app (op VP) s1) :=
      hiff2.mp hs2
    have hzero : Φ.hom.val.app (op VP) s1 = 0 :=
      hF ((smallEtalePostcomp B S hS ρ'sp hρ'Et).obj VP) (Φ.hom.val.app (op VP) s1) hs3
    -- Recover `s1 = 0` from `hzero` by applying `Φ.inv` and using `Φ.hom ≫ Φ.inv = 𝟙`, then
    -- transport that back to `s = 0` along the chart equality.
    have hzero' : (Φ.hom.val.app (op VP)).hom s1 = 0 := hzero
    have e := Stacks.SheafOfModules.comp_val_app_hom_apply Φ.hom Φ.inv (op VP) s1
    rw [hzero', map_zero] at e
    rw [Φ.hom_inv_id] at e
    have hs1zero : s1 = 0 := e
    exact final hVeq.symm s hs1zero
  have hTclosed : IsClosed
      (exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS
      (strictTransformPullback B S hS f b).2
      (exceptionalPreimage B S hS f b (preimageClosedSubspace b Z).1).ι
      (exceptionalPreimage_isClosedSubspace B S hS f b (preimageClosedSubspace b Z).1
        (preimageClosedSubspace b Z).2).2
  have hsub := supportedSectionsSubmodule_union_eq
    (exceptionalPreimageSet B S hS f b (preimageClosedSubspace b Z).1)
    (pointsMap B S hS (strictTransformPullback B S hS f b).1
        (strictTransformPullbackToSource B S hS f b).hom ⁻¹'
      (pointsMap B S hS X.1 f.hom ⁻¹' subspacePointSet B S hS 𝔅.1 D.1))
    hTclosed
    ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F) hW
  rw [← exceptionalPreimageSet_preimage_sumClosedSubspaces B S hS Z D b f] at hsub
  exact congrArg (fun N : ((modulePullback B S hS
    (strictTransformPullbackToSource B S hS f b)).obj F).Submodule => cokernel N.ι) hsub

end StrictTransform

end AlgebraicGeometry.Space

end
