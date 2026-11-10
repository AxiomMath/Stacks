module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.AlgebraicGeometry.Etale.EtaleUpperShriekRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportHigher
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleRestrictionStalkIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AbelianHigherDirectImageSheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.DegreeZeroSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The long exact sequence of cohomology with support in a closed subscheme

Let `i : Z ⟶ X` be a closed immersion of schemes of a big étale site and let `j : U ⟶ X` be the
inclusion of the open complement.  The three functors `i_*ℋ_Z`, `𝟭` and `j_*(-|_U)` on abelian
sheaves of the small étale site of `X` form a short complex which is *short exact at every
injective* abelian sheaf, by
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportHigher`.  This file takes
the long exact sequence of their right derived functors and reads off the two assertions of
[Stacks, Tag 0A45] which the underived sequence of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportSequence` leaves out:

`0 ⟶ i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U) ⟶ i_*ℋ¹_Z(F) ⟶ 0`

is exact, and `R^p j_*(F|_U) ≅ i_*ℋ^{p+1}_Z(F)` for `p ≥ 1`.

## Main definitions

* `AlgebraicGeometry.closedComplementObject` — the open complement of the closed immersion,
  read as an object of the small étale site of the ambient scheme.
* `AlgebraicGeometry.complementPullbackPushforward` — the composite `j_*j^{-1}`, the target of
  `AlgebraicGeometry.complementRestriction`.  Its two factors `j^{-1}` and `j_*` are
  `AlgebraicGeometry.complementPullback` and `AlgebraicGeometry.complementPushforward`.
* `AlgebraicGeometry.supportedCohomologyDelta` — the connecting morphism
  `R^n(j_*(-|_U)) ⟶ R^{n+1}(i_*ℋ_Z)` of the long exact sequence.
* `AlgebraicGeometry.complementToSupportedCohomologyOne` — the map `j_*(F|_U) ⟶ i_*ℋ¹_Z(F)`
  completing the four-term sequence.

## Main results

* `AlgebraicGeometry.preservesInjectiveObjects_abelianRestriction` and
  `AlgebraicGeometry.preservesInjectiveObjects_abPullback_structureMorphism` — restriction of
  abelian sheaves to an object of a small étale site carries injective sheaves to injective
  sheaves, in the two spellings of restriction the library uses.
* `AlgebraicGeometry.complementPullbackPushforwardRightDerivedIso` —
  `R^n(j_*j^{-1}) ≅ j^{-1} ⋙ R^nj_*`.
* `AlgebraicGeometry.exact_supportedCohomology_composableArrows₅` — exactness of every six-term
  window of the long exact sequence.
* `AlgebraicGeometry.complementHigherDirectImageSupportedIso` — **Stacks 0A45**,
  `R^p j_*(F|_U) ≅ i_*ℋ^{p+1}_Z(F)` for `p ≥ 1`.
* `AlgebraicGeometry.exact_complementToSupportedCohomologyOne_app` and
  `AlgebraicGeometry.epi_complementToSupportedCohomologyOne_app` — **Stacks 0A45**, the
  four-term sequence is exact at `j_*(F|_U)` and ends in a surjection onto `i_*ℋ¹_Z(F)`.

## Implementation notes

The engine is `CategoryTheory.exact_rightDerived_composableArrows₅`, the long exact sequence of
the right derived functors of a short complex of additive functors which is short exact on
injective objects.  Its hypothesis is exactly
`AlgebraicGeometry.supportedSectionsShortComplex_shortExact_of_injective`, whose epimorphism
half is [Stacks, Tag 093X].  Three further inputs turn the resulting sequence into the one of
the source.

* The middle functor is the identity, whose higher right derived functors vanish because it is
  exact (`CategoryTheory.Functor.isZero_rightDerived_of_exact`).  That is what collapses the
  six-term windows: in positive degree the connecting morphism is squeezed between two zero
  objects and is therefore invertible, and in degree zero it is only epi.
* `R^n(j_*j^{-1})` is `R^nj_*` at the restricted sheaf.  This needs `j^{-1}` to be exact and to
  carry injective abelian sheaves to injective abelian sheaves.  Exactness is available, the
  inverse image being left exact and a left adjoint; the preservation of injectives is proved
  here, from the adjunction `j_! ⊣ j^{-1}` of
  `AlgebraicGeometry.SmallEtale.fShriekAdjunctionRestriction` and the exactness of `j_!`
  ([Stacks, Tag 03S5], `AlgebraicGeometry.SmallEtale.fShriekFunctor_exact`).  The two spellings
  of `j^{-1}` in the library — restriction along composition with `j`, and inverse image along
  base change — are identified by `AlgebraicGeometry.etaleRestrictionIso`, so the statement is
  recorded for both.
* In degree zero the outer terms of the long exact sequence are the zeroth right derived
  functors of `𝟭` and of `j_*(-|_U)`, both left exact, and
  `CategoryTheory.Functor.rightDerivedZeroIsoSelf` identifies them with the functors
  themselves.  `CategoryTheory.Functor.toRightDerivedZero_naturality_app` makes that
  identification compatible with the restriction map, which is what lets the exactness be
  stated at `F ⟶ j_*(F|_U)` rather than at the derived functors.

The remaining assertion of [Stacks, Tag 0A45], that
`i_*Rℋ_Z(F) ⟶ F ⟶ Rj_*(F|_U) ⟶ i_*Rℋ_Z(F)[1]` is a distinguished triangle in the derived
category, is not proved here; it is the derived-category packaging of the same hypothesis, for
which `CategoryTheory.triangleOfInjectiveCochainComplex_distinguished` is the corresponding
engine.

## References

* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
* [Stacks Project, Tag 093X](https://stacks.math.columbia.edu/tag/093X)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)]

/-- The open complement of a closed immersion, as an object of the small étale site of the
ambient scheme: its structure morphism is the inclusion of that complement, an open immersion
and hence étale. -/
public def closedComplementObject : SmallEtale B X.obj X.property :=
  ⟨Over.mk (closedComplementInclusion B i), by
    change Etale (B.inclusion.map (closedComplementInclusion B i))
    infer_instance⟩

/-- The structure morphism of the open complement, read as an object of the small étale site,
is the inclusion of the complement. -/
public theorem closedComplementObject_hom :
    (closedComplementObject B i).obj.hom = closedComplementInclusion B i := rfl

section Injectives

variable (Y : Scheme.{u}) (hY : B.Contains Y) (U : SmallEtale B Y hY)

/-- The direct image with compact support along the structure morphism of an object of the
small étale site preserves monomorphisms, being exact by [Stacks, Tag 03S5]. -/
public instance preservesMonomorphisms_fShriekFunctor_structureMorphism :
    (SmallEtale.fShriekFunctor.{u, u + 1} B U.obj.hom).PreservesMonomorphisms := by
  have hex := (exactFunctor_iff _).mp (SmallEtale.fShriekFunctor_exact.{u, u + 1} B U.obj.hom)
  have : PreservesFiniteLimits (SmallEtale.fShriekFunctor.{u, u + 1} B U.obj.hom) := hex.1
  constructor
  intro A A' g _
  exact preserves_mono_of_preservesLimit _ g

/-- **[Stacks, Tag 015Z] for restriction along an étale morphism.**  Restriction of abelian
sheaves to an object of the small étale site carries injective sheaves to injective sheaves: it
is right adjoint to the direct image with compact support along the structure morphism, and
that functor is exact. -/
public instance preservesInjectiveObjects_abelianRestriction :
    (abelianRestriction B Y hY U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (SmallEtale.fShriekAdjunctionRestriction B Y hY U)

/-- **Restriction of abelian sheaves along the structure morphism of an object of the small
étale site, in its base-change spelling, carries injective sheaves to injective sheaves.**  The
two spellings of restriction agree by `AlgebraicGeometry.etaleRestrictionIso`. -/
public instance preservesInjectiveObjects_abPullback_structureMorphism :
    (SmallEtale.abPullback.{u, u + 1} B U.obj.hom).PreservesInjectiveObjects where
  injective_obj {F} hF :=
    haveI : Injective F := hF
    Injective.of_iso ((etaleRestrictionIso B Y hY U).app F).symm
      (inferInstanceAs (Injective ((abelianRestriction B Y hY U).obj F)))

end Injectives

section Functoriality

variable {U Y : B.Scheme} (g : U ⟶ Y)

/-- Inverse image of abelian sheaves on the small étale sites along an arbitrary morphism
`g : U ⟶ Y` of `B`-schemes, with coefficients in the universe of
`AlgebraicGeometry.SmallEtaleAbelianSheaf`. -/
public abbrev smallEtaleAbInverseImage :
    SmallEtaleAbelianSheaf B Y ⥤ SmallEtaleAbelianSheaf B U :=
  (smallEtaleBaseChange B g).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B U.obj U.property)

/-- Direct image of abelian sheaves on the small étale sites along an arbitrary morphism
`g : U ⟶ Y` of `B`-schemes, with coefficients in the universe of
`AlgebraicGeometry.SmallEtaleAbelianSheaf`. -/
public abbrev smallEtaleAbDirectImage :
    SmallEtaleAbelianSheaf B U ⥤ SmallEtaleAbelianSheaf B Y :=
  (smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B U.obj U.property)

/-- The inverse image/direct image adjunction along a morphism of `B`-schemes. -/
public abbrev smallEtaleAbAdjunction : smallEtaleAbInverseImage B g ⊣ smallEtaleAbDirectImage B g :=
  (smallEtaleBaseChange B g).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B U.obj U.property)

end Functoriality

/-- Inverse image `j^{-1}` of abelian sheaves along the inclusion `j` of the open complement. -/
public abbrev complementPullback :
    SmallEtaleAbelianSheaf B X ⥤ SmallEtaleAbelianSheaf B (closedComplement B i) :=
  smallEtaleAbInverseImage B (closedComplementInclusion B i)

/-- Direct image `j_*` of abelian sheaves along the inclusion `j` of the open complement. -/
public abbrev complementPushforward :
    SmallEtaleAbelianSheaf B (closedComplement B i) ⥤ SmallEtaleAbelianSheaf B X :=
  smallEtaleAbDirectImage B (closedComplementInclusion B i)

/-- The inverse image/direct image adjunction `j^{-1} ⊣ j_*` along the inclusion of the open
complement. -/
public abbrev complementAdjunction : complementPullback B i ⊣ complementPushforward B i :=
  smallEtaleAbAdjunction B (closedComplementInclusion B i)

section LongExact

/-- The functor `F ↦ j_*(F|_U)`, the target of `AlgebraicGeometry.complementRestriction`. -/
public abbrev complementPullbackPushforward :
    SmallEtaleAbelianSheaf B X ⥤ SmallEtaleAbelianSheaf B X :=
  complementPullback B i ⋙ complementPushforward B i

/-- Restriction to the open complement preserves injective abelian sheaves: the complement is
an object of the small étale site of the ambient scheme. -/
public instance preservesInjectiveObjects_complementPullback :
    (complementPullback B i).PreservesInjectiveObjects :=
  preservesInjectiveObjects_abPullback_structureMorphism B X.obj X.property
    (closedComplementObject B i)

/-- Restriction to the open complement is right exact, being a left adjoint. -/
public instance preservesFiniteColimits_complementPullback :
    PreservesFiniteColimits (complementPullback B i) :=
  haveI : (complementPullback B i).IsLeftAdjoint :=
    ((smallEtaleBaseChange B (closedComplementInclusion B i)).sheafAdjunctionContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (closedComplement B i).obj
        (closedComplement B i).property)).isLeftAdjoint
  inferInstance

/-- **The right derived functors of `F ↦ j_*(F|_U)` are the higher direct images of the
restriction.**  Restriction to the open complement is exact and carries injective abelian
sheaves to injective abelian sheaves, so the right derived functors of the composite are the
right derived functors of the direct image, evaluated at the restricted sheaf. -/
public def complementPullbackPushforwardRightDerivedIso (n : ℕ) :
    (complementPullbackPushforward B i).rightDerived n ≅
      complementPullback B i ⋙ (complementPushforward B i).rightDerived n :=
  Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
    (complementPullback B i) (complementPushforward B i) n

/-- The sequence `i_*ℋ_Z ⟶ 𝟭 ⟶ j_*(-|_U)` of functors is short exact at every injective
abelian sheaf: this is `supportedSectionsShortComplex_shortExact_of_injective`. -/
public theorem supportedShortComplex_shortExact_on_injectives
    (F : SmallEtaleAbelianSheaf B X) (hF : Injective F) :
    (NatTrans.appShortComplex (supportedSectionsPushforwardInclusion B i)
      (complementRestriction B i)
      (supportedSectionsPushforwardInclusion_comp_complementRestriction B i) F).ShortExact :=
  have : Injective F := hF
  supportedSectionsShortComplex_shortExact_of_injective B i F

/-- The connecting morphism `R^n(j_*(-|_U)) ⟶ R^{n+1}(i_*ℋ_Z)` of the long exact sequence of
[Stacks, Tag 0A45]. -/
public def supportedCohomologyDelta (n : ℕ) :
    (complementPullbackPushforward B i).rightDerived n ⟶
      (supportedSectionsPushforward B i).rightDerived (n + 1) :=
  rightDerivedDelta (supportedSectionsPushforwardInclusion B i) (complementRestriction B i)
    (supportedSectionsPushforwardInclusion_comp_complementRestriction B i)
    (supportedShortComplex_shortExact_on_injectives B i) n

/-- Exactness of the six-term window
`R^n(i_*ℋ_Z)(F) ⟶ R^n(F) ⟶ R^n(j_*(F|_U)) ⟶ R^{n+1}(i_*ℋ_Z)(F) ⟶ R^{n+1}(F) ⟶ R^{n+1}(j_*(F|_U))`
of the long exact sequence of [Stacks, Tag 0A45]. -/
public theorem exact_supportedCohomology_composableArrows₅
    (F : SmallEtaleAbelianSheaf B X) (n : ℕ) :
    (ComposableArrows.mk₅
      ((NatTrans.rightDerived (supportedSectionsPushforwardInclusion B i) n).app F)
      ((NatTrans.rightDerived (complementRestriction B i) n).app F)
      ((supportedCohomologyDelta B i n).app F)
      ((NatTrans.rightDerived (supportedSectionsPushforwardInclusion B i) (n + 1)).app F)
      ((NatTrans.rightDerived (complementRestriction B i) (n + 1)).app F)).Exact :=
  exact_rightDerived_composableArrows₅ (supportedSectionsPushforwardInclusion B i)
    (complementRestriction B i)
    (supportedSectionsPushforwardInclusion_comp_complementRestriction B i)
    (supportedShortComplex_shortExact_on_injectives B i) (injectiveResolution F) n

/-- The higher right derived functors of the identity on abelian sheaves vanish: the identity
is exact. -/
public theorem isZero_rightDerived_id_obj (F : SmallEtaleAbelianSheaf B X) (n : ℕ) (hn : 0 < n) :
    IsZero (((𝟭 (SmallEtaleAbelianSheaf B X)).rightDerived n).obj F) :=
  Functor.isZero_rightDerived_of_exact (𝟭 (SmallEtaleAbelianSheaf B X)) F n hn

/-- The restriction map and the connecting morphism in degree `n` form an exact short complex. -/
private theorem exact_rightDerived_complementRestriction_supportedCohomologyDelta
    (F : SmallEtaleAbelianSheaf B X) (n : ℕ) :
    (ShortComplex.mk ((NatTrans.rightDerived (complementRestriction B i) n).app F)
      ((supportedCohomologyDelta B i n).app F)
      ((exact_supportedCohomology_composableArrows₅ B i F n).toIsComplex.zero' 1 2 3)).Exact :=
  (exact_supportedCohomology_composableArrows₅ B i F n).exact 1

/-- The connecting morphism is an epimorphism, since the next term is a higher right derived
functor of the identity. -/
private theorem epi_supportedCohomologyDelta_app (F : SmallEtaleAbelianSheaf B X) (n : ℕ) :
    Epi ((supportedCohomologyDelta B i n).app F) := by
  have h := exact_supportedCohomology_composableArrows₅ B i F n
  have hd : (ShortComplex.mk ((supportedCohomologyDelta B i n).app F)
      ((NatTrans.rightDerived (supportedSectionsPushforwardInclusion B i) (n + 1)).app F)
      (h.toIsComplex.zero' 2 3 4)).Exact := h.exact 2
  exact (ShortComplex.exact_iff_epi _
    ((isZero_rightDerived_id_obj B F (n + 1) n.succ_pos).eq_of_tgt _ 0)).1 hd

/-- **The connecting morphism of [Stacks, Tag 0A45] is invertible in positive degree.**  The
two neighbouring terms of the long exact sequence are the higher right derived functors of the
identity, which vanish, so the connecting morphism is both a monomorphism and an epimorphism. -/
public theorem isIso_supportedCohomologyDelta_app (F : SmallEtaleAbelianSheaf B X) (n : ℕ)
    (hn : 0 < n) : IsIso ((supportedCohomologyDelta B i n).app F) := by
  have hmono : Mono ((supportedCohomologyDelta B i n).app F) :=
    (ShortComplex.exact_iff_mono _ ((isZero_rightDerived_id_obj B F n hn).eq_of_src _ 0)).1
      (exact_rightDerived_complementRestriction_supportedCohomologyDelta B i F n)
  have := epi_supportedCohomologyDelta_app B i F n
  exact isIso_of_mono_of_epi _

/-- **Stacks 0A45: the isomorphism `R^p j_*(F|_U) ≅ i_*ℋ^{p+1}_Z(F)` for `p ≥ 1`.**  For an
abelian sheaf `F` on the small étale site of `X`, the `p`-th higher direct image along the
inclusion `j` of the open complement of the closed subscheme `Z`, applied to the restriction
`F|_U`, is the direct image along `i` of the `(p+1)`-st cohomology sheaf with support in `Z`.

The comparison is the connecting morphism of the long exact sequence of right derived functors
of `i_*ℋ_Z ⟶ 𝟭 ⟶ j_*(-|_U)`, read through the collapse of the right derived functors of the
composite `j_*j^{-1}`.  It is invertible because the two neighbouring terms of that sequence
are higher right derived functors of the identity. -/
@[sga "4 XIX 3.2" "partial"]
public def complementHigherDirectImageSupportedIso (F : SmallEtaleAbelianSheaf B X) (n : ℕ)
    (hn : 0 < n) :
    ((complementPushforward B i).rightDerived n).obj ((complementPullback B i).obj F) ≅
      ((supportedSectionsPushforward B i).rightDerived (n + 1)).obj F :=
  haveI := isIso_supportedCohomologyDelta_app B i F n hn
  ((complementPullbackPushforwardRightDerivedIso B i n).app F).symm ≪≫
    asIso ((supportedCohomologyDelta B i n).app F)

/-! ### The four-term sequence -/

/-- The direct image along the inclusion of the open complement is left exact, being a right
adjoint. -/
public instance preservesFiniteLimits_complementPushforward :
    PreservesFiniteLimits (complementPushforward B i) :=
  haveI : (complementPushforward B i).IsRightAdjoint :=
    ((smallEtaleBaseChange B (closedComplementInclusion B i)).sheafAdjunctionContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (closedComplement B i).obj
        (closedComplement B i).property)).isRightAdjoint
  inferInstance

/-- The functor `F ↦ j_*(F|_U)` is left exact: restriction is exact and the direct image is a
right adjoint. -/
public instance preservesFiniteLimits_complementPullbackPushforward :
    PreservesFiniteLimits (complementPullbackPushforward B i) := by
  dsimp only [complementPullbackPushforward]
  infer_instance

/-- The canonical map `j_*(F|_U) ⟶ i_*ℋ¹_Z(F)` completing the sequence of [Stacks, Tag 0A45]
on the right: the connecting morphism in degree zero, read through the identification of the
zeroth right derived functor of the left exact functor `j_*(-|_U)` with itself. -/
public def complementToSupportedCohomologyOne :
    complementPullbackPushforward B i ⟶ (supportedSectionsPushforward B i).rightDerived 1 :=
  (Functor.rightDerivedZeroIsoSelf (complementPullbackPushforward B i)).inv ≫
    supportedCohomologyDelta B i 0

/-- **Stacks 0A45: the sequence `0 ⟶ i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U) ⟶ i_*ℋ¹_Z(F) ⟶ 0` ends in a
surjection.**  The term to the right of `i_*ℋ¹_Z(F)` in the long exact sequence is the first
right derived functor of the identity, which vanishes. -/
public theorem epi_complementToSupportedCohomologyOne_app (F : SmallEtaleAbelianSheaf B X) :
    Epi ((complementToSupportedCohomologyOne B i).app F) := by
  have := epi_supportedCohomologyDelta_app B i F 0
  dsimp only [complementToSupportedCohomologyOne]
  rw [NatTrans.comp_app]
  exact epi_comp _ _

/-- The restriction to the open complement followed by the map to `i_*ℋ¹_Z` vanishes. -/
public theorem complementRestriction_comp_complementToSupportedCohomologyOne_app
    (F : SmallEtaleAbelianSheaf B X) :
    (complementRestriction B i).app F ≫ (complementToSupportedCohomologyOne B i).app F = 0 := by
  have hsq := Functor.toRightDerivedZero_naturality_app (complementRestriction B i) F
  have hz : (NatTrans.rightDerived (complementRestriction B i) 0).app F ≫
      (supportedCohomologyDelta B i 0).app F = 0 :=
    (exact_supportedCohomology_composableArrows₅ B i F 0).toIsComplex.zero' 1 2 3
  dsimp only [complementToSupportedCohomologyOne, Functor.rightDerivedZeroIsoSelf]
  rw [NatTrans.comp_app]
  change (complementRestriction B i).app F ≫
      (complementPullbackPushforward B i).toRightDerivedZero.app F ≫
        (supportedCohomologyDelta B i 0).app F = 0
  rw [← Category.assoc, ← hsq, Category.assoc, hz, comp_zero]

/-- **Stacks 0A45: the sequence `0 ⟶ i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U) ⟶ i_*ℋ¹_Z(F) ⟶ 0` is exact at
`j_*(F|_U)`.**  The two maps are the restriction to the open complement and the connecting
morphism in degree zero, the latter read through the identification of the zeroth right derived
functor of the left exact functor `j_*(-|_U)` with itself. -/
public theorem exact_complementToSupportedCohomologyOne_app (F : SmallEtaleAbelianSheaf B X) :
    (ShortComplex.mk ((complementRestriction B i).app F)
        ((complementToSupportedCohomologyOne B i).app F)
        (complementRestriction_comp_complementToSupportedCohomologyOne_app B i F)).Exact := by
  have hsq := Functor.toRightDerivedZero_naturality_app (complementRestriction B i) F
  have e : (ShortComplex.mk ((NatTrans.rightDerived (complementRestriction B i) 0).app F)
        ((supportedCohomologyDelta B i 0).app F)
        ((exact_supportedCohomology_composableArrows₅ B i F 0).toIsComplex.zero' 1 2 3)) ≅
      (ShortComplex.mk ((complementRestriction B i).app F)
        ((complementToSupportedCohomologyOne B i).app F)
        (complementRestriction_comp_complementToSupportedCohomologyOne_app B i F)) :=
    ShortComplex.isoMk
      (asIso ((𝟭 (SmallEtaleAbelianSheaf B X)).toRightDerivedZero.app F)).symm
      (asIso ((complementPullbackPushforward B i).toRightDerivedZero.app F)).symm (Iso.refl _)
      (by
        change inv ((𝟭 (SmallEtaleAbelianSheaf B X)).toRightDerivedZero.app F) ≫
            (complementRestriction B i).app F =
          (NatTrans.rightDerived (complementRestriction B i) 0).app F ≫
            inv ((complementPullbackPushforward B i).toRightDerivedZero.app F)
        rw [IsIso.inv_comp_eq, ← Category.assoc, hsq, Category.assoc, IsIso.hom_inv_id,
          Category.comp_id])
      (by
        change inv ((complementPullbackPushforward B i).toRightDerivedZero.app F) ≫
            (complementToSupportedCohomologyOne B i).app F =
          (supportedCohomologyDelta B i 0).app F ≫ 𝟙 _
        dsimp only [complementToSupportedCohomologyOne, Functor.rightDerivedZeroIsoSelf]
        rw [NatTrans.comp_app, Category.comp_id]
        change inv ((complementPullbackPushforward B i).toRightDerivedZero.app F) ≫
            (complementPullbackPushforward B i).toRightDerivedZero.app F ≫
              (supportedCohomologyDelta B i 0).app F =
          (supportedCohomologyDelta B i 0).app F
        rw [IsIso.inv_hom_id_assoc])
  exact ShortComplex.exact_of_iso e
    (exact_rightDerived_complementRestriction_supportedCohomologyDelta B i F 0)

end LongExact

end AlgebraicGeometry

end
