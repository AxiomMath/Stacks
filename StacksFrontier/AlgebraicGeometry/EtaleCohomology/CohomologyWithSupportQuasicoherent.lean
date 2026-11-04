module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComplementAssociatedSheaf
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.QuasicoherentSupportedDegreewise
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology with support of a quasi-coherent module on the small étale site

Let `X` be a scheme, `i : Z ⟶ X` a closed immersion with open complement `j : U ⟶ X`, and `𝓕` a
quasi-coherent `𝒪_X`-module with associated sheaf `𝓕ᵃ` on the small étale site of `X`.  If `U` is
retrocompact in `X`, then for every `q` the étale sheaf `i_*ℋ^q_Z(𝓕ᵃ)` is the sheaf associated to
the Zariski sheaf `i_*ℋ^q_Z(𝓕)`, and the latter is a quasi-coherent `𝒪_X`-module.  This is the
second clause of [Stacks, Tag 0A46].

The proof is the source's.  On both sites, `0 ⟶ i_*ℋ^0_Z ⟶ 𝟭 ⟶ j_*(-|_U)` is short exact on
injectives, so `i_*ℋ^0_Z` and `i_*ℋ^1_Z` are the kernel and cokernel of the restriction map
`𝓕 ⟶ j_*(𝓕|_U)`, and `i_*ℋ^{p+1}_Z = R^p j_*(-|_U)` for `p ≥ 1` (Stacks 0A45).  The functor
`𝓕 ↦ 𝓕ᵃ` is exact, carries the Zariski restriction map to the étale one and commutes with the
higher direct images along the quasi-compact `j` (Descent, Lemma 071N), so it carries the
Zariski `i_*ℋ^q_Z(𝓕)` to the étale `i_*ℋ^q_Z(𝓕ᵃ)` in every degree.  Quasi-coherence of the
Zariski `i_*ℋ^q_Z(𝓕)` is [Stacks, Tag 0G7G] (1), read in one degree.

## Main definitions

* `AlgebraicGeometry.complementJStarIsoPullback`: restriction to the open complement in the
  ringed-space spelling of the Zariski `i_*ℋ_Z` is the pullback along `j`, compatibly with the
  units of the two adjunctions.
* `AlgebraicGeometry.supportedCohomologyAssociatedSheafIso`: `i_*ℋ^q_Z(𝓕ᵃ) ≅ (i_*ℋ^q_Z(𝓕))ᵃ`.

## Main results

* `AlgebraicGeometry.supportedCohomology_isQuasicoherent_and_associatedSheaf`: **Stacks 0A46
  (2)**, both halves, in every degree.

## Implementation notes

*The étale `i_*ℋ^q_Z` is applied to the universe lift of `𝓕ᵃ`.*  The library's functor of
sections supported on `Z` on the small étale site,
`AlgebraicGeometry.supportedSectionsPushforward`, and its long exact sequence are defined for
abelian sheaves with coefficients in the universe after that of the schemes,
`AlgebraicGeometry.SmallEtaleAbelianSheaf`, whereas `𝓕ᵃ`,
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`, has sections in the universe of the
schemes.  The statement therefore applies `i_*ℋ^q_Z` to the universe lift of `𝓕ᵃ`
(`AlgebraicGeometry.SmallEtale.associatedSheafULift`) and compares it with the universe lift of
`(i_*ℋ^q_Z(𝓕))ᵃ`.  This is the source's object: the universe lift of abelian sheaves is fully
faithful and exact (`Stacks.Sheaves.UniverseLift.fullyFaithfulUliftSheafFunctor`) and commutes
with the right derived functors of pushforwards
(`Stacks.Sheaves.UniverseLift.rightDerivedComplementPushforwardULiftIso`), so it changes neither
the objects nor the cohomology in question.  The isomorphism is one of abelian sheaves, the étale
`i_*ℋ_Z` being defined on abelian sheaves.

*Two models of the small étale site.*  Clause (1), `AlgebraicGeometry.supportedCohomologyEtaleIso`,
is stated on Mathlib's small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology`, where the
comparison of Stacks 03P2 is available.  Clause (2) is stated on the small étale site cut out of
a big étale site `B` containing `X`, `AlgebraicGeometry.SmallEtale.topology`, which is the site
of the source's set-theoretic conventions and the one on which the étale `i_*ℋ_Z`, the exact
functor `𝓕 ↦ 𝓕ᵃ` (Stacks 08H8) and Descent, Lemma 071N
(`AlgebraicGeometry.SmallEtale.higherDirectImageAssociatedSheafIso`) are proved.  On both sites
`𝓕ᵃ` is the sheaf of sections `(T ⟶ X) ↦ Γ(T, T^*𝓕)`; on the second, that description is
`AlgebraicGeometry.BigFppfOver.smallEtaleAssociatedModuleIsoSheaf`.  The two topoi are
equivalent (`AlgebraicGeometry.smallEtaleToCommonToposEquiv`, for coefficients in the universe
after that of the schemes), but no comparison of the two models of `𝓕ᵃ` along that equivalence
is used here.

*The Zariski side.*  The Zariski `i_*ℋ_Z` and its sequence are stated for ringed spaces, with
restriction to the open complement `ExtensionByZeroModules.jStar` and its right adjoint
`ExtensionByZeroModules.jPush`, whereas Descent, Lemma 071N is stated with
`AlgebraicGeometry.Scheme.Modules.pullback` along `j`.  The direct images agree definitionally,
and `AlgebraicGeometry.complementJStarIsoPullback` is the comparison of the left adjoints given
by uniqueness of adjoints, which is what makes it compatible with the units.

## References

* [Stacks Project, Tag 0A46](https://stacks.math.columbia.edu/tag/0A46)
* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 0G7G](https://stacks.math.columbia.edu/tag/0G7G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ExtensionByZeroModules
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.SectionsWithSupport (openComplement)
open Stacks.SheafOfModules.SupportedSections

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)]

/-- **Restriction to the open complement is the pullback along its inclusion.**  The functor
`ExtensionByZeroModules.jStar` of the ringed-space development and
`AlgebraicGeometry.Scheme.Modules.pullback` along `j : U ⟶ X` are both left adjoint to the direct
image along `j`, and this is the comparison of left adjoints given by uniqueness of adjoints. -/
public def complementJStarIsoPullback :
    jStar (closedComplementOpen B i) (structureSheafRing X.obj.toRingedSpace) ≅
      Scheme.Modules.pullback (closedComplementSchemeHom B i) :=
  Adjunction.leftAdjointUniq (jStarAdjunction _ _)
    (Scheme.Modules.pullbackPushforwardAdjunction (closedComplementSchemeHom B i))

/-- `AlgebraicGeometry.complementJStarIsoPullback` carries the unit of `j^* ⊣ j_*` in the
ringed-space spelling to the unit of `AlgebraicGeometry.Scheme.Modules.pullback` along `j` and
the direct image. -/
public theorem jStarAdjunction_unit_app_comp_complementJStarIsoPullback (F : X.obj.Modules) :
    (jStarAdjunction (closedComplementOpen B i) (structureSheafRing X.obj.toRingedSpace)).unit.app
        F ≫ (jPush (closedComplementOpen B i) (structureSheafRing X.obj.toRingedSpace)).map
          ((complementJStarIsoPullback B i).hom.app F) =
      (Scheme.Modules.pullbackPushforwardAdjunction (closedComplementSchemeHom B i)).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

/-- The underlying closed subset of `X` of a closed immersion `i` is closed. -/
public theorem isClosed_range_closedImmersion :
    IsClosed (Set.range (B.inclusion.map i).base) :=
  (B.inclusion.map i).isClosedEmbedding.isClosed_range

/-- A retrocompact open complement has quasi-compact inclusion. -/
public theorem quasiCompact_closedComplementSchemeHom
    (hU : IsRetrocompact (Set.range (B.inclusion.map i).base)ᶜ) :
    QuasiCompact (closedComplementSchemeHom B i) :=
  Stacks.Perfect.SupportedQuasicoherent.quasiCompact_ι_of_isRetrocompact X.obj
    (closedComplementOpen B i) hU

/-- **`i_*ℋ^q_Z(𝓕ᵃ) ≅ (i_*ℋ^q_Z(𝓕))ᵃ`** for a closed immersion `i : Z ⟶ X` with retrocompact
open complement and a quasi-coherent `𝒪_X`-module `𝓕`, in every degree `q`.  On the left is the
étale `i_*ℋ^q_Z` applied to the universe lift of `𝓕ᵃ`; on the right the universe lift of the
abelian sheaf underlying the associated module of the Zariski `i_*ℋ^q_Z(𝓕)`.

It is `AlgebraicGeometry.supportedCohomologyAssociatedSheafULiftIso`, whose hypotheses are the
compatibility of `𝓕 ↦ 𝓕ᵃ` with the restriction map `𝓕 ⟶ j_*(𝓕|_U)`
(`AlgebraicGeometry.complementAssociatedSheafULiftIso`) and with the higher direct images along
`j`, which is Descent, Lemma 071N
(`AlgebraicGeometry.complementHigherDirectImageAssociatedSheafULiftIso`). -/
public def supportedCohomologyAssociatedSheafIso
    (hU : IsRetrocompact (Set.range (B.inclusion.map i).base)ᶜ) (𝓕 : X.obj.Modules)
    [𝓕.IsQuasicoherent] (q : ℕ) :
    ((supportedSectionsPushforward B i).rightDerived q).obj
        ((SmallEtale.associatedSheafULift B X).obj 𝓕) ≅
      (SmallEtale.associatedSheafULift B X).obj
        (((supportedSectionsFunctor X.obj.toRingedSpace
          (Set.range (B.inclusion.map i).base)).rightDerived q).obj 𝓕) :=
  have := quasiCompact_closedComplementSchemeHom B i hU
  (supportedCohomologyAssociatedSheafULiftIso B i (Set.range (B.inclusion.map i).base)
    (isClosed_range_closedImmersion B i) 𝓕
    ((SmallEtale.associatedSheafULift B X).mapIso
        ((jPush (closedComplementOpen B i) (structureSheafRing X.obj.toRingedSpace)).mapIso
          ((complementJStarIsoPullback B i).app 𝓕)) ≪≫
      complementAssociatedSheafULiftIso B i 𝓕)
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (complementAssociatedSheafULiftIso B i 𝓕).hom)
        (((SmallEtale.associatedSheafULift B X).map_comp _ _).symm.trans
          (congrArg (SmallEtale.associatedSheafULift B X).map
            (jStarAdjunction_unit_app_comp_complementJStarIsoPullback B i 𝓕)))).trans
        (associatedSheafULift_map_unit_comp_complementAssociatedSheafULiftIso_hom B i 𝓕)))
    (fun p _ => (SmallEtale.associatedSheafULift B X).mapIso
        ((restrictPushRightDerivedIso X.obj.toRingedSpace (Set.range (B.inclusion.map i).base)
            (isClosed_range_closedImmersion B i) p).app 𝓕 ≪≫
          ((jPush (closedComplementOpen B i)
            (structureSheafRing X.obj.toRingedSpace)).rightDerived p).mapIso
            ((complementJStarIsoPullback B i).app 𝓕)) ≪≫
      (complementHigherDirectImageAssociatedSheafULiftIso B i p 𝓕).symm) q).symm

/-- Let `i : Z ⟶ X` be a closed immersion whose open complement is retrocompact in `X`, and let
`𝓕` be a quasi-coherent `𝒪_X`-module.  Then for every `q` the Zariski sheaf `i_*ℋ^q_Z(𝓕)` is a
quasi-coherent `𝒪_X`-module, and the étale sheaf `i_*ℋ^q_Z(𝓕ᵃ)` is its associated sheaf
`(i_*ℋ^q_Z(𝓕))ᵃ`.

The étale `i_*ℋ^q_Z` is the library's, on abelian sheaves of the small étale site with
coefficients in the universe after that of the schemes, and `𝓕ᵃ` is
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`, read as an abelian sheaf and then by the
universe lift, which is fully faithful and exact; see the implementation notes.  The first half
is [Stacks, Tag 0G7G] (1) in one degree, the second
`AlgebraicGeometry.supportedCohomologyAssociatedSheafIso`. -/
@[stacks 0A46 "clause (2): for a closed immersion with retrocompact open complement and a \
quasi-coherent module F, i_*H^q_Z(F) is quasi-coherent and i_*H^q_Z(F^a) = (i_*H^q_Z(F))^a on \
the small etale site, for every q"]
public theorem supportedCohomology_isQuasicoherent_and_associatedSheaf
    (hU : IsRetrocompact (Set.range (B.inclusion.map i).base)ᶜ) (𝓕 : X.obj.Modules)
    [𝓕.IsQuasicoherent] (q : ℕ) :
    (((supportedSectionsFunctor X.obj.toRingedSpace
        (Set.range (B.inclusion.map i).base)).rightDerived q).obj 𝓕).IsQuasicoherent ∧
      Nonempty (((supportedSectionsPushforward B i).rightDerived q).obj
          ((Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u}
            (SmallEtale.topology B X.obj X.property)).obj
            ((SheafOfModules.toSheaf.{u} (SmallEtale.structureSheaf B X.obj X.property)).obj
              ((SmallEtale.associatedModuleOfSheaf B X.obj X.property).obj 𝓕))) ≅
        (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u}
          (SmallEtale.topology B X.obj X.property)).obj
          ((SheafOfModules.toSheaf.{u} (SmallEtale.structureSheaf B X.obj X.property)).obj
            ((SmallEtale.associatedModuleOfSheaf B X.obj X.property).obj
              (((supportedSectionsFunctor X.obj.toRingedSpace
                (Set.range (B.inclusion.map i).base)).rightDerived q).obj 𝓕)))) :=
  ⟨Stacks.Perfect.SupportedQuasicoherent.isQuasicoherent_rightDerived_supportedSectionsFunctor_obj
      X.obj _ (isClosed_range_closedImmersion B i) hU 𝓕 ‹_› q,
    ⟨supportedCohomologyAssociatedSheafIso B i hU 𝓕 q⟩⟩

end AlgebraicGeometry

end
