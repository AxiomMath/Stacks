module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportPushExcision
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionNaturality
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.LocalCohomologyExcision
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologySheafExcision
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# Excision for `i_*ℋ ⁿ_T` in the cohomology-sheaf spelling of Tag 0G7Q

The target of the class map of [Stacks, Tag 0G7Q] is
`Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor`, the degree-`n` cohomology sheaf
of `i_* R𝓗_T(ℱ[0])`. This file proves that it is **local on the ambient scheme**: for an open
subscheme `W ⊆ X` and `T' = W ∩ T`,

`(i_*ℋ ⁿ_T(ℱ))|_W ≅ i'_*ℋ ⁿ_{T'}(ℱ|_W)`,

which is what lets the Gysin maps of the equation charts of [Stacks, Tag 0G86] land in one sheaf
on `X`.

The excision is **the derived one**, `Stacks.Perfect.SupportPushExcision.supportPushPullbackIso`,
read on degree-`n` cohomology. Nothing abelian enters: the project also has excision for the
*abelian* right derived functors of the subsheaf of supported sections
(`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso`), and routing the chart
transports through that one would require identifying the two independently constructed
isomorphisms across
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafFunctorLocalCohomologyIso`, a coherence
the library does not have. Reading the derived excision on cohomology sheaves needs no such
identification, which is why `Stacks.Gysin.gysinTarget` is spelled at
`supportCohomologySheafFunctor`.

## Main definitions

* `Stacks.Gysin.supportCohomologyPullbackIso`: **excision in degree `n`, for an open immersion of
  ringed spaces.** The pullback along `f` of the degree-`n` cohomology sheaf of `i_* R𝓗_T(ℱ[0])`
  is the degree-`n` cohomology sheaf of `i'_* R𝓗_{T'}((f^*ℱ)[0])`.
* `Stacks.Gysin.modulePullbackRestrictFunctorIso`: pullback of modules along the ringed-space
  inclusion of an open subscheme is `AlgebraicGeometry.Scheme.Modules.restrictFunctor` along the
  inclusion of that open subscheme.
* `Stacks.Gysin.supportCohomologyRestrictIso`: **the same excision for a scheme and an open
  subscheme**, with the restriction written as `restrictFunctor`. This is the transport the
  equation charts of [Stacks, Tag 0G86] use.

## Main results

* `Stacks.Gysin.supportCohomologySheaf_congr`: the cohomology sheaf depends on the supporting
  closed subset only through the subset, not through the proof that it is closed, so an equality
  of subsets transports it.

## Implementation notes

**The chain.** With `P = f^*`, `L = Lf^*`, `S = i_* R𝓗_T`, `S' = i'_* R𝓗_{T'}`, `s = (-)[0]` and
`H = H ⁿ`, the composite is

`P ∘ H ∘ S ∘ s ≅ H ∘ D(P) ∘ S ∘ s ≅ H ∘ L ∘ S ∘ s ≅ H ∘ S' ∘ L ∘ s ≅ H ∘ S' ∘ D(P) ∘ s
  ≅ H ∘ S' ∘ s ∘ P`,

whose five steps are: an exact functor commutes with the cohomology of a complex
(`StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso`); the derived pullback along
an open immersion is the degreewise one
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso`, used twice, in the two
directions); **the derived excision**
`Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso`; and an exact functor
commutes with the embedding of a module as a complex in degree `0`
(`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`). Only the middle step is
mathematics; the other four are the passage between the derived category and the abelian
category, and each of them is an isomorphism *of functors* already in the library.

**Why only the object-level isomorphism is recorded.** Every factor of the chain is natural in
the coefficient module, so the composite is too; it is recorded at an object because that is
what the consumers — `Stacks.Gysin.chartClsHom` and `Stacks.Gysin.chartTargetHom` — apply it at,
and because assembling it at the level of functors would force the crossing between the two
spellings `AlgebraicGeometry.Scheme.Modules` and `SheafOfModules (structureSheafRing _)` of the
category of modules to be made at a functor equality rather than at an object.

**What is *not* here, and what is now elsewhere.** Nothing *in this file* identifies this
isomorphism with the abelian excision
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso` read across
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafFunctorLocalCohomologyIso`; that
coherence is exactly what the respelling of `Stacks.Gysin.gysinTarget` makes unnecessary **for the
`𝒪`-linear chart transports of [Stacks, Tag 0G86]** — and what it does *not* make unnecessary for
the square of [Stacks, Tag 0G87], whose right vertical arrow is the action of [Stacks, Tag 0G74]
part (2) on the de Rham differential and so lives in the abelian model. The reading of this
isomorphism through the forgetful functor to abelian sheaves, the `𝒪`-linear half of its
compatibility with that action, and the one statement that remains
(`Stacks.Gysin.SupportCohomologyRestrictAbNatural`) are in
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcisionAbelian.lean`. And
nothing here is a base-change statement for the class map of [Stacks, Tag 0G7Q] itself, which is
[Stacks, Tag 0G7U].

**That coherence is now proved.** It is
`Stacks.Gysin.supportCohomologyRestrictIso_hom_eq_localCohomologyRestrictNatIso` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcisionAbelianComparison.lean`: for
`W ⊆ Y` open, `T ⊆ Y` closed, `T' = W ∩ T` and `β = Stacks.Gysin.supportCohomologyOnIso`,

`(supportCohomologyRestrictIso W hT hTW n ℱ).hom =
  (Scheme.Modules.restrictFunctor W.ι).map (β.hom.app ℱ) ≫
    (localCohomologyRestrictNatIso T W n).hom.app ℱ ≫ β'.inv.app ((restrictFunctor W.ι).obj ℱ)`.

Its proof consists of the following steps:

* `Stacks.Perfect.SupportPushExcision.foldZeroIso` and
  `…derivedSupportedPushforwardPullbackIso_hom_app_eq_derivedExcision` of
  `StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/SupportPushExcisionFold.lean`: the
  derived excision of [Stacks, Tag 0G78] at the pushed-forward spelling **is** the comparison that
  the uniqueness of right derived functors produces from the degree-zero excision of
  `H_T^{on T} ⋙ i_*`, which is `Stacks.DerivedFunctor.foldZero` of the degreewise excision and the
  underived base change `closedSubsetPushforwardPullbackNatIso`. This is
  `Stacks.DerivedFunctor.eq_foldDerived` applied, with
  `Stacks.Cohomology.SupportedComplexes.supportedPullbackBaseChangeMap_eq_mapDerivedCategory` and
  `…supportedPullbackNatTrans_eq_derivedSupportedSectionsOnClosedPullbackNatIso` identifying the
  two factors of the fold-in. The degree-zero half was **not** missing: it is
  `Stacks.Cohomology.SupportedComplexes.closedSubsetPushforwardPullbackNatIso_comp_map_eq`, proved
  in `StacksFrontier/Topology/Sheaves/Cohomology/SupportedComplexes/LocalCohomologyExcisionCounit.lean`.
* `Stacks.Gysin.supportCohomologyOnIso_hom_app_eq_bridge` of
  `GysinSupportCohomologyOnBridge.lean`: `β` **is** the derived/classical bridge
  `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` for `H_T^{on T} ⋙ i_*`,
  with the identification `H_T^{on T} ⋙ i_* ≅ H_T` folded in by
  `CategoryTheory.NatTrans.rightDerived`. This is
  `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_postComp_app` together with
  `Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso_eq` — the three copies of
  "an exact functor commutes with `Hⁿ`" that the development carries are identified, so no fourth
  was written.
* `Stacks.Gysin.supportCohomologyPullbackIso_hom_eq_supportedSectionsRightDerivedPullback` of
  `GysinSupportCohomologyExcisionClassical.lean`: the equation in the
  `RingedSpaceModuleAdjunction.modulePullback` spelling, by
  `Stacks.DerivedIndexing.classicalExcision_eq_derivedExcision_app` and
  `Stacks.Cohomology.DerivedCompTransport.classicalExcision_natTrans_app`.
* `Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso_hom_app_modulePullback`
  and `…localCohomologyRestrictNatIso_eq_pullback`: the crossing of
  `Stacks.Gysin.modulePullbackRestrictFunctorIso` between
  `RingedSpaceModuleAdjunction.modulePullback` and
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, in degree zero and in every degree, which
  the generic lemmas above are stated at a single exact functor and so do not perform.

The transitivity of these isomorphisms over two nested opens is *not* here, but it is in the
library: `Stacks.Gysin.supportCohomologyPullbackIso_comp` for
`supportCohomologyPullbackIso` and `Stacks.Gysin.supportCohomologyRestrictCompIso_hom` for
`supportCohomologyRestrictIso`. Neither needs the composition coherence of [Stacks, Tag 0D5S]
for the *derived* pullback, which the library indeed has only for the derived pullback itself:
the two copies of
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso` surrounding the excision
cancel, so only the composition isomorphism of the *degreewise* pullback enters. See the
implementation notes of `GysinTargetExcisionComp.lean`.

## References

* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedOpenImmersion
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.SupportedFraction
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)
open StacksDraft.DerivedCategoryHomology

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Excision in degree `n`, for an open immersion of ringed spaces -/

section RingedSpaces

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]

variable (T : Set X.carrier) (hT : IsClosed T) (n : ℤ)

/-- **Excision for `i_*ℋ ⁿ_T` along an open immersion of ringed spaces.**  For `f : X' ⟶ X` an
open immersion, `T ⊆ X` closed and `T' = f^{-1}(T)`, the pullback along `f` of the degree-`n`
cohomology sheaf of `i_* R𝓗_T(ℱ[0])` is the degree-`n` cohomology sheaf of
`i'_* R𝓗_{T'}((f^*ℱ)[0])`.

This is the derived excision
`Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso` read on degree-`n`
cohomology sheaves; the module docstring lists the four passages between the derived and the
abelian category that surround it. -/
def supportCohomologyPullbackIso (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullback f).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) n).obj
          ((derivedSupportedPushforward X T hT).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).obj M))) ≅
      (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X')) n).obj
        ((derivedSupportedPushforward X' (closedSubsetPreimage f T)
            (isClosed_closedSubsetPreimage f T hT)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X')) 0).obj ((modulePullback f).obj M))) :=
  letI := preservesFiniteLimits_modulePullback_of_isOpenImmersion f
  ((mapDerivedCategoryHomologyIso (modulePullback f) n).app
      ((derivedSupportedPushforward X T hT).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X)) 0).obj M))).symm ≪≫
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X')) n).mapIso
      ((derivedPullbackOpenImmersionIso f).symm.app
          ((derivedSupportedPushforward X T hT).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) ≪≫
        (Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso f T hT).app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).obj M) ≪≫
          (derivedSupportedPushforward X' (closedSubsetPreimage f T)
              (isClosed_closedSubsetPreimage f T hT)).mapIso
            ((derivedPullbackOpenImmersionIso f).app
                ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing X)) 0).obj M) ≪≫
              ((modulePullback f).mapDerivedCategorySingleFunctor 0).app M))

end RingedSpaces

/-! ### The same for a scheme and an open subscheme -/

section Schemes

variable {Y : Scheme.{u}} (W : Y.Opens)

/-- **Pullback of modules along the ringed-space inclusion of an open subscheme is restriction
along the inclusion of that open subscheme.**  This is Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, read through the definitional
equality `AlgebraicGeometry.pullback_scheme_eq` of the pullback of modules along a morphism of
schemes with the pullback along the underlying morphism of ringed spaces.

**Why this identification and not `Stacks.Cohomology.DerivedOpenImmersion.modulePullbackJStarIso`,
which has the same source and target.**  The two are the
`CategoryTheory.Adjunction.leftAdjointUniq` comparisons of two pairs of adjunctions with the same
right adjoint `ι_*`, so they agree; but
making that agreement a *theorem* means comparing
`Stacks.Cohomology.RelativeMayerVietoris.moduleRestrictionAdjunction` with
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction` across the functor equality
`Stacks.Perfect.LocalCohomologyExcision.restrictFunctor_eq_jStar`, which is an equality of
functors whose source and target categories agree only up to unfolding, so the `eqToHom` it
produces cannot even be simplified in place.  Taking Mathlib's comparison instead makes the
excision below available along an **arbitrary** open immersion of schemes, by
`Stacks.Gysin.supportCohomologyOpenImmersionIso`, and in particular along
`AlgebraicGeometry.Scheme.homOfLE`, which is what a nested equation chart meets; see
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/ChartDataExcision.lean`.  Nothing downstream uses any
property of this identification beyond its being an isomorphism of the two functors. -/
def modulePullbackRestrictFunctorIso :
    modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) ≅
      Scheme.Modules.restrictFunctor W.ι :=
  Stacks.Perfect.CechDerivedSupportBaseChange.modulePullbackRestrictIso W

/-- **Excision for the target of the class map of [Stacks, Tag 0G7Q], for a scheme and an open
subscheme.**  The restriction to `W` of `i_*ℋ ⁿ_T(ℱ)` is `i'_*ℋ ⁿ_{W ∩ T}(ℱ|_W)`, both read in
the spelling `Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor` in which
[Stacks, Tag 0G7Q] and [Stacks, Tag 0G7S] are stated.

This is `Stacks.Gysin.supportCohomologyPullbackIso` for the ringed-space inclusion of `W`, whose
pullback is `restrictFunctor` by `Stacks.Gysin.modulePullbackRestrictFunctorIso`.  It is **the
derived excision** of [Stacks, Tag 0G78], not the abelian one; see the module docstring. -/
def supportCohomologyRestrictIso {T : Set Y} (hT : IsClosed T) (hTW : IsClosed (W.ι ⁻¹' T))
    (n : ℤ) (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor W.ι).obj ((supportCohomologySheafFunctor hT n).obj M) ≅
      (supportCohomologySheafFunctor hTW n).obj
        ((Scheme.Modules.restrictFunctor W.ι).obj M) :=
  ((modulePullbackRestrictFunctorIso W).app
      ((supportCohomologySheafFunctor hT n).obj M)).symm ≪≫
    supportCohomologyPullbackIso (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT n M ≪≫
      (supportCohomologySheafFunctor hTW n).mapIso ((modulePullbackRestrictFunctorIso W).app M)

end Schemes

/-! ### Transport along an equality of supporting closed subsets -/

/-- **The cohomology sheaf `i_*ℋ ⁿ_T(ℱ)` depends on `T` only as a subset.**  Two closed subsets
that are equal give the same sheaf, the proofs of closedness being proofs of one proposition
once the subsets are identified.  This replaces, for this spelling of the cohomology sheaf, the
transport `congrArg (fun T => (localCohomologyOn _ T _).obj _)` that the right derived functor
admits because it carries no closedness hypothesis.

Stated at `Stacks.Perfect.SupportedFraction.supportCohomologySheaf` rather than at
`supportCohomologySheafFunctor` applied to an object — the two are equal by definition, by
`Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor_obj` — because that is the
spelling of the target of
`Stacks.Perfect.SupportedFraction.supportedFractionSource`, and a transport whose source is
spelled one way and whose target is spelled the other cannot be rewritten in: `rw` re-typechecks
its goal at a transparency at which the two spellings are not interchangeable. -/
theorem supportCohomologySheaf_congr {Y : Scheme.{u}} {T T' : Set Y} (hTT' : T = T')
    (hT : IsClosed T) (hT' : IsClosed T') (n : ℤ) (F : Y.Modules) :
    supportCohomologySheaf hT F n = supportCohomologySheaf hT' F n := by
  subst hTT'
  rfl

end Stacks.Gysin

end
