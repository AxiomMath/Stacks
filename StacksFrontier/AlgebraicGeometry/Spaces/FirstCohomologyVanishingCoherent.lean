module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingAffine
public import StacksFrontier.CategoryTheory.Triangulated.ZeroRetract
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# First cohomology of a coherent module from the dévissage criterion

Let `X` be a Noetherian algebraic space. The dévissage criterion [Stacks, Tag 07UT] reduces a
property of coherent `𝒪_X`-modules to the three hypotheses recalled in its own statement. Here
the criterion is run for the property `H¹(X, 𝓕) = 0`, and the hypotheses which do not depend
on `X` beyond its being Noetherian are discharged: the zero module, closure under extensions of
coherent modules, and descent of the property from a finite direct sum to a summand. What is
left over is hypothesis (3) of the criterion, the existence of generic subsheaves, which is
where the geometry of the particular `X` enters.

This is step (2) of the proof of [Stacks, Tag 07VP] — "condition (1) comes from the long exact
cohomology sequence, condition (2) because `H¹(X, -)` is additive". The tag 07VP itself is
**not** proved here; see the discussion at the end of this docstring.

## Main definitions

* `AlgebraicGeometry.Space.FirstCohomologyVanishes` is the property of a single `𝒪_X`-module
  that its first cohomology on `X` vanishes, read at the module universe of the structure
  rings. It is the pointwise form of
  `AlgebraicGeometry.Space.FirstCohomologyVanishingAtRingUniverse`, which is its restriction to
  the quasi-coherent modules and universally quantified; the two are related by
  `AlgebraicGeometry.Space.firstCohomologyVanishingAtRingUniverse_iff`.
* `AlgebraicGeometry.Space.firstCohomologyDeltaFunctor` is the cohomology of `𝒪_X`-modules at
  that same universe, packaged as a cohomological `δ`-functor, hence carrying the long exact
  cohomology sequence of a short exact sequence of modules.

## Main results

* `AlgebraicGeometry.Space.isZero_firstCohomology_of_isCoherent_of_hasGenericSubsheaves`: on a
  Noetherian algebraic space whose first-cohomology vanishing has generic subsheaves in the
  sense of `AlgebraicGeometry.Space.HasGenericSubsheaves`, every coherent `𝒪_X`-module has
  vanishing first cohomology.

## Implementation notes

*Which universe, and why a new `δ`-functor.* The dévissage criterion [Stacks, Tag 07UT] is
stated for `AlgebraicGeometry.Space.Modules.{u, u}`, the `𝒪_X`-modules whose sections lie in
the universe of the structure rings; this is the one universe at which the direct image of
modules exists, and it is the universe at which
`AlgebraicGeometry.Space.FirstCohomologyVanishingAtRingUniverse` reads the vanishing hypothesis
of [Stacks, Tag 07UY]. The objects of the small étale site of `X` live one universe higher, so
the first cohomology there is the first right derived functor of
`Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}`. That instantiation is
not reachable through `Stacks.Cohomology.SiteModules.globalModuleCohomology`, whose module
universe is forced to absorb the universe of the site, and so neither is it reachable through
`Stacks.Cohomology.SiteModules.cohomologyDeltaFunctor`. The `δ`-functor is therefore built here
by applying the generic
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives` to the global-sections
functor at the universes which do occur, exactly as `cohomologyDeltaFunctor` does at its own.

*The three hypotheses.* The zero module is handled by additivity of a `δ`-functor in each
degree. Closure under extensions is exactness of `H¹(𝓕₁) ⟶ H¹(𝓕₂) ⟶ H¹(𝓕₃)`, a three-term
stretch of the long exact sequence, so a module whose two neighbours in a short exact sequence
have vanishing `H¹` has vanishing `H¹` itself; coherence of the three terms is not used.
Descent from a direct sum to a summand is not additivity but the weaker fact that a summand is
a retract: for `r ≥ 1` the module `𝓕` is a retract of `⨁_{i < r} 𝓕` through
`CategoryTheory.Limits.biproduct.ι` and `CategoryTheory.Limits.biproduct.π`, an additive
functor carries that retraction to a retraction, and a retract of a zero object is zero.

### What this route to Tag 07VP still lacks

[Stacks, Tag 07VP] asserts that a Noetherian algebraic space receiving a finite surjective
morphism from an affine scheme is affine, and its proof has three steps. The result of this
file is the part of step (2) which does not involve the morphism. Two further steps are
missing, and the second of them is missing from the development entirely.

* Hypothesis (3) of the criterion, `AlgebraicGeometry.Space.HasGenericSubsheaves` for
  first-cohomology vanishing, is what the finite surjection `f : Y ⟶ X` from an affine `Y`
  supplies: the coherent module with full support on a reduced irreducible closed subspace
  `i : Z ⟶ X` is `f'_*𝒪_{Z'}` for the base change `f' : Z' ⟶ Z` of `f`, by
  `AlgebraicGeometry.Space.isCoherent_modulePushforward_structureSheaf_preimage` and
  `AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_structureSheaf_preimage_eq_univ`
  ([Stacks, Tag 0GF7]), and the submodule attached to a nonzero quasi-coherent ideal `ℐ` is
  `f'_*ℐ'` for the image `ℐ'` of `(f')^*ℐ`, by
  `AlgebraicGeometry.Space.idealSmul_pushforward_eq_of_isQuasicoherentOnSite`
  ([Stacks, Tag 0GF8]). The vanishing of `H¹(X, i_*f'_*ℐ')` then comes from
  `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isAffineHom`
  ([Stacks, Tag 073H]) and the Leray collapse
  `Stacks.Cohomology.Leray.nonempty_cohomologyIso_pushforward` ([Stacks, Tag 0733]). Of those
  four the last is unconditional, but the first carries a hypothesis `hchart` and the third a
  hypothesis `h03DW` which are the same statement: the étale-site analogue of
  [Stacks, Tag 01XC], that along an affine morphism the higher direct images of a quasi-coherent
  module vanish on every étale scheme chart of the target. Both label it [Stacks, Tag 03DW], and
  it has no carrier in this development. The three declarations which do carry `@[stacks 03DW]`
  — `AlgebraicGeometry.BigFppfOver.hZeroBaseAssociatedModuleAddEquiv`,
  `AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso` and
  `AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso` — prove the comparison of the
  cohomology of a quasi-coherent module on the big and small sites, which is a different
  assertion of that tag and does not discharge the chart statement. So this step cannot be
  completed unconditionally as its inputs now stand.
* The passage from coherent to quasi-coherent modules, by
  `AlgebraicGeometry.Space.isFiltered_and_nonempty_isColimit_coherentSubobjectCocone`
  ([Stacks, Tag 07UV]) and
  `AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_globalSections`
  ([Stacks, Tag 073E]), which both are proved unconditionally. The one gap is that 073E is
  stated for the abelian-sheaf cohomology `(Sheaf.Γ J Ab).rightDerived p`, so it has to be
  transported along `ModuleSheafCohomology.globalSectionsComparisonIso` ([Stacks, Tag 03FD])
  and `Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology`; no lemma in the library
  composes those two.
* Finally [Stacks, Tag 07V6], Serre's criterion for affineness of an algebraic space, which
  turns the vanishing of `H¹` on all quasi-coherent modules into affineness. It is proved, in
  the situation of [Stacks, Tag 07UY], as
  `AlgebraicGeometry.Space.CohomologyVanishingSituation.isAffineSpace`
  (`StacksFrontier/AlgebraicGeometry/Spaces/AffinenessCriteria.lean`), and its neighbours
  [Stacks, Tag 07V4] and [Stacks, Tag 07V5] are proved unconditionally as
  `…CohomologyVanishingSituation.universallyInjective_toSpecGlobalFunctionsOverIntegers` and
  `…CohomologyVanishingSituation.isSeparated_toSpecGlobalFunctions`.
  [Stacks, Tag 07VP] itself is proved by another route, as
  `AlgebraicGeometry.Space.isAffineSpace_of_isFinite_of_isSurjective`
  (`StacksFrontier/AlgebraicGeometry/Spaces/FiniteSurjectiveAffineSource.lean`), and not through
  this file.

## References

* [Stacks Project, Tag 07VP](https://stacks.math.columbia.edu/tag/07VP)
* [Stacks Project, Tag 07UT](https://stacks.math.columbia.edu/tag/07UT)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 07V6](https://stacks.math.columbia.edu/tag/07V6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- Vanishing of the first cohomology of a single `𝒪_X`-module, read at the module universe of
the structure rings.

This is the pointwise form of `AlgebraicGeometry.Space.FirstCohomologyVanishingAtRingUniverse`,
the vanishing hypothesis of [Stacks, Tag 07UY]: that one quantifies this over the quasi-coherent
modules. The pointwise form is what the dévissage criterion [Stacks, Tag 07UT] takes as its
property of coherent modules. -/
def FirstCohomologyVanishes (M : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  have := enoughInjectives_modules B S hS X.1 X.2
  IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj M)

/-- The vanishing hypothesis of [Stacks, Tag 07UY] at the module universe of the structure rings
is the pointwise vanishing `AlgebraicGeometry.Space.FirstCohomologyVanishes` quantified over the
quasi-coherent modules. -/
theorem firstCohomologyVanishingAtRingUniverse_iff :
    FirstCohomologyVanishingAtRingUniverse B S hS X ↔
      ∀ M : Modules.{u, u} B S hS X.1 X.2, M.IsQuasicoherentOnSite →
        FirstCohomologyVanishes B S hS X M :=
  Iff.rfl

/-- The cohomology of `𝒪_X`-modules at the module universe of the structure rings, as a
cohomological `δ`-functor: the long exact cohomology sequence of a short exact sequence of
`𝒪_X`-modules, with its connecting maps.

`Stacks.Cohomology.SiteModules.cohomologyDeltaFunctor` is the same construction, but its module
universe absorbs the universe of the site and so cannot be the universe of the structure rings;
see this file's implementation notes. -/
def firstCohomologyDeltaFunctor :
    CategoryTheory.DeltaFunctor (Modules.{u, u} B S hS X.1 X.2)
      (ModuleCat.{u + 1} (GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) :=
  have := enoughInjectives_modules B S hS X.1 X.2
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- **Step (2) of the proof of [Stacks, Tag 07VP].** On a Noetherian algebraic space `X` for
which first-cohomology vanishing has generic subsheaves — hypothesis (3) of the dévissage
criterion [Stacks, Tag 07UT] — every coherent `𝒪_X`-module has vanishing first cohomology.

The remaining three hypotheses of the criterion are discharged from the long exact cohomology
sequence and additivity, as the source says: the zero module because a `δ`-functor is additive
in each degree, closure under extensions of coherent modules because `H¹(𝓕₁) ⟶ H¹(𝓕₂) ⟶ H¹(𝓕₃)`
is exact, and descent from a finite direct sum to a summand because a summand is a retract and
a retract of a zero object is zero.

This is **not** [Stacks, Tag 07VP]: the generic subsheaves are a hypothesis here, and the tag
needs besides them the passage from coherent to quasi-coherent modules and Serre's criterion for
affineness [Stacks, Tag 07V6]. See this file's docstring for the three missing steps. -/
theorem isZero_firstCohomology_of_isCoherent_of_hasGenericSubsheaves
    (noeth : IsNoetherian B S hS B.contains_terminal X.1)
    (generic : HasGenericSubsheaves B S hS X (FirstCohomologyVanishes B S hS X))
    (F : Modules.{u, u} B S hS X.1 X.2) (coherent : IsCoherent B S hS X.1 X.2 F) :
    FirstCohomologyVanishes B S hS X F := by
  refine property_of_isCoherent_of_hasGenericSubsheaves B S hS X
    (FirstCohomologyVanishes B S hS X) noeth (fun M hM => ?_) (fun E hE _ _ _ h₁ h₃ => ?_)
    (fun G _ r hr h => ?_) generic F coherent
  · have := (firstCohomologyDeltaFunctor B S hS X).additive 1
    exact ((firstCohomologyDeltaFunctor B S hS X).functor 1).map_isZero hM
  · exact ((firstCohomologyDeltaFunctor B S hS X).exact_map hE 1).isZero_X₂_iff.2
      ⟨h₁.eq_of_src _ _, h₃.eq_of_tgt _ _⟩
  · have := enoughInjectives_modules B S hS X.1 X.2
    set Φ := (globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1 with hΦ
    exact IsZero.of_retract h
      { i := Φ.map (biproduct.ι (fun _ : Fin r => G) ⟨0, hr⟩)
        r := Φ.map (biproduct.π (fun _ : Fin r => G) ⟨0, hr⟩)
        retract := by rw [← Φ.map_comp, biproduct.ι_π_self, Φ.map_id] }

end AlgebraicGeometry.Space

end

end
