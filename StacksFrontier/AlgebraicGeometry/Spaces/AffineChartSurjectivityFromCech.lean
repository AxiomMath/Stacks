module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstVanishingAndSections

/-!
# Surjectivity on affine-chart sections from Čech vanishing on finite affine families

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Eleven places
in this tree carry, byte-identically, one uniform hypothesis in the shape of Descent,
Proposition 03DW:

    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)))

— five binders in `StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivity`, three in
`StacksFrontier.AlgebraicGeometry.Spaces.CokernelShortExactEssSurj` and three in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentColimitsEssSurj`.  Its consumers are
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_h03DW`,
`AlgebraicGeometry.Space.surjective_g_val_app_of_shortExact_of_h03DW`,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_essSurj_of_h03DW` and the colimit and
short-exact clauses alongside them.

**This file discharges that uniform hypothesis from Čech vanishing alone.**  It is not the
only route to it:
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isCartesianOnAffineCharts_kernel` of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartSurjectivityFromAmitsur.lean` proves the same
uniform statement with no hypothesis at all, by computing the first Čech cohomology of the kernel
along a finite affine covering family as the degree-one cohomology of an Amitsur complex.  What is
below remains the shortest route *from* a Čech vanishing input; it is kept because it names the
Stacks 03F8 reduction explicitly.  The input it needs
is the vanishing of the *first* Čech cohomology group of a module cartesian on affine charts,
for the *finite affine* covering families of an *affine* chart — that is, the étale instance of
Descent, Lemma 03FJ in degree one.  Everything else is already in this repository, and the
reduction consumes it rather than deferring it:

* the local-character argument, the 1-cocycle, its coboundary and both uses of the sheaf
  condition are Cohomology on Sites, Lemma 03F8, proved in full generality for an arbitrary site
  as `Stacks.CechSite.surjective_on_sections_of_isZero_cechCohomology`.  **03F8 does not appear
  in the dependency list recorded for 03DW**;
* the cofinality of the finite affine covering families among all covering sieves of an affine
  chart is `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement`, itself resting
  on the dense-subsite theorem Stacks 04JS;
* the passage from `𝒪_F`-modules to abelian sheaves is exact in the two senses needed:
  `Stacks.SheafOfModules.EpiMono.preservesEpimorphismsToSheaf` for epimorphisms and Mathlib's
  `PreservesFiniteLimits (SheafOfModules.toSheaf R)` for the kernel.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_preZeroHypercover`: a covering sieve
  of an affine étale chart is refined by a finite affine covering family, presented as a
  `CategoryTheory.PreZeroHypercover` at index universe `0`.
* `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_covering`: an affine étale chart
  *has* a finite affine covering family.  This is not decoration: it is what makes the Čech
  hypothesis of the main theorem quantify over a non-empty domain, hence a real assumption
  rather than a vacuous one.
* `AlgebraicGeometry.Space.shortExact_toSheaf_kernelSequence`: for an epimorphism `q` of
  `𝒪_F`-modules, the sequence `0 → ker q → P → Q → 0` of underlying abelian sheaves is short
  exact.
* `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian`: **the uniform form
  of Stacks 03DW, from Čech vanishing.**

## Implementation notes

**What is assumed, and what is not.**  The hypothesis `hCech` of the main theorem is the étale,
degree-one, finite-family instance of Descent, Lemma 03FJ.

**Lemma 03FJ is proved.**  What is registered:

* 03FJ, eight sites — `AlgebraicGeometry.cechComplexIsoAmitsurStandardCovering` and
  `AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf` (case (a), a standard
  covering of an object of `Over S`, **unconditional**), and cases (b) and (c) on the two small
  sites in `StacksFrontier/AlgebraicGeometry/Topologies/CechAmitsurSmallSites.lean`, of which
  `AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf_smallEtale` is the
  positive-degree vanishing clause;
* 03FI, twelve sites, among them `Stacks.CechSite.coproductRefinement` part (2);
* 023M, in *every* degree and not only in degrees `-1` and `0`, at the two
  `amitsurExtendedCochainComplex_acyclic_of_faithfullyFlat` declarations of
  `StacksFrontier/AlgebraicGeometry/Descent/Module/AmitsurAcyclic.lean` and
  `StacksFrontier/AlgebraicGeometry/Descent/ModuleEquivalence/FaithfullyFlatAmitsur.lean`, whose
  conclusion is `(amitsurExtendedCochainComplex R A M).Acyclic` for a faithfully flat `A`.

Only 023F has none, and it is a *section* reference rather than a result.  The Zariski analogue
is also proved, as `@[stacks 01X9]
AlgebraicGeometry.isZero_cechCohomology_of_isStandardOpenCover`.

**The site transport is proved; `hCech` is still not a consequence of it.**  The transport of
case (a) from `Over (chartScheme W)` to the small étale site of the algebraic space at the
affine chart `W` is
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_associatedPresheafIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartCechVanishing.lean`.  It needs neither
`AlgebraicGeometry.Space.chartSchemeEquivalence` nor
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` nor the private family-moving helpers
of `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineCohomologyVanishing.lean`: the
comparison is a change of *slice depth*, the Čech
complex of a family with target `W` being built from products in `Over W` while the Čech complex
of a family with target an object of `Over (chartScheme W)` is built one slice deeper.  So the
family is read in `Over W` with target the terminal object and
`Stacks.CechSite.cechCohomologyIsoOfFunctor` is applied twice, along
`CategoryTheory.Over.forget W` and along
`AlgebraicGeometry.Space.SmallEtale.sliceToOver` — which is `CategoryTheory.Over.post` of the
projection taking a chart to its scheme — with
`Stacks.Sites.preservesLimit_fibreProducts_overPost` discharging both hypotheses.  The covering
condition is enough for the `jointly_surjective` field of
`AlgebraicGeometry.IsStandardCovering`, by
`AlgebraicGeometry.Space.SmallEtale.iUnion_range_eq_univ_of_sieve₀_mem_topology`.

Two things still separate that theorem from `hCech`, and neither of them is an assembly step.

*The coefficients.*  Every form of 03FJ demands coefficients `𝓕ᵃ` for a **quasi-coherent** `𝓕`
on `chartScheme W`, whereas the module `K` of `hCech` is only assumed
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`.  That gap is **not** the implication
between cartesianness and quasi-coherence, which is proved in both directions and
unconditionally —
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`.  It is the
*essential surjectivity* of `(-)ᵃ` on the slice at an affine chart: the hypothesis `hEss` of
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj`, which produces from
`K` a quasi-coherent `M` on the chart's scheme together with an isomorphism
`sliceModule W K ≅ sliceAssociatedModule W M`.  That is not available in this tree.  It is not
blocked by a localization argument: the global presentation *on the slice* at an affine chart is
proved and unconditional, `AlgebraicGeometry.Space.hasGlobalPresentation_over_of_isAffine` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSpaceGlobalPresentation.lean`; so are the free step
and the full faithfulness of Tag 0GN7 on that slice, in
`StacksFrontier/AlgebraicGeometry/Spaces/SliceAssociatedModuleSheafCondition.lean`.  The
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SliceAssociatedModuleEssSurj.lean` record what is left:
that `M ↦ Mᵃ` on the slice carries a cokernel of free modules to the cokernel, which on the
small étale site of a *scheme* is formal because the associated module there is a
`CategoryTheory.SheafOfModules.pullback`, a left adjoint, and which on the slice is owed because
`AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule` is built by hand instead.  There is a
second route: essential surjectivity for the small étale site of a *scheme* is proved with no
hypothesis,
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`, it is already applied at
the chart's scheme over `AlgebraicGeometry.associatedBigEtaleSite B` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeModuleSections.lean`, and
`AlgebraicGeometry.Space.exists_isQuasicoherent_iso_over_of_isAffine` of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartSchemeModuleComparison.lean` already produces,
for a quasi-coherent `𝒪_F`-module and an affine chart, a quasi-coherent module on the chart's
scheme whose `AlgebraicGeometry.Space.representedAssociatedModule` is the chart restriction.
What that route still owes is the comparison of that associated module, taken on the small étale
site of the chart *space*, with `AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule` across
Tag 04M0 and `AlgebraicGeometry.Space.representedSmallEtaleEquivalence`; no declaration in this
tree mentions both.

Granting `hEss` at the chart `W` and nothing else, the Čech vanishing for the abelian presheaf
underlying `K` *is* proved, in exactly the coefficient spelling `hCech` uses, as
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_essSurj_at`.

*The index universe.*  The transport is stated for a
`CategoryTheory.PreZeroHypercover.{u}`, because
`AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf` is stated at the single
universe of its schemes, while the `hCech` of
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian` quantifies over
`PreZeroHypercover.{0}`.  Crossing that gap needs no isomorphism between the Čech complex of a
family and the Čech complex of its `ULift` reindexing (which is not available for
`Stacks.CechSite.cechComplex`), and none is used: the cofinal system that Stacks 03F8 is applied
to is chosen by the caller, so the refinement is produced at index universe `u` to begin with,
by `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_preZeroHypercover_univ` — the lifted
family has the *same arrows*, hence literally the same generated sieve, and no Čech complex is
reindexed.  `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian_univ` is
the resulting statement, and
`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartSurjectivityFromEssSurj.lean` composes it with
the transport, leaving `hEss` as the single open input of this route to Stacks 03DW on
this site.  Stacks 03DW itself, in the uniform form, is a theorem of this development by the
Amitsur route named at the top of this note, so nothing depends on `hEss`.

The Čech cohomology this file names is
`Stacks.CechSite.cechCohomology` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/ComplexOfAFamily.lean`, the same construction
the 03FJ declarations use — `StacksFrontier/AlgebraicGeometry/Topologies/CechAmitsurSmallSites.lean`
and `StacksFrontier/AlgebraicGeometry/Topologies/CechVanishingStandardCovering.lean` both
`open Stacks.CechSite` — so no comparison of two Čech constructions is owed.

**Affineness of the chart is in `hCech` deliberately.**  The same hypothesis quantified over
*every* chart `W` would be stronger than anything needed below and almost certainly false: for a
non-affine `W` the finite fibre products of the members of a covering family need not be affine,
so `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` says nothing about the sections of the
module over them and the Čech complex is not the base change of the sections over `W`.

**Stacks 03F8 must be applied at explicit universes.**  Written
`Stacks.CechSite.surjective_on_sections_of_isZero_cechCohomology.{0, u, u + 1, u}`: the index
universe of the covering families is `0`, the morphisms of the small étale site of `F` are in
`Type u`, its objects in `Type (u + 1)`, and the coefficients are `AddCommGrpCat.{u}`.  Left
implicit, the coefficient universe is still a metavariable when `CategoryTheory.HasSheafify` is
synthesized, instance search reaches the generic sheafification — which needs the coefficient
universe to dominate the universe of the objects — and solves it at `u + 1`; the application
then fails with `failed to solve universe constraint u =?= u + 1` on `UnivLE.{u + 1, u}`.  The
site's own `CategoryTheory.HasSheafify` for `AddCommGrpCat.{u}` is available and is what the
annotation selects.

**Two things that cost nothing and are worth knowing.**  The index type of the refinement
produced by `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement` is in `Type`,
which is exactly `CategoryTheory.PreZeroHypercover.{0}`, so no reindexing is performed here.
And the conclusion of 03F8 — surjectivity of the abelian-sheaf map on sections — is
*definitionally* the surjectivity of `q.val.app (op W)`, so the final transport is `exact` with
no transport lemma; the two spellings differ syntactically and not otherwise.

**No new definition, structure, class or instance is introduced.**  In particular the finite
products in `CategoryTheory.Over W` that the Čech complex needs are produced by a local
`letI`/`have` from the terminal object of the slice and the pullbacks of the site
(`AlgebraicGeometry.Space.SmallEtale.instHasPullbacks`), and *not* registered as a global
`CategoryTheory.Limits.HasFiniteLimits` instance: a global instance here would oblige every
consumer to a full library build, and the covering-family predicate is written out in the
binder rather than abbreviated by a definition.

**No `@[stacks]` attribute is claimed.**  The conclusion is Stacks 03DW's uniform form and the
hypothesis is Stacks 03FJ; tagging either would report an unproved tag as proved.  The module
universe is `u`, as at every one of the eleven binder sites, because the statement names
`CategoryTheory.Limits.kernel` of `𝒪_F`-modules.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03F8](https://stacks.math.columbia.edu/tag/03F8)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### Finite affine covering families of an affine chart -/

/-- **A covering sieve of an affine étale chart is refined by a finite affine covering family,
presented as a `CategoryTheory.PreZeroHypercover` at index universe `0`.**

This is `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement` with its data
packaged as a pre-`0`-hypercover and its three side conditions — finiteness of the index type,
affineness of the members, and the covering property — grouped into the conjunction that
`Stacks.CechSite.surjective_on_sections_of_isZero_cechCohomology` asks of a cofinal system.  No
reindexing takes place: the refinement's index type is already in `Type`. -/
theorem SmallEtale.exists_finite_affine_preZeroHypercover (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (R : Sieve W) (hR : R ∈ SmallEtale.topology B S hS F W) :
    ∃ E : PreZeroHypercover.{0} W,
      (Finite E.I₀ ∧
          (∀ i, IsAffine
            ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) ∧
          E.sieve₀ ∈ SmallEtale.topology B S hS F W) ∧
        E.sieve₀ ≤ R := by
  obtain ⟨ι, hι, V, f, haff, hle, hmem⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS F W hW R hR
  exact ⟨⟨ι, V, f⟩, ⟨hι, haff, hmem⟩, hle⟩

universe v w

/-- **Reindexing a family of arrows along `ULift.down` leaves the presieve it generates
unchanged.** -/
private theorem ofArrows_ulift {C : Type*} [Category C] {X : C} {ι : Type v} (Y : ι → C)
    (f : ∀ i, Y i ⟶ X) :
    Presieve.ofArrows (fun i : ULift.{w} ι => Y i.down) (fun i => f i.down) =
      Presieve.ofArrows Y f := by
  funext Z
  ext g
  constructor
  · rintro ⟨i⟩
    exact ⟨i.down⟩
  · rintro ⟨i⟩
    exact ⟨ULift.up i⟩

/-- **A covering sieve of an affine étale chart is refined by a finite affine covering family
presented at index universe `u`**, the universe of the schemes.

This is `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_preZeroHypercover` with the
index type of the refinement lifted from `Type` to `Type u`; the lifted family has the same
arrows, hence the same generated sieve. -/
theorem SmallEtale.exists_finite_affine_preZeroHypercover_univ (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (R : Sieve W) (hR : R ∈ SmallEtale.topology B S hS F W) :
    ∃ E : PreZeroHypercover.{u} W,
      (Finite E.I₀ ∧
          (∀ i, IsAffine
            ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) ∧
          E.sieve₀ ∈ SmallEtale.topology B S hS F W) ∧
        E.sieve₀ ≤ R := by
  obtain ⟨ι, hι, V, f, haff, hle, hmem⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS F W hW R hR
  have _ : Finite ι := hι
  have hsieve : (PreZeroHypercover.mk (ULift.{u} ι) (fun i => V i.down)
        (fun i => f i.down) : PreZeroHypercover.{u} W).sieve₀ = Sieve.ofArrows V f := by
    change Sieve.generate _ = Sieve.generate _
    rw [ofArrows_ulift]
  exact ⟨⟨ULift.{u} ι, fun i => V i.down, fun i => f i.down⟩,
    ⟨inferInstance, fun i => haff i.down, hsieve ▸ hmem⟩, hsieve ▸ hle⟩

/-- **An affine étale chart has a finite affine covering family**, presented as a
`CategoryTheory.PreZeroHypercover` at index universe `0`. -/
theorem SmallEtale.exists_finite_affine_covering (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    ∃ E : PreZeroHypercover.{0} W,
      Finite E.I₀ ∧
        (∀ i, IsAffine
          ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) ∧
        E.sieve₀ ∈ SmallEtale.topology B S hS F W := by
  obtain ⟨E, hE, -⟩ := SmallEtale.exists_finite_affine_preZeroHypercover W hW ⊤
    ((SmallEtale.topology B S hS F).top_mem W)
  exact ⟨E, hE⟩

/-! ### The kernel sequence of an epimorphism, as abelian sheaves -/

/-- **For an epimorphism `q` of `𝒪_F`-modules, the sequence `0 → ker q → P → Q → 0` of
underlying abelian sheaves is short exact.** -/
theorem shortExact_toSheaf_kernelSequence {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q)
    (hq : Epi q) :
    ((ShortComplex.kernelSequence q).map (SheafOfModules.toSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)))).ShortExact := by
  have hepi : Epi (ShortComplex.kernelSequence q).g := hq
  exact { exact := ShortComplex.Exact.map_of_mono_of_preservesKernel
            (ShortComplex.kernelSequence_exact q) _ inferInstance inferInstance
          mono_f := (SheafOfModules.toSheaf _).map_mono _
          epi_g := (SheafOfModules.toSheaf _).map_epi _ }

/-! ### The uniform form of Stacks 03DW -/

/-- **The uniform form of Descent, Proposition 03DW, from Čech vanishing.**  An epimorphism of
`𝒪_F`-modules whose kernel is cartesian on affine charts is surjective on the sections over
every affine étale chart, granted the vanishing of the first Čech cohomology group of a
cartesian module on the finite affine covering families of an affine chart.

`hCech` is the étale instance of Descent, Lemma 03FJ in degree one; the finite products in the
slice over `W` that the Čech complex is built from come from the terminal object of the slice and
the pullbacks of the small étale site. -/
theorem surjective_val_app_of_epi_of_kernel_isCartesian
    (hCech : ∀ K : Modules.{u, u} B S hS F hF, IsCartesianOnAffineCharts K →
      ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        ∀ E : PreZeroHypercover.{0} W, Finite E.I₀ →
          (∀ i, IsAffine
            ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) →
          E.sieve₀ ∈ SmallEtale.topology B S hS F W →
          letI : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
          IsZero (Stacks.CechSite.cechCohomology E
            ((sheafToPresheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}).obj
              ((SheafOfModules.toSheaf
                ((Stacks.SheafOfModules.Tensor.ringSheaf
                  (smallEtaleRingedSite B S hS F hF).O))).obj K)) 1)) :
    ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)) := by
  intro P Q q hq hker W hW
  have hfl : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have hprod : ∀ E : PreZeroHypercover.{0} W,
      E ∈ {E : PreZeroHypercover.{0} W | Finite E.I₀ ∧
          (∀ i, IsAffine
            ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) ∧
          E.sieve₀ ∈ SmallEtale.topology B S hS F W} →
      ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
        HasProduct fun a ↦ Over.mk (E.f (i a)) := fun _ _ _ _ ↦ inferInstance
  exact Stacks.CechSite.surjective_on_sections_of_isZero_cechCohomology.{0, u, u + 1, u}
    (SmallEtale.topology B S hS F) _ (shortExact_toSheaf_kernelSequence q hq) W
    {E : PreZeroHypercover.{0} W | Finite E.I₀ ∧
      (∀ i, IsAffine
        ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) ∧
      E.sieve₀ ∈ SmallEtale.topology B S hS F W}
    (fun _ hE ↦ hE.2.2)
    (fun R hR ↦ SmallEtale.exists_finite_affine_preZeroHypercover W hW R hR) hprod
    (fun E hE ↦ hCech (kernel q) hker W hW E hE.1 hE.2.1 hE.2.2)

/-- **The uniform form of Descent, Proposition 03DW, from Čech vanishing for families indexed
at the universe of the schemes.**

This is `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian` with `hCech`
read at `CategoryTheory.PreZeroHypercover.{u}` instead of
`CategoryTheory.PreZeroHypercover.{0}`. -/
theorem surjective_val_app_of_epi_of_kernel_isCartesian_univ
    (hCech : ∀ K : Modules.{u, u} B S hS F hF, IsCartesianOnAffineCharts K →
      ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        ∀ E : PreZeroHypercover.{u} W, Finite E.I₀ →
          (∀ i, IsAffine
            ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) →
          E.sieve₀ ∈ SmallEtale.topology B S hS F W →
          letI : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
          IsZero (Stacks.CechSite.cechCohomology E
            ((sheafToPresheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}).obj
              ((SheafOfModules.toSheaf
                ((Stacks.SheafOfModules.Tensor.ringSheaf
                  (smallEtaleRingedSite B S hS F hF).O))).obj K)) 1)) :
    ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)) := by
  intro P Q q hq hker W hW
  have hfl : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have hprod : ∀ E : PreZeroHypercover.{u} W,
      E ∈ {E : PreZeroHypercover.{u} W | Finite E.I₀ ∧
          (∀ i, IsAffine
            ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) ∧
          E.sieve₀ ∈ SmallEtale.topology B S hS F W} →
      ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
        HasProduct fun a ↦ Over.mk (E.f (i a)) := fun _ _ _ _ ↦ inferInstance
  exact Stacks.CechSite.surjective_on_sections_of_isZero_cechCohomology.{u, u, u + 1, u}
    (SmallEtale.topology B S hS F) _ (shortExact_toSheaf_kernelSequence q hq) W
    {E : PreZeroHypercover.{u} W | Finite E.I₀ ∧
      (∀ i, IsAffine
        ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) ∧
      E.sieve₀ ∈ SmallEtale.topology B S hS F W}
    (fun _ hE ↦ hE.2.2)
    (fun R hR ↦ SmallEtale.exists_finite_affine_preZeroHypercover_univ W hW R hR) hprod
    (fun E hE ↦ hCech (kernel q) hker W hW E hE.1 hE.2.1 hE.2.2)

end AlgebraicGeometry.Space

end
