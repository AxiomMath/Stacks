module

public import StacksFrontier.AlgebraicGeometry.Limits.Descending.InfiniteProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineHypercoverRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCechVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSchemeSiteLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCohomologyBridge
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings

/-!
# Stacks 03F9 at the affine charts of the small étale site of an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `K` be
an `𝒪_F`-module which is quasi-coherent on the small étale site.  This file proves that the
positive-degree sheaf cohomology of the abelian sheaf underlying `K` vanishes over every
**affine** étale chart of `F`.

The proof is the Čech criterion of [Stacks, Tag 03F9] applied to the collection of affine
charts and the collection of finite affine covering families of an affine chart.  All four of
its hypotheses are discharged here:

* `hProducts` — the iterated fibre products of a covering family exist, the slice of the site at
  a chart having finite limits;
* `hCovObjects` — the target, the members and the iterated fibre products of such a family are
  affine charts again;
* `hCovCofinal` — the finite affine covering families are cofinal among the coverings of an
  affine chart, which is Stacks 0218 on this site;
* `hCech` — the positive-degree Čech cohomology of the coefficient presheaf vanishes on such a
  family, which is the `Ȟ^p = 0` clause of Descent, Lemma 03FJ, proved unconditionally as
  `AlgebraicGeometry.Space.isZero_cechCohomology_of_isQuasicoherentOnSite`.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.affineChartCov` — the collection `Cov` of
  [Stacks, Tag 03F9] used here: the finite covering families of an affine chart all of whose
  members are affine charts.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isAffine_chartScheme_piObj` — the third clause of
  `hCovObjects`: an iterated fibre product of affine charts over an affine chart is an affine
  chart.
* `AlgebraicGeometry.Space.SmallEtale.affineChartCov_covObjects` and
  `AlgebraicGeometry.Space.SmallEtale.affineChartCov_cofinal` — the hypotheses `hCovObjects` and
  `hCovCofinal` of [Stacks, Tag 03F9], verbatim.
* `AlgebraicGeometry.Space.SmallEtale.isZero_sheafH'_of_isZero_cechCohomology` — **[Stacks, Tag
  03F9] on this site, at the affine charts**: an abelian sheaf with vanishing positive-degree
  Čech cohomology on the finite affine covering families has vanishing positive-degree
  cohomology over every affine chart.
* `AlgebraicGeometry.Space.isZero_sheafH'_of_isQuasicoherentOnSite` — **the positive-degree
  sheaf cohomology of a quasi-coherent `𝒪_F`-module vanishes over every affine étale chart**, in
  Mathlib's `CategoryTheory.Sheaf.H'` spelling.

## Implementation notes

*No small model is needed.*  The `@[stacks 03F9]` declaration
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero` does ask `Small.{u}` of the
site, which the small étale site of an algebraic space does not carry — what it carries is
`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`, essential smallness at `u`, its
objects living in `Type (u + 1)`.  But smallness is used there for one thing only, producing the
homological inputs, and the criterion it reduces to,
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives`, is public
and takes those inputs as instances instead.  All four are available on this site at the
coefficient universe `u`:

* `CategoryTheory.EnoughInjectives` is
  `AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtale`;
* `CategoryTheory.HasExt` is `AlgebraicGeometry.Space.hasExt_sheaf_smallEtale`.  Its
  universe `max (u + 1) u`, that is `u + 1`, is the morphism universe of the category of abelian
  *sheaves* — not of the site, whose morphisms are in `Type u` — and it is also the universe the
  module-valued bridge
  `Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'`
  consumes, that one being `max u₂ uMod` for a site with objects in `Type u₂` and coefficients
  in `AddCommGrpCat.{uMod}`;
* `CategoryTheory.HasSheafify` and
  `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` are the site's own instances,
  `AlgebraicGeometry.Space.SmallEtale.instHasSheafify` and
  `AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective`.

So the equivalence with a small model, which
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineCohomologyVanishing.lean` carries
out for a chosen big site, is not needed here, and neither is the local `HasExt` instance of
`Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite`.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartCechVanishingUnconditional.lean` say
otherwise — that "the Čech criterion and every variant of it in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/VanishingAlongAFunctor.lean` asks `Small.{u}`
of the site it concludes about".  That is right about the tagged form and wrong about the
variants: `_of_enoughInjectives` here, and
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor_of_enoughInjectives`
in that file, ask no smallness, and the second says so in its own docstring.

*Three universe arguments of the criterion are given explicitly*, as `.{u + 1, u, u}`: the
`Ext` universe, the covering-index universe `w`, and the universe `v`, which enters the criterion
only through the site's morphism universe `max v w` and the coefficients
`AddCommGrpCat.{max v w}`.  The third is the one that has to be given, as supplying the
arguments one at a time shows: with `v` left to be inferred the application fails with

    failed to solve universe constraint u =?= u + 1
    while trying to unify UnivLE.{u + 1, u} with UnivLE.{u + 1, u + 1}

the elaborator not reading off `v := u` from `max v w = u`.  The object universe of the site is
then determined and is left out.

*The index universe of the covering families* is the universe `u` of the schemes, because that
is where the Čech hypothesis is proved: `isZero_cechCohomology_of_isQuasicoherentOnSite` takes a
`CategoryTheory.PreZeroHypercover.{u}`.  That is also the largest it may be, the criterion
needing the coefficient universe to contain it and the coefficients being `AddCommGrpCat.{u}`.
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement` produces its family indexed
by a `Type`, so the cofinality statement reindexes it by `ULift.{u}`, which changes neither the
presieve it generates — the two `CategoryTheory.Presieve.ofArrows` are equal, each arrow of one
being an arrow of the other — nor finiteness.  This is the same reindexing
`AlgebraicGeometry.Space.SmallEtaleModel.exists_finite_affine_hypercover_hom` performs.

*Why `HasFiniteLimits (Over U)` is a `local instance`*, and not registered: the small étale site
has no terminal object in general, so the slices' finite limits do not come from the site's, and
a global instance would oblige every consumer of the site to carry it.  That is the choice
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartCechVanishing.lean` makes with `haveI`, for
the reason its implementation notes give; here the instance is needed in the *statements* of the
`hCovObjects` clauses, so it is local to the file instead.

*The affineness of the iterated fibre products* is the transport of the scheme-side
`AlgebraicGeometry.isAffine_left_piObj` along the slice projection
`AlgebraicGeometry.Space.SmallEtale.sliceToOver`, which preserves finite limits
(`AlgebraicGeometry.Space.SmallEtale.preservesFiniteLimits_sliceToOver`).  The proof is the
scheme-side one with the ad-hoc preservation argument replaced by that instance: the product of
the family in the schemes over the chart's scheme has affine structure morphism, by
`AlgebraicGeometry.isAffineHom_over_finiteProduct`, hence affine source over the affine chart.

No `@[stacks]` attribute is claimed.  [Stacks, Tag 03F9] is already registered, on
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero`; what is here is its
application on one site, and the vanishing it yields is the étale-site half of Descent,
Proposition 03DW rather than a tag of its own.

## References

* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 0218](https://stacks.math.columbia.edu/tag/0218)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/- The slice of the small étale site at a chart has finite limits, as an instance local to this
file; the theorem is `AlgebraicGeometry.Space.hasFiniteLimits_overChart`, deliberately not an
instance there.  Only the attribute is local, so no second declaration is needed. -/
attribute [local instance] hasFiniteLimits_overChart

/- Enough injective abelian sheaves on the small étale site, and their `Ext`-groups, as
instances local to this file; the theorems are
`AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtale` and
`AlgebraicGeometry.Space.hasExt_sheaf_smallEtale`, deliberately not instances there.
Only the attribute is local, so no second declaration of either statement is needed. -/
attribute [local instance] enoughInjectives_sheaf_smallEtale hasExt_sheaf_smallEtale

namespace SmallEtale

/-- **The collection `Cov` of [Stacks, Tag 03F9] on the small étale site of an algebraic
space**: the covering families of an *affine* chart, indexed by a type of the universe of the
schemes, which are finite and all of whose members are affine charts. -/
def affineChartCov (U : SmallEtale B S hS F) :
    Set { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ SmallEtale.topology B S hS F U } :=
  {E | IsAffine (chartScheme U) ∧ Finite E.1.I₀ ∧ ∀ i, IsAffine (chartScheme (E.1.X i))}

/-- **The third clause of the hypothesis `hCovObjects` of [Stacks, Tag 03F9].**  An iterated
fibre product, in the small étale site, of affine charts over an affine chart is again an affine
chart.

This is `AlgebraicGeometry.isAffine_left_piObj` transported along the slice projection
`AlgebraicGeometry.Space.SmallEtale.sliceToOver`, which preserves finite limits.  The product of
the images is a product of schemes over the chart's scheme whose structure morphisms are affine,
so its own structure morphism is affine and its source is affine over the affine chart. -/
theorem isAffine_chartScheme_piObj {U : SmallEtale B S hS F} (hU : IsAffine (chartScheme U))
    (E : PreZeroHypercover.{w} U) (hX : ∀ i, IsAffine (chartScheme (E.X i))) (p : ℕ)
    (i : Fin (p + 1) → E.I₀) :
    IsAffine (chartScheme (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left) := by
  let A : Fin (p + 1) → Over U := fun a ↦ Over.mk (E.f (i a))
  let G : Over U ⥤ Over (chartScheme U) := sliceToOver B S hS F U
  have hF : ∀ a, _root_.AlgebraicGeometry.IsAffineHom (G.obj (A a)).hom := fun a ↦ by
    have : IsAffine (G.obj (A a)).left := hX (i a)
    exact isAffineHom_of_isAffine _
  have : _root_.AlgebraicGeometry.IsAffineHom (∏ᶜ (fun a ↦ G.obj (A a))).hom :=
    isAffineHom_over_finiteProduct _ hF
  have haff : IsAffine (∏ᶜ (fun a ↦ G.obj (A a))).left :=
    isAffine_of_isAffineHom (∏ᶜ (fun a ↦ G.obj (A a))).hom
  have e : chartScheme (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left ≅
      (∏ᶜ (fun a ↦ G.obj (A a))).left :=
    (Over.forget (chartScheme U)).mapIso (PreservesProduct.iso G A)
  exact IsAffine.of_isIso e.hom

/-- **The hypothesis `hCovObjects` of [Stacks, Tag 03F9]**, verbatim, for the affine charts and
the collection `AlgebraicGeometry.Space.SmallEtale.affineChartCov`: the target of such a
covering family, each of its members and each of its iterated fibre products is an affine
chart. -/
theorem affineChartCov_covObjects {U : SmallEtale B S hS F}
    (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ SmallEtale.topology B S hS F U })
    (hE : E ∈ affineChartCov B S hS F U) :
    U ∈ SmallEtale.affineObjects B S hS F ∧
      (∀ i, E.1.X i ∈ SmallEtale.affineObjects B S hS F) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := fun _ _ ↦ inferInstance
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ SmallEtale.affineObjects B S hS F :=
  ⟨hE.1, hE.2.2, fun p i ↦ isAffine_chartScheme_piObj B S hS F hE.1 E.1 hE.2.2 p i⟩

/-- **The hypothesis `hCovCofinal` of [Stacks, Tag 03F9]**, verbatim: the finite affine covering
families are cofinal among the covering sieves of an affine chart.

This is `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement`, the sieve-level
form of Stacks 0218 on this site, with its index type reindexed by `ULift.{u}`; the two
presieves are equal, so the sieve is unchanged. -/
theorem affineChartCov_cofinal (U : SmallEtale B S hS F)
    (hU : U ∈ SmallEtale.affineObjects B S hS F) (R : Sieve U)
    (hR : R ∈ SmallEtale.topology B S hS F U) :
    ∃ E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ SmallEtale.topology B S hS F U },
      E ∈ affineChartCov B S hS F U ∧ E.1.sieve₀ ≤ R := by
  obtain ⟨ι, hfin, V, f, hVaff, hle, hcov⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS F U hU R hR
  have hpre : Presieve.ofArrows (fun j : ULift.{u} ι ↦ V j.down) (fun j ↦ f j.down) =
      Presieve.ofArrows V f := by
    refine le_antisymm ?_ ?_
    · rintro Y g ⟨j⟩
      exact ⟨j.down⟩
    · rintro Y g ⟨j⟩
      exact ⟨ULift.up j⟩
  have hsieve : (Sieve.generate
      (Presieve.ofArrows (fun j : ULift.{u} ι ↦ V j.down) (fun j ↦ f j.down))) =
      Sieve.ofArrows V f := by
    rw [Sieve.ofArrows, hpre]
  refine ⟨⟨{ I₀ := ULift.{u} ι, X := fun j ↦ V j.down, f := fun j ↦ f j.down }, ?_⟩,
    ⟨hU, inferInstance, fun j ↦ hVaff j.down⟩, ?_⟩
  · show Sieve.generate (Presieve.ofArrows _ _) ∈ _
    rw [hsieve]
    exact hcov
  · show Sieve.generate (Presieve.ofArrows _ _) ≤ R
    rw [hsieve]
    exact hle

/-- **[Stacks, Tag 03F9] on the small étale site of an algebraic space, at the affine charts.**
An abelian sheaf whose positive-degree Čech cohomology vanishes on every finite affine covering
family of an affine chart has vanishing positive-degree cohomology over every affine chart.

This is `Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives`
— the criterion of [Stacks, Tag 03F9] with its homological inputs taken as instances rather
than deduced from smallness of the site — at `AlgebraicGeometry.Space.SmallEtale.affineObjects`
and `AlgebraicGeometry.Space.SmallEtale.affineChartCov`.  The module documentation explains why
no small model is needed. -/
theorem isZero_sheafH'_of_isZero_cechCohomology
    (G : Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u})
    (hCech : ∀ {V : SmallEtale B S hS F}
      (E : { E : PreZeroHypercover.{u} V // E.sieve₀ ∈ SmallEtale.topology B S hS F V })
      (_ : E ∈ affineChartCov B S hS F V) (q : ℕ), 0 < q →
      letI : ∀ (r : ℕ) (i : Fin (r + 1) → E.1.I₀),
        HasProduct (fun a ↦ Over.mk (E.1.f (i a))) := fun _ _ ↦ inferInstance
      IsZero (Stacks.CechSite.cechCohomology E.1 G.obj q))
    (U : SmallEtale B S hS F) (hU : IsAffine (chartScheme U)) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u + 1} G p U) :=
  Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives.{u + 1, u, u}
    (SmallEtale.topology B S hS F) (SmallEtale.affineObjects B S hS F)
    (affineChartCov B S hS F)
    (fun _ _ _ _ ↦ inferInstance)
    (fun E hE ↦ affineChartCov_covObjects B S hS F E hE)
    (affineChartCov_cofinal B S hS F)
    G (fun E hE q hq ↦ hCech E hE q hq) U hU p hp

end SmallEtale

variable {B S hS F}
variable {hF : IsAlgebraicSpace B S hS F}

/-- **The positive-degree sheaf cohomology of a quasi-coherent `𝒪_F`-module vanishes over every
affine étale chart of an algebraic space.**

Cohomology is Mathlib's `CategoryTheory.Sheaf.H'`, the `Ext`-group out of the free abelian sheaf
on the chart, taken at the morphism universe `u + 1` of the category of abelian sheaves on the
site — which is also the universe the module-valued bridge
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'`
consumes.

This is `AlgebraicGeometry.Space.SmallEtale.isZero_sheafH'_of_isZero_cechCohomology` with its
Čech hypothesis supplied by
`AlgebraicGeometry.Space.isZero_cechCohomology_of_isQuasicoherentOnSite`, the `Ȟ^p = 0` clause
of Descent, Lemma 03FJ on this site. -/
theorem isZero_sheafH'_of_isQuasicoherentOnSite (K : Modules.{u, u} B S hS F hF)
    (hK : K.IsQuasicoherentOnSite) (U : SmallEtale B S hS F)
    (hU : IsAffine (chartScheme U)) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u + 1} (J := SmallEtale.topology B S hS F)
      ((SheafOfModules.toSheaf
        (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj K) p U) :=
  SmallEtale.isZero_sheafH'_of_isZero_cechCohomology B S hS F
    ((SheafOfModules.toSheaf
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj K)
    (fun {V} E hE q hq ↦
      have : IsAffine (chartScheme V) := hE.1
      have : ∀ (r : ℕ) (i : Fin (r + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (i a))) := fun _ _ ↦ inferInstance
      isZero_cechCohomology_of_isQuasicoherentOnSite K hK V E.1 hE.2.1
        (fun i ↦ hE.2.2 i) E.2 q hq)
    U hU p hp

end AlgebraicGeometry.Space

end
