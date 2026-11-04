module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.AssociatedModuleOnTheSmallEtaleSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleFibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineFibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ImageFibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingStandardCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelianSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStandardCoverings
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall

/-!
# The associated module of a quasi-coherent module is acyclic on affine objects

Let `S` be a scheme and `F` a quasi-coherent `𝒪_S`-module, and let `Fᵃ` be the associated
module of [Stacks, Tag 03DU].  This file proves that the higher cohomology of `Fᵃ` vanishes on
every object with affine total space, both on a localized big `τ`-site of `S` and on the small
étale site of `S`.

Both statements are one application of the Čech-vanishing criterion of [Stacks, Tag 03F9] in
the form transferred along a functor of sites,
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor`
respectively its `_of_enoughInjectives` sibling.  Every hypothesis of that criterion is
already available: the standard coverings of an affine object are cofinal, their fibre products
exist and are computed in the slice of all schemes, and the Čech cohomology of the image
covering vanishes by
`AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf`.

## Main results

* `AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine`: the big-site statement.
* `AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine`: the small étale statement.

**No `@[stacks]` attribute is attached.**  [Stacks, Tag 03P2] is a single equality, and neither
statement below is a part of it that the source delimits: both are an intermediate step towards
it.  The theorem is the comparison `H^p(S, ℱ) = H^p_τ(S, Fᵃ)`, whose proof is this
affine vanishing — in which both sides are zero, the left-hand one by [Stacks, Tag 01XD] — fed
into the Leray collapse along `ε : 𝒞 ⟶ S_Zar`.  That collapse is
`Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso`, and its hypothesis is the
vanishing of the higher direct images `R^q ε_* Fᵃ`.  That vanishing *does* follow from the
statements below, by
`isZero_rightDerived_pushforward_of_sheafCohomology_cover` in the namespace
`Stacks.Cohomology.HigherDirectImageOnACover`, once every object of the small Zariski
site of `S` has a covering family whose members go to affine objects of `𝒞`.  That covering
family is the affine opens below an open of `S`, which the functor from the opens of `S` into
`𝒞` carries to objects of `AlgebraicGeometry.overAffineObjects` respectively
`AlgebraicGeometry.smallEtaleAffineObjects`
(`AlgebraicGeometry.mem_overAffineObjects_opensBelowToOver` and its small étale counterpart),
and the identification `ε_* Fᵃ ≅ ℱ` the collapse compares against is
`AlgebraicGeometry.bigOverSectionsUnitIso` respectively
`AlgebraicGeometry.smallEtaleSectionsUnitIso`.  So the comparison itself is proved, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.BigSiteQuasiCoherentCohomology`
and `...CechComparison.SmallEtaleQuasiCoherentCohomology`, which are where the attributes of
[Stacks, Tag 03P2] and [Stacks, Tag 03DW] sit.

## Implementation notes

The topology on the slice of all schemes over `S` is taken to be the localization of the fpqc
topology in both cases.  Only two things are asked of it — that `Fᵃ` be a sheaf for it and that
the presenting functor be continuous into it — and both are available at the fpqc topology
uniformly, by `Stacks.EtaleCohomology.isSheaf_associatedPresheaf_of_le` at `le_rfl` and by
`AlgebraicGeometry.isContinuous_overToSlice_fpqc` respectively
`AlgebraicGeometry.Scheme.Etale.forget_isContinuous_fpqcOver`.  The pushforward along the
presenting functor is restriction, so the sheaf whose cohomology is computed does not depend on
that choice.

`CategoryTheory.Sheaf.H'` carries its `Ext` universe as a parameter, and the small étale
statement needs it to be the morphism universe `u` of the site, as the big-site statement
already has it: that is the universe at which
`Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections` — hence the
`Sheaf.H'` form of `isZero_rightDerived_pushforward_of_sheafCohomology_cover`, in the namespace
`Stacks.Cohomology.HigherDirectImageOnACover` — is available.  Instance search picks `u + 1`
instead, because
`AlgebraicGeometry.hasExt_sheaf_smallEtaleTopology` is declared after
`CategoryTheory.IsGrothendieckAbelian.hasExt`, which also applies, the abelian sheaves on that
site being Grothendieck abelian at `u`.  The criterion resolves its own `HasExt` binder by
instance search before unifying with the expected type, so writing `Sheaf.H'.{u}` in the
statement does not fix it; the priority is flipped locally instead, at that one declaration.

That flip is a workaround for an instance-priority accident between two available instances, not
a mathematical constraint.  The principled remedy is a version of
`sheafCohomologyIsoRightDerivedSections` with its `Ext` universe free rather than pinned to the
morphism universe of the site; that would make the flip unnecessary and would additionally allow
the `HasExt`-free
`Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_cover` to be
used here.

The small étale site uses the `_of_enoughInjectives` form of the criterion, not the plain
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor`: the category of
all schemes étale over `S` is **not** essentially small at the morphism universe of the site,
since `∐ i : I, S` is étale over `S` for every index type `I`.  The four homological inputs
the plain form derives from essential smallness are instead instances of
`StacksFrontier/AlgebraicGeometry/Topologies/SmallEtaleAbelianSheaves.lean`.

## References

* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03OZ](https://stacks.math.columbia.edu/tag/03OZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CechSite
open scoped AlgebraicGeometry

universe u

-- The localized big sites are essentially small, so these two supply the homological inputs of
-- the Čech-vanishing criterion there.  They are not global instances, and `CategoryTheory.Sheaf.H'`
-- is defined through `Ext`, so without them the *statements* below do not even elaborate.
attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

namespace AlgebraicGeometry

variable (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]

/-- `Fᵃ` as a sheaf on the localization at `S` of the fpqc topology on all schemes.  This is
the sheaf the two acyclicity statements below restrict along the presenting functor of their
site. -/
public def fpqcOverAssociatedSheaf : Sheaf (Scheme.fpqcTopology.{u}.over S) AddCommGrpCat.{u} :=
  ⟨quasiCoherentPresheafFunctor S F,
    Stacks.EtaleCohomology.isSheaf_associatedPresheaf_of_le S F le_rfl⟩

/-! ### The big `τ`-site -/

variable (τ : CoveringTopology) (B : BigSite.{u} τ) (hS : S.size < cutoff τ B)

/-- **The higher cohomology of `Fᵃ` vanishes on an object of a localized big `τ`-site with
affine total space.**  This is an intermediate step towards [Stacks, Tag 03P2] and not a part
of it: at an affine object and in positive degree both sides of the comparison
`H^p(U, f^*ℱ) = H^p_τ(U, Fᵃ)` vanish, the left-hand one by [Stacks, Tag 01XD].  The comparison
itself is `AlgebraicGeometry.bigOverQuasiCoherentCohomologyIso`, which this feeds through the
Leray collapse; see the module documentation. -/
public theorem isZero_sheafCohomology_succ_overAffine (U : Over (base B S hS))
    (hU : U ∈ overAffineObjects τ B S hS) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' (((overToSlice τ B S hS).sheafPushforwardContinuous AddCommGrpCat.{u}
      (overTopology τ B S hS) (Scheme.fpqcTopology.{u}.over S)).obj
        (fpqcOverAssociatedSheaf S F)) p U) := by
  refine sheafCohomology_isZero_of_cechCohomology_isZero_of_functor_of_enoughInjectives
    (overTopology τ B S hS) (Scheme.fpqcTopology.{u}.over S) (overToSlice τ B S hS)
    (overAffineObjects τ B S hS) (overStandardCoverings τ B S hS)
    (overStandardCoverings_hasProducts τ B S hS)
    (overStandardCoverings_hasImageProducts τ B S hS)
    (overStandardCoverings_covObjects τ B S hS)
    (overStandardCoverings_cofinal τ B S hS)
    (overStandardCoverings_comparison τ B S hS) (fpqcOverAssociatedSheaf S F) ?_ U hU p hp
  intro V E hE q hq
  obtain ⟨hV, hstd⟩ := hE
  have : IsAffine ((overToSlice τ B S hS).obj V).left := hV
  exact isZero_cechCohomology_succ_quasiCoherentPresheaf ((overToSlice τ B S hS).obj V) τ F
    (E.1.map (overToSlice τ B S hS)) hstd q hq

/-! ### The small étale site -/

-- `CategoryTheory.Sheaf.H'` carries its `Ext` universe as a parameter, and on the small étale
-- site instance search resolves it to `u + 1` rather than to the morphism universe `u` of the
-- site, because `AlgebraicGeometry.hasExt_sheaf_smallEtaleTopology` is declared after
-- `CategoryTheory.IsGrothendieckAbelian.hasExt` and so wins.  The criterion below resolves its
-- own `CategoryTheory.HasExt` binder by instance search *before* unifying with the expected
-- type, so pinning the universe in the statement does not help; the priority has to be flipped.
-- See the implementation notes for the principled remedy.
attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- **The higher cohomology of `Fᵃ` vanishes on an object of the small étale site of `S` with
affine total space.**  This is the same intermediate step towards [Stacks, Tag 03P2] in the
case `𝒞 = S_étale`; see `AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine`.

The `Ext` universe of `CategoryTheory.Sheaf.H'` here is the morphism universe `u` of the site,
as it is on the big `τ`-sites, and not the `u + 1` that instance search picks by default; that
is what makes this statement composable with
`isZero_rightDerived_pushforward_of_sheafCohomology_cover`, in the namespace
`Stacks.Cohomology.HigherDirectImageOnACover`. -/
public theorem isZero_sheafCohomology_succ_smallEtaleAffine (U : S.Etale)
    (hU : U ∈ smallEtaleAffineObjects S) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' (((Scheme.Etale.forget S).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Scheme.smallEtaleTopology S) (Scheme.fpqcTopology.{u}.over S)).obj
        (fpqcOverAssociatedSheaf S F)) p U) := by
  refine sheafCohomology_isZero_of_cechCohomology_isZero_of_functor_of_enoughInjectives
    (Scheme.smallEtaleTopology S) (Scheme.fpqcTopology.{u}.over S) (Scheme.Etale.forget S)
    (smallEtaleAffineObjects S) (smallEtaleStandardCoverings S)
    (smallEtaleStandardCoverings_hasProducts S)
    (smallEtaleStandardCoverings_hasImageProducts S)
    (smallEtaleStandardCoverings_covObjects S)
    (smallEtaleStandardCoverings_cofinal S)
    (smallEtaleStandardCoverings_isIso_cechProductMapOfFunctor S)
    (fpqcOverAssociatedSheaf S F) ?_ U hU p hp
  intro V E hE q hq
  obtain ⟨hV, hstd⟩ := hE
  have : IsAffine ((Scheme.Etale.forget S).obj V).left := hV
  exact isZero_cechCohomology_succ_quasiCoherentPresheaf ((Scheme.Etale.forget S).obj V) .etale F
    (E.1.map (Scheme.Etale.forget S)) hstd q hq

end AlgebraicGeometry

end
