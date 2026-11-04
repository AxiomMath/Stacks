module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianSmallEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyOnALargeSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SmallSiteAbelianInstances

/-!
# Filtered colimits and étale cohomology on the size-bounded small étale site

Let `X` be a quasi-compact and quasi-separated scheme belonging to a big étale site `B`, and let
it carry the size-bounded small étale site of [Stacks, Tag 021B]. Then for every degree `p` the
canonical map

> `colim_i H^p_étale(X, F_i) ⟶ H^p_étale(X, colim_i F_i)`

is an isomorphism, for every filtered system `F` of abelian sheaves on that site.

On Mathlib's choice-free small étale site this is [Stacks, Tag 03Q5], available as
`Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_Γ_smallEtale`. The size-bounded site is a
dense subsite of Mathlib's, so restriction of abelian sheaves along the embedding is an
equivalence of sheaf categories commuting with global sections, and the colimit comparison for
the right derived functors of global sections travels back along it.

## Main results

* `Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_Γ_boundedSmallEtale` — **the étale
  cohomology of a quasi-compact, quasi-separated scheme commutes with filtered colimits of
  abelian sheaves on the size-bounded small étale site of [Stacks, Tag 021B].**
* `Stacks.EtaleCohomology.additive_Γ_boundedSmallEtale` and
  `Stacks.EtaleCohomology.additive_Γ_smallEtaleTopology` — additivity of global sections on the
  two sites at the coefficient universe `u + 1`, registered because it appears in the type of
  the statement above.

## Implementation notes

The transport statement is `isIso_colimit_post_rightDerived_globalSections_of_isDenseSubsite` of
the namespace `Stacks.Cohomology.ColimitsOfCohomology`, and the work here is supplying its
instance arguments at the universes of the two étale sites, whose objects live in `u + 1` and
whose morphisms live in `u` for `X : Scheme.{u}`.

Four of them have to be supplied, because `CategoryTheory.Functor.rightDerived` asks for
injective resolutions in its source and for additivity of the functor. Injective resolutions on
either side come from Grothendieck-abelianness relative to `u + 1`, whose two statements
(`AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf_succ` and
`Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse`) mention that
universe with the scheme universe free and are therefore kept out of instance resolution by their
authors; they are reinstated here as local instances. Additivity of global sections,
`Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ`, is left unregistered there too, but
appears in the *type* of the statement below rather than only in its proof, so a local instance
will not do: it is registered at the one coefficient universe `u + 1` this file works with.

The limits of shape `StructuredArrow _ (SmallEtale.toEtaleSite B X hX).op` needed to restrict
sheaves along the embedding are supplied in the proof: those comma categories are essentially
small in the universe of the schemes, the size-bounded site being essentially small there.

Instantiating [Stacks, Tag 03Q5] takes its free coefficient universe to be `u + 1`; the join
`max (u + 1) (u + 1)` appearing in its statement is then `u + 1` on the nose.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ColimitsOfCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf_succ
  isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- Global sections of abelian sheaves on the size-bounded small étale site of
[Stacks, Tag 021B] is an additive functor, being a right adjoint. -/
public instance additive_Γ_boundedSmallEtale
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) :
    (Sheaf.Γ (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).Additive :=
  additive_sheafΓ _ _

/-- Global sections of abelian sheaves on Mathlib's small étale site is an additive functor,
being a right adjoint. -/
public instance additive_Γ_smallEtaleTopology (X : Scheme.{u}) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).Additive :=
  additive_sheafΓ _ _

/-- The comma categories controlling restriction of sheaves along the embedding of the
size-bounded small étale site into Mathlib's have limits at abelian coefficients: they are
essentially small in the universe of the schemes, because the size-bounded site is. -/
private theorem hasLimitsOfShape_structuredArrow_toEtaleSite
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) :
    ∀ T : (X.Etale)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow T (SmallEtale.toEtaleSite B X hX).op) AddCommGrpCat.{u + 1} :=
  fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- **Étale cohomology commutes with filtered colimits on the size-bounded small étale site of
[Stacks, Tag 021B].** Let `X` be a quasi-compact and quasi-separated scheme belonging to a big
étale site `B`. For every degree `p` and every filtered system `F` of abelian sheaves on the
small étale site of `X` cut out of `B`, the canonical map

> `colim_i H^p_étale(X, F_i) ⟶ H^p_étale(X, colim_i F_i)`

is an isomorphism.

This is [Stacks, Tag 03Q5], which is
`Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_Γ_smallEtale` on Mathlib's small étale
site, transported back along the embedding of the size-bounded site as a dense subsite. -/
public theorem isIso_colimit_post_rightDerived_Γ_boundedSmallEtale
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    [CompactSpace X] [QuasiSeparatedSpace X] (p : ℕ)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).rightDerived p)) := by
  have := hasLimitsOfShape_structuredArrow_toEtaleSite B X hX
  refine isIso_colimit_post_rightDerived_globalSections_of_isDenseSubsite
    (SmallEtale.topology B X hX) X.smallEtaleTopology (SmallEtale.toEtaleSite B X hX)
    AddCommGrpCat.{u + 1} p F ?_
  exact isIso_colimit_post_rightDerived_Γ_smallEtale.{u + 1, u} X p _

end Stacks.EtaleCohomology

end
