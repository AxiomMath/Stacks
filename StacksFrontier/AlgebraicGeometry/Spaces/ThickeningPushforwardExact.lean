module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbelianPushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos

/-!
# Exactness of the small étale direct image along the inclusion of a thickening

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`G ⊂ X` be a thickening, that is a closed subspace whose inclusion is surjective on points.
The inclusion `ι : G ⟶ X` is integral (Stacks 05ZL), so Stacks 0A4K applies to it: the direct
image `ι_* : Ab(G_étale) ⥤ Ab(X_étale)` is an exact functor and `R^p ι_* = 0` for `p > 0`.

Both conclusions are proved here, with no hypothesis beyond the thickening.  The general case of
Stacks 0A4K, for an arbitrary integral morphism, is *not* proved here, and **no declaration in
this file carries a `@[stacks 0A4K]` attribute**: restricting the source's "integral" to "the
inclusion of a thickening" strengthens the hypothesis rather than isolating a clause, so it is
not something an attribute may record.  See the implementation notes for what the general case
still needs.

The reason the thickening case is unconditional is that for it the single open input of the
general case is not needed at all.  The general route, carried out in
`StacksFrontier.AlgebraicGeometry.Spaces.AbelianPushforwardExact` and
`StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPreservesEpi`, reduces Stacks 0A4K to the
statement that the small étale direct image transforms surjections of sheaves of *sets* into
surjections — Stacks 04C2, part (1) — and that statement is what is owed.  For the inclusion of
a thickening it is immediate: base change of étale scheme charts along the inclusion exhibits
the small étale site of `X` as a dense subsite of the small étale site of `G` (Stacks 05ZM), the
direct image *is* restriction along that base change (Stacks 03G2, part (4)), and restriction
along a dense subsite inclusion is an equivalence of sheaf categories, hence a left adjoint,
hence preserves epimorphisms.

## Main results

* `AlgebraicGeometry.Space.smallEtalePushforward_isEquivalence_of_isDenseSubsite`: the small
  étale direct image along a representable morphism whose chart base change is a dense subsite
  inclusion is an equivalence of the categories of sheaves of sets.
* `AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms_of_isThickening`: for the
  inclusion of a thickening the small étale direct image transforms surjections of sheaves of
  sets into surjections.  This is Stacks 04C2, part (1) at that morphism, and it is the
  hypothesis `hepi` of
  `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_exact` discharged.
* `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_exact_of_isThickening` and
  `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_rightDerivedPlus_isZero_of_isThickening`
  are the two conclusions of Stacks 0A4K for the inclusion of a thickening.

## Implementation notes

**What is covered and what is not.**  Only the case of the inclusion of a thickening is proved.
Everything formal on top of Stacks 04C2, part (1) is already proved and unconditional —
Stacks 04DB from its condition (1)
(`Stacks.Topos.AbelianPushforward.abelianPushforward_exact`), the vanishing of the higher right
derived functors of an exact functor
(`CategoryTheory.Functor.isZero_rightDerivedPlus_of_exact`), and the reduction of Stacks 04C2,
part (1) along an étale covering of the target
(`AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms_of_etaleCover`).  So the
general case of Stacks 0A4K needs exactly one further input, and it is a statement about
*sheaves of sets*: that the small étale direct image along an integral morphism whose target is
a scheme of the site transforms surjections into surjections.  That is the hypothesis `hscheme`
of `AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms`.

**Where that input stands.**  For schemes it is formalized as
`Stacks.EtaleCohomology.smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom`, but on
`AlgebraicGeometry.Scheme.smallEtaleTopology`, the small étale site of *all* étale schemes over
the base, whereas the algebraic-spaces development works with the small étale site cut down to
the objects of the big site.  The two sites *are* compared, and completely: the embedding
`AlgebraicGeometry.SmallEtale.toEtaleSite` is a dense subsite inclusion
(`AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`) and the two categories of sheaves
are equivalent (`AlgebraicGeometry.SmallEtale.sheafEquiv`).  What is missing is not the
comparison of the sites but the compatibility of the two *base-change* functors with it: a
natural isomorphism `smallEtaleBaseChange B f ⋙ toEtaleSite ≅ toEtaleSite ⋙
Stacks.EtaleCohomology.smallEtaleBaseChange`, and the corresponding compatibility of
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` with
`AlgebraicGeometry.Space.smallBaseChange`, which is the hop from the étale charts of an
algebraic space to the schemes étale over a scheme of the site.

**Why a thickening escapes that.**  The dense-subsite inclusion of Stacks 05ZM is proved for the
bounded site directly, `AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite`, so no
comparison of sites is involved.  Its fourth condition — that chart base change both preserves
and reflects covering sieves — is where surjectivity on points enters, and it is exactly what
fails for a closed immersion that is not a thickening; the other three conditions hold for every
closed immersion, by Stacks 04E5.

**Integrality is carried, not assumed away.**  The two conclusions below take the thickening as
their only hypothesis and derive integrality of the inclusion from it through
`AlgebraicGeometry.Space.isIntegralHom_ι_of_isThickening`, so the hypothesis of the source is
discharged rather than restated.

The universe of the sheaves of sets is `Type (u + 1)`, the universe of the objects of the small
étale site of an algebraic space over `Scheme.{u}`, and the coefficient category of the abelian
sheaves is `AddCommGrpCat.{u + 1}`; these are the universes at which
`AlgebraicGeometry.Space.smallToposMorphism` and the two conclusions of Stacks 0A4K are already
stated.

## References

* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 04DB](https://stacks.math.columbia.edu/tag/04DB)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 05ZL](https://stacks.math.columbia.edu/tag/05ZL)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The direct image along a dense-subsite chart base change -/

/-- **The small étale direct image along a dense-subsite inclusion is an equivalence.** Let
`i : Z ⟶ X` be a representable morphism of algebraic spaces over `S` whose base change on étale
scheme charts exhibits the small étale site of `X` as a dense subsite of the small étale site of
`Z`.  Then the direct image of sheaves of sets along the morphism of small étale topoi of
Stacks 03G2, part (3), is an equivalence of categories.

By Stacks 03G2, part (4), that direct image is restriction of sheaves along chart base change,
and restriction along a dense subsite inclusion is an equivalence — the comparison lemma. -/
theorem smallEtalePushforward_isEquivalence_of_isDenseSubsite
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom)
    (hds : (smallBaseChange B S hS i hi).IsDenseSubsite
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)) :
    (smallToposMorphism B S hS i).pushforward.IsEquivalence :=
  have := hds
  have := (smallBaseChange_isMorphismOfSites B S hS i hi).toIsContinuous
  have : ((smallBaseChange B S hS i hi).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)).IsEquivalence :=
    inferInstance
  Functor.isEquivalence_of_iso (smallBaseChange_topos B S hS i hi).symm

/-- **The small étale direct image along a dense-subsite inclusion preserves surjections.** An
equivalence of categories is a left adjoint, and a left adjoint preserves epimorphisms. -/
theorem smallEtalePushforward_preservesEpimorphisms_of_isDenseSubsite
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom)
    (hds : (smallBaseChange B S hS i hi).IsDenseSubsite
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)) :
    (smallToposMorphism B S hS i).pushforward.PreservesEpimorphisms :=
  have := smallEtalePushforward_isEquivalence_of_isDenseSubsite B S hS i hi hds
  Functor.preservesEpimorphisms_of_adjunction
    (smallToposMorphism B S hS i).pushforward.asEquivalence.toAdjunction

/-! ### Stacks 04C2, part (1) for the inclusion of a thickening -/

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- **Stacks 04C2, part (1), for the inclusion of a thickening.** For a thickening `G ⊂ X` of
algebraic spaces over `S` the small étale direct image along the inclusion `G ⟶ X` transforms
surjections of sheaves of sets into surjections.

Base change of étale scheme charts along the inclusion is a dense subsite inclusion, which is
Stacks 05ZM, so
`AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms_of_isDenseSubsite`
applies. -/
theorem smallEtalePushforward_preservesEpimorphisms_of_isThickening
    (hG : IsThickening B S hS X G) :
    (smallToposMorphism B S hS
      (IsThickening.inclusion B S hS hG)).pushforward.PreservesEpimorphisms :=
  smallEtalePushforward_preservesEpimorphisms_of_isDenseSubsite B S hS
    (IsThickening.inclusion B S hS hG)
    (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep
    (thickeningChartBaseChange_isDenseSubsite B S hS hG)

/-! ### Stacks 0A4K for the inclusion of a thickening -/

/-- **Stacks 0A4K, exactness, for the inclusion of a thickening.** Let `X` be an algebraic space
over a scheme `S` and let `G ⊂ X` be a thickening of it.  The inclusion `ι : G ⟶ X` is integral,
and the direct image `ι_* : Ab(G_étale) ⥤ Ab(X_étale)` on the abelian sheaves of the small étale
sites is an exact functor.

Integrality of the inclusion is Stacks 05ZL.  The passage from surjections of sheaves of sets to
exactness on abelian sheaves is Stacks 04DB, available as
`Stacks.Topos.AbelianPushforward.abelianPushforward_exact` and applied through
`AlgebraicGeometry.Space.smallEtaleAbelianPushforward_exact`; its hypothesis is
`AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms_of_isThickening`.

This is the first conclusion of Stacks 0A4K at the inclusion of a thickening, and it carries no
`@[stacks 0A4K]` attribute: the source states that conclusion for an arbitrary integral
morphism, and a thickening is a special case of that hypothesis rather than a clause of the
statement. -/
theorem smallEtaleAbelianPushforward_exact_of_isThickening (hG : IsThickening B S hS X G) :
    exactFunctor
      (Sheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).obj)
        AddCommGrpCat.{u + 1})
      (Sheaf (SmallEtale.topology B S hS X.obj) AddCommGrpCat.{u + 1})
      (Stacks.Topos.AbelianPushforward.abelianPushforward
        (SmallEtale.topology B S hS (IsThickening.space B S hS hG).obj)
        (smallToposMorphism B S hS (IsThickening.inclusion B S hS hG))) :=
  smallEtaleAbelianPushforward_exact B S hS (IsThickening.inclusion B S hS hG)
    (isIntegralHom_ι_of_isThickening B S hS hG)
    fun _ => smallEtalePushforward_preservesEpimorphisms_of_isThickening B S hS hG

/-- **Stacks 0A4K, vanishing of the positive-degree higher direct images, for the inclusion of a
thickening.** With `ι : G ⟶ X` the inclusion of a thickening of algebraic spaces over `S`, the
higher direct images `R^p ι_*` vanish on every abelian sheaf on the small étale site of `G`, for
every `p > 0`.

Given exactness this is formal — it is
`CategoryTheory.Functor.isZero_rightDerivedPlus_of_exact`, applied through
`AlgebraicGeometry.Space.smallEtaleAbelianPushforward_rightDerivedPlus_isZero`, the abelian
sheaves on the small étale site having enough injectives.

This is the second conclusion of Stacks 0A4K at the inclusion of a thickening, and it carries no
`@[stacks 0A4K]` attribute, for the reason recorded on
`AlgebraicGeometry.Space.smallEtaleAbelianPushforward_exact_of_isThickening`. -/
theorem smallEtaleAbelianPushforward_rightDerivedPlus_isZero_of_isThickening
    (hG : IsThickening B S hS X G)
    (F : Sheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).obj)
      AddCommGrpCat.{u + 1})
    (p : ℤ) (hp : 0 < p) :
    IsZero (((Stacks.Topos.AbelianPushforward.abelianPushforward
      (SmallEtale.topology B S hS (IsThickening.space B S hS hG).obj)
      (smallToposMorphism B S hS
        (IsThickening.inclusion B S hS hG))).rightDerivedPlus p).obj F) :=
  smallEtaleAbelianPushforward_rightDerivedPlus_isZero B S hS
    (IsThickening.inclusion B S hS hG) (isIntegralHom_ι_of_isThickening B S hS hG)
    (fun _ => smallEtalePushforward_preservesEpimorphisms_of_isThickening B S hS hG) F p hp

end AlgebraicGeometry.Space

end
