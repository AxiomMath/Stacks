module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeAlgebraSystemCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SiteEquivalenceGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedSectionsVersusSiteCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeAlgebraSystemCohomologySupplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomologySupplement

/-!
# The cohomology of Stacks 09YQ is the library's etale cohomology

Stacks 09YQ computes the cohomology of a limit `X = lim_i X_i` of schemes with affine transition
morphisms as a filtered colimit, and its cohomology groups are the right derived functors of
`sheafSections` over the terminal object of the *universe-raised small affine etale site* that
Stacks 09YP is stated on. This file identifies those groups with the library's mainstream etale
cohomology functor `Stacks.EtaleCohomology.etaleCohomologyFunctor`, both at the limit and at the
levels of the system.

## Main results

* `limitCohomologyFunctorIsoEtaleCohomology` — **the vertex of the cohomology cocone of Stacks
  09YQ is the etale cohomology of the limit.** The derived functors of sections over the image of
  the terminal object of a level in the site of the limit are
  `H^p_etale(X, -)`.
* `isDenseSubsite_levelFunctor` — the equivalence of Stacks 0EYL between a level of the site
  system and the small affine etale site of `X_i` is an equivalence of *sites*: a dense subsite
  inclusion for the two topologies.
* `levelCohomologyFunctorIsoEtaleCohomology` — **the cohomology of a level site is the etale
  cohomology of `X_i`.**
* `levelTerminalCohomologyIsoEtaleCohomology` — **the groups of the cohomology diagram of Stacks
  09YQ are the etale cohomology groups of the `X_i`.** The derived functors of sections over the
  terminal object of the level `i` are `H^p_etale(X_i, -)`.

## Implementation notes

Both identifications are the same two-step passage. A level of the system of Stacks 0EYL is a
small model, equivalent as a site to the small affine etale site of `X_i` but with its morphisms
one universe up; the site of the limit is the small affine etale site of `X` with its morphisms
raised through `CategoryTheory.AsSmall`. In both cases the comparison functor is an equivalence of
categories and an equivalence of sites, so restriction along it is an equivalence of abelian sheaf
categories and
`Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence` applies at *independent
morphism universes*. That lands the cohomology on the small affine etale site of the scheme, and
`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.affineEtaleCohomologyFunctorIso` — the
cohomological form of Stacks 04HR, which needs no affineness of its scheme — carries it to the
small etale site, where it is the library's functor by
`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.etaleCohomologyFunctor_eq`.

The dense-subsite property of the level equivalence is not read off the construction of
`AlgebraicGeometry.affineEtaleSiteColimit`, whose internals are private, but proved from the
public `AlgebraicGeometry.affineEtaleSiteColimit_level_cover`: a sieve is covering at a level
exactly when its image generates a covering sieve of the affine etale site, which is the condition
`CategoryTheory.Functor.IsDenseSubsite.functorPushforward_mem_iff` asks for; cover density, local
fullness and local faithfulness come for free from the functor being an equivalence.

Passing from sections over the terminal object to global sections, and from there to the
`Ext`-groups out of the constant sheaf, goes through `CategoryTheory.Sheaf.ΓNatIsoSheafSections`
and `Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH`. It is carried out at an
*arbitrary* terminal object rather than at a chosen one, because the objects the cohomology of
Stacks 09YQ is taken over are the transition images of a terminal object and are terminal without
being equal to any canonical choice.

## References

* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)
* [Stacks 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks 04HR](https://stacks.math.columbia.edu/tag/04HR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe v u

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.BaseChangeAlgebraSystem

attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion hasSheafify_smallAffineEtale hasSheafify_smallEtale
  locallySmall_smallAffineEtale locallySmall_smallEtale enoughInjectives_smallAffineEtale
  enoughInjectives_smallEtale hasExt_smallAffineEtale hasExt_smallEtale
  restrictToAffineEtale_isEquivalence CategoryTheory.AsSmall.isDenseSubsite_up
  hasSheafify_raisedAffineEtale locallySmall_raisedAffineEtale
  enoughInjectives_raisedAffineEtale hasExt_raisedAffineEtale

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-! ### The abelian machinery of the site of the limit

The site Stacks 09YP computes on is `limitSite`, carrying the topology generated by
`limitSitePrecoverage`. That topology is the raised etale topology
`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.raisedAffineEtaleTopology` of `X` on the nose
(`limitSitePrecoverage_toGrothendieck`), but instance search does not see through the two
definitions, so the four facts abelian sheaf cohomology needs are restated at this spelling.
-/

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- The topology of the site of the limit is the raised etale topology of `X`. -/
theorem limitSitePrecoverage_toGrothendieck :
    (limitSitePrecoverage D c B hX).toGrothendieck = raisedAffineEtaleTopology B c.pt hX :=
  rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- Abelian sheaves on the site of the limit admit sheafification. -/
theorem hasSheafify_limitSite :
    HasSheafify (limitSitePrecoverage D c B hX).toGrothendieck AddCommGrpCat.{max u v + 1} :=
  CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v + 1, max u v + 1,
    max u v + 1} _

attribute [local instance] hasSheafify_limitSite

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- Abelian sheaves on the site of the limit are locally `(max u v + 1)`-small. -/
theorem locallySmall_limitSite :
    LocallySmall.{max u v + 1}
      (Sheaf (limitSitePrecoverage D c B hX).toGrothendieck AddCommGrpCat.{max u v + 1}) :=
  CategoryTheory.Sheaf.locallySmall_of_small.{max u v + 1, max u v + 1, max u v + 1,
    max u v + 1, max u v + 2} (limitSitePrecoverage D c B hX).toGrothendieck
    AddCommGrpCat.{max u v + 1}

attribute [local instance] locallySmall_limitSite

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- Abelian sheaves on the site of the limit have enough injectives. -/
theorem enoughInjectives_limitSite :
    EnoughInjectives
      (Sheaf (limitSitePrecoverage D c B hX).toGrothendieck AddCommGrpCat.{max u v + 1}) :=
  CategoryTheory.Sheaf.enoughInjectives_of_small.{max u v + 1, max u v + 1, max u v + 1,
    max u v + 1, max u v + 2} (limitSitePrecoverage D c B hX).toGrothendieck
    AddCommGrpCat.{max u v + 1}

attribute [local instance] enoughInjectives_limitSite

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- `Ext`-groups of abelian sheaves on the site of the limit exist. -/
theorem hasExt_limitSite :
    HasExt.{max u v + 1}
      (Sheaf (limitSitePrecoverage D c B hX).toGrothendieck AddCommGrpCat.{max u v + 1}) :=
  hasExt_of_enoughInjectives.{max u v + 1} _

attribute [local instance] hasExt_limitSite

/-! ### Sections over an arbitrary terminal object -/

/-- **The right derived functors of sections over a terminal object of the raised site of the
limit are its sheaf cohomology.** Sections over a terminal object are global sections
(`CategoryTheory.Sheaf.ΓNatIsoSheafSections`), whose right derived functors are the `Ext`-groups
out of the constant sheaf on `ℤ`. The terminal object is arbitrary: the objects Stacks 09YQ takes
its cohomology over are images of terminal objects, not a canonical choice.

**No affineness of the limit is used.** This is
`Stacks.Cohomology.GlobalSections.rightDerivedSectionsIsoFunctorH`, which holds on any site: all
that is needed of `W` is that it be terminal. Only the existence of such a `W` is special to an
affine limit; the identification itself is not. -/
def rightDerivedSectionsLimitTerminalIso
    (W : limitSite D c B hX) (hW : IsTerminal W) (p : ℕ) :
    (((sheafSections (limitSitePrecoverage D c B hX).toGrothendieck
          AddCommGrpCat.{max u v + 1}).obj (op W)).rightDerived p) ≅
      raisedAffineEtaleCohomologyFunctor B c.pt hX p :=
  Stacks.Cohomology.GlobalSections.rightDerivedSectionsIsoFunctorH
    (limitSitePrecoverage D c B hX).toGrothendieck W hW p

/-- **The cohomology of Stacks 09YQ at the limit is the library's etale cohomology of `X`.** For
every degree `p` and every terminal object `W` of the raised small affine etale site of
`X = lim_i X_i`, the right derived functors of sections over `W` are

`H^p(AsSmall X_{affine,etale}, -) ≅ H^p_etale(X, -)`,

the right hand side being `Stacks.EtaleCohomology.etaleCohomologyFunctor` of the abelian sheaf on
the small etale site of `X` that the sheaf comes from.

This is `rightDerivedSectionsLimitTerminalIso` composed with
`BaseChangeAlgebraSystem.raisedAffineEtaleCohomologyFunctorIsoEtaleCohomology`. Neither factor
needs any affineness — not of the levels and not of `X` — so neither does this: a terminal object
of the raised site is all that is asked for. -/
def limitCohomologyFunctorIsoEtaleCohomology
    (W : limitSite D c B hX) (hW : IsTerminal W) (p : ℕ) :
    (((sheafSections (limitSitePrecoverage D c B hX).toGrothendieck
          AddCommGrpCat.{max u v + 1}).obj (op W)).rightDerived p) ≅
      raisedToSmallEtale B c.pt hX ⋙
        Stacks.EtaleCohomology.etaleCohomologyFunctor B ⟨c.pt, hX⟩ p :=
  rightDerivedSectionsLimitTerminalIso D c B hX W hW p ≪≫
    raisedAffineEtaleCohomologyFunctorIsoEtaleCohomology B c.pt hX p

/-! ### The level sites

A level of the system of Stacks 0EYL is a small model of the small affine etale site of `X_i`:
equivalent to it as a category, with its morphisms one universe up. The level equivalence is an
equivalence of *sites*, and the same passage as at the limit identifies the cohomology of the
level with the etale cohomology of `X_i`.
-/

section Levels

variable (i : (sys D c B hD hX hc).I)

/-- The index of the system of schemes that the level `i` of the site system sits over. -/
abbrev levelIndex : Iᵒᵖ :=
  (affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i

/-- `X_i`, the scheme of the level `i`. -/
abbrev levelScheme : Scheme.{max u v} := D.obj (levelIndex D c B hD hX hc i)

/-- The equivalence of Stacks 0EYL between the level `i` and the small affine etale site of
`X_i`. -/
abbrev levelAffineEtaleFunctor :
    (sys D c B hD hX hc).C i ⥤
      AlgebraicGeometry.SmallAffineEtale B (levelScheme D c B hD hX hc i)
        (hD (levelIndex D c B hD hX hc i)) :=
  ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor

/-- **The level equivalence of Stacks 0EYL is an equivalence of sites**: the inclusion of a dense
subsite for the topology of the level and the etale topology of the small affine etale site of
`X_i`.

Cover density, local fullness and local faithfulness hold because the functor is an equivalence of
categories; the remaining condition — a sieve is covering at the level exactly when its image is
covering downstairs — is `AlgebraicGeometry.affineEtaleSiteColimit_level_cover`, read on the sieve
generated by a presieve. -/
theorem isDenseSubsite_levelFunctor :
    (levelAffineEtaleFunctor D c B hD hX hc i).IsDenseSubsite ((sys D c B hD hX hc).J i)
      (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
        (hD (levelIndex D c B hD hX hc i))) := by
  refine { functorPushforward_mem_iff := fun {Y S} => ?_ }
  have h := affineEtaleSiteColimit_level_cover D c B hD hX hc i Y S.arrows
  rw [GrothendieckTopology.arrows_mem_toPrecoverage_iff,
    GrothendieckTopology.mem_toPrecoverage_iff, Sieve.generate_map_eq_functorPushforward,
    Sieve.generate_sieve] at h
  exact h.symm

attribute [local instance] isDenseSubsite_levelFunctor

/-- Abelian sheaves on the level `i` admit sheafification. -/
theorem hasSheafify_level :
    HasSheafify ((sys D c B hD hX hc).J i) AddCommGrpCat.{max u v + 1} :=
  CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v + 1, max u v + 1,
    max u v + 1} _

attribute [local instance] hasSheafify_level

/-- Abelian sheaves on the level `i` are locally `(max u v + 1)`-small. -/
theorem locallySmall_level :
    LocallySmall.{max u v + 1}
      (Sheaf ((sys D c B hD hX hc).J i) AddCommGrpCat.{max u v + 1}) :=
  CategoryTheory.Sheaf.locallySmall_of_small.{max u v + 1, max u v + 1, max u v + 1,
    max u v + 1, max u v + 2} ((sys D c B hD hX hc).J i) AddCommGrpCat.{max u v + 1}

attribute [local instance] locallySmall_level

/-- Abelian sheaves on the level `i` have enough injectives. -/
theorem enoughInjectives_level :
    EnoughInjectives (Sheaf ((sys D c B hD hX hc).J i) AddCommGrpCat.{max u v + 1}) :=
  CategoryTheory.Sheaf.enoughInjectives_of_small.{max u v + 1, max u v + 1, max u v + 1,
    max u v + 1, max u v + 2} ((sys D c B hD hX hc).J i) AddCommGrpCat.{max u v + 1}

attribute [local instance] enoughInjectives_level

/-- `Ext`-groups of abelian sheaves on the level `i` exist. -/
theorem hasExt_level :
    HasExt.{max u v + 1} (Sheaf ((sys D c B hD hX hc).J i) AddCommGrpCat.{max u v + 1}) :=
  hasExt_of_enoughInjectives.{max u v + 1} _

attribute [local instance] hasExt_level

/-- **Restriction of an abelian sheaf from the small affine etale site of `X_i` to the level
`i`.** -/
abbrev restrictToLevel :
    Sheaf (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
        (hD (levelIndex D c B hD hX hc i))) AddCommGrpCat.{max u v + 1} ⥤
      Sheaf ((sys D c B hD hX hc).J i) AddCommGrpCat.{max u v + 1} :=
  (levelAffineEtaleFunctor D c B hD hX hc i).sheafPushforwardContinuous AddCommGrpCat.{max u v + 1}
    ((sys D c B hD hX hc).J i)
    (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
      (hD (levelIndex D c B hD hX hc i)))

/-- Restriction to the level `i` is an equivalence on abelian sheaves. -/
theorem restrictToLevel_isEquivalence : (restrictToLevel D c B hD hX hc i).IsEquivalence :=
  inferInstance

attribute [local instance] restrictToLevel_isEquivalence

/-- The `p`-th cohomology functor of abelian sheaves on the level `i`: the `Ext`-groups out of the
constant sheaf on `ℤ`. -/
abbrev levelCohomologyFunctor (p : ℕ) :
    Sheaf ((sys D c B hD hX hc).J i) AddCommGrpCat.{max u v + 1} ⥤ AddCommGrpCat.{max u v + 1} :=
  Sheaf.functorH.{max u v + 1, max u v + 1, max u v + 1, max u v + 1}
    ((sys D c B hD hX hc).J i) p

/-- **Passing to the small model of a level does not change cohomology.** -/
def levelCohomologyFunctorIso (p : ℕ) :
    restrictToLevel D c B hD hX hc i ⋙ levelCohomologyFunctor D c B hD hX hc i p ≅
      affineEtaleCohomologyFunctor B (levelScheme D c B hD hX hc i)
        (hD (levelIndex D c B hD hX hc i)) p :=
  Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence.{max u v + 1,
      max u v + 1, max u v, max u v + 1} ((sys D c B hD hX hc).J i)
    (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
      (hD (levelIndex D c B hD hX hc i))) (levelAffineEtaleFunctor D c B hD hX hc i) p

/-- **Passing to the small model of a level does not change cohomology, read on injective
resolutions.** The same statement as `levelCohomologyFunctorIso` and under the same hypotheses,
built from `Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence'` in place of
`Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence`, so that its engine is
Stacks 015Z on the globally chosen injective resolution. That is what makes it comparable
with the Leray edge morphism; see
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp_inv_app_eq_edge_app`. -/
def levelCohomologyFunctorIso' (p : ℕ) :
    restrictToLevel D c B hD hX hc i ⋙ levelCohomologyFunctor D c B hD hX hc i p ≅
      affineEtaleCohomologyFunctor B (levelScheme D c B hD hX hc i)
        (hD (levelIndex D c B hD hX hc i)) p :=
  Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence'.{max u v + 1,
      max u v + 1, max u v, max u v + 1} ((sys D c B hD hX hc).J i)
    (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
      (hD (levelIndex D c B hD hX hc i))) (levelAffineEtaleFunctor D c B hD hX hc i) p

/-- **The abelian sheaf on the small etale site of `X_i` that an abelian sheaf on the level `i`
comes from.** Invert the level equivalence, then invert the equivalence of Stacks 04HR. -/
abbrev levelToSmallEtale :
    Sheaf ((sys D c B hD hX hc).J i) AddCommGrpCat.{max u v + 1} ⥤
      Sheaf (AlgebraicGeometry.SmallEtale.topology B (levelScheme D c B hD hX hc i)
        (hD (levelIndex D c B hD hX hc i))) AddCommGrpCat.{max u v + 1} :=
  (restrictToLevel D c B hD hX hc i).asEquivalence.inverse ⋙
    (restrictToAffineEtale B (levelScheme D c B hD hX hc i)
      (hD (levelIndex D c B hD hX hc i))).asEquivalence.inverse

/-- **The cohomology of the level `i` is the library's etale cohomology of `X_i`.** For every
degree `p`,

`H^p(C_i, F) ≅ H^p_etale(X_i, F')`

naturally in the abelian sheaf `F` on the level, where `F'` is the abelian sheaf on the small
etale site of `X_i` that `F` comes from (`levelToSmallEtale`). -/
def levelCohomologyFunctorIsoEtaleCohomology (p : ℕ) :
    levelCohomologyFunctor D c B hD hX hc i p ≅
      levelToSmallEtale D c B hD hX hc i ⋙
        Stacks.EtaleCohomology.etaleCohomologyFunctor B
          ⟨levelScheme D c B hD hX hc i, hD (levelIndex D c B hD hX hc i)⟩ p :=
  ((restrictToLevel D c B hD hX hc i).asEquivalence.invFunIdAssoc
      (levelCohomologyFunctor D c B hD hX hc i p)).symm ≪≫
    Functor.isoWhiskerLeft _ (levelCohomologyFunctorIso D c B hD hX hc i p) ≪≫
    Functor.isoWhiskerLeft _ (affineEtaleCohomologyFunctorIsoInv B
      (levelScheme D c B hD hX hc i) (hD (levelIndex D c B hD hX hc i)) p) ≪≫
    (Functor.associator _ _ _).symm

/-- **The cohomology of the level `i` is the library's etale cohomology of `X_i`, read on
injective resolutions.** The same statement as `levelCohomologyFunctorIsoEtaleCohomology` and
under the same hypotheses, built from `levelCohomologyFunctorIso'`, so that the comparison of the
level with its small model is Stacks 015Z on the globally chosen injective resolution rather than
δ-functor universality.

This is the form a consumer must use to relate the object-by-object identification of the
cohomology diagram of Stacks 09YQ to the Leray edge morphisms that are its transition maps: the
transition maps are edge morphisms by
`Stacks.WeakSites.ColimitSiteCohomology.CohomologyCocone.diagram_map_eq_edge_app`, and an edge
morphism is identified with the engine of this comparison by
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp_inv_app_eq_edge_app`, whereas no such
identification is available for `levelCohomologyFunctorIsoEtaleCohomology`. -/
def levelCohomologyFunctorIsoEtaleCohomology' (p : ℕ) :
    levelCohomologyFunctor D c B hD hX hc i p ≅
      levelToSmallEtale D c B hD hX hc i ⋙
        Stacks.EtaleCohomology.etaleCohomologyFunctor B
          ⟨levelScheme D c B hD hX hc i, hD (levelIndex D c B hD hX hc i)⟩ p :=
  ((restrictToLevel D c B hD hX hc i).asEquivalence.invFunIdAssoc
      (levelCohomologyFunctor D c B hD hX hc i p)).symm ≪≫
    Functor.isoWhiskerLeft _ (levelCohomologyFunctorIso' D c B hD hX hc i p) ≪≫
    Functor.isoWhiskerLeft _ (affineEtaleCohomologyFunctorIsoInv B
      (levelScheme D c B hD hX hc i) (hD (levelIndex D c B hD hX hc i)) p) ≪≫
    (Functor.associator _ _ _).symm

/-- **The right derived functors of sections over a terminal object of the level `i` are its sheaf
cohomology.** The terminal object is arbitrary: the objects the cohomology diagram of Stacks 09YQ
is taken over are transition images of a terminal object. -/
def rightDerivedSectionsLevelTerminalIso
    (W : (sys D c B hD hX hc).C i) (hW : IsTerminal W) (p : ℕ) :
    (((sheafSections ((sys D c B hD hX hc).J i) AddCommGrpCat.{max u v + 1}).obj
        (op W)).rightDerived p) ≅ levelCohomologyFunctor D c B hD hX hc i p :=
  Stacks.Cohomology.GlobalSections.rightDerivedSectionsIsoFunctorH
    ((sys D c B hD hX hc).J i) W hW p

/-- **The cohomology of Stacks 09YQ at a level is the library's etale cohomology of `X_i`.** For
every terminal object `W` of the level `i` and every degree `p`, the right derived functors of
sections over `W` are `H^p_etale(X_i, -)`. -/
def levelTerminalCohomologyIsoEtaleCohomology
    (W : (sys D c B hD hX hc).C i) (hW : IsTerminal W) (p : ℕ) :
    (((sheafSections ((sys D c B hD hX hc).J i) AddCommGrpCat.{max u v + 1}).obj
        (op W)).rightDerived p) ≅
      levelToSmallEtale D c B hD hX hc i ⋙
        Stacks.EtaleCohomology.etaleCohomologyFunctor B
          ⟨levelScheme D c B hD hX hc i, hD (levelIndex D c B hD hX hc i)⟩ p :=
  rightDerivedSectionsLevelTerminalIso D c B hD hX hc i W hW p ≪≫
    levelCohomologyFunctorIsoEtaleCohomology D c B hD hX hc i p

end Levels

/-! ### Stacks 09YQ with the cohomology at the limit identified -/

section Affine

open Stacks.WeakSites.ColimitSiteCohomology

variable [∀ i : Iᵒᵖ, IsAffine (D.obj i)]

/-- **The object of the site of the limit that Stacks 09YQ takes its cohomology over is
terminal**: it is the image of the terminal object `X_i` of a level. -/
def toLimitLevelTerminal_isTerminal (i : (sys D c B hD hX hc).I) :
    IsTerminal ((toLimitSmall D c B hD hX hc i).obj (levelTerminal D c B hD hX hc i)) :=
  toLimitImage_isTerminal D c B hD hX hc i _ (levelTerminal_isTerminal D c B hD hX hc i)

variable (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, v, max u v + 1, max u v + 1}
    (sys D c B hD hX hc))
  (𝒢 : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1})

/-- **The vertex of the cohomology cocone of Stacks 09YQ is the etale cohomology group
`H^p_etale(X, -)`.** -/
def coconeVertexIsoEtaleCohomology (i : (sys D c B hD hX hc).I) (p : ℕ) :
    ((((sheafSections (limitSitePrecoverage D c B hX).toGrothendieck
            Ab.{max u v + 1}).obj
          (op ((toLimitSmall D c B hD hX hc i).obj
            (levelTerminal D c B hD hX hc i)))).rightDerived p).obj 𝒢) ≅
      (Stacks.EtaleCohomology.etaleCohomologyFunctor B ⟨c.pt, hX⟩ p).obj
        ((raisedToSmallEtale B c.pt hX).obj 𝒢) :=
  (limitCohomologyFunctorIsoEtaleCohomology D c B hX _
    (toLimitLevelTerminal_isTerminal D c B hD hX hc i) p).app 𝒢

variable (ι : ∀ j, (F.obj j).obj ⟶ (toLimitSmall D c B hD hX hc j).op ⋙ 𝒢.obj)

/-- **Stacks 09YQ in the affine case, with the cohomology at the limit identified with the
library's etale cohomology.** The canonical cohomology cocone of Stacks 09YQ, with its vertex
transported along `coconeVertexIsoEtaleCohomology`, is a colimit cocone: so the filtered colimit
over the arrows `a : j ⟶ i` of the groups `H^p(X_j, F_j)` is the etale cohomology group
`H^p_etale(X, 𝒢')`, where `𝒢'` is the abelian sheaf on the small etale site of `X` that `𝒢`
comes from. -/
def etaleCohomologyColimit_isColimit_of_affine_etaleVertex
    (hcolim : IsColimitPresentation.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) F 𝒢 ι)
    (i : (sys D c B hD hX hc).I) (p : ℕ)
    (E : CohomologyCocone.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) F 𝒢 ι i
      (levelTerminal D c B hD hX hc i) p) :
    IsColimit (E.cocone.extend
      (coconeVertexIsoEtaleCohomology D c B hD hX hc 𝒢 i p).hom) :=
  IsColimit.ofIsoColimit
    (etaleCohomologyColimit_isColimit_of_affine D c B hD hX hc F 𝒢 ι hcolim i p E)
    (Cocone.ext (coconeVertexIsoEtaleCohomology D c B hD hX hc 𝒢 i p) fun _ => rfl)

/-- **Every group of the cohomology diagram of Stacks 09YQ is an etale cohomology group of a level
scheme.** The value of the diagram at an arrow `A : j ⟶ i` is `H^p_etale(X_j, F_j')`, where `F_j'`
is the abelian sheaf on the small etale site of `X_j` that the sheaf `F_j` of the system comes
from.

The object the cohomology is taken over is the transition image of the terminal object of the
level `i`, which is terminal (`transitionImage_isTerminal`), so
`levelTerminalCohomologyIsoEtaleCohomology` applies to it. -/
def diagramObjIsoEtaleCohomology
    (ι : ∀ j, (F.obj j).obj ⟶ (toLimitSmall D c B hD hX hc j).op ⋙ 𝒢.obj)
    (i : (sys D c B hD hX hc).I) (p : ℕ)
    (E : CohomologyCocone.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) F 𝒢 ι i
      (levelTerminal D c B hD hX hc i) p)
    (A : Over i) :
    E.diagram.obj (op A) ≅
      (Stacks.EtaleCohomology.etaleCohomologyFunctor B
          ⟨levelScheme D c B hD hX hc A.left, hD (levelIndex D c B hD hX hc A.left)⟩ p).obj
        ((levelToSmallEtale D c B hD hX hc A.left).obj (F.obj A.left)) :=
  E.objIso A ≪≫
    (levelTerminalCohomologyIsoEtaleCohomology D c B hD hX hc A.left _
      (transitionImage_isTerminal D c B hD hX hc A.hom (levelTerminal D c B hD hX hc i)
        (levelTerminal_isTerminal D c B hD hX hc i)) p).app (F.obj A.left)

end Affine

end Stacks.EtaleCohomology.AffineLimitCohomology

end
