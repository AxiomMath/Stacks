module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyAlongAMorphismOfLocalizedSites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.AbelianComparisonSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiCohomologyPresheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.Sheafification
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.FibrewiseSoftPullback

/-!
# Cohomology of a Zariski comparison inverse image at the open subobjects of an object

Let `S` be a locally quasi-compact Zariski situation, let `q : T ⟶ X` be a morphism of its site —
that is, an object `Over.mk q` of the localized Zariski site `LC_Zar/X` — and let
`π_X : Sh(LC_Zar/X) → Sh(X_Zar)` be the comparison morphism of topoi. For an abelian sheaf `J` on
the small Zariski site of `X` this file computes

`H^p(V, q^{-1} J) ≅ H^p_{LC_Zar/X}(ι_T V, π_X^{-1} J)`   for `V` an open subset of `T`,

**naturally in `V`**, where `ι_T V` is the open subobject of `Over.mk q` cut out by `V`, that is
`(Over.map q) ((S.opensToSlice T) V)`.

`zariskiRightDerivedSectionsOverIso` is the same computation at one object `Over.mk q` only, and a
per-object isomorphism cannot transport a statement about *restriction maps*. The derived clause of
[Stacks, Tag 0DCU] needs exactly that: the local vanishing it must verify at an object `W` of
`LC_Zar/Y` says that a class dies after restriction along the open immersions of a cover of
`W.left`, and the classes on the two sides of the comparison are matched by this isomorphism. So
naturality in the open subset is the point, and that is what is proved here.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiRightDerivedPresheafOverOpensIso`:
  the displayed isomorphism, as an isomorphism of presheaves on `Opens T`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.enoughInjectives_sheafOpens_site`: abelian
  sheaves on the small Zariski site of an object of the situation have enough injectives in the
  situation's coefficient universe.

## Implementation notes

The three steps are the three clauses of the tag that are already in the library, each in its
*presheaf* form rather than at one object:

1. `zariskiRightDerivedPresheafComparisonIso` at `T`, the cohomology clause natural in the open
   subset: `H^p(-, q^{-1}J) ≅ H^p_{LC_Zar/T}(ι_T(-), π_T^{-1}(q^{-1}J))`;
2. `abelianZariskiComparisonSquareIso` at `q`, the commutative-square clause on abelian sheaves,
   which identifies `π_T^{-1}(q^{-1}J)` with the restriction of `π_X^{-1}J` along `Over.map q`;
3. `Stacks.Cohomology.LocalizedSite.overMapPullbackRightDerivedSheafToPresheafIso` at `Over.map q`,
   cohomology along a morphism of localized sites as presheaves on `LC_Zar/T` — the presheaf form
   of the objectwise `overMapPullbackRightDerivedSectionsIso` that
   `zariskiRightDerivedSectionsOverIso` uses.

Steps 2 and 3 live on `LC_Zar/T` and are composed there, then whiskered with
`(S.opensToSlice T).1.op`; step 1 already lands on `Opens T`. Because every step is an
isomorphism of presheaves, no passage between `ι_T ⊤` and `Over.mk (𝟙 T)` is needed, and the
terminal-object gymnastics of `zariskiRightDerivedSectionsOverIso` disappears.

The three `EnoughInjectives` hypotheses have to be binders, because `Functor.rightDerived` needs
`HasInjectiveResolutions` already to *state* the isomorphism; but they are not restrictions on
the generality, and `enoughInjectives_sheafOpens_site` and `enoughInjectives_zariskiSliceSheaf`
discharge them at every object of the situation. `HasSheafify` is an instance of the situation,
`hasSheafify_opens` and `hasSheafify_zariskiOver`, including in the `∀ U` form that cohomology
along a morphism of localized sites asks for.

The coefficients of `Stacks.Topology.inverseImageUnivLE` are a free universe, so writing `q^{-1}J`
through it rather than through `TopCat.Sheaf.pullback` is what lets the statement be read at
`max (u + 1) v`; the two agree on the nose when the coefficient universe is that of the space.

This declaration carries no tag. Stacks 0DCU has eight claim-sites and the covering set of the tag
is not complete until all of them are in the library.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- **The cohomology of a Zariski comparison inverse image at the open subobjects of an object of
the big site.** For `q : T ⟶ X` a morphism of the locally quasi-compact Zariski site and `J` an
abelian sheaf on the small Zariski site of `X`,

`H^p(V, q^{-1} J) ≅ H^p_{LC_Zar/X}((Over.map q) (ι_T V), π_X^{-1} J)`,

an isomorphism of presheaves on `Opens T`, hence natural in the open subset `V`.

At one object this is `zariskiRightDerivedSectionsOverIso`; the naturality in `V` is what the
derived clause of [Stacks, Tag 0DCU] needs, since the local vanishing it has to verify is a
statement about restriction along the open immersions of a cover. -/
def zariskiRightDerivedPresheafOverOpensIso {T X : S.category} (q : T ⟶ X)
    [EnoughInjectives (Sheaf (Opens.grothendieckTopology T.obj) AddCommGrpCat.{max (u + 1) v})]
    [EnoughInjectives (Sheaf (S.zariskiTopology.over T) AddCommGrpCat.{max (u + 1) v})]
    [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]
    (p : ℕ)
    (J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) :
    (((sheafToPresheaf (Opens.grothendieckTopology T.obj)
            AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
        ((inverseImageUnivLE.{max (u + 1) v}
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map q)).obj J)) ≅
      (S.opensToSlice T).1.op ⋙ (Over.map q).op ⋙
        (((sheafToPresheaf (S.zariskiTopology.over X)
            AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J)) :=
  (zariskiRightDerivedPresheafComparisonIso.{u, w, v} S T p).app
      ((inverseImageUnivLE.{max (u + 1) v}
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map q)).obj J) ≪≫
    Functor.isoWhiskerLeft (S.opensToSlice T).1.op
      ((((sheafToPresheaf (S.zariskiTopology.over T)
              AddCommGrpCat.{max (u + 1) v}).rightDerived p).mapIso
            ((abelianZariskiComparisonSquareIso.{u, w, v} S q).app J)) ≪≫
        (Stacks.Cohomology.LocalizedSite.overMapPullbackRightDerivedSheafToPresheafIso
            S.zariskiTopology q p).app
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J))

/-- **The `EnoughInjectives` hypotheses of
`zariskiRightDerivedPresheafOverOpensIso` are inhabited at every object of the situation.** For
the small Zariski site this is `Stacks.Topology.enoughInjectives_sheafOpens`, which applies
because `UnivLE.{u, max (u + 1) v}` holds with no hypothesis; for the localized big site it is
`enoughInjectives_zariskiSliceSheaf`. -/
theorem enoughInjectives_sheafOpens_site (T : S.category) :
    EnoughInjectives (Sheaf (Opens.grothendieckTopology T.obj) AddCommGrpCat.{max (u + 1) v}) :=
  Stacks.Topology.enoughInjectives_sheafOpens.{max (u + 1) v}
    ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj T)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
