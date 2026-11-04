module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SiteEquivalenceGlobalCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# An equivalence of chaotic sites does not change sheaf cohomology

Let `e : C ≌ D` be an equivalence of categories and endow both with the chaotic topology `⊥` of
[Stacks, Tag 07GE], for which every presheaf is a sheaf.  Restriction of abelian sheaves along
`e.functor` is then an equivalence of the two sheaf topoi, and it changes neither the constant
sheaf on `ℤ` nor the injective objects, hence not the `Ext`-groups out of the constant sheaf:

`H^p(C, F|_C) ≅ H^p(D, F)`,

naturally in the abelian sheaf `F` on `(D, ⊥)` and in every degree `p`, where `H^p` is Mathlib's
`CategoryTheory.Sheaf.functorH`.

The cohomological content is entirely
`Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence`, which asks for no
terminal object and does not tie the morphism universes of the two sites together.  What this
file supplies are the three site-theoretic inputs that make that statement available for a bare
equivalence of categories with the chaotic topology: every functor is continuous for the chaotic
topologies, every functor is cocontinuous into a chaotic site, and restriction of sheaves along an
equivalence of chaotic sites is an equivalence.

## Main definitions

* `Stacks.ChaoticSite.chaoticRestriction` — restriction of abelian sheaves along `e.functor`
  between the two chaotic sites.

## Main results

* `Stacks.ChaoticSite.isContinuous_bot_bot` — every functor is continuous for the chaotic
  topologies.
* `Stacks.ChaoticSite.isCocontinuous_bot` — every functor is cocontinuous into a chaotic site,
  for an arbitrary topology on the source.
* `Stacks.ChaoticSite.isEquivalence_chaoticRestriction` — **restriction of sheaves along an
  equivalence of chaotic sites is an equivalence of the sheaf topoi.**
* `Stacks.ChaoticSite.chaoticCohomologyIsoOfEquivalence` — **an equivalence of chaotic sites does
  not change global cohomology**, as an isomorphism of functors.
* `Stacks.ChaoticSite.sheafHAddEquivOfEquivalence` — the same at a fixed abelian sheaf, as an
  additive equivalence of the cohomology groups.
* `Stacks.ChaoticSite.sheafHAddEquivOfEquivalence'` — the form in which a sheaf given on the
  *source* site is transported: the cohomology of a sheaf on `(C, ⊥)` is the cohomology of its
  image under the inverse equivalence on `(D, ⊥)`.

## Implementation notes

[Stacks, Tag 03YU] is the statement that restriction along a suitable functor of sites does not
change global cohomology; what is below is its specialisation to an equivalence of chaotic sites.

The two sheaf categories must admit sheafification, have enough injectives and have `Ext`-groups
in their common morphism universe.  The two sites are required to have their
*objects* in one universe, because
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp`, through which the comparison is proved,
needs the two abelian categories to share their morphism universe, and the morphism universe of
a sheaf category is the join of the object universe of the site with the coefficient universe.
Their *morphism* universes are independent, which is what a small model of a site needs; see
`Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence`.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 07GE](https://stacks.math.columbia.edu/tag/07GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace Stacks.ChaoticSite

universe w vA uA v v' u u'

/-! ### The site-theoretic inputs -/

section Sites

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- **Every functor is continuous for the chaotic topologies.**  Restriction of a presheaf along
a functor is a presheaf, and for the chaotic topology every presheaf is a sheaf. -/
instance isContinuous_bot_bot (G : C ⥤ D) :
    G.IsContinuous (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D) where
  op_comp_isSheaf_of_types _ := Presieve.isSheaf_bot

/-- **Every functor is cocontinuous into a chaotic site**, for an arbitrary topology on the
source.  The only covering sieve of the chaotic topology is the maximal one, whose pullback is
maximal and therefore covering. -/
instance isCocontinuous_bot (G : C ⥤ D) (J : GrothendieckTopology C) :
    G.IsCocontinuous J (⊥ : GrothendieckTopology D) where
  cover_lift {U S} hS := by
    rw [GrothendieckTopology.bot_covering] at hS
    subst hS
    exact J.top_mem U

variable (e : C ≌ D) (A : Type uA) [Category.{vA} A]

/-- **Restriction of sheaves along an equivalence of chaotic sites**, `F ↦ F|_C`. -/
abbrev chaoticRestriction :
    Sheaf (⊥ : GrothendieckTopology D) A ⥤ Sheaf (⊥ : GrothendieckTopology C) A :=
  e.functor.sheafPushforwardContinuous A (⊥ : GrothendieckTopology C)
    (⊥ : GrothendieckTopology D)

/-- **Restriction of sheaves along an equivalence of chaotic sites is an equivalence** of the two
sheaf topoi.  Both directions of the equivalence are cocontinuous for the chaotic topologies, so
`e.inverse` exhibits a dense subsite and restriction along `e.functor` is the inverse of
Mathlib's `CategoryTheory.Equivalence.sheafCongr`. -/
instance isEquivalence_chaoticRestriction : (chaoticRestriction e A).IsEquivalence :=
  have := Equivalence.isDenseSubsite_inverse_of_isCocontinuous
    (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D) e
  Functor.isEquivalence_of_iso
    (Iso.refl _ :
      (e.sheafCongr (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D) A).inverse ≅
        chaoticRestriction e A)

/-- The equivalence of sheaf topoi attached to an equivalence of chaotic sites, with restriction
along `e.functor` as its inverse. -/
abbrev chaoticSheafEquiv :
    Sheaf (⊥ : GrothendieckTopology C) A ≌ Sheaf (⊥ : GrothendieckTopology D) A :=
  have := Equivalence.isDenseSubsite_inverse_of_isCocontinuous
    (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D) e
  e.sheafCongr (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D) A

end Sites

/-! ### The comparison of cohomology -/

section Cohomology

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v'} D] (e : C ≌ D)
  [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{w}]
  [HasSheafify (⊥ : GrothendieckTopology D) AddCommGrpCat.{w}]
  [HasExt.{max u w} (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w})]
  [HasExt.{max u w} (Sheaf (⊥ : GrothendieckTopology D) AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf (⊥ : GrothendieckTopology D) AddCommGrpCat.{w})]
  [∀ X, HasLimitsOfShape (StructuredArrow X e.functor.op) AddCommGrpCat.{w}]

/-- **An equivalence of chaotic sites does not change global cohomology.**  For every degree `p`,

`H^p(C, F|_C) ≅ H^p(D, F)`

naturally in the abelian sheaf `F` on `(D, ⊥)`.  This is
`Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence` with its three
site-theoretic hypotheses supplied by `isContinuous_bot_bot`, `isCocontinuous_bot` and
`isEquivalence_chaoticRestriction`; no terminal object is involved, and the morphism universes of
the two sites need not agree. -/
def chaoticCohomologyIsoOfEquivalence (p : ℕ) :
    chaoticRestriction e AddCommGrpCat.{w} ⋙
        Sheaf.functorH.{max u w, w, v, u} (⊥ : GrothendieckTopology C) p ≅
      Sheaf.functorH.{max u w, w, v', u} (⊥ : GrothendieckTopology D) p :=
  Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence.{w, v, v', u}
    (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D) e.functor p

/-- **The cohomology of an abelian sheaf on a chaotic site is the cohomology of its restriction
along an equivalence**, at a fixed sheaf and in the form of an additive equivalence of the
cohomology groups. -/
def sheafHAddEquivOfEquivalence (F : Sheaf (⊥ : GrothendieckTopology D) AddCommGrpCat.{w})
    (p : ℕ) :
    Sheaf.H.{max u w, w} ((chaoticRestriction e AddCommGrpCat.{w}).obj F) p ≃+
      Sheaf.H.{max u w, w} F p :=
  ((chaoticCohomologyIsoOfEquivalence.{w} e p).app F).addCommGroupIsoToAddEquiv

/-- **The cohomology of an abelian sheaf on a chaotic site is the cohomology of its transport
across an equivalence.**  This is `sheafHAddEquivOfEquivalence` read in the other direction: a
sheaf `G` on `(C, ⊥)` is carried to the sheaf `chaoticSheafEquiv e _ |>.functor.obj G` on
`(D, ⊥)` whose restriction is `G` again, up to the unit isomorphism of the equivalence. -/
def sheafHAddEquivOfEquivalence' (G : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w})
    (p : ℕ) :
    Sheaf.H.{max u w, w} G p ≃+
      Sheaf.H.{max u w, w}
        ((chaoticSheafEquiv e AddCommGrpCat.{w}).functor.obj G) p :=
  (((Sheaf.functorH.{max u w, w, v, u} (⊥ : GrothendieckTopology C) p).mapIso
      ((chaoticSheafEquiv e AddCommGrpCat.{w}).unitIso.app G)).addCommGroupIsoToAddEquiv).trans
    (sheafHAddEquivOfEquivalence.{w} e
      ((chaoticSheafEquiv e AddCommGrpCat.{w}).functor.obj G) p)

end Cohomology

end Stacks.ChaoticSite

end
