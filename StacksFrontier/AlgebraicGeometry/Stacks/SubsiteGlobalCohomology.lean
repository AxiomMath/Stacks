module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteObjectwiseCohomology

/-!
# Global cohomology on a full subsite of the site of an algebraic stack

Stacks 0GR0 compares the cohomology of an abelian sheaf on the étale (respectively fppf) site of
an algebraic stack with the cohomology of its inverse image on the lisse-étale (respectively
flat-fppf) site of Stacks 0787, both *over an object* — parts (1)(b) and (2)(b), proved in
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteObjectwiseCohomology.lean` — and *globally*, which
is parts (1)(a) and (2)(a). This file is about the global half.

What it proves is the reduction of the global comparison to its own degree-zero case: for a full
subsite whose inclusion is continuous and cocontinuous, if the restriction of an injective
abelian sheaf is acyclic (Stacks 0D6X) and if the lower shriek carries the constant sheaf on `ℤ`
of the subsite to the constant sheaf on `ℤ` of the ambient site, then the comparison holds in
*every* degree. The same for sheaves of modules, with the constant sheaf replaced by the
structure sheaf.

## Main results

* `AlgebraicGeometry.Stack.subsiteCohomologyIso`: the global comparison of abelian cohomology
  along the inclusion of a full subsite, from acyclicity and the degree-zero comparison.
* `AlgebraicGeometry.Stack.subsiteModuleCohomologyIso`: the same for sheaves of modules.

Both are **untagged**: they are the reduction, and the two inputs are proved for every full
subcategory satisfying the conditions of Stacks 07AK in
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteCohomologyAtlas.lean`, which carries the
registration of the tag.

## Why the two engines cannot be used at a terminal object

The library's engines for the comparison of global cohomology along a functor of sites,
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfAcyclic` and
`Stacks.Cohomology.BiggerSiteModules.moduleCohomologyIsoOfAcyclic`, ask for a terminal object of
the source site whose image is terminal in the target. That hypothesis is **not available here**,
and not for an accidental reason: by
`CategoryTheory.Functor.IsFiberedInGroupoids.not_isTerminal_of_faithful_of_ne_id`, a full
subcategory of a category fibred in groupoids has a terminal object only if every object of that
subcategory has trivial vertical automorphisms. An algebraic stack with a nontrivial automorphism
therefore has no terminal object in `𝒳_τ` and none in either subsite of Stacks 0787. (Parts
(1)(b) and (2)(b) are unaffected: there the site is the *slice* `𝒳'/x`, whose terminal object is
`𝟙 x` whatever the automorphisms of `𝒳` — which is exactly why the objectwise half goes through
and the global half does not.)

Nor is *finality* of the inclusion the real requirement, though `final_of_isTerminal_obj` was
built for this area. Finality enters only the module engine, and only as a route to invertibility
of Mathlib's `SheafOfModules.pullbackObjUnitToUnit`; the abelian engine does not mention finality
at all, using the terminal objects through
`Stacks.Cohomology.BiggerSiteGlobal.lowerShriekConstantSheafIso` instead. In both halves the one
datum consumed is the comparison of **unit objects**, `g_! ℤ_{𝒳'} ≅ ℤ_𝒳` and `g_! g^*O ≅ O`. So
the statements below are instances of the two engines with the terminal objects weakened to that
datum: `Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIsoOfAcyclic` and
`Stacks.Cohomology.BiggerSiteModules.moduleCohomologyIsoOfUnitIsoOfAcyclic`.

## What the reduction says

By the adjunction `g_! ⊣ g^{-1}`, the unit comparison `g_! ℤ_{𝒳'} ≅ ℤ_𝒳` is equivalent to
`Γ(𝒳', g^{-1}F) ≅ Γ(𝒳, F)`, naturally in `F` — that is, to parts (1)(a) and (2)(a) of Stacks
0GR0 *in degree zero*. So what the statements below say is: **degree zero plus Stacks 0D6X gives
every degree.** The propagation is the universality of `Ext` as a `δ`-functor,
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIsoOfAcyclic`.

This is a strictly shorter route than the source's. The proof of Stacks 07AK which 0GR0 cites
compares the full Čech-to-cohomology spectral sequences (\ref{07AL}) and (\ref{07AM}) of Stacks
079Z for the covering `h_x ⟶ *` given by the smooth surjective atlas of 07AK (2), degree by
degree. Only the `E_1^{•,0}` row of that comparison — the degree-zero statement — is needed
above; the spectral sequence of Stacks 079Z is not.

## References

* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 0GR0](https://stacks.math.columbia.edu/tag/0GR0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open Stacks.Cohomology.BiggerSiteModules Stacks.Cohomology.DerivedLowerShriek

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
  (τ : GrothendieckTopology B.Schemes) (P : ObjectProperty X)

/-! ### Sheafification, injectives and `Ext` on the two global sites

Neither site is small, and the morphisms live in a smaller universe than the objects, so the
coefficient universe is the join of the two. At that universe every site admits sheafification
and enough injective abelian sheaves and has `Ext`-groups, by the statements of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/CohomologyOfModules.lean`; they are recorded
here as instances with the universe pinned, because left free it is a metavariable the elaborator
cannot solve against these sites. This is the unsliced counterpart of the `SliceInstances`
section of `StacksFrontier/AlgebraicGeometry/Stacks/SubsiteObjectwiseCohomology.lean`. -/

section SiteInstances

/-- Abelian presheaves on the full subsite admit sheafification. -/
instance hasSheafify_fullSubsite :
    HasSheafify (subsiteTopology B S hS p τ P) AddCommGrpCat.{max v w} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{v, w, max v w}

/-- Abelian presheaves on the site associated to the stack admit sheafification. -/
instance hasSheafify_associatedSite :
    HasSheafify (associatedTopology B S hS p τ) AddCommGrpCat.{max v w} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{v, w, max v w}

/-- On the full subsite, the morphisms of abelian presheaves inverted by sheafification are the
locally bijective ones. -/
instance wEqualsLocallyBijective_fullSubsite :
    (subsiteTopology B S hS p τ P).WEqualsLocallyBijective AddCommGrpCat.{max v w} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{v, w, max v w}

/-- On the site associated to the stack, the morphisms of abelian presheaves inverted by
sheafification are the locally bijective ones. -/
instance wEqualsLocallyBijective_associatedSite :
    (associatedTopology B S hS p τ).WEqualsLocallyBijective AddCommGrpCat.{max v w} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{v, w, max v w}

/-- The category of abelian sheaves on the full subsite has enough injectives. -/
instance enoughInjectives_sheaf_fullSubsite :
    EnoughInjectives (Sheaf (subsiteTopology B S hS p τ P) AddCommGrpCat.{max v w}) :=
  Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{v, w, max v w}

/-- The category of abelian sheaves on the site associated to the stack has enough injectives. -/
instance enoughInjectives_sheaf_associatedSite :
    EnoughInjectives (Sheaf (associatedTopology B S hS p τ) AddCommGrpCat.{max v w}) :=
  Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{v, w, max v w}

/-- The category of abelian sheaves on the full subsite has `Ext`-groups in universe `max v w`. -/
instance hasExt_sheaf_fullSubsite :
    HasExt.{max v w} (Sheaf (subsiteTopology B S hS p τ P) AddCommGrpCat.{max v w}) :=
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{v, w, max v w}

/-- The category of abelian sheaves on the site associated to the stack has `Ext`-groups in
universe `max v w`. -/
instance hasExt_sheaf_associatedSite :
    HasExt.{max v w} (Sheaf (associatedTopology B S hS p τ) AddCommGrpCat.{max v w}) :=
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{v, w, max v w}

end SiteInstances

/-- Restriction of abelian sheaves along the inclusion of a full subsite: the inverse image
`g^{-1}` of the morphism of topoi of Stacks 07AK. -/
abbrev subsiteRestriction
    [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)] :
    Sheaf (associatedTopology B S hS p τ) AddCommGrpCat.{max v w} ⥤
      Sheaf (subsiteTopology B S hS p τ P) AddCommGrpCat.{max v w} :=
  P.ι.sheafPushforwardContinuous AddCommGrpCat.{max v w}
    (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)

variable [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
  [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
  [(subsiteRestriction B S hS p τ P).IsRightAdjoint]

/-- **Stacks 07AK, global cohomology, from acyclicity and the degree-zero comparison.** Let `P`
cut out a full subcategory of the objects of a category fibred in groupoids over the big fppf
category of `S`, endowed with the site of Stacks 06TP, and suppose the inclusion is continuous
and cocontinuous — which, by Stacks 07AK (1), it is as soon as `P` is closed under the morphisms
lying over the relevant class of morphisms of schemes. Suppose that `g_!` carries the constant
sheaf on `ℤ` of the subsite to the constant sheaf on `ℤ` of the ambient site, and that the
restriction of an injective abelian sheaf is acyclic on the subsite. Then for every degree `q`

`H^q(P, g^{-1}F) ≅ H^q(𝒳, F)`

naturally in the abelian sheaf `F` on the ambient site.

The second hypothesis is Stacks 0D6X for the inclusion. The first is the degree-zero case of the
conclusion: by the adjunction `g_! ⊣ g^{-1}` it says exactly that restriction does not change
global sections. So this statement is the implication *degree zero implies every degree*, and the
spectral sequence of Stacks 079Z which the source's proof of 07AK uses is not needed for it; see
the module docstring. -/
def subsiteCohomologyIso
    (hunit : (Stacks.Cohomology.lowerShriekAbelian
          (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ) P.ι).obj
        ((constantSheaf (subsiteTopology B S hS p τ P) AddCommGrpCat.{max v w}).obj
          (AddCommGrpCat.of (ULift.{max v w} ℤ))) ≅
      (constantSheaf (associatedTopology B S hS p τ) AddCommGrpCat.{max v w}).obj
        (AddCommGrpCat.of (ULift.{max v w} ℤ)))
    (hacyclic : ∀ I : Sheaf (associatedTopology B S hS p τ) AddCommGrpCat.{max v w},
      Injective I → ∀ (n : ℕ)
      (a : Sheaf.H ((subsiteRestriction B S hS p τ P).obj I) (n + 1)), a = 0)
    (q : ℕ) :
    subsiteRestriction B S hS p τ P ⋙
        Sheaf.functorH.{max v w, max v w, w, v} (subsiteTopology B S hS p τ P) q ≅
      Sheaf.functorH.{max v w, max v w, w, v} (associatedTopology B S hS p τ) q :=
  haveI := (Functor.sheafAdjunctionCocontinuous P.ι AddCommGrpCat.{max v w}
    (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)).isLeftAdjoint
  Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIsoOfAcyclic
    (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ) P.ι hunit hacyclic q

/-! ### Sheaves of modules

The source's "the same holds for sheaves of modules" is the same comparison with abelian sheaves
replaced by sheaves of modules over the structure sheaf and `H^q` replaced by
`Stacks.Cohomology.BiggerSiteModules.moduleFunctorH`, the `Ext`-groups out of the structure
sheaf. The unit object of `Mod(O)` is `O` itself, so the degree-zero datum there is the
comparison `g_! g^*O ≅ O` rather than `g_! ℤ ≅ ℤ`. -/

section Modules

variable (O : Sheaf (associatedTopology B S hS p τ) RingCat.{max v w t})

/-- The sheaf of rings `g^{-1}O` on a full subsite: the restriction along the inclusion of a
sheaf of rings on the ambient site. For the structure sheaf this is `O_{𝒳'}`, by the
identification `g^{-1}O_𝒳 = O_{𝒳'}` of Stacks 0788 (f). -/
abbrev subsiteRing : Sheaf (subsiteTopology B S hS p τ P) RingCat.{max v w t} :=
  inverseImageRing.{max v w t, w, v, w, v}
    (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ) P.ι O

/-- Restriction of sheaves of modules along the inclusion of a full subsite: the pullback `g^*`
of the morphism of ringed topoi of Stacks 07AK. -/
abbrev subsiteModuleRestriction :
    SheafOfModules.{max v w t} O ⥤
      SheafOfModules.{max v w t} (subsiteRing.{u, v, w, t} B S hS p τ P O) :=
  restrictionModules.{max v w t, w, v, w, v}
    (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ) P.ι O

/-- **Stacks 07AK for sheaves of modules, global cohomology, from acyclicity and the degree-zero
comparison.** Hypotheses as in `AlgebraicGeometry.Stack.subsiteCohomologyIso`, with the constant
sheaf on `ℤ` replaced by the structure sheaf: `g_!` is assumed to exist on sheaves of modules —
the first sentence of Stacks 0789, here for the unsliced subsite — and to carry `g^*O` to `O`,
and the restriction of an injective sheaf of `O`-modules is assumed to have vanishing higher
`Ext` out of the structure sheaf. Then for every degree `q`

`H^q(P, g^*F) ≅ H^q(𝒳, F)`

naturally in the sheaf of `O`-modules `F`, where `H^q` is
`Stacks.Cohomology.BiggerSiteModules.moduleFunctorH`.

As in the abelian case the second hypothesis is the degree-zero case of the conclusion: by the
adjunction `g_! ⊣ g^*` it says that restriction does not change the global sections of a sheaf of
modules. -/
def subsiteModuleCohomologyIso
    [(SheafOfModules.pushforward.{max v w t} (F := P.ι)
      (idRingMap (subsiteTopology B S hS p τ P)
        (associatedTopology B S hS p τ) P.ι O)).IsRightAdjoint]
    (hunit : IsIso (SheafOfModules.pullbackObjUnitToUnit.{_, _, _, _, max v w t}
      (idRingMap (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ) P.ι O)))
    (hacyclic : ∀ I : SheafOfModules.{max v w t} O, Injective I → ∀ (n : ℕ)
      (a : Ext (SheafOfModules.unit (subsiteRing.{u, v, w, t} B S hS p τ P O))
        ((subsiteModuleRestriction.{u, v, w, t} B S hS p τ P O).obj I) (n + 1)), a = 0)
    (q : ℕ) :
    subsiteModuleRestriction.{u, v, w, t} B S hS p τ P O ⋙
        moduleFunctorH.{t, w, v} (subsiteTopology B S hS p τ P)
          (subsiteRing.{u, v, w, t} B S hS p τ P O) q ≅
      moduleFunctorH.{t, w, v} (associatedTopology B S hS p τ) O q :=
  moduleCohomologyIsoOfUnitIsoOfAcyclic.{t, w, v} _ _ _ O hunit hacyclic q

end Modules

end AlgebraicGeometry.Stack

end
