module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.EssentiallySmallSite
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryRingedTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.BiggerSiteGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.BiggerSiteModuleCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous

/-!
# Cohomology over an object of a full subsite of the site of an algebraic stack

Stacks 0GR0 compares the cohomology of an abelian sheaf on the étale (respectively fppf) site of
an algebraic stack with the cohomology of its inverse image on the lisse-étale (respectively
flat-fppf) site of Stacks 0787, both globally and over an object of the subsite. This file proves
the *over an object* half — parts (1)(b) and (2)(b) of the source — for an arbitrary full subsite
at once, and then states it for the two subsites the source names.

## Main results

* `AlgebraicGeometry.Stack.subsiteCohomologyOverObjectIso`: for a full subcategory `P` of the
  objects of an algebraic stack whose inclusion is continuous, and for an object `x` of `P`,
  restriction does not change cohomology over `x`.
* `AlgebraicGeometry.Stack.FlatFppf.cohomologyOverObjectIso`: **Stacks 0GR0** (2)(b), for the
  flat-fppf site.
* `AlgebraicGeometry.Stack.LisseEtale.cohomologyOverObjectIso`: **Stacks 0GR0** (1)(b), for the
  lisse-étale site.
* `AlgebraicGeometry.Stack.subsiteModuleCohomologyOverObjectIso`,
  `AlgebraicGeometry.Stack.FlatFppf.moduleCohomologyOverObjectIso` and
  `AlgebraicGeometry.Stack.LisseEtale.moduleCohomologyOverObjectIso`: the same three statements
  for sheaves of modules, which is the source's "the same holds for sheaves of modules".

## The one hypothesis, and what the tags say

The proof is the second paragraph of the proof of Stacks 07AK, which 0GR0 cites: for a covering
`{x_i → x}` of the subsite the two Čech complexes agree, so an injective abelian sheaf on the
ambient site restricts to a sheaf with vanishing higher Čech cohomology, hence — the coverings of
the subsite being cofinal — to a sheaf with vanishing higher cohomology over every object. That
makes injective sheaves on the ambient site acyclic for cohomology over `x` on the subsite, and
the comparison of the two derived functors follows.

That acyclicity is **Stacks 0D6X**, and it is carried below as the explicit hypothesis
`hacyclic`, named in each tag note. It is *not* available as an instance of the library's form
`Stacks.CechSite.injective_sheaf_sheafCohomology_isZero_of_functor`: that statement requires the
source site's morphism universe to be its coefficient universe and the site itself to be
`Small`, whereas these sites have objects in `Type (u + 1)`, morphisms in `Type u`, and
coefficients in `Type (u + 1)` — the same universe obstruction recorded in the module docstring
of `StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfDerivedLowerShriek.lean` for the acyclicity
input of Stacks 07AS.

What is **not** hypothesised is injectivity of the restriction. Restriction along the inclusion
of either subsite does not preserve injective abelian sheaves, because its left adjoint `g_!` is
not exact: neither subsite is closed under fibre products — a fibre product of two flat objects
over a flat object need not be flat. That is why the comparison is proved here from
`Stacks.Cohomology.BiggerSiteGlobal.cohomologyOverObjectIsoOfAcyclic` rather than from
`Stacks.Cohomology.BiggerSiteGlobal.cohomologyOverObjectIso`, which is Stacks 03YU and asks for
injectivity.

Both statements are conditional on that acyclicity alone, and the two module clauses on its
module form — the vanishing of `Ext^{≥1}` out of the structure sheaf on the restriction of an
injective sheaf of modules. The closure condition of Stacks
07AK (1), which is what makes the inclusion of either subsite continuous and cocontinuous, is
discharged for every algebraic stack with no hypothesis: in the lisse-étale case by
`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`, and in the flat-fppf case by
`AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms`.

## Implementation notes

The two slice sites are essentially small with no hypothesis on the fibres of the stack, by
`AlgebraicGeometry.Stack.essentiallySmall_over_fullSubsite`; but nothing below needs that,
because the sheafification, injectivity and `Ext` inputs are supplied by the universe-enlarging
statements of `StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/CohomologyOfModules.lean`,
which hold for an arbitrary site at coefficients in the join of its two universes. They are
installed as local instances.

Continuity of the slice functor `Over.post P.ι` is
`CategoryTheory.Functor.isContinuous_overPost`; cocontinuity is a Mathlib instance. Together they
make restriction on the slices a functor with adjoints on both sides, whence exact, which is the
remaining input of the comparison.

The module clauses do need the essential smallness of the slice: there the comparison runs
through `Stacks.Cohomology.BiggerSiteModules.moduleCohomologyIsoOfAcyclic`, whose input beyond
exactness of `g^*` is the existence of `g_!` on sheaves of modules, and that is what essential
smallness supplies. For sheaves of modules the ring and the module sections must live in one
universe, the unit object of `Mod(O)` being `O` itself, and that universe must contain the site
for `Mod(O)` to be Grothendieck abelian; so the module universe here is `max (u + 1) t`, one
above the universe `u` in which the slice is essentially small. Moving the smallness up is
`CategoryTheory.essentiallySmall_of_le`.

## References

* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
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

/-! ### Sheafification, injectives and `Ext` on the two slice sites

The slices of the two sites are not small, and their morphisms live in a smaller universe than
their objects, so the coefficient universe is the join of the two. At that universe every site
admits sheafification and enough injective abelian sheaves and has `Ext`-groups, by the
statements of `StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/CohomologyOfModules.lean`.
Those are theorems with a free coefficient universe; they are recorded here as instances with
the universe pinned, because left free it is a metavariable that the elaborator cannot solve
against the slice sites. -/

section SliceInstances

variable (x : P.FullSubcategory) (y : X)

instance hasSheafify_over_fullSubcategory :
    HasSheafify ((subsiteTopology B S hS p τ P).over x) AddCommGrpCat.{max v w} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, max v w}

instance hasSheafify_over_obj :
    HasSheafify ((associatedTopology B S hS p τ).over y) AddCommGrpCat.{max v w} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, max v w}

instance enoughInjectives_sheaf_over_fullSubcategory :
    EnoughInjectives (Sheaf ((subsiteTopology B S hS p τ P).over x) AddCommGrpCat.{max v w}) :=
  Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{max v w, w, max v w}

instance enoughInjectives_sheaf_over_obj :
    EnoughInjectives (Sheaf ((associatedTopology B S hS p τ).over y) AddCommGrpCat.{max v w}) :=
  Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{max v w, w, max v w}

instance hasExt_sheaf_over_fullSubcategory :
    HasExt.{max v w}
      (Sheaf ((subsiteTopology B S hS p τ P).over x) AddCommGrpCat.{max v w}) :=
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{max v w, w, max v w}

instance hasExt_sheaf_over_obj :
    HasExt.{max v w}
      (Sheaf ((associatedTopology B S hS p τ).over y) AddCommGrpCat.{max v w}) :=
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{max v w, w, max v w}

end SliceInstances

/-- Restriction of abelian sheaves along the inclusion of a full subsite, localized at an object
of the subsite: the inverse image of the morphism of topoi of Stacks 07AK, on the slices. -/
abbrev subsiteSliceRestriction (x : P.FullSubcategory)
    [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)] :
    Sheaf ((associatedTopology B S hS p τ).over (P.ι.obj x)) AddCommGrpCat.{max v w} ⥤
      Sheaf ((subsiteTopology B S hS p τ P).over x) AddCommGrpCat.{max v w} :=
  haveI := Functor.isContinuous_overPost (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι x
  (Over.post (X := x) P.ι).sheafPushforwardContinuous AddCommGrpCat.{max v w}
    ((subsiteTopology B S hS p τ P).over x)
    ((associatedTopology B S hS p τ).over (P.ι.obj x))

/-- **Stacks 07AK, cohomology over an object of the subsite, from acyclicity.** Let `P` cut out a
full subcategory of the objects of a category fibred in groupoids over the big fppf category of
`S`, endowed with the site of Stacks 06TP, and suppose the inclusion is continuous and
cocontinuous — which, by Stacks 07AK (1), it is as soon as `P` is closed under the morphisms
lying over the relevant class of morphisms of schemes. Let `x` be an object of `P` and suppose
that the restriction to the slice at `x` of an injective abelian sheaf on the slice of the
ambient site at `x` has vanishing higher cohomology there. Then for every degree `q`

`H^q(P/x, g⁻¹ F) ≅ H^q(𝒳/x, F)`

naturally in the abelian sheaf `F` on the ambient site.

The acyclicity hypothesis is Stacks 0D6X for the inclusion; see the module docstring. -/
def subsiteCohomologyOverObjectIso (x : P.FullSubcategory)
    [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
    [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
    (hacyclic : ∀ I : Sheaf ((associatedTopology B S hS p τ).over (P.ι.obj x))
        AddCommGrpCat.{max v w}, Injective I → ∀ (n : ℕ)
      (a : Sheaf.H ((subsiteSliceRestriction B S hS p τ P x).obj I) (n + 1)), a = 0)
    (q : ℕ) :
    haveI := Functor.isContinuous_overPost (subsiteTopology B S hS p τ P)
      (associatedTopology B S hS p τ) P.ι x
    P.ι.sheafPushforwardContinuous AddCommGrpCat.{max v w}
          (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ) ⋙
        (subsiteTopology B S hS p τ P).overPullback AddCommGrpCat.{max v w} x ⋙
          Sheaf.functorH ((subsiteTopology B S hS p τ P).over x) q ≅
      (associatedTopology B S hS p τ).overPullback AddCommGrpCat.{max v w} (P.ι.obj x) ⋙
        Sheaf.functorH ((associatedTopology B S hS p τ).over (P.ι.obj x)) q :=
  haveI := Functor.isContinuous_overPost (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι x
  haveI := (Functor.sheafAdjunctionCocontinuous (Over.post (X := x) P.ι)
    AddCommGrpCat.{max v w} ((subsiteTopology B S hS p τ P).over x)
    ((associatedTopology B S hS p τ).over (P.ι.obj x))).isLeftAdjoint
  Stacks.Cohomology.BiggerSiteGlobal.cohomologyOverObjectIsoOfAcyclic
    (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ) P.ι x hacyclic q

/-! ### Sheaves of modules over an object of the subsite

The source's "the same holds for sheaves of modules" is the same comparison with abelian sheaves
replaced by sheaves of modules over the structure sheaf and `H^p` replaced by
`Stacks.Cohomology.BiggerSiteModules.moduleFunctorH`, the `Ext`-groups out of the structure
sheaf. The engine is `Stacks.Cohomology.BiggerSiteModules.moduleCohomologyIsoOfAcyclic`, which
needs restriction of modules on the slices to have a left adjoint; that is the first sentence of
Stacks 0789 for the slice sites, and it is discharged here from essential smallness of the slice
of the subsite rather than assumed. -/

section Modules

variable (x : P.FullSubcategory)
  [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
  [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]

/-- Continuity of the slice functor `Over.post P.ι`, as a local instance so that the restriction
of sheaves of modules below elaborates. -/
local instance isContinuous_overPost_subsite :
    (Over.post (X := x) P.ι).IsContinuous ((subsiteTopology B S hS p τ P).over x)
      ((associatedTopology B S hS p τ).over (P.ι.obj x)) :=
  Functor.isContinuous_overPost (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι x

variable (O : Sheaf ((associatedTopology B S hS p τ).over (P.ι.obj x)) RingCat.{max v w t})

/-- The sheaf of rings `g^{-1}O` on the slice of the subsite at `x`: the restriction along
`Over.post P.ι` of a sheaf of rings on the slice of the ambient site at `P.ι x`. For the
structure sheaf this is `O_{𝒳'}`, by the identification `g^{-1}O_𝒳 = O_{𝒳'}` of Stacks
0788 (f). -/
abbrev subsiteSliceRing : Sheaf ((subsiteTopology B S hS p τ P).over x) RingCat.{max v w t} :=
  inverseImageRing.{max v w t, w, max v w, w, max v w}
    ((subsiteTopology B S hS p τ P).over x)
    ((associatedTopology B S hS p τ).over (P.ι.obj x)) (Over.post (X := x) P.ι) O

/-- Restriction of sheaves of modules along the inclusion of a full subsite, localized at an
object `x` of the subsite: the pullback `g^*` of the morphism of ringed topoi of Stacks 07AK, on
the slices. -/
abbrev subsiteSliceModuleRestriction :
    SheafOfModules.{max v w t} O ⥤
      SheafOfModules.{max v w t} (subsiteSliceRing.{u, v, w, t} B S hS p τ P x O) :=
  restrictionModules.{max v w t, w, max v w, w, max v w}
    ((subsiteTopology B S hS p τ P).over x)
    ((associatedTopology B S hS p τ).over (P.ι.obj x)) (Over.post (X := x) P.ι) O

omit [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)] in
/-- **The first sentence of Stacks 0789 for the slice of a full subsite**: restriction of sheaves
of modules to the slice of the subsite at `x` has a left adjoint `g_!`.

This is `Stacks.Sheaves.ToposPullback.isRightAdjoint_restrictionModules` — restriction of modules
along a continuous functor whose source is essentially small in the universe of the sheaf of
rings has a left adjoint — at the slice functor `Over.post P.ι`. The slice of a full subsite of
the fppf site of a category fibred in groupoids is essentially small with no hypothesis on the
fibres, by `AlgebraicGeometry.Stack.essentiallySmall_over_fullSubsite`; that is what discharges
the smallness hypothesis in the two geometric cases below, through
`CategoryTheory.essentiallySmall_of_le`, the slice being essentially small in the universe of
the schemes and the modules living one universe up. -/
theorem isRightAdjoint_subsiteSliceModuleRestriction
    [EssentiallySmall.{max v w t} (Over x)] :
    (subsiteSliceModuleRestriction.{u, v, w, t} B S hS p τ P x O).IsRightAdjoint :=
  have : HasSheafify ((associatedTopology B S hS p τ).over (P.ι.obj x))
      AddCommGrpCat.{max v w t} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, t}
  have : ((associatedTopology B S hS p τ).over (P.ι.obj x)).WEqualsLocallyBijective
      AddCommGrpCat.{max v w t} :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{max v w, w, t}
  Stacks.Sheaves.ToposPullback.isRightAdjoint_restrictionModules.{max v w t, w, max v w, w,
    max v w} _ _ _ O

/-- **Stacks 07AK for sheaves of modules, cohomology over an object of the subsite, from
acyclicity.** Let `P` cut out a full subcategory of the objects of a category fibred in groupoids
over the big fppf category of `S`, endowed with the site of Stacks 06TP, and suppose the
inclusion is continuous and cocontinuous — which, by Stacks 07AK (1), it is as soon as `P` is
closed under the morphisms lying over the relevant class of morphisms of schemes. Let `x` be an
object of `P`, let `O` be a sheaf of rings on the slice of the ambient site at `P.ι x`, and
suppose that the restriction to the slice of the subsite of an injective sheaf of `O`-modules has
vanishing higher `Ext` out of the structure sheaf. Then for every degree `q`

`H^q(P/x, g^*F) ≅ H^q(𝒳/x, F)`

naturally in the sheaf of `O`-modules `F`, where `H^q` is
`Stacks.Cohomology.BiggerSiteModules.moduleFunctorH`, the `Ext`-groups out of the structure
sheaf.

The acyclicity hypothesis is the module form of Stacks 0D6X for the inclusion; see
`Stacks.Cohomology.BiggerSiteModules.moduleCohomologyIsoOfAcyclic` for why it cannot be replaced
by preservation of injective objects. -/
def subsiteModuleCohomologyOverObjectIso
    [EssentiallySmall.{max v w t} (Over x)]
    (hacyclic : ∀ I : SheafOfModules.{max v w t} O, Injective I → ∀ (n : ℕ)
      (a : Ext (SheafOfModules.unit (subsiteSliceRing.{u, v, w, t} B S hS p τ P x O))
        ((subsiteSliceModuleRestriction.{u, v, w, t} B S hS p τ P x O).obj I) (n + 1)), a = 0)
    (q : ℕ) :
    haveI := isRightAdjoint_subsiteSliceModuleRestriction.{u, v, w, t} B S hS p τ P x O
    subsiteSliceModuleRestriction.{u, v, w, t} B S hS p τ P x O ⋙
        moduleFunctorH.{t, w, max v w} ((subsiteTopology B S hS p τ P).over x)
          (subsiteSliceRing.{u, v, w, t} B S hS p τ P x O) q ≅
      moduleFunctorH.{t, w, max v w}
        ((associatedTopology B S hS p τ).over (P.ι.obj x)) O q :=
  haveI := isRightAdjoint_subsiteSliceModuleRestriction.{u, v, w, t} B S hS p τ P x O
  moduleCohomologyIsoOfAcyclic.{t, w, max v w} _ _ _ O (e := Over.mk (𝟙 x)) Over.mkIdTerminal
    (Over.mkIdTerminal (X := P.ι.obj x)) hacyclic q

end Modules

/-! ### The flat-fppf site -/

namespace FlatFppf

variable (𝒴 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 0GR0, part (2)(b).** For an algebraic stack `𝒳`, an abelian sheaf `F` on the fppf
site of `𝒳` and a flat object `x` of `𝒳`,

`H^q(x, F) = H^q(𝒳_{flat,fppf}/x, g⁻¹ F)`,

naturally in `F`, where `g⁻¹` is restriction to the flat-fppf site of Stacks 0787 and cohomology
over an object is the global cohomology on the slice site.

The closure condition of Stacks 07AK (1) is discharged — it holds for every algebraic stack, by
`AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms` — so the inclusion of the flat
objects is continuous and cocontinuous with no hypothesis. What remains open is the acyclicity
statement of Stacks 0D6X for the slice at `x`, carried here as the hypothesis `hacyclic`: see the
module docstring for why the library's form of 0D6X does not apply at these universes. -/
@[stacks 0GR0 "part (2)(b), cohomology over a flat object; conditional on the acyclicity \
statement of 0D6X only"]
def cohomologyOverObjectIso
    (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒴))
    (hacyclic : haveI := isContinuous_inclusion B S hS 𝒴 flatClosure
      ∀ I : Sheaf ((fppfTopology B S hS 𝒴).over ((objectProperty B S hS 𝒴).ι.obj x))
          AddCommGrpCat.{u + 1}, Injective I → ∀ (n : ℕ)
        (a : Sheaf.H ((subsiteSliceRestriction B S hS 𝒴.val.val.p B.topology
          (objectProperty B S hS 𝒴) x).obj I) (n + 1)), a = 0)
    (q : ℕ) :
    haveI := isContinuous_inclusion B S hS 𝒴 flatClosure
    haveI := Functor.isContinuous_overPost (inclusionTopology B S hS 𝒴)
      (fppfTopology B S hS 𝒴) (objectProperty B S hS 𝒴).ι x
    (objectProperty B S hS 𝒴).ι.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (inclusionTopology B S hS 𝒴) (fppfTopology B S hS 𝒴) ⋙
        (inclusionTopology B S hS 𝒴).overPullback AddCommGrpCat.{u + 1} x ⋙
          Sheaf.functorH ((inclusionTopology B S hS 𝒴).over x) q ≅
      (fppfTopology B S hS 𝒴).overPullback AddCommGrpCat.{u + 1}
            ((objectProperty B S hS 𝒴).ι.obj x) ⋙
        Sheaf.functorH ((fppfTopology B S hS 𝒴).over
          ((objectProperty B S hS 𝒴).ι.obj x)) q :=
  haveI := isContinuous_inclusion B S hS 𝒴 flatClosure
  haveI := isCocontinuous_inclusion B S hS 𝒴 flatClosure
  subsiteCohomologyOverObjectIso B S hS 𝒴.val.val.p B.topology
    (objectProperty B S hS 𝒴) x hacyclic q

/-- The structure sheaf of `𝒳` of Stacks 06TV, restricted to the slice of the fppf site at a
flat object `x`: the sheaf of rings whose modules part (2)(b) of the source is about. -/
noncomputable abbrev sliceStructureRing
    (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒴)) :
    Sheaf ((fppfTopology B S hS 𝒴).over ((objectProperty B S hS 𝒴).ι.obj x))
      RingCat.{max (u + 1) t} :=
  (ringStructureSheaf.{u, u + 1, u, t} B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
    B.topology le_rfl).over ((objectProperty B S hS 𝒴).ι.obj x)

/-- **Stacks 0GR0, part (2)(b) for sheaves of modules** — the source's "the same holds for
sheaves of modules". For an algebraic stack `𝒳`, a sheaf `F` of `O_𝒳`-modules and a flat object
`x` of `𝒳`,

`H^q(x, F) = H^q(𝒳_{flat,fppf}/x, g^*F)`,

naturally in `F`, where `g^*` is restriction of sheaves of modules to the flat-fppf site of
Stacks 0787, cohomology over an object is the global cohomology on the slice site, and `H^q` of a
sheaf of modules is `Ext^q` out of the structure sheaf.

Three of the four inputs are discharged rather than assumed. The closure condition of Stacks
07AK (1) holds for every algebraic stack, by
`AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms`. The existence of `g_!` on sheaves of
modules on the slices — the first sentence of Stacks 0789 — is
`AlgebraicGeometry.Stack.isRightAdjoint_subsiteSliceModuleRestriction`, from essential smallness
of the slice of a full subsite. Exactness of `g^*` is
`Stacks.Cohomology.DerivedLowerShriek.restriction_exact`. What remains open is the module form of
the acyclicity statement of Stacks 0D6X for the slice at `x`, carried here as the hypothesis
`hacyclic`: see the module docstring for why the library's form of 0D6X does not apply at these
universes.

The sheaf of modules is quantified over the slice site at `x` rather than over `𝒳` itself, which
is the generalization the comparison naturally has: the source's `H^q(x, F)` for `F` on `𝒳` is
the cohomology of the restriction of `F` to the slice, so instantiating at that restriction gives
the source's statement. -/
@[stacks 0GR0 "part (2)(b), modules; conditional on the module form of the acyclicity statement \
of 0D6X only"]
noncomputable def moduleCohomologyOverObjectIso
    (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒴))
    (hacyclic : haveI := isContinuous_inclusion B S hS 𝒴 flatClosure
      haveI := isCocontinuous_inclusion B S hS 𝒴 flatClosure
      ∀ I : SheafOfModules.{max (u + 1) t} (sliceStructureRing.{u, w, t} B S hS 𝒴 x),
          Injective I → ∀ (n : ℕ)
        (a : Ext (SheafOfModules.unit (subsiteSliceRing.{u, u + 1, u, t} B S hS 𝒴.val.val.p
              B.topology (objectProperty B S hS 𝒴) x
              (sliceStructureRing.{u, w, t} B S hS 𝒴 x)))
            ((subsiteSliceModuleRestriction.{u, u + 1, u, t} B S hS 𝒴.val.val.p B.topology
              (objectProperty B S hS 𝒴) x
              (sliceStructureRing.{u, w, t} B S hS 𝒴 x)).obj I) (n + 1)), a = 0)
    (q : ℕ) :
    haveI := isContinuous_inclusion B S hS 𝒴 flatClosure
    haveI := isCocontinuous_inclusion B S hS 𝒴 flatClosure
    haveI := isRightAdjoint_subsiteSliceModuleRestriction.{u, u + 1, u, t} B S hS 𝒴.val.val.p
      B.topology (objectProperty B S hS 𝒴) x (sliceStructureRing.{u, w, t} B S hS 𝒴 x)
    subsiteSliceModuleRestriction.{u, u + 1, u, t} B S hS 𝒴.val.val.p B.topology
          (objectProperty B S hS 𝒴) x (sliceStructureRing.{u, w, t} B S hS 𝒴 x) ⋙
        moduleFunctorH.{t, u, u + 1} ((inclusionTopology B S hS 𝒴).over x)
          (subsiteSliceRing.{u, u + 1, u, t} B S hS 𝒴.val.val.p B.topology
            (objectProperty B S hS 𝒴) x (sliceStructureRing.{u, w, t} B S hS 𝒴 x)) q ≅
      moduleFunctorH.{t, u, u + 1}
        ((fppfTopology B S hS 𝒴).over ((objectProperty B S hS 𝒴).ι.obj x))
        (sliceStructureRing.{u, w, t} B S hS 𝒴 x) q :=
  haveI := isContinuous_inclusion B S hS 𝒴 flatClosure
  haveI := isCocontinuous_inclusion B S hS 𝒴 flatClosure
  haveI : EssentiallySmall.{max (u + 1) t} (Over x) :=
    haveI := essentiallySmall_over_fullSubsite B S hS 𝒴.val (objectProperty B S hS 𝒴) x
    CategoryTheory.essentiallySmall_of_le.{u, max (u + 1) t}
  subsiteModuleCohomologyOverObjectIso.{u, u + 1, u, t} B S hS 𝒴.val.val.p B.topology
    (objectProperty B S hS 𝒴) x (sliceStructureRing.{u, w, t} B S hS 𝒴 x) hacyclic q

end FlatFppf

/-! ### The lisse-étale site -/

namespace LisseEtale

variable (𝒴 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 0GR0, part (1)(b).** For an algebraic stack `𝒳`, an abelian sheaf `F` on the étale
site of `𝒳` and a smooth object `x` of `𝒳`,

`H^q(x, F) = H^q(𝒳_{lisse,étale}/x, g⁻¹ F)`,

naturally in `F`, where `g⁻¹` is restriction to the lisse-étale site of Stacks 0787.

The closure condition of Stacks 07AK (1) for the smooth objects is discharged — it holds for
every algebraic stack, by `AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms` — so
the inclusion of the smooth objects is continuous and cocontinuous with no hypothesis. What
remains open is the acyclicity statement of Stacks 0D6X for the slice at `x`, carried here as the
hypothesis `hacyclic`: see the module docstring for why the library's form of 0D6X does not apply
at these universes. -/
@[stacks 0GR0 "part (1)(b), cohomology over a smooth object; conditional on the acyclicity \
statement of 0D6X only"]
def cohomologyOverObjectIso
    (x : ObjectProperty.FullSubcategory (smoothObject.{u, w} B S hS 𝒴))
    (hacyclic : haveI := isContinuous_inclusion B S hS 𝒴 (closedUnderSmoothMorphisms B S hS 𝒴)
      ∀ I : Sheaf ((associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)).over
            ((smoothObject.{u, w} B S hS 𝒴).ι.obj x)) AddCommGrpCat.{u + 1},
          Injective I → ∀ (n : ℕ)
        (a : Sheaf.H ((subsiteSliceRestriction B S hS 𝒴.val.val.p (etaleTopology B)
          (smoothObject.{u, w} B S hS 𝒴) x).obj I) (n + 1)), a = 0)
    (q : ℕ) :
    haveI := isContinuous_inclusion B S hS 𝒴 (closedUnderSmoothMorphisms B S hS 𝒴)
    haveI := Functor.isContinuous_overPost (inclusionTopology.{u, w} B S hS 𝒴)
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒴).ι x
    (smoothObject.{u, w} B S hS 𝒴).ι.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (inclusionTopology.{u, w} B S hS 𝒴)
          (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)) ⋙
        (inclusionTopology.{u, w} B S hS 𝒴).overPullback AddCommGrpCat.{u + 1} x ⋙
          Sheaf.functorH ((inclusionTopology.{u, w} B S hS 𝒴).over x) q ≅
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)).overPullback
            AddCommGrpCat.{u + 1} ((smoothObject.{u, w} B S hS 𝒴).ι.obj x) ⋙
        Sheaf.functorH ((associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)).over
          ((smoothObject.{u, w} B S hS 𝒴).ι.obj x)) q :=
  haveI := isContinuous_inclusion B S hS 𝒴 (closedUnderSmoothMorphisms B S hS 𝒴)
  haveI := isCocontinuous_inclusion B S hS 𝒴 (closedUnderSmoothMorphisms B S hS 𝒴)
  subsiteCohomologyOverObjectIso B S hS 𝒴.val.val.p (etaleTopology B)
    (smoothObject.{u, w} B S hS 𝒴) x hacyclic q

/-- The structure sheaf of `𝒳` of Stacks 06TV, restricted to the slice of the étale site at a
smooth object `x`: the sheaf of rings whose modules part (1)(b) of the source is about. -/
noncomputable abbrev sliceStructureRing
    (x : ObjectProperty.FullSubcategory (smoothObject.{u, w} B S hS 𝒴)) :
    Sheaf ((associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)).over
        ((smoothObject.{u, w} B S hS 𝒴).ι.obj x)) RingCat.{max (u + 1) t} :=
  (ringStructureSheaf.{u, u + 1, u, t} B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
    (etaleTopology B) (etaleTopology_le_topology B)).over
      ((smoothObject.{u, w} B S hS 𝒴).ι.obj x)

/-- **Stacks 0GR0, part (1)(b) for sheaves of modules** — the source's "the same holds for
sheaves of modules". For an algebraic stack `𝒳`, a sheaf `F` of `O_𝒳`-modules and a smooth object
`x` of `𝒳`,

`H^q(x, F) = H^q(𝒳_{lisse,étale}/x, g^*F)`,

naturally in `F`, where `g^*` is restriction of sheaves of modules to the lisse-étale site of
Stacks 0787 and `H^q` of a sheaf of modules is `Ext^q` out of the structure sheaf.

As in the flat-fppf case, three of the four inputs are discharged rather than assumed: the
closure condition of Stacks 07AK (1) by
`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`, the existence of `g_!` on
sheaves of modules on the slices by
`AlgebraicGeometry.Stack.isRightAdjoint_subsiteSliceModuleRestriction`, and exactness of `g^*` by
`Stacks.Cohomology.DerivedLowerShriek.restriction_exact`. What remains open is the module form of
the acyclicity statement of Stacks 0D6X for the slice at `x`, carried here as the hypothesis
`hacyclic`.

The sheaf of modules is quantified over the slice site at `x`, which is the generalization the
comparison naturally has; see
`AlgebraicGeometry.Stack.FlatFppf.moduleCohomologyOverObjectIso`. -/
@[stacks 0GR0 "part (1)(b), modules; conditional on the module form of the acyclicity statement \
of 0D6X only"]
noncomputable def moduleCohomologyOverObjectIso
    (x : ObjectProperty.FullSubcategory (smoothObject.{u, w} B S hS 𝒴))
    (hacyclic :
      haveI := isContinuous_inclusion B S hS 𝒴 (closedUnderSmoothMorphisms B S hS 𝒴)
      haveI := isCocontinuous_inclusion B S hS 𝒴 (closedUnderSmoothMorphisms B S hS 𝒴)
      ∀ I : SheafOfModules.{max (u + 1) t} (sliceStructureRing.{u, w, t} B S hS 𝒴 x),
          Injective I → ∀ (n : ℕ)
        (a : Ext (SheafOfModules.unit (subsiteSliceRing.{u, u + 1, u, t} B S hS 𝒴.val.val.p
              (etaleTopology B) (smoothObject.{u, w} B S hS 𝒴) x
              (sliceStructureRing.{u, w, t} B S hS 𝒴 x)))
            ((subsiteSliceModuleRestriction.{u, u + 1, u, t} B S hS 𝒴.val.val.p (etaleTopology B)
              (smoothObject.{u, w} B S hS 𝒴) x
              (sliceStructureRing.{u, w, t} B S hS 𝒴 x)).obj I) (n + 1)), a = 0)
    (q : ℕ) :
    haveI := isContinuous_inclusion B S hS 𝒴 (closedUnderSmoothMorphisms B S hS 𝒴)
    haveI := isCocontinuous_inclusion B S hS 𝒴 (closedUnderSmoothMorphisms B S hS 𝒴)
    haveI := isRightAdjoint_subsiteSliceModuleRestriction.{u, u + 1, u, t} B S hS 𝒴.val.val.p
      (etaleTopology B) (smoothObject.{u, w} B S hS 𝒴) x
      (sliceStructureRing.{u, w, t} B S hS 𝒴 x)
    subsiteSliceModuleRestriction.{u, u + 1, u, t} B S hS 𝒴.val.val.p (etaleTopology B)
          (smoothObject.{u, w} B S hS 𝒴) x (sliceStructureRing.{u, w, t} B S hS 𝒴 x) ⋙
        moduleFunctorH.{t, u, u + 1} ((inclusionTopology.{u, w} B S hS 𝒴).over x)
          (subsiteSliceRing.{u, u + 1, u, t} B S hS 𝒴.val.val.p (etaleTopology B)
            (smoothObject.{u, w} B S hS 𝒴) x
            (sliceStructureRing.{u, w, t} B S hS 𝒴 x)) q ≅
      moduleFunctorH.{t, u, u + 1}
        ((associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)).over
          ((smoothObject.{u, w} B S hS 𝒴).ι.obj x))
        (sliceStructureRing.{u, w, t} B S hS 𝒴 x) q :=
  haveI := isContinuous_inclusion B S hS 𝒴 (closedUnderSmoothMorphisms B S hS 𝒴)
  haveI := isCocontinuous_inclusion B S hS 𝒴 (closedUnderSmoothMorphisms B S hS 𝒴)
  haveI : EssentiallySmall.{max (u + 1) t} (Over x) :=
    haveI := essentiallySmall_over_fullSubsite B S hS 𝒴.val (smoothObject.{u, w} B S hS 𝒴) x
    CategoryTheory.essentiallySmall_of_le.{u, max (u + 1) t}
  subsiteModuleCohomologyOverObjectIso.{u, u + 1, u, t} B S hS 𝒴.val.val.p (etaleTopology B)
    (smoothObject.{u, w} B S hS 𝒴) x (sliceStructureRing.{u, w, t} B S hS 𝒴 x) hacyclic q

end LisseEtale

end AlgebraicGeometry.Stack

end
