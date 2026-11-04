module

public import StacksFrontier.AlgebraicGeometry.Descent.SmallAffineRingedTopos
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsEtaleCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsEtaleCohomologyColimitGlobal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitColimitSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.OpensAcyclicityTransport
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteObjectCohomology
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposReplacement

/-!
# The raised small affine étale site is a dense subsite of the one-universe model

For a scheme `S` of a big étale site `B`, the small affine étale site of [Stacks, Tag 021B],
universe-raised by `CategoryTheory.AsSmall` so that it becomes a small category whose morphisms
live in the same universe as its objects, is a dense subsite of the one-universe model
`Stacks.EtaleCohomology.MayerVietoris.Site S` of Mathlib's small étale site of `S`.

The inclusion is the four-step composite

`AsSmall.down ⋙ SmallAffineEtale.inclusion ⋙ SmallEtale.toEtaleSite ⋙ AsSmall.up`,

each step of which is a dense subsite inclusion already: the raising by
`Stacks.EtaleCohomology.AffineEtaleModel.isDenseSubsite_down` below, [Stacks, Tag 04HR] by
`AlgebraicGeometry.SmallAffineEtale.inclusion_isDenseSubsite`, the size bound by
`AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`, and the raising at the other end by
`Stacks.EtaleCohomology.ConstantTransport.asSmallUp_isDenseSubsite`. Contracting them to one is
`CategoryTheory.Functor.isDenseSubsite_comp`.

## Why the composite and not the four steps

Everything that consumes a dense subsite at abelian coefficients pins the coefficient universe to
the *morphism* universe shared by its two sites, because `CategoryTheory.yoneda` on a category with
morphisms in `Type a` gives presheaves of types in `Type a`. The two ends of this chain have
morphisms in `Type (u + 1)` and the two middle sites have morphisms in `Type u`, so the
coefficients `AddCommGrpCat.{u + 1}` at which the étale cohomology of this library is taken are
carried by the composite and by no single step of it.

## Main definitions

* `Stacks.EtaleCohomology.AffineEtaleModel.Site`, `precoverage`, `topology` — the raised small
  affine étale site. These are the site, precoverage and topology of
  `Stacks.EtaleCohomology.AffineLimitCohomology.limitSite` and `limitSitePrecoverage`, written for
  an arbitrary scheme of `B` rather than for the vertex of a limit cone, and are definitionally
  equal to them.
* `Stacks.EtaleCohomology.AffineEtaleModel.toModel` — the composite inclusion.

## Main results

* `Stacks.EtaleCohomology.AffineEtaleModel.isDenseSubsite_down` — **universe raising along
  `CategoryTheory.AsSmall` is a dense subsite inclusion**, for the comap precoverage. The two
  halves are `CategoryTheory.AsSmall.coverPreserving_down` and `coverPreserving_up`.
* `Stacks.EtaleCohomology.AffineEtaleModel.toModel_isDenseSubsite` — **the composite is a dense
  subsite inclusion.**
* `Stacks.EtaleCohomology.AffineEtaleModel.subsingleton_opensCohomology_of_vanishesOnObjects` —
  **the crossing**: if the restriction of an abelian sheaf `F` on the one-universe model to the
  raised small affine étale site has vanishing cohomology over every object of that site, then the
  cohomology of `F` over every affine open of `S` vanishes in positive degrees.
* `AffineEtaleModel.subsingleton_H_smallEtaleOpensRestrict_of_vanishesOnObjects`
  — the same conclusion in the shape of the hypothesis `haff` of
  `OpensAcyclicity.subsingleton_H_smallEtale_of_affineOpens_acyclic_of_sectionsDifference`:
  the vanishing of the *global* cohomology of the restriction of `F` to the small étale site of the
  affine open.

## Implementation notes

The crossing is
`Stacks.Cohomology.DenseSubsiteObject.subsingleton_cohomologyPresheaf_of_vanishesOnObjects`
and **not** `Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso`, the comparison of
[Stacks, Tag 03YU], statement 2. That comparison asks for equalizers in the source site, preserved
by the functor, and the small affine étale site genuinely has none: the equalizer of two morphisms
of affine étale objects is an open subscheme of an affine scheme, which need not be affine. The
dense-subsite transport asks for no limits in either site, restriction along a dense subsite
inclusion being an equivalence of sheaf categories outright, and it leaves the two `Ext`-universes
unrelated.

The affine open `V` is read as an object of the small affine étale site by
`Stacks.EtaleCohomology.QcqsLimitCohomology.objOfAffineOpen`, whose image in `S.Etale` has `V` as
its scheme and the open immersion `V.ι` as its structure morphism — the same data as
`Stacks.EtaleCohomology.MayerVietoris.opensToSite`, though not the same term, so the two are
identified by an isomorphism and not by an equality.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 07A1](https://stacks.math.columbia.edu/tag/07A1)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.StrictlyHenselian (opensCohomology)
open Stacks.Cohomology (VanishesOnObjects)
open CategoryTheory.Sites.InverseSystem

universe w v₁ u₁ u

namespace Stacks.EtaleCohomology.AffineEtaleModel

/-! ### Universe raising is a dense subsite inclusion -/

section AsSmall

variable {C : Type u₁} [Category.{v₁} C]

/-- Pulling a sieve of a universe-raised category back along `AsSmall.up` and then along
`AsSmall.down` returns it: the two functors are mutually inverse on the nose. -/
public theorem functorPullback_down_functorPullback_up (Z : AsSmall.{w} C) (S : Sieve Z) :
    Sieve.functorPullback (AsSmall.down : AsSmall.{w} C ⥤ C)
        (Sieve.functorPullback (AsSmall.up : C ⥤ AsSmall.{w} C) S) = S :=
  rfl

/-- **`CategoryTheory.AsSmall.down` is a dense subsite inclusion** from the comap precoverage of a
precoverage `K` on `C` to `K` itself. It is cover dense because every morphism of `C` is already a
morphism between `AsSmall.down`-images, and a sieve is covering upstairs exactly when its image
downstairs is, by the two statements
`CategoryTheory.AsSmall.coverPreserving_down` and `CategoryTheory.AsSmall.coverPreserving_up`. -/
public theorem isDenseSubsite_down (K : Precoverage C) :
    (AsSmall.down : AsSmall.{w} C ⥤ C).IsDenseSubsite
      (K.comap AsSmall.down).toGrothendieck K.toGrothendieck :=
  have : (AsSmall.down : AsSmall.{w} C ⥤ C).IsEquivalence :=
    (AsSmall.equiv (C := C)).isEquivalence_inverse
  { isCoverDense' := by
      refine ⟨fun U => ?_⟩
      convert K.toGrothendieck.top_mem U
      refine le_antisymm le_top fun Y f _ => ?_
      exact ⟨⟨AsSmall.up.obj Y, 𝟙 _, f, Category.id_comp f⟩⟩
    functorPushforward_mem_iff := fun {Z S} => by
      refine ⟨fun hS => ?_, (AsSmall.coverPreserving_down K).cover_preserve⟩
      have hS' : Sieve.functorPullback (AsSmall.up : C ⥤ AsSmall.{w} C) S ∈
          K.toGrothendieck (AsSmall.down.obj Z) := by
        rw [← AsSmall.functorPushforward_down Z S]
        exact hS
      refine (K.comap (AsSmall.down : AsSmall.{w} C ⥤ C)).toGrothendieck.superset_covering
        ?_ ((AsSmall.coverPreserving_up K).cover_preserve hS')
      rintro Y f ⟨Z', g, i, hg, rfl⟩
      exact S.downward_closed hg i }

end AsSmall

/-! ### The raised small affine étale site -/

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The small affine étale site of [Stacks, Tag 021B], universe-raised.** This is
`Stacks.EtaleCohomology.AffineLimitCohomology.limitSite` for an arbitrary scheme of `B`. -/
public abbrev Site : Type (u + 1) :=
  AsSmall.{u + 1} (AlgebraicGeometry.SmallAffineEtale B S hS)

/-- The precoverage of the raised small affine étale site. This is
`Stacks.EtaleCohomology.AffineLimitCohomology.limitSitePrecoverage` for an arbitrary scheme
of `B`. -/
public abbrev precoverage : Precoverage (Site B S hS) :=
  (AlgebraicGeometry.SmallAffineEtale.precoverage B S hS).comap AsSmall.down

/-- The topology of the raised small affine étale site. -/
public abbrev topology : GrothendieckTopology (Site B S hS) :=
  (precoverage B S hS).toGrothendieck

/-- **The inclusion of the raised small affine étale site into the one-universe model of
Mathlib's small étale site**: lower the universe, include the affine objects among all étale
objects of the size-bounded site, forget the size bound, and raise the universe again. -/
public def toModel : Site B S hS ⥤ MayerVietoris.Site S :=
  AsSmall.down ⋙ AlgebraicGeometry.SmallAffineEtale.inclusion B S hS ⋙
    AlgebraicGeometry.SmallEtale.toEtaleSite B S hS ⋙ AsSmall.up

/-- `CategoryTheory.AsSmall.down` out of the raised small affine étale site is an equivalence,
being half of `CategoryTheory.AsSmall.equiv`. -/
public theorem asSmallDown_isEquivalence :
    (AsSmall.down : Site B S hS ⥤ AlgebraicGeometry.SmallAffineEtale B S hS).IsEquivalence :=
  (AsSmall.equiv (C := AlgebraicGeometry.SmallAffineEtale B S hS)).isEquivalence_inverse

/-- The inclusion `toModel B S hS` is full. -/
public instance : (toModel B S hS).Full :=
  haveI := asSmallDown_isEquivalence B S hS
  inferInstanceAs ((AsSmall.down ⋙ AlgebraicGeometry.SmallAffineEtale.inclusion B S hS ⋙
    AlgebraicGeometry.SmallEtale.toEtaleSite B S hS ⋙ AsSmall.up).Full)

/-- The inclusion `toModel B S hS` is faithful. -/
public instance : (toModel B S hS).Faithful :=
  haveI := asSmallDown_isEquivalence B S hS
  inferInstanceAs ((AsSmall.down ⋙ AlgebraicGeometry.SmallAffineEtale.inclusion B S hS ⋙
    AlgebraicGeometry.SmallEtale.toEtaleSite B S hS ⋙ AsSmall.up).Faithful)

/-- **The raised small affine étale site is a dense subsite of the one-universe model of
Mathlib's small étale site.** The four steps of the composite are dense subsite inclusions —
universe raising by `isDenseSubsite_down`, [Stacks, Tag 04HR] by
`AlgebraicGeometry.SmallAffineEtale.inclusion_isDenseSubsite`, the size bound by
`AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`, and universe raising again by
`Stacks.EtaleCohomology.ConstantTransport.asSmallUp_isDenseSubsite` — and
`CategoryTheory.Functor.isDenseSubsite_comp` contracts them. -/
public instance toModel_isDenseSubsite :
    (toModel B S hS).IsDenseSubsite (topology B S hS) (MayerVietoris.topology S) := by
  have := asSmallDown_isEquivalence B S hS
  have h₀ : (AsSmall.down :
      Site B S hS ⥤ AlgebraicGeometry.SmallAffineEtale B S hS).IsDenseSubsite
      (topology B S hS) (AlgebraicGeometry.SmallAffineEtale.topology B S hS) :=
    isDenseSubsite_down _
  have h₁ := Functor.isDenseSubsite_comp
    (AlgebraicGeometry.SmallEtale.topology B S hS) S.smallEtaleTopology
    (MayerVietoris.topology S)
    (AlgebraicGeometry.SmallEtale.toEtaleSite B S hS)
    (AsSmall.up : S.Etale ⥤ MayerVietoris.Site S)
  have h₂ := Functor.isDenseSubsite_comp
    (AlgebraicGeometry.SmallAffineEtale.topology B S hS)
    (AlgebraicGeometry.SmallEtale.topology B S hS) (MayerVietoris.topology S)
    (AlgebraicGeometry.SmallAffineEtale.inclusion B S hS)
    (AlgebraicGeometry.SmallEtale.toEtaleSite B S hS ⋙
      (AsSmall.up : S.Etale ⥤ MayerVietoris.Site S))
  exact Functor.isDenseSubsite_comp
    (topology B S hS) (AlgebraicGeometry.SmallAffineEtale.topology B S hS)
    (MayerVietoris.topology S)
    (AsSmall.down : Site B S hS ⥤ AlgebraicGeometry.SmallAffineEtale B S hS)
    (AlgebraicGeometry.SmallAffineEtale.inclusion B S hS ⋙
      AlgebraicGeometry.SmallEtale.toEtaleSite B S hS ⋙
      (AsSmall.up : S.Etale ⥤ MayerVietoris.Site S))

/-! ### Sheafification, injectives and `Ext` for the raised small affine étale site

Instance search cannot find these on its own — `topology B S hS` is a precoverage of a raised full
subcategory of a slice of a full subcategory of schemes, and unfolding it exhausts the
`synthInstance` heartbeat budget before any proof runs — so each is registered with a head that
matches syntactically. None of them is a new statement: each is an existing abstract fact about an
arbitrary small site. They are
`Stacks.EtaleCohomology.QcqsLimitCohomology.hasSheafify_limitSitePrecoverage`,
`enoughInjectives_limitSitePrecoverage` and `hasExt_limitSitePrecoverage` with the vertex of a
limit cone replaced by a variable; those three are instances for a *definitionally equal* topology
written through the opaque `AffineLimitCohomology.limitSitePrecoverage`, which instance search
cannot unfold, so they are not found for this spelling and these are what make the statements below
elaborate. -/

/-- Sheafification of abelian sheaves on the raised small affine étale site.

The site is written out as `AffineEtaleModel.topology` rather than relying on the namespace,
because the bare name makes this statement textually identical to
`AlgebraicGeometry.ProEtale.SmallProetale.hasSheafify_smallProetale`, which is the same sentence
about the small *pro-étale* site of a different big site. They are distinct instances about
distinct topologies, and a duplicate scan keyed on statement text reports them as one. -/
public instance hasSheafify_topology :
    HasSheafify (AffineEtaleModel.topology B S hS) AddCommGrpCat.{u + 1} :=
  Stacks.WeakSites.ColimitSiteCohomology.hasSheafifyAb.{u + 1, u + 1} _

/-- Abelian sheaves on the raised small affine étale site have enough injectives. -/
public instance enoughInjectives_topology :
    EnoughInjectives (Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) :=
  Stacks.WeakSites.ColimitSiteCohomology.enoughInjectivesAb.{u + 1, u + 1} _

/-- `Ext`-groups exist for abelian sheaves on the raised small affine étale site. -/
public instance hasExt_topology :
    HasExt.{u + 1} (Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-! ### The crossing -/

/-- **An abelian sheaf on the one-universe model of Mathlib's small étale site, restricted to the
raised small affine étale site.** -/
public abbrev modelRestrict :
    Sheaf (MayerVietoris.topology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology B S hS) AddCommGrpCat.{u + 1} :=
  (toModel B S hS).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (topology B S hS) (MayerVietoris.topology S)

/-- **An affine open of `S`, read as an object of the one-universe model through the small affine
étale site, is the affine open read there directly.** Both objects of `S.Etale` have `V` as their
scheme and the open immersion `V.ι` as their structure morphism; they are not the same term,
`Stacks.EtaleCohomology.QcqsLimitCohomology.objOfAffineOpen` producing the latter as the image
under the inclusion of the size-bounded site of a chosen preimage of `V.ι`. -/
public def toModelObjOfAffineOpenIso (V : S.Opens) (hV : IsAffineOpen V) :
    (toModel B S hS).obj
        (AsSmall.up.obj (QcqsLimitCohomology.objOfAffineOpen B S hS V hV)) ≅
      (MayerVietoris.opensToSite S).obj V :=
  (AsSmall.up : S.Etale ⥤ MayerVietoris.Site S).mapIso
    (MorphismProperty.Over.isoMk (Iso.refl _)
      ((Category.id_comp V.ι).trans
        (QcqsLimitCohomology.structMap_objOfAffineOpen B S hS V hV).symm))

/-- **The crossing: vanishing on the objects of the raised small affine étale site gives vanishing
over the affine opens.** If the restriction of an abelian sheaf `F` on the one-universe model of
Mathlib's small étale site of `S` to the raised small affine étale site satisfies
`Stacks.Cohomology.VanishesOnObjects` — condition (1) of [Stacks, Tag 07A1] — then the cohomology
of `F` over every affine open of `S` vanishes in every positive degree.

This is `Stacks.Cohomology.DenseSubsiteObject.subsingleton_cohomologyPresheaf_of_vanishesOnObjects`
at the dense subsite inclusion `toModel`, followed by `toModelObjOfAffineOpenIso`. The
`Ext`-universe in which the hypothesis is read is unrelated to the model's own, which is the one
the conclusion is in. -/
public theorem subsingleton_opensCohomology_of_vanishesOnObjects
    [instSheafify : HasSheafify (topology B S hS) AddCommGrpCat.{u + 1}]
    [instExt : HasExt.{w} (Sheaf (topology B S hS) AddCommGrpCat.{u + 1})]
    (F : Sheaf (MayerVietoris.topology S) AddCommGrpCat.{u + 1})
    (hF : VanishesOnObjects.{w} (topology B S hS) ((modelRestrict B S hS).obj F))
    (V : S.Opens) (hV : IsAffineOpen V) (p : ℕ) (hp : 0 < p) :
    Subsingleton ((opensCohomology F p).obj (op V)) :=
  have := Stacks.Cohomology.DenseSubsiteObject.subsingleton_cohomologyPresheaf_of_vanishesOnObjects
    (topology B S hS) (MayerVietoris.topology S) (toModel B S hS) F hF
    (AsSmall.up.obj (QcqsLimitCohomology.objOfAffineOpen B S hS V hV)) p hp
  ((F.cohomologyPresheaf p).mapIso
      (toModelObjOfAffineOpenIso B S hS V hV).op).addCommGroupIsoToAddEquiv.toEquiv.subsingleton

/-- Let `F` be an abelian sheaf on Mathlib's small étale site of `S`. If the restriction of `F` —
read on the one-universe model and then on the raised small affine étale site — has vanishing
cohomology over every object of that site, then for every affine open `V` of `S` the restriction of
`F` to the small étale site of `V` has vanishing *global* cohomology in every positive degree. -/
public theorem subsingleton_H_smallEtaleOpensRestrict_of_vanishesOnObjects
    [instSheafify : HasSheafify (topology B S hS) AddCommGrpCat.{u + 1}]
    [instExt : HasExt.{w} (Sheaf (topology B S hS) AddCommGrpCat.{u + 1})]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : VanishesOnObjects.{w} (topology B S hS)
      ((modelRestrict B S hS).obj ((MayerVietoris.mayerVietorisRestrict S).obj F)))
    (V : S.Opens) (hV : IsAffineOpen V) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H.{u + 1} ((OpensAcyclicity.smallEtaleOpensRestrict S V).obj F) p) :=
  Stacks.Cohomology.DenseSubsiteSheaf.subsingleton_H_of_subsingleton_H_restriction_of_isDenseSubsite
    (MayerVietoris.topology V.toScheme) V.toScheme.smallEtaleTopology
    (AsSmall.down : MayerVietoris.Site V.toScheme ⥤ V.toScheme.Etale)
    (MayerVietoris.selfIsTerminal V.toScheme)
    (MayerVietoris.isTerminalAsSmallDownSelf V.toScheme)
    ((OpensAcyclicity.smallEtaleOpensRestrict S V).obj F) p
    ((OpensAcyclicity.subsingleton_opensCohomology_smallEtale_iff S V F p).2
      (subsingleton_opensCohomology_of_vanishesOnObjects B S hS
        ((MayerVietoris.mayerVietorisRestrict S).obj F) hF V hV p hp))

end Stacks.EtaleCohomology.AffineEtaleModel

end
