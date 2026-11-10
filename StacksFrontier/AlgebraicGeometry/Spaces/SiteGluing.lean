module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingInSite

/-!
# Stacks 01JJ for the big fppf site over a scheme

Mathlib proves Stacks 01JJ for the category of all schemes: a `Type u`-valued Zariski sheaf on
`Sch` admitting a jointly locally surjective family of relatively representable open immersions
from representable presheaves is representable
(`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`). The algebraic-spaces chapter
needs that statement one level down, for a sheaf on the big fppf site over a scheme `S`, where
the representing object must itself be an object of that site. Mathlib's statement does not give
it, because the scheme it glues is produced in `Sch` with no size control.

`StacksFrontier.AlgebraicGeometry.Spaces.SiteRepresentability` builds the glued object of the site
and its charts. This file supplies the comparison which identifies the sheaf it represents with
the given sheaf, and so completes the transfer.

## Main definitions

* `AlgebraicGeometry.Space.gluedObjOfContains` and `AlgebraicGeometry.Space.toGluedOfContains`
  are the glued object of the site and its charts, taking as hypothesis that the glued
  *scheme* lies in the site rather than a bound on the index type of the covering family.
  `AlgebraicGeometry.Space.gluedObjOfContains_eq` and
  `AlgebraicGeometry.Space.toGluedOfContains_eq` identify them with
  `AlgebraicGeometry.Space.gluedObj` and `AlgebraicGeometry.Space.toGlued`.
* `AlgebraicGeometry.Space.oneHypercover` is the `1`-hypercover of the glued object given by the
  charts, with the overlaps of the glueing data as the coverings of the fibre products.
* `AlgebraicGeometry.Space.gluedSheaf` is the glued object viewed as a sheaf, and
  `AlgebraicGeometry.Space.gluedSection` the section of the given sheaf over it obtained by
  glueing the sections which correspond to the charts.
* `AlgebraicGeometry.Space.gluedToSheaf` is the comparison morphism.

## Main results

* `AlgebraicGeometry.BigFppfOver.sieve_ofArrows_mem_topology_of_jointlySurjective`: a jointly
  surjective family of open immersions of the site generates a covering sieve. This generalizes
  `AlgebraicGeometry.BigFppfOver.sieve_ofArrows_mem_topology_of_isColimit`, whose family is a
  coproduct decomposition.
* `AlgebraicGeometry.Space.isPullback_toGlued`: the overlaps of the glueing data are the fibre
  products of the charts over the glued object, in the site.
* `AlgebraicGeometry.Space.comp_toGlued_eq`: two charts agree on the glued object wherever
  their subfunctors do.
* `AlgebraicGeometry.Space.isLocallyInjective_gluedToSheaf` and
  `AlgebraicGeometry.Space.isLocallySurjective_gluedToSheaf`, hence
  `AlgebraicGeometry.Space.isIso_gluedToSheaf`.
* `AlgebraicGeometry.BigFppfSite.contains_glueData_glued_of_le_power` and
  `AlgebraicGeometry.Space.contains_schemeGlueData_glued_of_le_power`: the glued scheme lies in
  the site as soon as the index type and every chart are bounded by `size T ^ ℵ₀` for a single
  object `T` of the site. No bound on the *number* of charts beyond that is needed.
* `AlgebraicGeometry.Space.isRepresentable_of_openCover_of_le_power` is Stacks 01JJ for the
  site under exactly that cardinal bound. This is the form to use for a family indexed by the
  affine opens of an object of the site.
* `AlgebraicGeometry.Space.isRepresentable_of_openCover_of_contains` is Stacks 01JJ for the
  site, hypothesising only that the glued scheme lies in the site, and
  `AlgebraicGeometry.Space.isRepresentable_of_openCover_of_size` is its repackaging for a
  glued scheme known only up to isomorphism.
* `AlgebraicGeometry.Space.isRepresentable_of_openCover` is Stacks 01JJ for the site,
  hypothesising instead a bound on the index type of the covering family.

## Implementation notes

What makes the glued scheme an object of the site is a *size* bound on it, and that is the
hypothesis of `AlgebraicGeometry.Space.isRepresentable_of_openCover_of_contains`. The bound
`#ι < B.cutoff.ord.cof` on the index type of the covering family is one way to obtain it, by
`AlgebraicGeometry.Space.contains_schemeGlueData_glued`: the glued scheme is covered by the
images of its charts, so Stacks 000Q bounds its size by `max #ι (⨆ i, size (X i))`, and the
supremum is below the cutoff exactly when the index type is below the cutoff's cofinality.
Uncountable cofinality of the cutoff is a field of `AlgebraicGeometry.BigFppfSite`, so an at
most countable family qualifies automatically. This is the set-theoretic condition which the
source flags in Stacks 02WQ.

It is only one way, and the strictly stronger one. A family indexed by an arbitrarily large
type can glue to a scheme of size below the cutoff, so the cofinality bound cannot be recovered
from the size of the glued object; a caller which bounds the glued scheme directly -- it is a
base change of something small, or finite over an object of the site -- should use
`AlgebraicGeometry.Space.isRepresentable_of_openCover_of_contains` and never mention `#ι`.

The containment hypothesis of
`AlgebraicGeometry.Space.isRepresentable_of_openCover_of_contains` is, however, close to being
*implied by its conclusion* once the remaining hypotheses are in force: if `G` is represented
by an object `V` of the site then the charts become open immersions into `V`, and if their
images covered the points of `V` then `V` would carry the glueing datum and its scheme would be
the glued scheme. That last step is the one direction this repo does not have -- that a covering
sieve of `AlgebraicGeometry.BigFppfOver.topology` is jointly surjective on points, flagged as
missing in `StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverSpace` -- so the implication is not
formally available and the containment form is not literally circular. It is still only as
useful as the means available for discharging it, and the discharging lemma is the point:
`AlgebraicGeometry.Space.contains_schemeGlueData_glued_of_le_power` replaces the cofinality
bound by `#ι ≤ T.size ^ ℵ₀` for a single object `T` of the site, which is a statement about the
given data and asserts nothing about representability.
`AlgebraicGeometry.Space.isRepresentable_of_openCover_of_le_power` is the resulting theorem and
the one a caller should reach for first. What makes it work is that the cutoff is a strong
prelimit, so a chart-by-chart bound by `T.size ^ ℵ₀` needs no bound on the number of charts;
`AlgebraicGeometry.Space.contains_schemeGlueData_glued` instead discharges the supremum of the
chart sizes with `Cardinal.iSup_lt_of_lt_cof_ord`, which does.

Mathlib proves the corresponding statement for `Sch` under
`backward.isDefEq.respectTransparency` and `backward.defeqAttrib.useBackward`. No flag is used
here, at the cost of a discipline which the glueing-data file already had to adopt: through
`CategoryTheory.GlueData.mapGlueData` the index type of the glueing data of schemes is
`(schemeGlueData f hf).J` rather than `ι`, and `AlgebraicGeometry.Space.gluedObj` is built from
the glued *scheme* rather than as a multicoequalizer in the site, so the two spellings of an
overlap are only *reducibly* equal. Goals mentioning them are therefore not type-correct at
`implicit` transparency, which is the transparency at which `rw` and `simp only` match — on
`AlgebraicGeometry.Space.glueData_f_comp_toGlued` both `rw` and `simp only [Functor.map_comp]`
fail outright. Every such step is consequently a composition of named equations, since a term is
checked at `default` transparency. `AlgebraicGeometry.Space.isPullback_congr` exists for the one
place where an equation has to be moved under the dependently typed `IsPullback`: taking the two
equations as separate arguments turns the transport into a `subst`.

The comparison itself needs no such care, because
`AlgebraicGeometry.Space.gluedSheaf`'s sections are morphisms of the site and the two sides of
local injectivity are both spelled with `CategoryTheory.yonedaEquiv`; retyping the two sections
at `U ⟶ gluedObjOfContains f hf hg` when they are introduced is what makes `op_comp` match
there.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A family of morphisms of the site, reindexed into the universe where the site's covering
families are indexed. -/
public noncomputable def coverHypercover {I : Type v} [Small.{u} I]
    (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (j : ∀ i, U i ⟶ V) :
    PreZeroHypercover.{u + 1} V :=
  (⟨I, U, j⟩ : PreZeroHypercover.{v} V).reindex
    ((Equiv.ulift.{u + 1, u}).trans (equivShrink I).symm)

/-- The presieve of `AlgebraicGeometry.BigFppfOver.coverHypercover` is the presieve of the
family it reindexes. -/
public theorem presieve₀_coverHypercover {I : Type v} [Small.{u} I]
    (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (j : ∀ i, U i ⟶ V) :
    (coverHypercover B S hS U V j).presieve₀ = Presieve.ofArrows U j :=
  PreZeroHypercover.presieve₀_reindex _ _

/-- A jointly surjective family of open immersions of the site, reindexed by
`AlgebraicGeometry.BigFppfOver.coverHypercover`, is an fppf covering. -/
public theorem coverHypercover_isFppf {I : Type v} [Small.{u} I]
    (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (j : ∀ i, U i ⟶ V)
    (hopen : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((toScheme B S hS).map (j i)))
    (hsurj : ∀ y : (toScheme B S hS).obj V,
      ∃ i, y ∈ Set.range ((toScheme B S hS).map (j i)).base) :
    IsFppfCovering ⟨V.left,
      (coverHypercover B S hS U V j).map (Over.forget (B.obj hS))⟩ := by
  have hZ : (Presieve.ofArrows (fun i => (toScheme B S hS).obj (U i))
      (fun i => (toScheme B S hS).map (j i))) ∈
      Scheme.zariskiPrecoverage ((toScheme B S hS).obj V) :=
    (Scheme.ofArrows_mem_precoverage_iff
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})).2
      ⟨hsurj, hopen⟩
  unfold IsFppfCovering
  rw [Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀_map,
    presieve₀_coverHypercover, Presieve.map_ofArrows, Presieve.map_ofArrows]
  exact Scheme.zariskiPrecoverage_le_fppfPrecoverage ((toScheme B S hS).obj V) hZ

/-- **A jointly surjective family of open immersions of the site generates a covering sieve.**
The family need not be one of the site's chosen covering families: it is a Zariski, hence an
fppf, covering, because its legs are jointly surjective open immersions.

This generalizes `AlgebraicGeometry.BigFppfOver.sieve_ofArrows_mem_topology_of_isColimit`,
which asks the underlying family of schemes to be a coproduct decomposition; the two
hypotheses here are exactly what that lemma extracts from the colimit. -/
theorem sieve_ofArrows_mem_topology_of_jointlySurjective {I : Type v} [Small.{u} I]
    (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (j : ∀ i, U i ⟶ V)
    (hopen : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((toScheme B S hS).map (j i)))
    (hsurj : ∀ y : (toScheme B S hS).obj V,
      ∃ i, y ∈ Set.range ((toScheme B S hS).map (j i)).base) :
    Sieve.ofArrows U j ∈ topology B S hS V := by
  have hgen := B.generate_mem_topology
    ((coverHypercover B S hS U V j).map (Over.forget (B.obj hS)))
    (coverHypercover_isFppf B S hS U V j hopen hsurj)
  have heq : Sieve.ofArrows U j =
      (Sieve.overEquiv V).symm
        (Sieve.ofArrows (fun i => (U i).left) (fun i => (j i).left)) := by
    apply (Sieve.overEquiv V).injective
    rw [OrderIso.apply_symm_apply]
    exact Sieve.overEquiv_ofArrows (X := B.obj hS) (Y := V) _ _
  rw [heq]
  apply B.topology.overEquiv_symm_mem_over
  rwa [PreZeroHypercover.presieve₀_map, presieve₀_coverHypercover,
    Presieve.map_ofArrows] at hgen

end BigFppfOver

namespace BigFppfSite

/-- **A big fppf site is closed under gluing along a family bounded by `size T ^ ℵ₀`.** If
every chart of a gluing datum of schemes has size at most `size T ^ ℵ₀` for a single object `T`
of the site, and the index type is bounded by the same cardinal, then the glued scheme lies in
the site.

This is `AlgebraicGeometry.BigFppfSite.contains_glueData_glued` with the hypothesis on the
index type weakened from `#D.J < B.cutoff.ord.cof` to `#D.J ≤ T.size ^ ℵ₀`. Both discharge the
open-cover bound of Stacks 000Q, but by different means: the cofinality hypothesis bounds the
supremum of the chart sizes by `AlgebraicGeometry.Cardinal.iSup_lt_of_lt_cof_ord`, which needs
a bound on the number of charts, while here every chart is bounded by one cardinal below the
cutoff and the cutoff is a strong prelimit, so no bound on the number of charts beyond
`size T ^ ℵ₀` is required. Neither hypothesis implies the other. -/
theorem contains_glueData_glued_of_le_power (B : BigFppfSite.{u}) (D : Scheme.GlueData.{u})
    {T : Scheme.{u}} (hT : B.Contains T) (hJ : #D.J ≤ T.size ^ ℵ₀)
    (hU : ∀ i, (D.U i).size ≤ T.size ^ ℵ₀) : B.Contains D.glued := by
  rcases isEmpty_or_nonempty D.J with hJe | hJn
  · have : IsEmpty D.glued := ⟨fun x ↦ (D.ι_jointly_surjective x).elim fun i _ ↦ hJe.elim i⟩
    have e : D.glued ≅ (∅ : Scheme.{u}) :=
      (isInitialOfIsEmpty (X := D.glued)).uniqueUpToIso emptyIsInitial
    exact lt_of_le_of_lt ((Scheme.size_congr e).trans_le Scheme.size_empty_le_aleph0)
      B.aleph0_lt_cutoff
  · have hcov : ⨆ i, (D.ι i).opensRange = ⊤ := by
      refine top_le_iff.mp fun x _ ↦ ?_
      obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, hy⟩
    exact Scheme.size_lt_of_openCover B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      (fun i ↦ (D.ι i).opensRange) hcov hT hJ
      fun i ↦ (Scheme.size_congr (D.ι i).isoOpensRange).symm.trans_le (hU i)

end BigFppfSite

namespace Space

/-- Transport a pullback square along equalities of the two morphisms it is taken over. The
equations are separate arguments so that the transport is a `subst` rather than a rewrite
under the dependently typed `IsPullback`. -/
private theorem isPullback_congr {C : Type v} [Category C] {P A A' Z : C} {fst : P ⟶ A}
    {snd : P ⟶ A'} {g₁ g₁' : A ⟶ Z} {g₂ g₂' : A' ⟶ Z} (h : IsPullback fst snd g₁ g₂)
    (e₁ : g₁ = g₁') (e₂ : g₂ = g₂') : IsPullback fst snd g₁' g₂' := e₁ ▸ e₂ ▸ h

section GlueData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ι : Type u} {X : ι → BigFppfOver B S hS}
  (f : (i : ι) → yoneda.obj (X i) ⟶ F)
  (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i))

/-! ### The glued object from a bound on the glued scheme

`AlgebraicGeometry.Space.gluedObj` is indexed by a bound `#ι < B.cutoff.ord.cof` on the index
type of the covering family. That bound is consumed in exactly one place, by
`AlgebraicGeometry.Space.contains_schemeGlueData_glued`, and only to conclude that the glued
scheme lies in the site; nothing else in the construction or in this file looks at `ι` again.
The declarations below are the same construction with that conclusion taken as the hypothesis,
so that a caller which can bound the glued scheme by other means does not have to bound the
index type at all.

The two hypotheses are not interderivable, which is why this variant is needed rather than a
reduction: a scheme of size below the cutoff can be covered by a family indexed by an
arbitrarily large type -- take every chart to be the whole scheme -- so containment of the
glued scheme implies no bound whatsoever on `#ι`.

Nothing new is constructed here. `AlgebraicGeometry.BigFppfSite.Contains` is a proposition, so
the containment proof appearing in `AlgebraicGeometry.Space.gluedObj` and the one taken as a
hypothesis here are definitionally equal, and
`AlgebraicGeometry.Space.gluedObjOfContains_eq` and
`AlgebraicGeometry.Space.toGluedOfContains_eq` are proved by `rfl`.
-/

/-- **The glued scheme lies in the site when the covering family is bounded by
`size T ^ ℵ₀`.** This is `AlgebraicGeometry.Space.contains_schemeGlueData_glued` with the
hypothesis on the index type weakened from `#ι < B.cutoff.ord.cof` to `#ι ≤ T.size ^ ℵ₀`, for
`T` an object of the site; see
`AlgebraicGeometry.BigFppfSite.contains_glueData_glued_of_le_power`.

This is the form which applies to a family indexed by the affine opens of an object `U` of the
site: there `#ι ≤ U.size ≤ U.size ^ ℵ₀`, which is a bound by `B.cutoff` and not by
`B.cutoff.ord.cof`. -/
theorem contains_schemeGlueData_glued_of_le_power {T : Scheme.{u}} (hT : B.Contains T)
    (hιT : #ι ≤ T.size ^ ℵ₀)
    (hX : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ T.size ^ ℵ₀) :
    B.Contains (schemeGlueData f hf).glued :=
  B.contains_glueData_glued_of_le_power (schemeGlueData f hf) hT hιT hX

/-- **The glued object of the site, from a bound on the glued scheme itself.** This is
`AlgebraicGeometry.Space.gluedObj` with the hypothesis on the index type replaced by the
containment of the glued scheme which is all that hypothesis is used to prove. -/
noncomputable def gluedObjOfContains (hg : B.Contains (schemeGlueData f hf).glued) :
    BigFppfOver B S hS :=
  Over.mk (Y := B.obj hg) (B.inclusion.preimage (gluedStructureHom f hf))

/-- The underlying scheme of `AlgebraicGeometry.Space.gluedObjOfContains` is the glued scheme. -/
theorem gluedObjOfContains_left (hg : B.Contains (schemeGlueData f hf).glued) :
    B.inclusion.obj (gluedObjOfContains f hf hg).left = (schemeGlueData f hf).glued := rfl

/-- The glued object built from a bound on the index type is the glued object built from the
containment that bound proves, on the nose. -/
theorem gluedObjOfContains_eq (hι : #ι < B.cutoff.ord.cof) :
    gluedObjOfContains f hf (contains_schemeGlueData_glued f hf hι) = gluedObj f hf hι := rfl

/-- The structure morphism of `AlgebraicGeometry.Space.gluedObjOfContains` is the structure
morphism of the glued scheme. -/
theorem toScheme_map_gluedObjOfContains_hom (hg : B.Contains (schemeGlueData f hf).glued) :
    B.inclusion.map (gluedObjOfContains f hf hg).hom = gluedStructureHom f hf :=
  B.inclusion.map_preimage _

/-- The `i`-th chart into the glued scheme, as a morphism of the underlying category of the
site. This is `AlgebraicGeometry.Space.toGluedLeft` with the hypothesis on the index type
replaced by containment of the glued scheme. -/
noncomputable def toGluedLeftOfContains (hg : B.Contains (schemeGlueData f hf).glued) (i : ι) :
    (X i).left ⟶ B.obj hg :=
  B.inclusion.preimage ((schemeGlueData f hf).ι i)

/-- On underlying schemes, the `i`-th chart into the glued object is the `i`-th inclusion
`(schemeGlueData f hf).ι i` into the glued scheme. -/
theorem inclusion_map_toGluedLeftOfContains
    (hg : B.Contains (schemeGlueData f hf).glued) (i : ι) :
    B.inclusion.map (toGluedLeftOfContains f hf hg i) = (schemeGlueData f hf).ι i :=
  B.inclusion.map_preimage _

/-- The `i`-th chart as a morphism of the big fppf site over `S` into the glued object. This is
`AlgebraicGeometry.Space.toGlued` with the hypothesis on the index type replaced by containment
of the glued scheme. -/
noncomputable def toGluedOfContains (hg : B.Contains (schemeGlueData f hf).glued) (i : ι) :
    X i ⟶ gluedObjOfContains f hf hg :=
  Over.homMk (toGluedLeftOfContains f hf hg i)
    (B.inclusion.map_injective
      ((B.inclusion.map_comp _ _).trans
        ((congrArg (· ≫ B.inclusion.map (gluedObjOfContains f hf hg).hom)
            (inclusion_map_toGluedLeftOfContains f hf hg i)).trans
          ((congrArg ((schemeGlueData f hf).ι i ≫ ·)
              (toScheme_map_gluedObjOfContains_hom f hf hg)).trans
            (ι_gluedStructureHom f hf i)))))

/-- On underlying schemes, the `i`-th chart of the site into the glued object is the `i`-th
inclusion `(schemeGlueData f hf).ι i` into the glued scheme. -/
theorem toScheme_map_toGluedOfContains (hg : B.Contains (schemeGlueData f hf).glued) (i : ι) :
    (BigFppfOver.toScheme B S hS).map (toGluedOfContains f hf hg i) =
      (schemeGlueData f hf).ι i :=
  inclusion_map_toGluedLeftOfContains f hf hg i

/-- The charts of the glued object built from a bound on the index type are the charts built
from the containment that bound proves, on the nose. -/
theorem toGluedOfContains_eq (hι : #ι < B.cutoff.ord.cof) (i : ι) :
    toGluedOfContains f hf (contains_schemeGlueData_glued f hf hι) i = toGlued f hf hι i := rfl

/-- Each chart is an open immersion into the glued object, in the site. -/
theorem toGluedOfContains_openImmersion (hg : B.Contains (schemeGlueData f hf).glued) (i : ι) :
    openImmersionOver B S hS (toGluedOfContains f hf hg i) :=
  Eq.mpr (congrArg (fun m ↦ _root_.AlgebraicGeometry.IsOpenImmersion m)
      (toScheme_map_toGluedOfContains f hf hg i))
    ((schemeGlueData f hf).ι_isOpenImmersion i)

/-- The charts are jointly surjective onto the glued object. -/
theorem toGluedOfContains_jointly_surjective (hg : B.Contains (schemeGlueData f hf).glued)
    (x : (schemeGlueData f hf).glued) :
    ∃ (i : ι) (y : (BigFppfOver.toScheme B S hS).obj (X i)),
      ((BigFppfOver.toScheme B S hS).map (toGluedOfContains f hf hg i)).base y = x := by
  obtain ⟨i, y, hy⟩ := (schemeGlueData f hf).ι_jointly_surjective x
  rw [← toScheme_map_toGluedOfContains f hf hg i] at hy
  exact ⟨i, y, hy⟩

/-! ### The glue condition and the hypercover -/

/-- The charts of the glued object satisfy the glue condition of the gluing data. -/
theorem glueData_f_comp_toGlued (hg : B.Contains (schemeGlueData f hf).glued) (i j : ι) :
    (glueData f hf).f i j ≫ toGluedOfContains f hf hg i =
      ((glueData f hf).t i j ≫ (glueData f hf).f j i) ≫ toGluedOfContains f hf hg j := by
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  have e1 := (BigFppfOver.toScheme B S hS).map_comp ((glueData f hf).f i j)
    (toGluedOfContains f hf hg i)
  have e2 := congrArg ((schemeGlueData f hf).f i j ≫ ·) (toScheme_map_toGluedOfContains f hf hg i)
  have e3 := ((schemeGlueData f hf).glue_condition i j).symm
  have e4 := (Category.assoc ((schemeGlueData f hf).t i j) ((schemeGlueData f hf).f j i)
    ((schemeGlueData f hf).ι j)).symm
  have e5 := congrArg (· ≫ (schemeGlueData f hf).ι j)
    ((BigFppfOver.toScheme B S hS).map_comp ((glueData f hf).t i j)
      ((glueData f hf).f j i)).symm
  have e6 := congrArg ((BigFppfOver.toScheme B S hS).map
    ((glueData f hf).t i j ≫ (glueData f hf).f j i) ≫ ·)
      (toScheme_map_toGluedOfContains f hf hg j).symm
  have e7 := ((BigFppfOver.toScheme B S hS).map_comp
    ((glueData f hf).t i j ≫ (glueData f hf).f j i) (toGluedOfContains f hf hg j)).symm
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))

/-- **The overlaps of the gluing data are the fibre products of the charts over the glued
object**, in the site. The square of schemes is a pullback because the glued scheme is glued
along open immersions, and the functor to schemes reflects it. -/
theorem isPullback_toGlued (hg : B.Contains (schemeGlueData f hf).glued) (i j : ι) :
    IsPullback ((glueData f hf).f i j) ((glueData f hf).t i j ≫ (glueData f hf).f j i)
      (toGluedOfContains f hf hg i) (toGluedOfContains f hf hg j) := by
  let := B.hasPullbacks_schemes
  exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS)
    (isPullback_congr (IsPullback.of_isLimit ((schemeGlueData f hf).vPullbackConeIsLimit i j))
      (toScheme_map_toGluedOfContains f hf hg i).symm
      (toScheme_map_toGluedOfContains f hf hg j).symm)

/-- **The charts of the glued object generate a covering sieve.** -/
theorem sieve_ofArrows_toGlued_mem_topology (hg : B.Contains (schemeGlueData f hf).glued) :
    Sieve.ofArrows X (toGluedOfContains f hf hg) ∈
      BigFppfOver.topology B S hS (gluedObjOfContains f hf hg) :=
  BigFppfOver.sieve_ofArrows_mem_topology_of_jointlySurjective B S hS X _
    (toGluedOfContains f hf hg)
    (fun i => toGluedOfContains_openImmersion f hf hg i)
    (fun y => by
      obtain ⟨i, z, hz⟩ := toGluedOfContains_jointly_surjective f hf hg y
      exact ⟨i, z, hz⟩)

/-- The 1-hypercover of the glued object given by the charts: the charts cover it, and the
overlaps of the gluing data cover their fibre products. -/
noncomputable def oneHypercover (hg : B.Contains (schemeGlueData f hf).glued) :
    (BigFppfOver.topology B S hS).OneHypercover.{u} (gluedObjOfContains f hf hg) where
  I₀ := ι
  X := X
  f := toGluedOfContains f hf hg
  I₁ _ _ := PUnit
  Y i j _ := (glueData f hf).V (i, j)
  p₁ i j _ := (glueData f hf).f i j
  p₂ i j _ := (glueData f hf).t i j ≫ (glueData f hf).f j i
  w i j _ := glueData_f_comp_toGlued f hf hg i j
  mem₀ := sieve_ofArrows_toGlued_mem_topology f hf hg
  mem₁ i j W q₁ q₂ hw := by
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      ((BigFppfOver.topology B S hS).top_mem W)
    intro T g _
    refine ⟨⟨⟩, g ≫ (isPullback_toGlued f hf hg i j).lift q₁ q₂ hw, ?_, ?_⟩
    · exact ((Category.assoc _ _ _).trans (congrArg (g ≫ ·)
        ((isPullback_toGlued f hf hg i j).lift_fst q₁ q₂ hw))).symm
    · exact ((Category.assoc _ _ _).trans (congrArg (g ≫ ·)
        ((isPullback_toGlued f hf hg i j).lift_snd q₁ q₂ hw))).symm

/-- Two charts agree on the glued object wherever their subfunctors do. This is the step that
makes the comparison morphism locally injective. -/
theorem comp_toGlued_eq (hg : B.Contains (schemeGlueData f hf).glued)
    {W : BigFppfOver B S hS} {i j : ι}
    (a : W ⟶ X i) (b : W ⟶ X j) (h : yoneda.map a ≫ f i = yoneda.map b ≫ f j) :
    a ≫ toGluedOfContains f hf hg i = b ≫ toGluedOfContains f hf hg j := by
  rw [← (hf i).rep.lift'_fst a b h, Category.assoc]
  conv_rhs => rw [← (hf i).rep.lift'_snd a b h, ← Functor.relativelyRepresentable.symmetry_fst
    (hf i).rep (hf j).rep, Category.assoc, Category.assoc]
  exact congrArg _ (glueData_f_comp_toGlued f hf hg i j)

/-- The two charts of an overlap induce the same morphism to the presheaf. -/
theorem yoneda_map_glueData_f_comp (i j : ι) :
    yoneda.map ((glueData f hf).f i j) ≫ f i =
      yoneda.map ((glueData f hf).t i j ≫ (glueData f hf).f j i) ≫ f j :=
  (((hf i).rep.isPullback' (f j)).w).trans
    (congrArg (fun m => yoneda.map m ≫ f j)
      (Functor.relativelyRepresentable.symmetry_fst (hf i).rep (hf j).rep).symm)

end GlueData

section Sheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} {ι : Type u}
  {X : ι → BigFppfOver B S hS}
  (f : (i : ι) → yoneda.obj (X i) ⟶ G.obj)
  (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i))

/-- The glued object as a sheaf, through subcanonicity of the big fppf topology. -/
noncomputable def gluedSheaf (hg : B.Contains (schemeGlueData f hf).glued) :
    Sheaf (BigFppfOver.topology B S hS) (Type u) :=
  letI : (BigFppfOver.topology B S hS).Subcanonical := BigFppfOver.subcanonical B S hS
  (BigFppfOver.topology B S hS).yoneda.obj (gluedObjOfContains f hf hg)

/-- The underlying presheaf of `AlgebraicGeometry.Space.gluedSheaf` is the presheaf represented
by the glued object. -/
theorem gluedSheaf_obj (hg : B.Contains (schemeGlueData f hf).glued) :
    (gluedSheaf f hf hg).obj = yoneda.obj (gluedObjOfContains f hf hg) := rfl

/-- The section of the sheaf over the glued object obtained by glueing the sections which
correspond to the charts. -/
noncomputable def gluedSection (hg : B.Contains (schemeGlueData f hf).glued) :
    G.obj.obj (op (gluedObjOfContains f hf hg)) :=
  Multifork.IsLimit.sectionsEquiv ((oneHypercover f hf hg).isLimitMultifork G)
    { val := fun i => yonedaEquiv (f i)
      property := fun r =>
        (yonedaEquiv_naturality (f r.1.1) ((glueData f hf).f r.1.1 r.1.2)).trans
          ((congrArg yonedaEquiv (yoneda_map_glueData_f_comp f hf r.1.1 r.1.2)).trans
            (yonedaEquiv_naturality (f r.1.2)
              ((glueData f hf).t r.1.1 r.1.2 ≫ (glueData f hf).f r.1.2 r.1.1)).symm) }

/-- The glued section restricts along the `i`-th chart to the section corresponding to
`f i`. -/
theorem map_toGlued_gluedSection (hg : B.Contains (schemeGlueData f hf).glued) (i : ι) :
    G.obj.map (toGluedOfContains f hf hg i).op (gluedSection f hf hg) = yonedaEquiv (f i) :=
  Multifork.IsLimit.sectionsEquiv_apply_val
    ((oneHypercover f hf hg).isLimitMultifork G) _ i

/-- **The comparison morphism of Stacks 01JJ for the big fppf site over `S`**: the morphism
from the sheaf represented by the glued object to the given sheaf, determined by the charts. -/
noncomputable def gluedToSheaf (hg : B.Contains (schemeGlueData f hf).glued) :
    gluedSheaf f hf hg ⟶ G where
  hom := yonedaEquiv.symm (gluedSection f hf hg)

/-- The comparison morphism restricts along the `i`-th chart to `f i`. -/
theorem yoneda_map_toGlued_comp (hg : B.Contains (schemeGlueData f hf).glued) (i : ι) :
    yoneda.map (toGluedOfContains f hf hg i) ≫ (gluedToSheaf f hf hg).hom = f i :=
  yonedaEquiv.injective
    ((yonedaEquiv_naturality (yonedaEquiv.symm (gluedSection f hf hg))
        (toGluedOfContains f hf hg i)).symm.trans
      ((congrArg (G.obj.map (toGluedOfContains f hf hg i).op)
          (yonedaEquiv.apply_symm_apply (gluedSection f hf hg))).trans
        (map_toGlued_gluedSection f hf hg i)))

/-- **The comparison morphism is locally injective.** Two morphisms into the glued object with
the same image in the sheaf agree after restriction to the common refinement of the chart
covers they pull back to, by `AlgebraicGeometry.Space.comp_toGlued_eq`. -/
theorem isLocallyInjective_gluedToSheaf (hg : B.Contains (schemeGlueData f hf).glued) :
    Sheaf.IsLocallyInjective (gluedToSheaf f hf hg) := by
  constructor
  rintro ⟨U⟩ (α : U ⟶ gluedObjOfContains f hf hg) (β : U ⟶ gluedObjOfContains f hf hg) h
  have mem := sieve_ofArrows_toGlued_mem_topology f hf hg
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    ((BigFppfOver.topology B S hS).intersection_covering
      ((BigFppfOver.topology B S hS).pullback_stable α mem)
      ((BigFppfOver.topology B S hS).pullback_stable β mem))
  rintro V γ ⟨⟨W₁, a, _, ⟨i⟩, fac₁⟩, ⟨W₂, b, _, ⟨j⟩, fac₂⟩⟩
  change γ ≫ α = γ ≫ β
  replace h : G.obj.map α.op (gluedSection f hf hg) =
      G.obj.map β.op (gluedSection f hf hg) := h
  have hγ := congrArg (G.obj.map γ.op) h
  simp only [← Functor.map_comp_apply, ← op_comp] at hγ
  rw [← fac₁, ← fac₂] at hγ ⊢
  refine comp_toGlued_eq f hf hg a b (yonedaEquiv.injective ?_)
  rw [← yonedaEquiv_naturality, ← yonedaEquiv_naturality,
    ← map_toGlued_gluedSection f hf hg i, ← map_toGlued_gluedSection f hf hg j]
  simpa only [← Functor.map_comp_apply, ← op_comp] using hγ

/-- The charts factor the canonical morphism from the coproduct of the representables. -/
theorem sigmaDesc_yoneda_map_toGlued_comp (hg : B.Contains (schemeGlueData f hf).glued)
    [HasCoproduct fun i => yoneda.obj (X i)] :
    Sigma.desc (fun i => yoneda.map (toGluedOfContains f hf hg i)) ≫ (gluedToSheaf f hf hg).hom =
      Sigma.desc f :=
  Sigma.hom_ext _ _ fun i =>
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (gluedToSheaf f hf hg).hom) (Sigma.ι_comp_desc _ _)).trans
        ((yoneda_map_toGlued_comp f hf hg i).trans (Sigma.ι_comp_desc _ _).symm))

/-- **The comparison morphism is locally surjective**, because the family of charts is. -/
theorem isLocallySurjective_gluedToSheaf (hg : B.Contains (schemeGlueData f hf).glued)
    [HasCoproduct fun i => yoneda.obj (X i)]
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f)) :
    Sheaf.IsLocallySurjective (gluedToSheaf f hf hg) :=
  let := hsurj
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (sigmaDesc_yoneda_map_toGlued_comp f hf hg)

/-- **The comparison morphism is an isomorphism**, being locally injective and locally
surjective. -/
theorem isIso_gluedToSheaf (hg : B.Contains (schemeGlueData f hf).glued)
    [HasCoproduct fun i => yoneda.obj (X i)]
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f)) :
    IsIso (gluedToSheaf f hf hg) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (gluedToSheaf f hf hg)]
  exact ⟨isLocallyInjective_gluedToSheaf f hf hg,
    isLocallySurjective_gluedToSheaf f hf hg hsurj⟩

/-- **Stacks 01JJ for the big fppf site over `S`, from a bound on the glued scheme.** A sheaf
on the big fppf site over `S` which admits a jointly locally surjective family of relatively
representable open immersions from representable presheaves is representable, by an object of
that site, as soon as the *scheme* glued from the family lies in the site.

This is the form of the statement to use when what is available is a bound on the glued
object rather than on the index type of the family. `B.Contains` unfolds to a strict
inequality of sizes, so the hypothesis is literally
`(schemeGlueData f hf).glued.size < B.cutoff` and is dischargeable by the size API --
`AlgebraicGeometry.Scheme.size_lt_of_openCover`,
`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact`,
`AlgebraicGeometry.Scheme.size_le_of_mono_quasiCompact` and so on.

`AlgebraicGeometry.Space.isRepresentable_of_openCover` is the specialization to a bound on the
index type, which is strictly stronger: see the discussion above
`AlgebraicGeometry.Space.gluedObjOfContains`. -/
theorem isRepresentable_of_openCover_of_contains
    (hg : B.Contains (schemeGlueData f hf).glued)
    [HasCoproduct fun i => yoneda.obj (X i)]
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f)) :
    G.obj.IsRepresentable :=
  let := isIso_gluedToSheaf f hf hg hsurj
  ⟨gluedObjOfContains f hf hg,
    ⟨Functor.representableByEquiv.symm
      ((sheafToPresheaf _ _).mapIso (asIso (gluedToSheaf f hf hg)))⟩⟩

/-- **Stacks 01JJ for the big fppf site over `S`, from a bound on a scheme isomorphic to the
glued one.** The convenient repackaging of
`AlgebraicGeometry.Space.isRepresentable_of_openCover_of_contains` for a caller who knows the
glued scheme only up to isomorphism, for instance as a base change whose size is bounded by a
morphism property. -/
theorem isRepresentable_of_openCover_of_size
    (Z : Scheme.{u}) (hZ : Z.size < B.cutoff) (e : Z ≅ (schemeGlueData f hf).glued)
    [HasCoproduct fun i => yoneda.obj (X i)]
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f)) :
    G.obj.IsRepresentable :=
  isRepresentable_of_openCover_of_contains f hf ((Scheme.size_congr e).symm.trans_lt hZ) hsurj

include hf in
/-- **Stacks 01JJ for the big fppf site over `S`, from a cardinal bound on the covering
family.** A sheaf on the big fppf site over `S` which admits a jointly locally surjective
family of relatively representable open immersions from representable presheaves is
representable, by an object of that site, as soon as the index type of the family and every
member of it are bounded by `size T ^ ℵ₀` for a single object `T` of the site.

This is the turnkey form for a family indexed by the affine opens of an object `U` of the
site, which is bounded by `U.size` and so by `B.cutoff`, but not by `B.cutoff.ord.cof`. Unlike
`AlgebraicGeometry.Space.isRepresentable_of_openCover_of_contains`, whose hypothesis is nearly
recoverable from its conclusion once the remaining hypotheses are in force, the hypotheses here
are cardinal inequalities about the given data and assert nothing about representability. -/
theorem isRepresentable_of_openCover_of_le_power {T : Scheme.{u}} (hT : B.Contains T)
    (hιT : #ι ≤ T.size ^ ℵ₀)
    (hX : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ T.size ^ ℵ₀)
    [HasCoproduct fun i => yoneda.obj (X i)]
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f)) :
    G.obj.IsRepresentable :=
  isRepresentable_of_openCover_of_contains f hf
    (contains_schemeGlueData_glued_of_le_power f hf hT hιT hX) hsurj

include hf in
/-- **Stacks 01JJ for the big fppf site over `S`.** A sheaf on the big fppf site over `S`
which admits a jointly locally surjective family of relatively representable open immersions
from representable presheaves is representable, by an object of that site.

This is the statement Mathlib's
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable` does not give: Mathlib glues
in `Scheme` with no size control, so its representing object need not satisfy the site's size
cutoff. The hypothesis on the index type is one set-theoretic condition which makes the glued
scheme an object of the site; an at most countable family satisfies it automatically, since
uncountable cofinality of the cutoff is a field of `AlgebraicGeometry.BigFppfSite`. It is not
the weakest such condition:
`AlgebraicGeometry.Space.isRepresentable_of_openCover_of_contains` asks only that the glued
scheme lie in the site, however that is established. -/
@[stacks 01JJ "big fppf site over a scheme"]
theorem isRepresentable_of_openCover (hι : #ι < B.cutoff.ord.cof)
    [HasCoproduct fun i => yoneda.obj (X i)]
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc f)) :
    G.obj.IsRepresentable :=
  isRepresentable_of_openCover_of_contains f hf (contains_schemeGlueData_glued f hf hι) hsurj

end Sheaf

end Space

end AlgebraicGeometry

end
