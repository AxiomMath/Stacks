module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.BigEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp

/-!
# Comparison of the two small étale sites of an algebraic space

An étale scheme chart of an algebraic space `X` over `S` is in particular an algebraic space
étale over `X`, so the small étale site of Stacks 03ED includes into the spaces-étale site of
Stacks 03G0. This file constructs that inclusion and shows that it is a special cocontinuous
functor, hence that it induces an equivalence of the associated topoi.

## Main definitions

* `AlgebraicGeometry.Space.chartFunctor` sends a scheme chart of `X` to the algebraic space
  over `X` it represents, and `AlgebraicGeometry.Space.chartOver` is its value on an étale
  chart.
* `AlgebraicGeometry.Space.comparisonFunctor` is the comparison functor from the small étale
  site of `X` to its spaces-étale site.

## Main results

* `AlgebraicGeometry.Space.exists_comparisonFunctor`,
  `AlgebraicGeometry.Space.comparisonFunctor_obj` and
  `AlgebraicGeometry.Space.comparisonFunctor_map` characterize the comparison on objects and
  on arrows.
* `AlgebraicGeometry.Space.exists_scheme_chart_cover`: every object of the spaces-étale site of
  `X` admits a covering by a single étale scheme chart of `X`.  This is Stacks 03H7, and it is
  the density half of the comparison.
* `AlgebraicGeometry.Space.comparisonFunctor_specialCocontinuous`: the comparison is special
  cocontinuous in the sense of Stacks 03CG.
* `AlgebraicGeometry.Space.comparisonFunctor_isDenseSubsite` and
  `AlgebraicGeometry.Space.comparisonFunctor_isContinuous` expose the site properties to
  typeclass search, and `AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence` exposes
  the induced equivalence of topoi, for sheaves valued in any category.
* `AlgebraicGeometry.Space.exists_chosen_etaleCovering`: every étale covering family of
  `Sch_κ` has a combinatorially equivalent representative among the chosen étale covering
  families of the big étale site carried by `B`.
* `AlgebraicGeometry.Space.comparisonFunctor_full` and
  `AlgebraicGeometry.Space.comparisonFunctor_faithful`: the comparison is fully faithful.

## Implementation notes

The comparison is characterized on objects by the Yoneda algebraic space of a scheme chart
with its given structure map, and on arrows by Yoneda. Because the object part is an equality
of objects of a slice of a full subcategory, the arrow part can only be a `HEq`; the two are
therefore stated separately, and `AlgebraicGeometry.Space.exists_comparisonFunctor` records
that a functor satisfying both exists. The functor itself is *constructed*, so both
characterizations hold by `rfl` and no transport along them is ever needed — which is what
keeps the cocontinuity argument below free of `eqToHom` algebra.

Cocontinuity is where the two covering systems meet. A covering sieve of a chart in the
spaces-étale site is refined by a jointly point-surjective family of algebraic spaces étale
over it; choosing an atlas of each member turns that family into a family of *scheme* charts
which is jointly surjective on points, by Stacks 03H5 and the identification of the points of
a represented presheaf with the points of the representing scheme
(`AlgebraicGeometry.Space.pointsToScheme`). That family is an étale covering, but not
necessarily one of the *chosen* families of the big fppf site, whose index types are bounded;
`AlgebraicGeometry.Space.exists_chosen_etaleCovering` replaces it by a combinatorially
equivalent chosen one, which is what the small étale precoverage asks for. Pulling the chosen
family back into the small étale site and comparing it with the atlas family index by index
then exhibits each of its members as a refinement of a member of the original family, so the
sieve it generates is below the functor pullback of the covering sieve.

Density is the other half: every algebraic space étale over `X` is covered by a *single*
étale scheme chart, namely an atlas of it composed with its structure morphism, which is
étale by Stacks 03FT and surjective on points by Stacks 03H5. Together with full faithfulness
this identifies the small étale topology with the topology restricted from the spaces-étale
one, which is the remaining field of `CategoryTheory.Functor.IsDenseSubsite`.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Lemma 66.18.9 (Tag 03H7)](https://stacks.math.columbia.edu/tag/03H7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w w'

namespace AlgebraicGeometry.Space

/-! ### Chosen representatives of étale covering families -/

/-- Every étale covering family of `Sch_κ` is combinatorially equivalent to one of the chosen
étale covering families of the big étale site carried by `B`.

This is the étale case of the representative clause of Stacks 03FF, deduced from the fppf
case — which is a field of `AlgebraicGeometry.BigFppfSite` — because an étale covering is an
fppf covering and because combinatorially equivalent families generate the same presieve, so
that being an étale covering passes to any combinatorially equivalent family. -/
theorem exists_chosen_etaleCovering (B : BigFppfSite.{u}) (E : Covering B.Schemes)
    (hE : IsEtaleCovering E) :
    ∃ E' : Covering B.Schemes, B.etaleCovering E' ∧ Covering.CombEquiv E E' := by
  have hfp : IsFppfCovering E := by
    rw [IsFppfCovering, Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map]
    exact Scheme.etalePrecoverage_le_fppfPrecoverage _ hE
  obtain ⟨E', hE', hEquiv⟩ := B.fppf_has_representative E hfp
  refine ⟨E', ⟨hE', ?_⟩, hEquiv⟩
  obtain ⟨hbase, hComb⟩ := hEquiv
  obtain ⟨T, E₀⟩ := E
  obtain ⟨T', E₀'⟩ := E'
  obtain rfl : T = T' := hbase
  show IsEtaleCovering (⟨T, E₀'⟩ : Covering B.Schemes)
  change IsEtaleCovering (⟨T, E₀⟩ : Covering B.Schemes) at hE
  rw [IsEtaleCovering, PreZeroHypercover.presieve₀_map,
    ← PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb,
    ← PreZeroHypercover.presieve₀_map]
  exact hE

/-! ### The comparison functor -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- A scheme chart of `X` regarded as an algebraic space over `X`, functorially in the chart:
the presheaf it represents is an algebraic space over `S` by Stacks 025Z, and the chart itself
is the structure morphism to `X`. -/
def chartFunctor : CostructuredArrow yoneda X.1 ⥤ Over X where
  obj V := Over.mk (ObjectProperty.homMk V.hom :
    (⟨yoneda.obj V.left, isAlgebraicSpace_yoneda B S hS V.left⟩ : AlgebraicSpaces B S hS) ⟶ X)
  map {V W} f := Over.homMk
    (ObjectProperty.homMk (yoneda.map f.left) :
      (⟨yoneda.obj V.left, isAlgebraicSpace_yoneda B S hS V.left⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj W.left, isAlgebraicSpace_yoneda B S hS W.left⟩)
    (ObjectProperty.hom_ext _ (CostructuredArrow.w f))
  map_id V := by
    refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
    simp
  map_comp f g := by
    refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
    simp

/-- The algebraic space over `X` associated to an étale scheme chart of `X`. -/
def chartOver (U : SmallEtale B S hS X.1) : Over X :=
  Over.mk (ObjectProperty.homMk U.1.hom :
    (⟨yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U),
      isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS X.1).obj U)⟩ :
        AlgebraicSpaces B S hS) ⟶ X)

/-- **Stacks 03G1.** The canonical inclusion of the small étale site of `X` into its
spaces-étale site: an étale scheme chart of `X` is an algebraic space étale over `X`. -/
@[stacks 03G1 "the functor"]
def comparisonFunctor : SmallEtale B S hS X.1 ⥤ SpacesEtale B S hS X :=
  ObjectProperty.lift (IsEtaleOver B S hS X)
    (SmallEtale.inclusion B S hS X.1 ⋙ chartFunctor B S hS X)
    (fun U => isEtale_of_presheaf_etale B S hS U.2)

/-- **Stacks 03G1.** The comparison sends a scheme chart to its Yoneda algebraic space over
`X`. -/
@[stacks 03G1 "canonical action on objects"]
theorem comparisonFunctor_obj (U : SmallEtale B S hS X.1) :
    ((comparisonFunctor B S hS X).obj U).1 = chartOver B S hS X U := rfl

/-- **Stacks 03G1.** The comparison sends a chart morphism to its Yoneda morphism. -/
@[stacks 03G1 "canonical action on arrows"]
theorem comparisonFunctor_map {U V : SmallEtale B S hS X.1} (f : U ⟶ V) :
    HEq ((comparisonFunctor B S hS X).map f).hom.left.hom
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map f)) := HEq.rfl

/-- **Stacks 03G1.** There is a functor from the small étale site of `X` to its spaces-étale
site carrying each scheme chart to the corresponding algebraic-space chart and each arrow to
its Yoneda arrow. -/
theorem exists_comparisonFunctor :
    ∃ i : SmallEtale B S hS X.1 ⥤ SpacesEtale B S hS X,
      (∀ U, (i.obj U).1 = chartOver B S hS X U) ∧
      (∀ (U V : SmallEtale B S hS X.1) (f : U ⟶ V),
        HEq (i.map f).hom.left.hom
          (yoneda.map ((SmallEtale.toOver B S hS X.1).map f))) :=
  ⟨comparisonFunctor B S hS X, comparisonFunctor_obj B S hS X,
    fun _ _ f => comparisonFunctor_map B S hS X f⟩

/-! ### Full faithfulness -/

/-- The comparison functor is full: a morphism of algebraic spaces between two represented
charts is the Yoneda image of a morphism of the site, and the triangle over `X` descends. -/
theorem comparisonFunctor_full : (comparisonFunctor B S hS X).Full := by
  constructor
  intro U V f
  let α := f.hom.left.hom
  let g : U.1.left ⟶ V.1.left := yoneda.preimage α
  have hα : yoneda.map g = α := yoneda.map_preimage α
  have htriangle : yoneda.map g ≫ V.1.hom = U.1.hom := by
    have hw := congrArg (fun q => q.hom) f.hom.w
    change α ≫ V.1.hom = U.1.hom at hw
    rwa [hα]
  exact ⟨ObjectProperty.homMk (CostructuredArrow.homMk g htriangle),
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ hα))⟩

/-- The comparison functor is faithful, because `yoneda` is. -/
theorem comparisonFunctor_faithful : (comparisonFunctor B S hS X).Faithful := by
  constructor
  intro U V f g h
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
  have hh := congrArg (fun q => q.hom.left.hom) h
  change yoneda.map f.hom.left = yoneda.map g.hom.left at hh
  exact yoneda.map_injective hh

/-! ### Pulling an étale covering of a chart back into the small étale site -/

/-- An étale morphism of the big fppf site of `S` into the scheme underlying an étale chart
`U` of `X` is itself an étale chart of `X`, the structure morphism being the composite. -/
private def comparisonChartOfEtaleMap (U : SmallEtale B S hS X.1)
    {T : BigFppfOver B S hS} (f : T ⟶ U.1.left)
    (hf : Etale ((BigFppfOver.toScheme B S hS).map f)) : SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk (yoneda.map f ≫ U.1.hom), by
    have := isMultiplicative_presheaf_etale B S hS
    exact MorphismProperty.comp_mem _ (yoneda.map f) U.1.hom
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ f).2 hf) U.2⟩

/-- The morphism of étale charts underlying
`AlgebraicGeometry.Space.comparisonChartOfEtaleMap`. -/
private def comparisonChartMapTo (U : SmallEtale B S hS X.1)
    {T : BigFppfOver B S hS} (f : T ⟶ U.1.left)
    (hf : Etale ((BigFppfOver.toScheme B S hS).map f)) :
    comparisonChartOfEtaleMap B S hS X U f hf ⟶ U :=
  ObjectProperty.homMk (CostructuredArrow.homMk f (by simp [comparisonChartOfEtaleMap]))

/-- A chosen étale covering family of the scheme underlying an étale chart `U` of `X`, viewed
as a family of étale charts of `X` covering `U`. -/
private def comparisonSourceFamilyOfEtaleCover (U : SmallEtale B S hS X.1)
    (E : PreZeroHypercover.{u + 1} U.1.left.left)
    (hE : B.etaleCovering ⟨U.1.left.left, E⟩) :
    PreZeroHypercover.{u + 1} U := by
  have hf (i : E.I₀) :
      Etale ((BigFppfOver.toScheme B S hS).map
        (Over.homMk (E.f i) : (Over.mk (E.f i ≫ U.1.left.hom) : BigFppfOver B S hS) ⟶
          U.1.left)) := by
    have hmem : Presieve.ofArrows (fun i => (E.X i).1)
        (fun i => B.inclusion.map (E.f i)) ∈
        Scheme.precoverage (@Etale.{u} : MorphismProperty Scheme.{u})
          (B.inclusion.obj U.1.left.left) := hE.2
    rw [Scheme.ofArrows_mem_precoverage_iff
      (P := (@Etale.{u} : MorphismProperty Scheme.{u}))] at hmem
    exact hmem.2 i
  exact ⟨E.I₀, fun i => comparisonChartOfEtaleMap B S hS X U _ (hf i),
    fun i => comparisonChartMapTo B S hS X U _ (hf i)⟩

/-- The family of charts of `AlgebraicGeometry.Space.comparisonSourceFamilyOfEtaleCover` is a
covering family of the small étale site: its image under `toSchemes` is the given family. -/
private theorem comparisonSourceFamilyOfEtaleCover_isCovering (U : SmallEtale B S hS X.1)
    (E : PreZeroHypercover.{u + 1} U.1.left.left)
    (hE : B.etaleCovering ⟨U.1.left.left, E⟩) :
    SmallEtale.IsCovering B S hS X.1
      ⟨U, comparisonSourceFamilyOfEtaleCover B S hS X U E hE⟩ := hE

/-! ### Atlases of the members of a spaces-étale covering family -/

/-- A chosen scheme atlas of an algebraic space étale over `X`. -/
private noncomputable def comparisonAtlasSource (V : SpacesEtale B S hS X) :
    BigFppfOver B S hS :=
  Classical.choose ((SpacesEtale.toSpaces B S hS X).obj V).property.exists_atlas

/-- The chosen atlas morphism of an algebraic space étale over `X`. -/
private noncomputable def comparisonAtlasMap (V : SpacesEtale B S hS X) :
    yoneda.obj (comparisonAtlasSource B S hS X V) ⟶
      ((SpacesEtale.toSpaces B S hS X).obj V).1 :=
  Classical.choose (Classical.choose_spec
    ((SpacesEtale.toSpaces B S hS X).obj V).property.exists_atlas)

/-- The chosen atlas morphism is surjective after every representable base change. -/
private theorem comparisonAtlasMap_surjective (V : SpacesEtale B S hS X) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (comparisonAtlasMap B S hS X V) :=
  (Classical.choose_spec (Classical.choose_spec
    ((SpacesEtale.toSpaces B S hS X).obj V).property.exists_atlas)).1

/-- The chosen atlas morphism is étale after every representable base change. -/
private theorem comparisonAtlasMap_etale (V : SpacesEtale B S hS X) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (comparisonAtlasMap B S hS X V) :=
  (Classical.choose_spec (Classical.choose_spec
    ((SpacesEtale.toSpaces B S hS X).obj V).property.exists_atlas)).2

/-- For a family of algebraic spaces étale over the image of an étale chart `U`, the morphism
of the site refining the chosen atlas of a member along that member's structure morphism. -/
private noncomputable def comparisonAtlasRefinementMap (U : SmallEtale B S hS X.1)
    (E : PreZeroHypercover.{u + 1} ((comparisonFunctor B S hS X).obj U)) (i : E.I₀) :
    comparisonAtlasSource B S hS X (E.X i) ⟶ U.1.left :=
  yoneda.preimage (Y := U.1.left) (comparisonAtlasMap B S hS X (E.X i) ≫
    ((SpacesEtale.toSpaces B S hS X).map (E.f i)).hom)

/-- The defining property of `AlgebraicGeometry.Space.comparisonAtlasRefinementMap`. -/
private theorem comparisonAtlasRefinementMap_map (U : SmallEtale B S hS X.1)
    (E : PreZeroHypercover.{u + 1} ((comparisonFunctor B S hS X).obj U)) (i : E.I₀) :
    yoneda.map (comparisonAtlasRefinementMap B S hS X U E i) =
      comparisonAtlasMap B S hS X (E.X i) ≫
        ((SpacesEtale.toSpaces B S hS X).map (E.f i)).hom :=
  yoneda.map_preimage _

/-- The structure morphism of the image of `f` in `Spaces` commutes with the structure maps over
`X` of its source and target. -/
private theorem comparison_toSpaces_map_comp_hom {U V : SpacesEtale B S hS X} (f : U ⟶ V) :
    ((SpacesEtale.toSpaces B S hS X).map f).hom ≫
        ((SpacesEtale.inclusion B S hS X).obj V).hom.hom =
      ((SpacesEtale.inclusion B S hS X).obj U).hom.hom :=
  congrArg (fun q => q.hom) ((SpacesEtale.inclusion B S hS X).map f).w

/-- The structure morphism of a member of a family over the image of `U` is étale: it is a
morphism between two algebraic spaces each étale over `X`, so Stacks 03FV applies. -/
private theorem comparisonFamily_isEtale (U : SmallEtale B S hS X.1)
    (E : PreZeroHypercover.{u + 1} ((comparisonFunctor B S hS X).obj U)) (i : E.I₀) :
    IsEtale B S hS ((SpacesEtale.toSpaces B S hS X).map (E.f i)).hom := by
  refine isEtale_of_isEtale_over B S hS
    ((SpacesEtale.toSpaces B S hS X).obj (E.X i)).property
    ((SpacesEtale.toSpaces B S hS X).obj ((comparisonFunctor B S hS X).obj U)).property
    X.property (((SpacesEtale.toSpaces B S hS X).map (E.f i)).hom)
    (((SpacesEtale.inclusion B S hS X).obj (E.X i)).hom.hom)
    (((SpacesEtale.inclusion B S hS X).obj ((comparisonFunctor B S hS X).obj U)).hom.hom)
    (E.X i).property ((comparisonFunctor B S hS X).obj U).property
    (comparison_toSpaces_map_comp_hom B S hS X (E.f i))

/-- The refinement of a chosen atlas along the structure morphism of its member is an étale
morphism of schemes: it is a composite of two étale morphisms of algebraic spaces. -/
private theorem comparisonAtlasRefinementMap_etale (U : SmallEtale B S hS X.1)
    (E : PreZeroHypercover.{u + 1} ((comparisonFunctor B S hS X).obj U)) (i : E.I₀) :
    Etale ((BigFppfOver.toScheme B S hS).map
      (comparisonAtlasRefinementMap B S hS X U E i)) := by
  refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).1
    (presheaf_etale_of_isEtale B S hS ?_)
  rw [comparisonAtlasRefinementMap_map]
  exact isEtale_comp B S hS
    (isEtale_of_presheaf_etale B S hS (comparisonAtlasMap_etale B S hS X (E.X i)))
    (comparisonFamily_isEtale B S hS X U E i)

/-- The family of chosen atlases of the members of a jointly point-surjective family over the
image of an étale chart `U` is an étale covering of the scheme underlying `U`.

Joint surjectivity on points transfers to the schemes because the points of a represented
presheaf are the points of the representing scheme, and because an atlas is surjective on
points by Stacks 03H5. -/
private theorem comparison_atlas_family_isEtaleCovering (U : SmallEtale B S hS X.1)
    (E : PreZeroHypercover.{u + 1} ((comparisonFunctor B S hS X).obj U))
    (hE : SpacesEtale.IsCovering B S hS X ⟨(comparisonFunctor B S hS X).obj U, E⟩) :
    IsEtaleCovering (⟨U.1.left.left,
      ⟨E.I₀, fun i => (comparisonAtlasSource B S hS X (E.X i)).left,
        fun i => (comparisonAtlasRefinementMap B S hS X U E i).left⟩⟩ : Covering B.Schemes) := by
  show Presieve.ofArrows
      (fun i => (comparisonAtlasSource B S hS X (E.X i)).left.1)
      (fun i => B.inclusion.map (comparisonAtlasRefinementMap B S hS X U E i).left) ∈
    Scheme.precoverage (@Etale.{u} : MorphismProperty Scheme.{u})
      (B.inclusion.obj U.1.left.left)
  rw [Scheme.ofArrows_mem_precoverage_iff (P := (@Etale.{u} : MorphismProperty Scheme.{u}))]
  refine ⟨fun x => ?_, fun i => comparisonAtlasRefinementMap_etale B S hS X U E i⟩
  obtain ⟨w, hw⟩ := surjective_pointsToScheme B S hS U.1.left x
  obtain ⟨i, y, hy⟩ := hE w
  have hy' : pointsMap B S hS ((SpacesEtale.toSpaces B S hS X).obj (E.X i)).1
      (((SpacesEtale.toSpaces B S hS X).map (E.f i)).hom) y = w := hy
  obtain ⟨z, hz⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS
    ((SpacesEtale.toSpaces B S hS X).obj (E.X i)).1
    ((SpacesEtale.toSpaces B S hS X).obj (E.X i)).property
    (comparisonAtlasSource B S hS X (E.X i))
    (comparisonAtlasMap B S hS X (E.X i))).mp
      (comparisonAtlasMap_surjective B S hS X (E.X i)) y
  have h1 : pointsMap B S hS (yoneda.obj (comparisonAtlasSource B S hS X (E.X i)))
      (yoneda.map (comparisonAtlasRefinementMap B S hS X U E i)) z = w :=
    (congrArg
        (fun q => pointsMap B S hS
          (yoneda.obj (comparisonAtlasSource B S hS X (E.X i))) q z)
        (comparisonAtlasRefinementMap_map B S hS X U E i)).trans
      ((pointsMap_comp_apply B S hS (comparisonAtlasMap B S hS X (E.X i))
        (((SpacesEtale.toSpaces B S hS X).map (E.f i)).hom) z).trans
        (by rwa [hz]))
  refine ⟨i, pointsToScheme B S hS (comparisonAtlasSource B S hS X (E.X i)) z, ?_⟩
  show (BigFppfOver.toScheme B S hS).map (comparisonAtlasRefinementMap B S hS X U E i)
      (pointsToScheme B S hS (comparisonAtlasSource B S hS X (E.X i)) z) = x
  exact ((pointsToScheme_pointsMap_yoneda B S hS
        (comparisonAtlasRefinementMap B S hS X U E i) z).symm.trans
      (congrArg (pointsToScheme B S hS U.1.left) h1)).trans hw

/-! ### Cocontinuity -/

/-- A covering sieve of the spaces-étale topology is refined by a jointly point-surjective
family.

The three site axioms of `AlgebraicGeometry.Space.SpacesEtale.isSite` are exactly what is
needed to run the induction over the generation of the topology from the precoverage. -/
private theorem comparison_exists_covering_refining_sieve
    {Y : SpacesEtale B S hS X} {R : Sieve Y}
    (hR : R ∈ SpacesEtale.topology B S hS X Y) :
    ∃ E : PreZeroHypercover.{u + 1} Y,
      SpacesEtale.IsCovering B S hS X ⟨_, E⟩ ∧ E.presieve₀ ≤ R := by
  rw [SpacesEtale.topology, Precoverage.mem_toGrothendieck_iff] at hR
  induction hR with
  | of Y P hP =>
      obtain ⟨E, hEq, hE⟩ := hP
      exact ⟨E, hE, by rw [hEq]; exact Sieve.le_generate _⟩
  | top Y =>
      exact ⟨PreZeroHypercover.singleton (𝟙 Y),
        (SpacesEtale.isSite B S hS X).1 (𝟙 Y), fun _ _ _ => trivial⟩
  | pullback Y R hR Z f ih =>
      obtain ⟨E, hE, hle⟩ := ih
      obtain ⟨P, p₁, p₂, hpb, hP⟩ := (SpacesEtale.isSite B S hS X).2.2 ⟨Y, E⟩ hE Z f
      refine ⟨⟨E.I₀, P, p₂⟩, hP, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      intro i
      rw [Sieve.pullback_apply, ← (hpb i).w]
      exact R.downward_closed (hle _ _ ⟨i⟩) (p₁ i)
  | transitive Y R Q hR hRQ ihR ihRQ =>
      obtain ⟨E, hE, hle⟩ := ihR
      choose F hF hFle using fun i : E.I₀ => ihRQ (hle _ _ ⟨i⟩)
      refine ⟨E.bind F, (SpacesEtale.isSite B S hS X).2.1 ⟨Y, E⟩ hE
        (fun i ↦ ⟨E.X i, F i⟩) hF (fun _ ↦ rfl), ?_⟩
      rw [Presieve.ofArrows_le_iff]
      rintro ⟨i, j⟩
      show Q ((F i).f j ≫ E.f i)
      exact hFle i _ _ ⟨j⟩

/-- **A covering sieve of the spaces-étale topology is refined by a jointly point-surjective
family.**

The three site axioms of `AlgebraicGeometry.Space.SpacesEtale.isSite` are exactly what is
needed to run the induction over the generation of the topology from the precoverage.

This is how a consumer that argues with étale coverings of algebraic spaces meets a hypothesis
stated for the covering sieves of the site: the cocontinuity of the comparison functor below is
one such consumer, and the sheaf property of the rule of lifts of [Stacks Project, Tag 061A] is
another. -/
alias SpacesEtale.exists_covering_refining_sieve := comparison_exists_covering_refining_sieve

/-- **Stacks 03G1.** The comparison functor is cocontinuous. -/
private theorem comparisonFunctor_isCocontinuous :
    Functor.IsCocontinuous (comparisonFunctor B S hS X)
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) := by
  constructor
  intro U R hR
  obtain ⟨E, hE, hER⟩ := comparison_exists_covering_refining_sieve B S hS X hR
  obtain ⟨⟨T₁, E₁⟩, hEtale₁, hbase, hComb⟩ := exists_chosen_etaleCovering B
    ⟨U.1.left.left, ⟨E.I₀, fun i => (comparisonAtlasSource B S hS X (E.X i)).left,
      fun i => (comparisonAtlasRefinementMap B S hS X U E i).left⟩⟩
    (comparison_atlas_family_isEtaleCovering B S hS X U E hE)
  obtain rfl : U.1.left.left = T₁ := hbase
  set Esource := comparisonSourceFamilyOfEtaleCover B S hS X U E₁ hEtale₁
  have hsourceGenerate : Sieve.generate Esource.presieve₀ ∈
      SmallEtale.topology B S hS X.1 U :=
    Precoverage.generate_mem_toGrothendieck
      ⟨Esource, rfl, comparisonSourceFamilyOfEtaleCover_isCovering B S hS X U E₁ hEtale₁⟩
  refine (SmallEtale.topology B S hS X.1).superset_covering
    ((Sieve.generate_le_iff _ _).2 ?_) hsourceGenerate
  rw [Presieve.ofArrows_le_iff]
  intro i
  obtain ⟨α, hX, hf⟩ := hComb.symm.1
  -- The index `k` of the member of the original family that `i` refines, and the data of the
  -- refinement.
  set k := α i
  set m := comparisonAtlasRefinementMap B S hS X U E k
  have hXi : E₁.X i = (comparisonAtlasSource B S hS X (E.X k)).left := hX i
  have hfi : E₁.f i = eqToHom hXi ≫ m.left := hf i
  set atlas := comparisonAtlasMap B S hS X (E.X k)
  set arrow := ((SpacesEtale.toSpaces B S hS X).map (E.f k)).hom
  have hmmap : yoneda.map m = atlas ≫ arrow :=
    comparisonAtlasRefinementMap_map B S hS X U E k
  -- The source object of the family, and the comparison of the two refinements of `U`.
  set V : BigFppfOver B S hS := Over.mk (E₁.f i ≫ U.1.left.hom)
  set vmap : V ⟶ U.1.left := Over.homMk (E₁.f i)
  set f : V ⟶ comparisonAtlasSource B S hS X (E.X k) :=
    Over.homMk (eqToHom hXi) (by
      calc eqToHom hXi ≫ (comparisonAtlasSource B S hS X (E.X k)).hom
            = eqToHom hXi ≫ m.left ≫ U.1.left.hom := by rw [← Over.w m]
        _ = V.hom := congrArg (fun q => q ≫ U.1.left.hom) hfi.symm)
  have hfm : f ≫ m = vmap := Over.OverMorphism.ext hfi.symm
  have hyon : yoneda.map f ≫ yoneda.map m = yoneda.map vmap :=
    (yoneda.map_comp f m).symm.trans
      (congrArg (fun q : V ⟶ U.1.left => yoneda.map q) hfm)
  -- The structure morphism of the image of the member of the original family.
  have hArrowOver : arrow ≫ U.1.hom =
      (((SpacesEtale.inclusion B S hS X).obj (E.X k)).hom.hom) :=
    comparison_toSpaces_map_comp_hom B S hS X (E.f k)
  have hatlasBase : atlas ≫ (((SpacesEtale.inclusion B S hS X).obj (E.X k)).hom.hom) =
      yoneda.map m ≫ U.1.hom := by
    rw [← hArrowOver, hmmap]
    exact (Category.assoc atlas arrow U.1.hom).symm
  -- The factorization of the image of `Esource.f i` through `E.f k`.
  set g : (comparisonFunctor B S hS X).obj (Esource.X i) ⟶ E.X k :=
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (yoneda.map f ≫ atlas)) (by
      refine ObjectProperty.hom_ext _ ?_
      calc (yoneda.map f ≫ atlas) ≫
              (((SpacesEtale.inclusion B S hS X).obj (E.X k)).hom.hom)
            = yoneda.map f ≫ (yoneda.map m ≫ U.1.hom) := by rw [Category.assoc, hatlasBase]
        _ = (yoneda.map f ≫ yoneda.map m) ≫ U.1.hom := (Category.assoc _ _ _).symm
        _ = yoneda.map vmap ≫ U.1.hom :=
              congrArg (fun q => q ≫ U.1.hom) hyon))
  have hfactor : g ≫ E.f k = (comparisonFunctor B S hS X).map (Esource.f i) := by
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_))
    show (yoneda.map f ≫ atlas) ≫ arrow = yoneda.map vmap
    rw [Category.assoc, ← hmmap]
    exact hyon
  show R.arrows ((comparisonFunctor B S hS X).map (Esource.f i))
  rw [← hfactor]
  exact R.downward_closed (hER _ _ ⟨k⟩) g

/-- **Every algebraic space has an étale scheme chart which is surjective on points.**  A
chosen atlas of the space is such a chart, surjectivity on points being Stacks 03H5.

This is Stacks 03H7 read at the space itself, and it is weaker than Stacks 03H6, which also
makes the chart affine but needs quasi-compactness. -/
theorem exists_isSurjective_chart :
    ∃ V : SmallEtale B S hS X.1, IsSurjective B S hS V.1.hom := by
  obtain ⟨T, a, hsurj, hetale⟩ := X.property.exists_atlas
  exact ⟨⟨CostructuredArrow.mk a, hetale⟩,
    (surjective_iff_surjective_pointsMap B S hS X.1 X.property T a).1 hsurj⟩

/-! ### Cover density -/

/-- **Stacks 03H7.** Every algebraic space étale over `X` is covered, in the spaces-étale site
of `X`, by a single étale *scheme* chart of `X`, namely a chosen atlas of it composed with its
structure morphism. -/
@[stacks 03H7 "a scheme chart covering the étale space"]
theorem exists_scheme_chart_cover (U : SpacesEtale B S hS X) :
    ∃ (V : SmallEtale B S hS X.1) (f : (comparisonFunctor B S hS X).obj V ⟶ U),
      Sieve.generate (Presieve.singleton f) ∈ SpacesEtale.topology B S hS X U := by
  set Usp := (SpacesEtale.toSpaces B S hS X).obj U
  obtain ⟨T, a, hasurj, haetale⟩ := Usp.property.exists_atlas
  have hbEtale : IsEtale B S hS
      (a ≫ (((SpacesEtale.inclusion B S hS X).obj U).hom.hom)) :=
    isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS haetale) U.property
  set V : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (a ≫ (((SpacesEtale.inclusion B S hS X).obj U).hom.hom)),
      presheaf_etale_of_isEtale B S hS hbEtale⟩
  set f : (comparisonFunctor B S hS X).obj V ⟶ U :=
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk a) rfl)
  refine ⟨V, f, ?_⟩
  have hE : SpacesEtale.IsCovering B S hS X ⟨U, PreZeroHypercover.singleton f⟩ := by
    intro x
    obtain ⟨y, hy⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS Usp.1 Usp.property
      T a).mp hasurj x
    exact ⟨default, y, hy⟩
  rw [show Presieve.singleton f = (PreZeroHypercover.singleton f).presieve₀ from
    (PreZeroHypercover.presieve₀_singleton f).symm]
  exact Precoverage.generate_mem_toGrothendieck ⟨_, rfl, hE⟩

/-- **Stacks 03G1.** The comparison functor is cover dense. -/
private theorem comparisonFunctor_isCoverDense :
    (comparisonFunctor B S hS X).IsCoverDense (SpacesEtale.topology B S hS X) := by
  apply Functor.isCoverDense_of_generate_singleton_functor_π_mem
  exact exists_scheme_chart_cover B S hS X

/-! ### The dense-subsite property -/

/-- The image of a covering family of the small étale site is a covering family of the
spaces-étale site. -/
private theorem comparisonFunctor_mapsCoveringFamily (U : SmallEtale B S hS X.1)
    (E : PreZeroHypercover.{u + 1} U) (hE : SmallEtale.IsCovering B S hS X.1 ⟨U, E⟩) :
    SpacesEtale.IsCovering B S hS X
      ⟨(comparisonFunctor B S hS X).obj U,
        ⟨E.I₀, fun i => (comparisonFunctor B S hS X).obj (E.X i),
          fun i => (comparisonFunctor B S hS X).map (E.f i)⟩⟩ := by
  have hmem : Presieve.ofArrows
      (fun i => ((SmallEtale.toSchemes B S hS X.1).obj (E.X i)).1)
      (fun i => B.inclusion.map ((SmallEtale.toSchemes B S hS X.1).map (E.f i))) ∈
      Scheme.precoverage (@Etale.{u} : MorphismProperty Scheme.{u})
        (B.inclusion.obj ((SmallEtale.toSchemes B S hS X.1).obj U)) := hE.2
  rw [Scheme.ofArrows_mem_precoverage_iff
    (P := (@Etale.{u} : MorphismProperty Scheme.{u}))] at hmem
  intro x
  obtain ⟨i, y, hy⟩ := hmem.1 (pointsToScheme B S hS U.1.left x)
  obtain ⟨w, hw⟩ := surjective_pointsToScheme B S hS
    ((SmallEtale.toOver B S hS X.1).obj (E.X i)) y
  refine ⟨i, w, injective_pointsToScheme B S hS U.1.left ?_⟩
  show pointsToScheme B S hS U.1.left (pointsMap B S hS _
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map (E.f i))) w) = _
  rw [pointsToScheme_pointsMap_yoneda, hw]
  exact hy

/-- The small étale topology of `X` is the topology restricted along the comparison from the
spaces-étale topology.

One inclusion is `AlgebraicGeometry.Space.comparisonFunctor_mapsCoveringFamily`, which says
the small étale precoverage lies below the comap of the spaces-étale precoverage, together
with monotonicity of the generated topology. The other is cocontinuity. -/
private theorem comparisonFunctor_topology_eq_restricted :
    SmallEtale.topology B S hS X.1 =
      (comparisonFunctor B S hS X).restrictedTopology (SpacesEtale.topology B S hS X) := by
  have := comparisonFunctor_full B S hS X
  have := comparisonFunctor_faithful B S hS X
  have := comparisonFunctor_isCoverDense B S hS X
  refine le_antisymm ?_ ?_
  · have hpre : SmallEtale.precoverage B S hS X.1 ≤
        (SpacesEtale.precoverage B S hS X).comap (comparisonFunctor B S hS X) := by
      intro U R hR
      obtain ⟨E, hEq, hE⟩ := (SmallEtale.mem_precoverage_iff
        (B := B) (S := S) (hS := hS) (F := X.1)).mp hR
      rw [Precoverage.mem_comap_iff, hEq, ← PreZeroHypercover.presieve₀_map,
        SpacesEtale.mem_precoverage_iff]
      exact ⟨E.map (comparisonFunctor B S hS X), rfl, by
        simpa [PreZeroHypercover.map] using
          comparisonFunctor_mapsCoveringFamily B S hS X U E hE⟩
    have hcomp : (SpacesEtale.precoverage B S hS X).comap (comparisonFunctor B S hS X) ≤
        (SpacesEtale.topology B S hS X).toPrecoverage.comap
          (comparisonFunctor B S hS X) := fun U R hR =>
      Precoverage.mem_comap_iff.mpr
        ((SpacesEtale.precoverage B S hS X).le_toPrecoverage_toGrothendieck _
          (Precoverage.mem_comap_iff.mp hR))
    exact (Precoverage.toGrothendieck_monotone hpre).trans
      (Precoverage.toGrothendieck_monotone hcomp)
  · intro U R hR
    rw [Functor.mem_restrictedTopology_iff] at hR
    have hlift := (comparisonFunctor_isCocontinuous B S hS X).cover_lift hR
    rwa [Sieve.functorPullback_functorPushforward_eq (comparisonFunctor B S hS X)] at hlift

/-- **Stacks 03G1.** The comparison functor exhibits the small étale site as a dense subsite
of the spaces-étale site. -/
private theorem comparisonFunctor_denseSubsite :
    (comparisonFunctor B S hS X).IsDenseSubsite
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) := by
  have := comparisonFunctor_full B S hS X
  have := comparisonFunctor_faithful B S hS X
  have := comparisonFunctor_isCoverDense B S hS X
  refine { isCoverDense' := comparisonFunctor_isCoverDense B S hS X
           isLocallyFull' := inferInstance
           isLocallyFaithful' := inferInstance
           functorPushforward_mem_iff := ?_ }
  intro U R
  rw [comparisonFunctor_topology_eq_restricted]
  exact (Functor.mem_restrictedTopology_iff (G := comparisonFunctor B S hS X)).symm

/-! ### The equivalence of topoi -/

/-- **Stacks 03G1.** The comparison functor is special cocontinuous in the sense of Stacks
03CG. -/
@[stacks 03G1 "special cocontinuity"]
theorem comparisonFunctor_specialCocontinuous :
    IsSpecialCocontinuous (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)
      (comparisonFunctor B S hS X) :=
  ⟨comparisonFunctor_isCocontinuous B S hS X, comparisonFunctor_denseSubsite B S hS X⟩

/-- The comparison is a dense inclusion of sites. -/
instance comparisonFunctor_isDenseSubsite :
    (comparisonFunctor B S hS X).IsDenseSubsite
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) :=
  (comparisonFunctor_specialCocontinuous B S hS X).2

/-- The comparison is continuous as a functor of sites. -/
instance comparisonFunctor_isContinuous :
    (comparisonFunctor B S hS X).IsContinuous
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) := inferInstance

/-- **Stacks 03G1.** Restriction along the comparison functor is an equivalence of sheaf
categories, for sheaves valued in any category with the limits needed to define the
restriction. -/
@[stacks 03G1 "equivalence of topoi"]
instance comparisonFunctor_sheafEquivalence (A : Type w) [Category.{w'} A]
    [∀ Y, HasLimitsOfShape (StructuredArrow Y (comparisonFunctor B S hS X).op) A] :
    ((comparisonFunctor B S hS X).sheafPushforwardContinuous A
      (SmallEtale.topology B S hS X.1)
      (SpacesEtale.topology B S hS X)).IsEquivalence := inferInstance

end AlgebraicGeometry.Space

end
