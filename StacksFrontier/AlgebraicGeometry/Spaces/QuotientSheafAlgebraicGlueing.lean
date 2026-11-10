module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleEquivalenceRelationQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafChartFromDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafFppfOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover

/-!
# The quotient of an étale equivalence relation on an arbitrary base

Let `j = (t, s) : R ⟶ U ×_S U` be an étale equivalence relation on an object `U` of the big
fppf site of a scheme `S`. The quotient sheaf `U/R` is an algebraic space over `S` — with no
affineness assumption on `U`.

The affine case is `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_diagDescent`.
The general case follows by glueing: `U` is covered by its affine opens `Uᵢ`, each of which
lies in the site and is étale over `U`, so each restriction `jᵢ` of `j` along `Uᵢ ⟶ U` is an
étale equivalence relation on an affine object and each quotient `Uᵢ/Rᵢ` is an algebraic space.
The induced maps `Uᵢ/Rᵢ ⟶ U/R` are open immersions by Tag 02WU, their coproduct is an
algebraic space by Tag 02WQ, and the map from that coproduct to `U/R` is locally surjective
because the chart `h_U ⟶ U/R` is; so Tag 02WR applies.

A group acting on an object of the site with residue-field-faithful stabilizers has an étale
equivalence relation for its graph, so its quotient is an algebraic space as well.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_relation_of_diagDescent`, which lives
  in `StacksFrontier.AlgebraicGeometry.Spaces.EtaleEquivalenceRelationQuotient`: the quotient sheaf
  of an étale equivalence relation on an arbitrary object of the big fppf site of `S` is an
  algebraic space over `S`.
* `AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotient`: the quotient of an object of the
  big fppf site of `S` by a group action whose stabilizers act faithfully on fixed residue
  fields is an algebraic space over `S`.
* `Stacks.Groupoids.quotientChart_comp_quotientSheafMap` and
  `Stacks.Groupoids.quotientChart_comp_restrictQuotientSheafMap`: the charts of two quotient
  sheaves are compatible with the map induced by a morphism of pre-relations whose map of base
  objects comes from the site.

## Implementation notes

Both results carry one hypothesis beyond the source's, namely effective descent along the
covering sieves of the site at the monomorphisms locally of finite type
(`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve`). It is inherited unchanged
from the affine case, where it is the single remaining input of Tag 0265, and it is the
weakest of the forms in which that input occurs: it is taken at a property below the
monomorphisms, and `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_affineBase`
reduces it further to its affine-base body with no cardinal obligation. The affineness
assumption on `U`, by contrast, is genuinely removed here.

The affine opens of the underlying scheme of `U` lie in the site because an open immersion
does not increase the size of a scheme, and their coproduct does so because the site's cutoff
bounds a coproduct of at most `size U`-many schemes of size at most `size U`. That coproduct,
sliced over `S`, is the object of the site whose cofan witnesses the hypothesis of Tag 02WQ;
the corresponding family of arrows of the site generates a covering sieve because the family
of affine opens is an fppf covering of the underlying scheme and the site's chosen covering
families represent every fppf covering up to combinatorial equivalence.

Local surjectivity of the glueing map is deduced from local surjectivity of the chart by
factoring the coproduct map through it: the two composites agree on each summand by
`Stacks.Groupoids.quotientChart_comp_restrictQuotientSheafMap`.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.Groupoids

variable {S : Scheme.{u}} {C : Type v} [Category.{u} C]

/-- The charts of two quotient sheaves are compatible with the map induced by a morphism of
pre-relations whose map of base objects is `F.map φ` for an arrow `φ` of the site: composing
the chart of the source with the induced map gives the chart of the target restricted along
`φ`. -/
theorem quotientChart_comp_quotientSheafMap (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) {X X' : C} {R R' : Over S}
    (j : PreRelation R (F.obj X')) (j' : PreRelation R' (F.obj X)) (r : R ⟶ R') (φ : X' ⟶ X)
    (hs : r ≫ j'.source = j.source ≫ F.map φ)
    (ht : r ≫ j'.target = j.target ≫ F.map φ) :
    quotientChart J F X' j ≫ (quotientSheafMap J F j j' r (F.map φ) hs ht).hom =
      yoneda.map φ ≫ quotientChart J F X j' := by
  have hbase : yonedaToPoints F X' ≫ F.op.whiskerLeft (yoneda.map (F.map φ)) =
      yoneda.map φ ≫ yonedaToPoints F X := by
    ext T h
    exact (F.map_comp h φ).symm
  rw [quotientChart, quotientChart, Category.assoc, toQuotientSheaf_comp_quotientSheafMap,
    reassoc_of% hbase]

/-- The chart of the quotient sheaf of a pre-relation restricted along an arrow `φ` of the
site, composed with the induced map of quotient sheaves, is the chart of the quotient sheaf of
the original pre-relation restricted along `φ`. -/
theorem quotientChart_comp_restrictQuotientSheafMap (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) {X X' : C} {R : Over S}
    (j : PreRelation R (F.obj X)) (φ : X' ⟶ X) :
    quotientChart J F X' (AlgebraicGeometry.PreRelation.restrict j (F.map φ)) ≫
        (restrictQuotientSheafMap J F j (F.map φ)).hom =
      yoneda.map φ ≫ quotientChart J F X j :=
  quotientChart_comp_quotientSheafMap J F _ j
    (pullback.snd (prod.map (F.map φ) (F.map φ)) j) φ _ _

end Stacks.Groupoids

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

/-- A cofan in a slice category is a colimit as soon as the cofan of underlying objects is. -/
private noncomputable def cofanIsColimitOfLeft {D : Type v} [Category.{w} D] {Z : D}
    {I : Type u} {Y : I → Over Z} (c : Cofan Y)
    (hc : IsColimit (Cofan.mk c.pt.left fun i ↦ (c.inj i).left)) : IsColimit c :=
  isColimitOfReflects (Over.forget Z)
    ((Cofan.isColimitMapCoconeEquiv (Over.forget Z) Y c).symm hc)

set_option synthInstance.maxHeartbeats 200000 in
-- instance synthesis for coproducts of presheaves on the large category `C : Type (u + 1)`
/-- The coproduct of the presheaves represented by a covering family is locally surjective onto
the presheaf represented by the base of the family. -/
public theorem locallySurjective_sigmaDesc_yoneda_map {C : Type (u + 1)} [Category.{u} C]
    [LocallySmall.{u} C] (J : GrothendieckTopology C) {I : Type u} [Small.{u} I] {Y : I → C}
    {T : C} (f : ∀ i, Y i ⟶ T) (hcover : Sieve.ofArrows Y f ∈ J T) :
    Presheaf.IsLocallySurjective J (Sigma.desc fun i ↦ yoneda.map (f i)) := by
  classical
  have : Presheaf.IsLocallySurjective J (Sigma.desc fun i ↦ shrinkYoneda.map (f i)) :=
    (GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_shrinkYoneda_map
      J f).mp hcover
  have : HasColimitsOfShape (Discrete I) (Cᵒᵖ ⥤ Type u) :=
    functorCategoryHasColimitsOfShape
  let e : (∐ fun i ↦ shrinkYoneda.{u}.obj (Y i)) ≅ ∐ fun i ↦ yoneda.obj (Y i) :=
    Sigma.mapIso fun i ↦ shrinkYonedaIsoYoneda.app (Y i)
  have hfac : e.hom ≫ Sigma.desc (fun i ↦ yoneda.map (f i)) =
      Sigma.desc (fun i ↦ shrinkYoneda.map (f i)) ≫ (shrinkYonedaIsoYoneda.app T).hom := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    dsimp only [e]
    simp only [Sigma.ι_mapIso_hom_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    exact (shrinkYonedaIsoYoneda.hom.naturality (f i)).symm
  rw [← Presheaf.comp_isLocallySurjective_iff J e.hom, hfac]
  infer_instance

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  {R U : BigFppfOver B S hS} (s t : R ⟶ U)

/-- **Stacks 02Z2, the algebraic-space property.** The quotient of an object `V` of the big
fppf site of `S` by the action of a group whose stabilizers act faithfully on fixed residue
fields is an algebraic space over `S`.

The graph relation of such an action is an étale equivalence relation
(`AlgebraicGeometry.Space.actionRelation_isEtaleEquivalenceRelation`) on an object of the site
(`AlgebraicGeometry.Space.contains_actionRelationScheme`), so this is
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_relation_of_diagDescent` and carries the
same descent hypothesis. -/
theorem isAlgebraicSpace_actionQuotient {S : Scheme.{u}} (G : Type v) [Group G] [Small.{u} G]
    (B : BigFppfSite.{u}) (hS : B.Contains S) (V : BigFppfOver B S hS)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    IsAlgebraicSpace B S hS (actionQuotient G B hS V a) := by
  let hR : B.Contains (actionRelationScheme (underlyingOver B hS V) G).left :=
    contains_actionRelationScheme G B hS V a ha
  let sa : siteActionRelationScheme G B hS V hR ⟶ V := siteActionRelationSource G B hS V hR
  let ta : siteActionRelationScheme G B hS V hR ⟶ V := siteActionRelationTarget G B hS V hR a
  have hrel : relation B S hS sa ta = actionRelation (underlyingOver B hS V) G a := rfl
  have : IsEtaleEquivalenceRelation (relation B S hS sa ta) := by
    rw [hrel]
    exact actionRelation_isEtaleEquivalenceRelation (underlyingOver B hS V) G a ha
  have := isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B S hS sa ta hdesc
  rwa [hrel] at this

end AlgebraicGeometry.Space

end
