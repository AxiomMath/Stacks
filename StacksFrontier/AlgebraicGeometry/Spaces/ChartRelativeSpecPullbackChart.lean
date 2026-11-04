module

public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.BigSitePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRelationRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation

/-!
# The relative spectrum over a chart is the base change of the relative spectrum

Let `X` be an algebraic space over `S`, let `A` be a quasi-coherent sheaf of commutative
`𝒪_X`-algebras on its small étale site, and let `pr₁, pr₂ : V' ⟶ V₂` be a pair of morphisms of
étale charts of `X` exhibiting `V'` as `V₂ ×_X V₂`, with `V₂ ⟶ X` moreover surjective.
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecQuotient` builds the relative spectrum
`ν : X' = \underline{Spec}_X(A) ⟶ X` as the quotient of the étale equivalence relation of the
relative spectra over that pair of charts.  This file proves the cartesian square

`\underline{Spec}_{V₂}(A|_{V₂}) = X' ×_X V₂`,

which says that the relative spectrum of `A` over `X` restricts on the chart to the relative
spectrum over the chart.

## Main results

* `AlgebraicGeometry.Space.isEquivalenceRelation_chartRelation`: the relation of charts
  `V' ⇉ V₂` is an equivalence relation over `S`.
* `AlgebraicGeometry.Space.exists_iso_chartQuotientSheaf`: a surjective étale chart presents `X`
  as the quotient sheaf of its own relation, `V₂/V' ≅ X`.
* `AlgebraicGeometry.Space.isPullback_chartRelativeSpecQuotientHom`: **the cartesian square.**
  The relative spectrum over the chart is the fibre product of `ν : X' ⟶ X` and the chart.

## Implementation notes

**The square is Stacks 07S3 composed with an identification of the base.**  Stacks 07S3,
`Stacks.Groupoids.isPullback_toQuotientSheaf_of_subcanonical`, says that a morphism of
equivalence relations whose square on source maps is cartesian induces a cartesian square on
quotient sheaves.  Here the morphism of relations is the pair of structure morphisms
`\underline{Spec}_{V'}(A|_{V'}) ⟶ V'` and `\underline{Spec}_{V₂}(A|_{V₂}) ⟶ V₂`, whose
cartesianness over each projection of charts is
`AlgebraicGeometry.Space.isPullback_chartRelativeSpecSiteMap`.  What 07S3 delivers is the square
over the quotient `V₂/V'` of the relation of *charts*, so it is composed with the identification
`V₂/V' ≅ X` of `AlgebraicGeometry.Space.exists_iso_chartQuotientSheaf`.

**Both of the pieces that identification was recorded as owing were already in the library**,
under other names and in the right generality, and no new quotient-sheaf theory is developed
here.  The equivalence-relation condition on the relation of charts is
`AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback`, Stacks 0262 part (1), applied to
the chart as the morphism whose kernel pair the relation is — and its hypothesis is exactly the
`hsq` already carried by the construction of the quotient.  The identification of the quotient
sheaf with `X` is `Stacks.Groupoids.exists_iso_quotientSheaf_of_descent` fed by
`AlgebraicGeometry.existsUnique_desc_of_surjective_etale_atlas`, Stacks 0262 part (3); both are
stated for the `Stacks.Groupoids.quotientSheaf` of a `Stacks.Groupoids.PreRelation`, which is the
flavour the quotient is built in, so no bridge between two parallel quotient-sheaf developments
is needed.  The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn` recorded both of these as owed; both were
already present.

**Surjectivity of the chart is a genuine hypothesis and is not a weakening.**  The quotient of a
non-surjective chart's relation is the relative spectrum over the image of the chart, not over
`X`; every algebraic space has a surjective étale chart by the atlas clause of
`AlgebraicGeometry.IsAlgebraicSpace`, so nothing is lost.  The étaleness half is not a hypothesis
at all: it is the defining property of an object of the small étale site,
`AlgebraicGeometry.Space.IsEtaleChart`, which is *definitionally* the inverse-image étaleness
condition that clause states.

**No `stacks` attribute is carried.**  The square is not a numbered statement of the source; it
is the step by which the three clauses of Definition 0822 reduce to their chart-level forms, and
Stacks 07S3 is already registered on
`AlgebraicGeometry.isPullback_toQuotientSheaf_overTopology`.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

/-! ### The two comparisons between represented presheaves and restricted functors of points -/

/-- **The inverse of `AlgebraicGeometry.Space.pointsYonedaIso` is
`Stacks.Groupoids.yonedaToPoints`.**  Both send an arrow of the site to its image under the
presenting functor. -/
theorem pointsYonedaIso_inv_eq_yonedaToPoints {C : Type v} [Category.{u} C] {S : Scheme.{u}}
    (F : C ⥤ Over S) [F.Full] [F.Faithful] (U : C) :
    (pointsYonedaIso F U).inv = Stacks.Groupoids.yonedaToPoints F U := by
  ext T h
  rfl

/-- `AlgebraicGeometry.Space.pointsYonedaIso` cancels `Stacks.Groupoids.yonedaToPoints`. -/
theorem pointsYonedaIso_hom_comp_yonedaToPoints {C : Type v} [Category.{u} C] {S : Scheme.{u}}
    (F : C ⥤ Over S) [F.Full] [F.Faithful] (U : C) :
    (pointsYonedaIso F U).hom ≫ Stacks.Groupoids.yonedaToPoints F U =
      𝟙 (Stacks.Groupoids.points F (F.obj U)) := by
  rw [← pointsYonedaIso_inv_eq_yonedaToPoints, Iso.hom_inv_id]

/-- **A morphism out of a quotient sheaf is determined on the restricted functor of points by
its restriction to the represented presheaf.**  This is the chart of the quotient sheaf read
through `AlgebraicGeometry.Space.pointsYonedaIso`. -/
theorem toQuotientSheaf_comp_of_quotientChart_comp {C : Type v} [Category.{u} C]
    {S : Scheme.{u}} (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S)
    [F.Full] [F.Faithful] (U : C) {R : Over S} (j : Stacks.Groupoids.PreRelation R (F.obj U))
    {G : Cᵒᵖ ⥤ Type u} (m : (Stacks.Groupoids.quotientSheaf J F j).obj ⟶ G)
    (k : yoneda.obj U ⟶ G) (h : Stacks.Groupoids.quotientChart J F U j ≫ m = k) :
    Stacks.Groupoids.toQuotientSheaf J F j ≫ m = (pointsYonedaIso F U).hom ≫ k :=
  calc Stacks.Groupoids.toQuotientSheaf J F j ≫ m
      = ((pointsYonedaIso F U).hom ≫ Stacks.Groupoids.yonedaToPoints F U) ≫
          (Stacks.Groupoids.toQuotientSheaf J F j ≫ m) := by
        rw [pointsYonedaIso_hom_comp_yonedaToPoints, Category.id_comp]
    _ = (pointsYonedaIso F U).hom ≫
          (Stacks.Groupoids.yonedaToPoints F U ≫ Stacks.Groupoids.toQuotientSheaf J F j) ≫ m := by
        simp only [Category.assoc]
    _ = (pointsYonedaIso F U).hom ≫ Stacks.Groupoids.quotientChart J F U j ≫ m := rfl
    _ = (pointsYonedaIso F U).hom ≫ k := by rw [h]

/-! ### Fibre products in the big fppf category over `S` -/

/-- **Postcomposition with the inclusion of a big fppf site, from the big fppf category over `S`
to the schemes over `S`, preserves fibre products.**  Its composite with the forgetful functor to
schemes is `AlgebraicGeometry.BigFppfOver.toScheme`, which preserves them, and the forgetful
functor of a slice reflects them. -/
instance preservesLimitsOfShape_walkingCospan_bigFppfOverPost (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    PreservesLimitsOfShape WalkingCospan (Over.post (X := B.obj hS) B.inclusion) := by
  have : PreservesLimitsOfShape WalkingCospan
      (Over.post (X := B.obj hS) B.inclusion ⋙ Over.forget S) :=
    show PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) from
      preservesLimitsOfShape_walkingCospan_toScheme B S hS
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)

/-! ### The relation of charts -/

section ChartRelation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)

include hsq in
/-- **The relation of étale charts `V' ⇉ V₂` exhibiting `V'` as `V₂ ×_X V₂` is an equivalence
relation over `S`.**  It is the kernel pair of the chart `V₂ ⟶ X`, so this is Stacks 0262
part (1), `AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback`. -/
theorem isEquivalenceRelation_chartRelation :
    IsEquivalenceRelation
        (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
          ((SmallEtale.toOver B S hS X.1).map pr₁)).target
        (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
          ((SmallEtale.toOver B S hS X.1).map pr₁)).source := by
  rw [show (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
        ((SmallEtale.toOver B S hS X.1).map pr₁)).source =
      (Over.post (X := B.obj hS) B.inclusion).map
        ((SmallEtale.toOver B S hS X.1).map pr₂) from prod.lift_snd _ _,
    show (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
        ((SmallEtale.toOver B S hS X.1).map pr₁)).target =
      (Over.post (X := B.obj hS) B.inclusion).map
        ((SmallEtale.toOver B S hS X.1).map pr₁) from prod.lift_fst _ _]
  exact isEquivalenceRelation_of_isPullback B S hS V₂.obj.hom
    ((SmallEtale.toOver B S hS X.1).map pr₁) ((SmallEtale.toOver B S hS X.1).map pr₂) hsq

variable (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom)

include hsq hsurj in
/-- **A surjective étale chart presents `X` as the quotient sheaf of its own relation**:
`V₂/V' ≅ X`, by an isomorphism carrying the chart to the chart of the quotient sheaf.

Both presheaves are the coequalizer of the same pair of maps: for `X` that is Stacks 0262
part (3), `AlgebraicGeometry.existsUnique_desc_of_surjective_etale_atlas`, and for the quotient
sheaf it is its universal property, which is how
`Stacks.Groupoids.exists_iso_quotientSheaf_of_descent` compares the two. -/
theorem exists_iso_chartQuotientSheaf :
    ∃ e : X.1 ≅ (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion)
        (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
          ((SmallEtale.toOver B S hS X.1).map pr₁))).obj,
      V₂.obj.hom ≫ e.hom = Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) ((SmallEtale.toOver B S hS X.1).obj V₂)
        (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
          ((SmallEtale.toOver B S hS X.1).map pr₁)) :=
  Stacks.Groupoids.exists_iso_quotientSheaf_of_descent (BigFppfOver.topology B S hS)
    (Over.post (X := B.obj hS) B.inclusion) ((SmallEtale.toOver B S hS X.1).map pr₂)
    ((SmallEtale.toOver B S hS X.1).map pr₁) (prod.lift_snd _ _) (prod.lift_fst _ _)
    X.property.isSheaf V₂.obj.hom hsq.w.symm
    (fun A k hk => existsUnique_desc_of_surjective_etale_atlas B S hS X.property.isSheaf
      V₂.obj.hom hsq.flip hsurj V₂.property A.property k hk)

end ChartRelation

/-! ### The morphism of relations given by the structure morphisms of the relative spectra -/

section MorphismOfRelations

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV₂ : B.Contains (chartRelativeSpec B S hS X A hA V₂))

/-- The structure morphisms of the relative spectra over `V'` and over `V₂` commute with the
source maps of the two relations: the compatibility `hs` that Stacks 07S3 consumes. -/
theorem post_chartRelativeSpecSiteToChart_comp_source :
    (Over.post (X := B.obj hS) B.inclusion).map
          (chartRelativeSpecSiteToChart B S hS X A hA V' hV') ≫
        (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
          ((SmallEtale.toOver B S hS X.1).map pr₁)).source =
      (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
          (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)).source ≫
        (Over.post (X := B.obj hS) B.inclusion).map
          (chartRelativeSpecSiteToChart B S hS X A hA V₂ hV₂) := by
  rw [show (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
        ((SmallEtale.toOver B S hS X.1).map pr₁)).source =
      (Over.post (X := B.obj hS) B.inclusion).map
        ((SmallEtale.toOver B S hS X.1).map pr₂) from prod.lift_snd _ _,
    show (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
        (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)).source =
      (Over.post (X := B.obj hS) B.inclusion).map
        (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂) from prod.lift_snd _ _,
    ← Functor.map_comp, ← Functor.map_comp,
    (isPullback_chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂).w]

/-- The structure morphisms of the relative spectra over `V'` and over `V₂` commute with the
target maps of the two relations: the compatibility `ht` that Stacks 07S3 consumes. -/
theorem post_chartRelativeSpecSiteToChart_comp_target :
    (Over.post (X := B.obj hS) B.inclusion).map
          (chartRelativeSpecSiteToChart B S hS X A hA V' hV') ≫
        (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
          ((SmallEtale.toOver B S hS X.1).map pr₁)).target =
      (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
          (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)).target ≫
        (Over.post (X := B.obj hS) B.inclusion).map
          (chartRelativeSpecSiteToChart B S hS X A hA V₂ hV₂) := by
  rw [show (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
        ((SmallEtale.toOver B S hS X.1).map pr₁)).target =
      (Over.post (X := B.obj hS) B.inclusion).map
        ((SmallEtale.toOver B S hS X.1).map pr₁) from prod.lift_fst _ _,
    show (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
        (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)).target =
      (Over.post (X := B.obj hS) B.inclusion).map
        (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂) from prod.lift_fst _ _,
    ← Functor.map_comp, ← Functor.map_comp,
    (isPullback_chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂).w]

/-- The square of `AlgebraicGeometry.Space.isPullback_chartRelativeSpecSiteMap` at the second
projection, read in the schemes over `S`: the cartesianness hypothesis `hcart` of Stacks
07S3. -/
theorem isPullback_post_chartRelativeSpecSiteToChart :
    IsPullback
      ((Over.post (X := B.obj hS) B.inclusion).map
        (chartRelativeSpecSiteToChart B S hS X A hA V' hV'))
      (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
        (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)).source
      (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
        ((SmallEtale.toOver B S hS X.1).map pr₁)).source
      ((Over.post (X := B.obj hS) B.inclusion).map
        (chartRelativeSpecSiteToChart B S hS X A hA V₂ hV₂)) := by
  rw [show (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
        (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)).source =
      (Over.post (X := B.obj hS) B.inclusion).map
        (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂) from prod.lift_snd _ _,
    show (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
        ((SmallEtale.toOver B S hS X.1).map pr₁)).source =
      (Over.post (X := B.obj hS) B.inclusion).map
        ((SmallEtale.toOver B S hS X.1).map pr₂) from prod.lift_snd _ _]
  exact ((isPullback_chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂).flip).map
    (Over.post (X := B.obj hS) B.inclusion)

end MorphismOfRelations

/-! ### The cartesian square -/

section Square

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom)
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV₂ : B.Contains (chartRelativeSpec B S hS X A hA V₂))
    (hV'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback pr₁ pr₂)))

include hsq hsurj hV'' in
/-- **The relative spectrum of `A` over an étale chart of `X` is the fibre product of the
relative spectrum over `X` and the chart**:

`\underline{Spec}_{V₂}(A|_{V₂}) = \underline{Spec}_X(A) ×_X V₂`.

This is Stacks 07S3 at the morphism of equivalence relations given by the structure morphisms of
the relative spectra over `V'` and over `V₂` — cartesian over each projection of charts by
`AlgebraicGeometry.Space.isPullback_chartRelativeSpecSiteMap` — composed with the identification
`V₂/V' ≅ X` of `AlgebraicGeometry.Space.exists_iso_chartQuotientSheaf`. -/
theorem isPullback_chartRelativeSpecQuotientHom :
    IsPullback
      (Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion)
        (chartRelativeSpecSite B S hS X A hA V₂ hV₂)
        (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
          (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)))
      (yoneda.map (chartRelativeSpecSiteToChart B S hS X A hA V₂ hV₂))
      (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').hom
      V₂.obj.hom := by
  have := isEtaleEquivalenceRelation_chartRelativeSpecSiteMap_of_isPullback B S hS X A hA
    pr₁ pr₂ hsq hV' hV₂ hV''
  have := isEquivalenceRelation_chartRelation B S hS X pr₁ pr₂ hsq
  obtain ⟨e, he⟩ := exists_iso_chartQuotientSheaf B S hS X pr₁ pr₂ hsq hsurj
  -- the identification of the base, read on the represented presheaf and on the points
  have hbase : Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) ((SmallEtale.toOver B S hS X.1).obj V₂)
        (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
          ((SmallEtale.toOver B S hS X.1).map pr₁)) ≫ e.inv = V₂.obj.hom := by
    rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have htqs := toQuotientSheaf_comp_of_quotientChart_comp (BigFppfOver.topology B S hS)
    (Over.post (X := B.obj hS) B.inclusion) ((SmallEtale.toOver B S hS X.1).obj V₂)
    (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
      ((SmallEtale.toOver B S hS X.1).map pr₁)) e.inv V₂.obj.hom hbase
  -- Stacks 07S3 at the morphism of relations
  have h07S3 := Stacks.Groupoids.isPullback_toQuotientSheaf_of_subcanonical
    (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
    (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
      (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂))
    (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
      ((SmallEtale.toOver B S hS X.1).map pr₁))
    ((Over.post (X := B.obj hS) B.inclusion).map
      (chartRelativeSpecSiteToChart B S hS X A hA V' hV'))
    ((Over.post (X := B.obj hS) B.inclusion).map
      (chartRelativeSpecSiteToChart B S hS X A hA V₂ hV₂))
    (post_chartRelativeSpecSiteToChart_comp_source B S hS X A hA pr₁ pr₂ hV' hV₂)
    (post_chartRelativeSpecSiteToChart_comp_target B S hS X A hA pr₁ pr₂ hV' hV₂)
    (isPullback_post_chartRelativeSpecSiteToChart B S hS X A hA pr₁ pr₂ hV' hV₂)
  -- the right column of the pasted square is `ν`
  have hnu : (Stacks.Groupoids.quotientSheafMap (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion)
          (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
            (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂))
          (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
            ((SmallEtale.toOver B S hS X.1).map pr₁))
          ((Over.post (X := B.obj hS) B.inclusion).map
            (chartRelativeSpecSiteToChart B S hS X A hA V' hV'))
          ((Over.post (X := B.obj hS) B.inclusion).map
            (chartRelativeSpecSiteToChart B S hS X A hA V₂ hV₂))
          (post_chartRelativeSpecSiteToChart_comp_source B S hS X A hA pr₁ pr₂ hV' hV₂)
          (post_chartRelativeSpecSiteToChart_comp_target B S hS X A hA pr₁ pr₂
            hV' hV₂)).hom ≫ e.inv =
      (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').hom := by
    have key : Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
            (Over.post (X := B.obj hS) B.inclusion)
            (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
              (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)) ≫
          ((Stacks.Groupoids.quotientSheafMap (BigFppfOver.topology B S hS)
              (Over.post (X := B.obj hS) B.inclusion) _ _ _ _
              (post_chartRelativeSpecSiteToChart_comp_source B S hS X A hA pr₁ pr₂ hV' hV₂)
              (post_chartRelativeSpecSiteToChart_comp_target B S hS X A hA pr₁ pr₂
                hV' hV₂)).hom ≫ e.inv) =
        (pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion)
            (chartRelativeSpecSite B S hS X A hA V₂ hV₂)).hom ≫
          chartRelativeSpecSiteToSpace B S hS X A hA V₂ hV₂ := by
      rw [← Category.assoc, Stacks.Groupoids.toQuotientSheaf_comp_quotientSheafMap,
        Category.assoc, htqs, ← Category.assoc,
        whiskerLeft_yoneda_map_comp_pointsYonedaIso_hom, Category.assoc]
      rfl
    exact congrArg (fun m => m.hom) (chartRelativeSpecQuotientHom_unique B S hS X A hA
      pr₁ pr₂ hsq hV' hV₂ hV'' (ObjectProperty.homMk _) key)
  -- the comparison square between represented presheaves and restricted functors of points
  have hleft : IsPullback
      (Stacks.Groupoids.yonedaToPoints (Over.post (X := B.obj hS) B.inclusion)
        (chartRelativeSpecSite B S hS X A hA V₂ hV₂))
      (yoneda.map (chartRelativeSpecSiteToChart B S hS X A hA V₂ hV₂))
      ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft (yoneda.map
        ((Over.post (X := B.obj hS) B.inclusion).map
          (chartRelativeSpecSiteToChart B S hS X A hA V₂ hV₂))))
      (Stacks.Groupoids.yonedaToPoints (Over.post (X := B.obj hS) B.inclusion)
        ((SmallEtale.toOver B S hS X.1).obj V₂)) :=
    IsPullback.of_horiz_isIso ⟨Stacks.Groupoids.yonedaToPoints_naturality
      (Over.post (X := B.obj hS) B.inclusion)
      (chartRelativeSpecSiteToChart B S hS X A hA V₂ hV₂)⟩
  -- the identification of the base, as a cartesian square
  have hbot : IsPullback
      (Stacks.Groupoids.yonedaToPoints (Over.post (X := B.obj hS) B.inclusion)
          ((SmallEtale.toOver B S hS X.1).obj V₂) ≫
        Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion)
          (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
            ((SmallEtale.toOver B S hS X.1).map pr₁)))
      (𝟙 (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V₂))) e.inv V₂.obj.hom :=
    IsPullback.of_vert_isIso ⟨by rw [Category.id_comp]; exact hbase⟩
  have hpaste := (hleft.paste_horiz h07S3).paste_vert hbot
  rw [Category.comp_id, hnu] at hpaste
  exact hpaste

end Square

end AlgebraicGeometry.Space

end
