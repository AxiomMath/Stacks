module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.InfiniteProductRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional

/-!
# The algebraic space of the infinite product example

Let `k` be a ring, `S = Spec k`, `U = Spec (∏_{n ∈ ℕ} k)` and let

  `R = U ⨿ ∐_{(n, m) ∈ ℕ², n ≠ m} S ⇉ U`

be the étale equivalence relation of
`StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.InfiniteProductRelation`. Stacks
02Z8 concludes from Stacks 02WW that the quotient `X = U/R` is an algebraic space over `S`.
That is what is proved here, along with the presentation of `X` by `(U, R)`.

## Main definitions

* `AlgebraicGeometry.Space.InfiniteProduct.spaceChart` and
  `AlgebraicGeometry.Space.InfiniteProduct.relationChart`: `U` and `R` as objects of a big
  fppf site over `S`, and
  `AlgebraicGeometry.Space.InfiniteProduct.chartTarget`,
  `AlgebraicGeometry.Space.InfiniteProduct.chartSource`: the two projections as morphisms of
  that site.
* `AlgebraicGeometry.Space.InfiniteProduct.quotient`: the algebraic space `X = U/R`.
* `AlgebraicGeometry.Space.InfiniteProduct.baseChart`,
  `AlgebraicGeometry.Space.InfiniteProduct.chartCoordinate` and
  `AlgebraicGeometry.Space.InfiniteProduct.chartSummand`: the base `S`, the coordinate
  morphisms `S ⟶ U` and the summand inclusions `S ⟶ R`, in the site.
* `AlgebraicGeometry.Space.InfiniteProduct.coordinatePoint`: the point `x₀` of `X`, the
  common image of all the coordinate points of `U`.

## Main results

* `AlgebraicGeometry.Space.InfiniteProduct.isEtaleEquivalenceRelation_chart`: the
  pre-relation of the site attached to the two projections is an étale equivalence relation.
* `AlgebraicGeometry.Space.InfiniteProduct.isAlgebraicSpace_quotient`: `X` is an algebraic
  space over `S`.
* `AlgebraicGeometry.Space.InfiniteProduct.quotientMap_surjective` and
  `AlgebraicGeometry.Space.InfiniteProduct.quotientMap_etale`: the quotient map `U ⟶ X` is
  surjective and étale after every representable base change.
* `AlgebraicGeometry.Space.InfiniteProduct.presentation`: `(U, R, U ⟶ X)` is a presentation
  of `X`.
* `AlgebraicGeometry.Space.InfiniteProduct.quotientMap_isPullback`: `R` is the fibre product
  `U ×_X U`, so the points of `U` identified in `X` are exactly the related ones.
* `AlgebraicGeometry.Space.InfiniteProduct.quotientMap_comp_chartCoordinate_eq`: all the
  coordinate points of `U` have the same image `x₀` in `X`, and
  `AlgebraicGeometry.Space.InfiniteProduct.isTerminal_baseChart`: `S` is terminal in the
  site, so that image is a section of the structure morphism of `X`.

## Implementation notes

The site is arbitrary: `B` is any big fppf site containing `S`, `U` and `R`. A site
containing `U` contains `R` as well only after a size computation, which is not carried out;
containment of `R` is therefore a hypothesis.

`AlgebraicGeometry.Space.relation` of the two charted projections is literally the
pre-relation of the previous file — the comparison
`AlgebraicGeometry.Space.InfiniteProduct.relation_eq_preRelation` is proved by the
universal property of the product, the two components agreeing because
`CategoryTheory.Over.post B.inclusion` is fully faithful and the charted projections are by
definition its preimages.

The quotient and its properties come from the unconditional form of Stacks 02WW in
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional`, whose only
remaining hypothesis is the choice of universe in which the quotient presheaf is sheafified.

## References

* [Stacks Project, Tag 02Z8](https://stacks.math.columbia.edu/tag/02Z8)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.InfiniteProduct

variable (k : Type u) [CommRing k] (B : BigFppfSite.{u}) (hS : B.Contains (base k))
  (hU : B.Contains (space k)) (hR : B.Contains (relation k))

/-- The scheme `U`, as an object of a big fppf site over `S`. -/
noncomputable def spaceChart : BigFppfOver B (base k) hS :=
  BigFppfOver.mk B (base k) hS hU (structureMap k)

/-- The relation scheme `R`, as an object of a big fppf site over `S`. -/
noncomputable def relationChart : BigFppfOver B (base k) hS :=
  BigFppfOver.mk B (base k) hS hR (relationStructure k)

/-- The image of `spaceChart` in the category of schemes over `S` is `spaceOver`. -/
theorem spaceChart_post :
    (Over.post B.inclusion).obj (spaceChart k B hS hU) = spaceOver k := rfl

/-- The image of `relationChart` in the category of schemes over `S` is `relationOver`. -/
theorem relationChart_post :
    (Over.post B.inclusion).obj (relationChart k B hS hR) = relationOver k := rfl

/-- The target projection `R ⟶ U`, as a morphism of the site. -/
noncomputable def chartTarget : relationChart k B hS hR ⟶ spaceChart k B hS hU :=
  (Over.post B.inclusion).preimage (targetOver k)

/-- The source projection `R ⟶ U`, as a morphism of the site. -/
noncomputable def chartSource : relationChart k B hS hR ⟶ spaceChart k B hS hU :=
  (Over.post B.inclusion).preimage (sourceOver k)

/-- The image of `chartTarget` in the category of schemes over `S` is `targetOver`. -/
@[simp]
theorem post_chartTarget :
    (Over.post B.inclusion).map (chartTarget k B hS hU hR) = targetOver k :=
  (Over.post B.inclusion).map_preimage _

/-- The image of `chartSource` in the category of schemes over `S` is `sourceOver`. -/
@[simp]
theorem post_chartSource :
    (Over.post B.inclusion).map (chartSource k B hS hU hR) = sourceOver k :=
  (Over.post B.inclusion).map_preimage _

/-- The pre-relation of the site attached to the two charted projections is the pre-relation
of the example. -/
theorem relation_eq_preRelation :
    Space.relation B (base k) hS (chartSource k B hS hU hR) (chartTarget k B hS hU hR) =
      preRelation k := by
  refine Limits.prod.hom_ext ?_ ?_
  · exact (prod.lift_fst _ _).trans
      ((post_chartTarget ..).trans (preRelation_target k).symm)
  · exact (prod.lift_snd _ _).trans
      ((post_chartSource ..).trans (preRelation_source k).symm)

/-- **Stacks 02Z8.** The two charted projections form an étale equivalence relation on `U` in
the big fppf site over `S`. -/
@[stacks 02Z8 "the charted relation is an étale equivalence relation"]
theorem isEtaleEquivalenceRelation_chart :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (Space.relation B (base k) hS (chartSource k B hS hU hR) (chartTarget k B hS hU hR)) := by
  rw [relation_eq_preRelation]
  exact isEtaleEquivalenceRelation_preRelation k

section Quotient

variable [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)]

/-- **Stacks 02Z8.** The algebraic space `X = U/R` of the example: the quotient sheaf of the
étale equivalence relation `R` on `U` in the big fppf site over `S`. -/
noncomputable abbrev quotient : (BigFppfOver B (base k) hS)ᵒᵖ ⥤ Type u :=
  (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B (base k) hS) (Over.post B.inclusion)
    (Space.relation B (base k) hS (chartSource k B hS hU hR)
      (chartTarget k B hS hU hR))).obj

/-- **Stacks 02Z8.** The quotient `X = U/R` is an algebraic space over `S`. This is Stacks
02WW applied to the étale equivalence relation of the example. -/
@[stacks 02Z8 "the quotient X = U/R is an algebraic space"]
theorem isAlgebraicSpace_quotient :
    IsAlgebraicSpace B (base k) hS (quotient k B hS hU hR) :=
  have := isEtaleEquivalenceRelation_chart k B hS hU hR
  Space.isAlgebraicSpace_quotient_unconditional B (base k) hS (chartSource k B hS hU hR)
    (chartTarget k B hS hU hR)

/-- **Stacks 02Z8.** The quotient map `U ⟶ X` is surjective after every representable base
change: the morphism `|U| → |X|` of the source is surjective. -/
@[stacks 02Z8 "the quotient map U ⟶ X is surjective"]
theorem quotientMap_surjective :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (base k) hS)))
      (Space.quotientMap B (base k) hS (chartSource k B hS hU hR)
        (chartTarget k B hS hU hR)) :=
  have := isEtaleEquivalenceRelation_chart k B hS hU hR
  Space.quotientMap_surjective_unconditional B (base k) hS (chartSource k B hS hU hR)
    (chartTarget k B hS hU hR)

/-- **Stacks 02Z8.** The quotient map `U ⟶ X` is étale after every representable base
change. -/
@[stacks 02Z8 "the quotient map U ⟶ X is étale"]
theorem quotientMap_etale :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (base k) hS)))
      (Space.quotientMap B (base k) hS (chartSource k B hS hU hR)
        (chartTarget k B hS hU hR)) :=
  have := isEtaleEquivalenceRelation_chart k B hS hU hR
  Space.quotientMap_etale_unconditional B (base k) hS (chartSource k B hS hU hR)
    (chartTarget k B hS hU hR)

/-- **Stacks 02Z8.** The triple `(U, R, U ⟶ X)` is a presentation of the algebraic space
`X = U/R`. -/
@[stacks 02Z8 "the presentation of X by U and R"]
noncomputable def presentation :
    Space.Presentation B (base k) hS (quotient k B hS hU hR)
      (isAlgebraicSpace_quotient k B hS hU hR) :=
  have := isEtaleEquivalenceRelation_chart k B hS hU hR
  Space.quotientPresentation_unconditional B (base k) hS (chartSource k B hS hU hR)
    (chartTarget k B hS hU hR)

/-- **Stacks 02Z8.** The relation `R` is the fibre product `U ×_X U`: the points of `U` that
become equal in `X` are exactly the ones related by `R`. Together with
`AlgebraicGeometry.Space.InfiniteProduct.quotientMap_comp_chartCoordinate_eq` this is the
assertion of the source that the coordinate points of `U` all map to one point of `X` and
that no other point of `U` gets identified with anything. -/
@[stacks 02Z8 "exactly the related points of U are identified in X"]
theorem quotientMap_isPullback :
    IsPullback (yoneda.map (chartTarget k B hS hU hR))
      (yoneda.map (chartSource k B hS hU hR))
      (Space.quotientMap B (base k) hS (chartSource k B hS hU hR)
        (chartTarget k B hS hU hR))
      (Space.quotientMap B (base k) hS (chartSource k B hS hU hR)
        (chartTarget k B hS hU hR)) :=
  have := isEtaleEquivalenceRelation_chart k B hS hU hR
  Space.quotientMap_isPullback B (base k) hS (chartSource k B hS hU hR)
    (chartTarget k B hS hU hR)

end Quotient

/-! ### The coordinate point of the quotient -/

/-- The base `S`, as an object of the big fppf site over itself. -/
noncomputable def baseChart : BigFppfOver B (base k) hS :=
  BigFppfOver.mk B (base k) hS hS (𝟙 (base k))

/-- The image of `baseChart` in the category of schemes over `S` is `S` over itself. -/
theorem baseChart_post :
    (Over.post B.inclusion).obj (baseChart k B hS) = Over.mk (𝟙 (base k)) := rfl

/-- `S` is a terminal object of the big fppf site over `S`, so a morphism out of its functor
of points is a section of the structure morphism. -/
noncomputable def isTerminal_baseChart : IsTerminal (baseChart k B hS) :=
  Over.mkIdTerminal

/-- The `n`-th coordinate morphism `S ⟶ U`, as a morphism of schemes over `S`. -/
noncomputable def coordinateOver (n : ℕ) : Over.mk (𝟙 (base k)) ⟶ spaceOver k :=
  Over.homMk (coordinate k n) (coordinate_comp_structureMap k n)

/-- The inclusion of the summand of `R` indexed by `p = (n, m)`, as a morphism of schemes
over `S`. -/
noncomputable def summandOver (p : OffDiagonal) : Over.mk (𝟙 (base k)) ⟶ relationOver k :=
  Over.homMk (Sigma.ι (relationComponent k) (.inr p)) (ι_inr_relationStructure k p)

/-- The `n`-th coordinate morphism `S ⟶ U`, as a morphism of the site. -/
noncomputable def chartCoordinate (n : ℕ) : baseChart k B hS ⟶ spaceChart k B hS hU :=
  (Over.post B.inclusion).preimage (coordinateOver k n)

/-- The inclusion of the summand of `R` indexed by `p = (n, m)`, as a morphism of the
site. -/
noncomputable def chartSummand (p : OffDiagonal) :
    baseChart k B hS ⟶ relationChart k B hS hR :=
  (Over.post B.inclusion).preimage (summandOver k p)

/-- The image of `chartCoordinate` in the category of schemes over `S` is `coordinateOver`. -/
@[simp]
theorem post_chartCoordinate (n : ℕ) :
    (Over.post B.inclusion).map (chartCoordinate k B hS hU n) = coordinateOver k n :=
  (Over.post B.inclusion).map_preimage _

/-- The image of `chartSummand` in the category of schemes over `S` is `summandOver`. -/
@[simp]
theorem post_chartSummand (p : OffDiagonal) :
    (Over.post B.inclusion).map (chartSummand k B hS hR p) = summandOver k p :=
  (Over.post B.inclusion).map_preimage _

/-- A morphism `R ⟶ U` of the site over `e` sending the summand `p` to the `n`-th coordinate. -/
private theorem chartSummand_comp_eq {p n e f}
    (hf : (Over.post B.inclusion).map f = e)
    (h : Sigma.ι (relationComponent k) (.inr p) ≫ e.left = coordinate k n) :
    chartSummand k B hS hR p ≫ f = chartCoordinate k B hS hU n := by
  apply (Over.post B.inclusion).map_injective
  rw [Functor.map_comp, post_chartSummand, post_chartCoordinate, hf]
  exact Over.OverMorphism.ext h

/-- The target projection sends the summand indexed by `(n, m)` to the `n`-th coordinate. -/
theorem chartSummand_comp_chartTarget (p : OffDiagonal) :
    chartSummand k B hS hR p ≫ chartTarget k B hS hU hR =
      chartCoordinate k B hS hU p.1.1 :=
  chartSummand_comp_eq k B hS hU hR (post_chartTarget ..) (ι_inr_relationTarget k p)

/-- The source projection sends the summand indexed by `(n, m)` to the `m`-th coordinate. -/
theorem chartSummand_comp_chartSource (p : OffDiagonal) :
    chartSummand k B hS hR p ≫ chartSource k B hS hU hR =
      chartCoordinate k B hS hU p.1.2 :=
  chartSummand_comp_eq k B hS hU hR (post_chartSource ..) (ι_inr_relationSource k p)

section CoordinatePoint

variable [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)]

/-- **Stacks 02Z8.** All the coordinate points of `U` have the same image in `X`: the
composites of the coordinate morphisms `S ⟶ U` with the quotient map agree. -/
@[stacks 02Z8 "all the coordinate points of U map to one point of X"]
theorem quotientMap_comp_chartCoordinate_eq (n m : ℕ) :
    yoneda.map (chartCoordinate k B hS hU n) ≫
        Space.quotientMap B (base k) hS (chartSource k B hS hU hR)
          (chartTarget k B hS hU hR) =
      yoneda.map (chartCoordinate k B hS hU m) ≫
        Space.quotientMap B (base k) hS (chartSource k B hS hU hR)
          (chartTarget k B hS hU hR) := by
  by_cases hnm : n = m
  · rw [hnm]
  · have hw := (quotientMap_isPullback k B hS hU hR).w
    rw [← chartSummand_comp_chartTarget k B hS hU hR ⟨(n, m), hnm⟩,
      ← chartSummand_comp_chartSource k B hS hU hR ⟨(n, m), hnm⟩]
    simp [hw]

/-- **Stacks 02Z8.** The point `x₀` of `X`: the common image of all the coordinate points of
`U`. It is a section of the structure morphism of `X`, the base `S` being a terminal object
of the site by `AlgebraicGeometry.Space.InfiniteProduct.isTerminal_baseChart`. -/
@[stacks 02Z8 "x₀ is the image of a section S ⟶ X"]
noncomputable def coordinatePoint :
    yoneda.obj (baseChart k B hS) ⟶ quotient k B hS hU hR :=
  yoneda.map (chartCoordinate k B hS hU 0) ≫
    Space.quotientMap B (base k) hS (chartSource k B hS hU hR) (chartTarget k B hS hU hR)

/-- Every coordinate point of `U` maps to `x₀`. -/
theorem quotientMap_comp_chartCoordinate (n : ℕ) :
    yoneda.map (chartCoordinate k B hS hU n) ≫
        Space.quotientMap B (base k) hS (chartSource k B hS hU hR)
          (chartTarget k B hS hU hR) =
      coordinatePoint k B hS hU hR :=
  quotientMap_comp_chartCoordinate_eq k B hS hU hR n 0

end CoordinatePoint

end AlgebraicGeometry.Space.InfiniteProduct

end
