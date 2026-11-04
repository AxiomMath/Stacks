module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartRingedTopoi
import StacksCore.Tactic.StacksAttribute

/-!
# A small model of the site of polynomial charts

The site `C_{X/Λ}` of Tag 08VA has objects in `Type (u + 1)` and morphisms in `Type u`: a chart
records a `Type u` set of variables and an arbitrary scheme presented as the affine space on
them. This file replaces it by an equivalent genuinely small site at the universe `u + 1`, in
which the presentation is normalized away and the morphisms are shrunk.

## Main definitions

* `AlgebraicGeometry.PolynomialChart.NormalizedChartIndex` and
  `AlgebraicGeometry.PolynomialChart.normalizedChart`: the `Type (u + 1)` of triples
  `(U, σ, U ⟶ Spec Λ[σ])` over `Spec Λ`, and the chart such a triple names.
* `AlgebraicGeometry.PolynomialChart.SmallChartSite`: the small model, the morphisms of the
  normalized charts shrunk to `Type (u + 1)`.
* `AlgebraicGeometry.PolynomialChart.smallChartTopology`: the topology it inherits from the
  chart site.

## Main results

* `AlgebraicGeometry.PolynomialChart.smallChartEquiv`: the small model is equivalent to the
  chart site, and `AlgebraicGeometry.PolynomialChart.essentiallySmall_polynomialChart` records
  the resulting essential smallness at `u + 1`.
* `AlgebraicGeometry.PolynomialChart.smallChartSheafEquiv`: the two sites have equivalent
  categories of sheaves with values in any category, so nothing is lost by working on the small
  model.

## Implementation notes

A chart is isomorphic to one whose affine space is literally `Spec Λ[σ]` and whose presentation
is the identity, because the presentation is itself an isomorphism of schemes; that is
`normalizedIso`, and it is the only mathematical content here. The normalized charts form a full
subcategory whose objects are the triples above, a `Type (u + 1)`, and whose morphisms are those
of the chart site, a `Type u`; `ShrinkHoms` lifts the morphisms to `Type (u + 1)` and makes the
result a `SmallCategory`.

The universe `u + 1` is not lowered to `u`. A chart records an arbitrary `Type u` of variables,
and two charts are isomorphic only when their polynomial algebras are isomorphic over `Λ`, so
the objects of the site range over all cardinalities of `Type u`. The device that bounds them on
the affine polynomial site — the footnote to Tag 08PR, implemented as a cardinality-restricted
full subcategory in `StacksFrontier/Cotangent/PolynomialAlgebraSiteSmall.lean` — does not transfer:
there the bound is part of the source's definition of the site, whereas Tag 08VA's site carries
no bound, and a cardinality-restricted full subcategory of it is not cover-dense. The covering
families of `AlgebraicGeometry.PolynomialChart.topology` consist of strongly cartesian morphisms
over a cover of the open part, and a strongly cartesian morphism of the chart fibration has the
same affine space, hence the same set of variables, as its target; so a chart whose set of
variables exceeds the bound has no covering family inside the restricted subcategory.

## References

* [Stacks Project, Tag 08VA](https://stacks.math.columbia.edu/tag/08VA)
* [Stacks Project, Tag 08V8](https://stacks.math.columbia.edu/tag/08V8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t₂ t₁ u

namespace AlgebraicGeometry.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
    (structureMap : X ⟶ Spec (CommRingCat.of Λ))

/-! ### The normalized charts -/

/-- A triple consisting of an open subscheme `U` of `X`, a set `σ` of variables and an arrow
`U ⟶ Spec Λ[σ]` over `Spec Λ`: the data of a polynomial chart whose affine space is literally an
affine space. -/
abbrev NormalizedChartIndex : Type (u + 1) :=
  Σ U : X.Opens, Σ σ : Type u,
    { f : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of (MvPolynomial σ Λ)) //
        f ≫ Scheme.Spec.map
            (CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial σ Λ)).op =
          U.ι ≫ structureMap }

/-- The polynomial chart named by a triple `(U, σ, U ⟶ Spec Λ[σ])`: its affine space is
`Spec Λ[σ]` and its presentation is the identity. -/
def normalizedChart (i : NormalizedChartIndex Λ X structureMap) :
    PolynomialChart Λ X structureMap where
  openPart := i.1
  variableIndex := i.2.1
  affineSpace := Spec (CommRingCat.of (MvPolynomial i.2.1 Λ))
  affineEquiv := Iso.refl _
  toAffine := i.2.2.1
  comm := by simpa using i.2.2.2

/-- The triple attached to a polynomial chart by composing its arrow to the affine space with
its presentation. -/
def normalizedIndex (P : PolynomialChart Λ X structureMap) :
    NormalizedChartIndex Λ X structureMap :=
  ⟨P.openPart, P.variableIndex, P.toAffine ≫ P.affineEquiv.hom,
    (Category.assoc _ _ _).trans P.comm⟩

/-- **Every polynomial chart is isomorphic to a normalized one.** The presentation of the
affine space of a chart is an isomorphism of schemes, and transporting the chart along it
replaces the affine space by the affine space it presents. -/
def normalizedIso (P : PolynomialChart Λ X structureMap) :
    normalizedChart Λ X structureMap (normalizedIndex Λ X structureMap P) ≅ P where
  hom :=
    { open_le := le_rfl
      affine := P.affineEquiv.inv
      map_comm := by
        dsimp only [normalizedChart, normalizedIndex]
        simp [Scheme.homOfLE_rfl]
      base_comm := by
        dsimp only [normalizedChart, normalizedIndex, toBase]
        simp }
  inv :=
    { open_le := le_rfl
      affine := P.affineEquiv.hom
      map_comm := by
        dsimp only [normalizedChart, normalizedIndex]
        simp [Scheme.homOfLE_rfl]
      base_comm := by
        dsimp only [normalizedChart, normalizedIndex, toBase]
        simp }
  hom_inv_id := Hom.ext P.affineEquiv.inv_hom_id
  inv_hom_id := Hom.ext P.affineEquiv.hom_inv_id

/-- The full subcategory of the chart site on the normalized charts: a category whose objects
are the triples of `NormalizedChartIndex`, hence a `Type (u + 1)`, and whose morphisms are those
of the chart site, hence a `Type u`. -/
abbrev NormalizedChart : Type (u + 1) :=
  InducedCategory (PolynomialChart Λ X structureMap) (normalizedChart Λ X structureMap)

/-- The inclusion of the normalized charts into the site of polynomial charts is essentially
surjective: every chart is isomorphic to a normalized one. -/
instance essSurj_normalizedChartι :
    (inducedFunctor (normalizedChart Λ X structureMap)).EssSurj where
  mem_essImage P :=
    ⟨normalizedIndex Λ X structureMap P, ⟨normalizedIso Λ X structureMap P⟩⟩

/-- The inclusion of the normalized charts into the site of polynomial charts is an equivalence
of categories. -/
instance isEquivalence_normalizedChartι :
    (inducedFunctor (normalizedChart Λ X structureMap)).IsEquivalence where

/-- The category of normalized charts is locally small at `u + 1`. -/
instance locallySmall_normalizedChart :
    LocallySmall.{u + 1} (NormalizedChart Λ X structureMap) where
  hom_small _ _ := Small.mk' (Equiv.ulift.{u + 1}).symm

/-! ### The small model -/

/-- The small model of the site of polynomial charts: the normalized charts with their morphism
types shrunk, a category whose objects and whose morphisms both lie in `Type (u + 1)`. -/
abbrev SmallChartSite : Type (u + 1) := ShrinkHoms (NormalizedChart Λ X structureMap)

/-- The fully faithful essentially surjective functor from the small model to the site of
polynomial charts. -/
def smallChartFunctor : SmallChartSite Λ X structureMap ⥤ PolynomialChart Λ X structureMap :=
  (ShrinkHoms.equivalence (NormalizedChart Λ X structureMap)).inverse ⋙
    inducedFunctor (normalizedChart Λ X structureMap)

/-- The functor `smallChartFunctor` from the small model to the site of polynomial charts is an
equivalence of categories. -/
instance isEquivalence_smallChartFunctor :
    (smallChartFunctor Λ X structureMap).IsEquivalence :=
  inferInstanceAs (Functor.IsEquivalence
    ((ShrinkHoms.equivalence (NormalizedChart Λ X structureMap)).inverse ⋙ _))

/-- The small model is equivalent to the site of polynomial charts. -/
def smallChartEquiv : SmallChartSite Λ X structureMap ≌ PolynomialChart Λ X structureMap :=
  (smallChartFunctor Λ X structureMap).asEquivalence

/-- **The site of polynomial charts is essentially small at `u + 1`**, the universe of its
objects. -/
instance essentiallySmall_polynomialChart :
    EssentiallySmall.{u + 1} (PolynomialChart Λ X structureMap) :=
  EssentiallySmall.mk' (smallChartEquiv Λ X structureMap).symm

/-- The topology on the small model inherited from the topology of Tag 08VA. -/
abbrev smallChartTopology : GrothendieckTopology (SmallChartSite Λ X structureMap) :=
  (smallChartFunctor Λ X structureMap).inducedTopology (topology Λ X structureMap)

/-- **The small model carries the same sheaves as the chart site**, with values in an arbitrary
category: the two sites are equivalent and the topology of the model is the one inherited from
the chart site, so restriction along `smallChartFunctor` is an equivalence. -/
def smallChartSheafEquiv (A : Type t₁) [Category.{t₂} A] :
    Sheaf (topology Λ X structureMap) A ≌ Sheaf (smallChartTopology Λ X structureMap) A :=
  letI e := (smallChartFunctor Λ X structureMap).asEquivalence.symm
  letI : e.inverse.IsDenseSubsite (smallChartTopology Λ X structureMap)
      (topology Λ X structureMap) :=
    inferInstanceAs ((smallChartFunctor Λ X structureMap).IsDenseSubsite
      (smallChartTopology Λ X structureMap) (topology Λ X structureMap))
  e.sheafCongr (topology Λ X structureMap) (smallChartTopology Λ X structureMap) A

end AlgebraicGeometry.PolynomialChart

end
