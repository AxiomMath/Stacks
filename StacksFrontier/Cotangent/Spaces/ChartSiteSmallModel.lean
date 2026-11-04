module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartSpaceLiftedRingedTopoi

/-!
# A small model of the site of polynomial charts of an algebraic space

The site `C_{X/Λ}` of Tag 08VK has objects in `Type (u + 1)` and morphisms in `Type u`: a chart
records a `Type u` set of variables and an arbitrary scheme presented as the affine space on
them. This file replaces it by an equivalent genuinely small site at the universe `u + 1`, in
which the presentation is normalized away and the morphisms are shrunk.

## Main definitions

* `AlgebraicGeometry.Space.PolynomialChart.NormalizedChartIndex` and
  `AlgebraicGeometry.Space.PolynomialChart.normalizedChart`: the `Type (u + 1)` of triples
  `(U, σ, U ⟶ Spec Λ[σ])` over `Spec Λ`, with `U` an object of the small étale site of `X`, and
  the chart such a triple names.
* `AlgebraicGeometry.Space.PolynomialChart.SmallChartSite`: the small model, the morphisms of
  the normalized charts shrunk to `Type (u + 1)`.
* `AlgebraicGeometry.Space.PolynomialChart.smallChartTopology`: the topology it inherits from
  the chart site.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.smallChartEquiv`: the small model is equivalent to
  the chart site, and `AlgebraicGeometry.Space.PolynomialChart.essentiallySmall_polynomialChart`
  records the resulting essential smallness at `u + 1`.
* `AlgebraicGeometry.Space.PolynomialChart.hasSheafify_smallChartTopology` and
  `AlgebraicGeometry.Space.PolynomialChart.wEqualsLocallyBijective_smallChartTopology`: abelian
  sheafification on the small model in the universe `u + 1`, stated explicitly because instance
  search for it is otherwise stuck on a universe metavariable.
* `AlgebraicGeometry.Space.PolynomialChart.smallChartSheafEquiv`: the two sites have equivalent
  categories of sheaves with values in any category, so nothing is lost by working on the small
  model.

## Implementation notes

A chart is isomorphic to one whose affine space is literally `Spec Λ[σ]` and whose presentation
is the identity, because the presentation is itself an isomorphism of schemes; that is
`normalizedIso`, and it is the only mathematical content here. The normalized charts form a full
subcategory whose objects are the triples above, a `Type (u + 1)`, and whose morphisms are those
of the chart site, a `Type u`; `ShrinkHoms` lifts the morphisms to `Type (u + 1)` and makes the
result a `SmallCategory`.

As for the polynomial charts of a scheme, the universe `u + 1` cannot be lowered to `u`: a chart
records an arbitrary `Type u` of variables, and a strongly cartesian morphism of the chart
fibration has the same affine space, hence the same set of variables, as its target.

## References

* [Stacks Project, Tag 08VK](https://stacks.math.columbia.edu/tag/08VK)
* [Stacks Project, Tag 08VI](https://stacks.math.columbia.edu/tag/08VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t₂ t₁ u

namespace AlgebraicGeometry.Space.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

/-! ### The normalized charts -/

/-- A triple consisting of an object `U` of the small étale site of `X`, a set `σ` of variables
and an arrow `U ⟶ Spec Λ[σ]` over `Spec Λ`: the data of a polynomial chart whose affine space is
literally an affine space. -/
abbrev NormalizedChartIndex : Type (u + 1) :=
  Σ U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X, Σ σ : Type u,
    { f : (smallEtaleToScheme Λ B hS X).obj U ⟶ Spec (CommRingCat.of (MvPolynomial σ Λ)) //
        f ≫ Scheme.Spec.map
            (CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial σ Λ)).op =
          openPartToBase Λ B hS X U }

/-- The polynomial chart named by a triple `(U, σ, U ⟶ Spec Λ[σ])`: its affine space is
`Spec Λ[σ]` and its presentation is the identity. -/
def normalizedChart (i : NormalizedChartIndex Λ B hS X) : PolynomialChart Λ B hS X hX where
  openPart := i.1
  variableIndex := i.2.1
  affineSpace := Spec (CommRingCat.of (MvPolynomial i.2.1 Λ))
  affineEquiv := Iso.refl _
  toAffine := i.2.2.1
  comm := (congrArg (fun g => i.2.2.1 ≫ g) (Category.id_comp _)).trans i.2.2.2

/-- The triple attached to a polynomial chart by composing its arrow to the affine space with
its presentation. -/
def normalizedIndex (P : PolynomialChart Λ B hS X hX) : NormalizedChartIndex Λ B hS X :=
  ⟨P.openPart, P.variableIndex, P.toAffine ≫ P.affineEquiv.hom,
    (Category.assoc _ _ _).trans P.comm⟩

/-- **Every polynomial chart is isomorphic to a normalized one.** The presentation of the
affine space of a chart is an isomorphism of schemes, and transporting the chart along it
replaces the affine space by the affine space it presents. -/
def normalizedIso (P : PolynomialChart Λ B hS X hX) :
    normalizedChart Λ B hS X hX (normalizedIndex Λ B hS X hX P) ≅ P where
  hom :=
    { openMap := 𝟙 _
      affine := P.affineEquiv.inv
      map_comm := by
        dsimp only [normalizedChart, normalizedIndex]
        simp
      base_comm := by
        dsimp only [normalizedChart, normalizedIndex, toBase]
        simp }
  inv :=
    { openMap := 𝟙 _
      affine := P.affineEquiv.hom
      map_comm := by
        dsimp only [normalizedChart, normalizedIndex]
        simp
      base_comm := by
        dsimp only [normalizedChart, normalizedIndex, toBase]
        simp }
  hom_inv_id := Hom.ext (Category.id_comp _) P.affineEquiv.inv_hom_id
  inv_hom_id := Hom.ext (Category.id_comp _) P.affineEquiv.hom_inv_id

/-- The full subcategory of the chart site on the normalized charts: a category whose objects
are the triples of `NormalizedChartIndex`, hence a `Type (u + 1)`, and whose morphisms are those
of the chart site, hence a `Type u`. -/
abbrev NormalizedChart : Type (u + 1) :=
  InducedCategory (PolynomialChart Λ B hS X hX) (normalizedChart Λ B hS X hX)

/-- Every polynomial chart is isomorphic to a normalized chart, so the inclusion of the normalized
charts is essentially surjective. -/
instance essSurj_normalizedChartι :
    (inducedFunctor (normalizedChart Λ B hS X hX)).EssSurj where
  mem_essImage P :=
    ⟨normalizedIndex Λ B hS X hX P, ⟨normalizedIso Λ B hS X hX P⟩⟩

/-- The inclusion of the normalized charts into the site of polynomial charts is an equivalence. -/
instance isEquivalence_normalizedChartι :
    (inducedFunctor (normalizedChart Λ B hS X hX)).IsEquivalence where

/-- The category of normalized charts is locally small at `u + 1`. -/
instance locallySmall_normalizedChart :
    LocallySmall.{u + 1} (NormalizedChart Λ B hS X hX) where
  hom_small _ _ := Small.mk' (Equiv.ulift.{u + 1}).symm

/-! ### The small model -/

/-- The small model of the site of polynomial charts: the normalized charts with their morphism
types shrunk, a category whose objects and whose morphisms both lie in `Type (u + 1)`. -/
abbrev SmallChartSite : Type (u + 1) := ShrinkHoms (NormalizedChart Λ B hS X hX)

/-- The fully faithful essentially surjective functor from the small model to the site of
polynomial charts. -/
def smallChartFunctor : SmallChartSite Λ B hS X hX ⥤ PolynomialChart Λ B hS X hX :=
  (ShrinkHoms.equivalence (NormalizedChart Λ B hS X hX)).inverse ⋙
    inducedFunctor (normalizedChart Λ B hS X hX)

/-- The functor from the small model to the site of polynomial charts is an equivalence. -/
instance isEquivalence_smallChartFunctor :
    (smallChartFunctor Λ B hS X hX).IsEquivalence := by
  unfold smallChartFunctor
  infer_instance

/-- The small model is equivalent to the site of polynomial charts. -/
def smallChartEquiv : SmallChartSite Λ B hS X hX ≌ PolynomialChart Λ B hS X hX :=
  (smallChartFunctor Λ B hS X hX).asEquivalence

/-- **The site of polynomial charts is essentially small at `u + 1`**, the universe of its
objects. -/
instance essentiallySmall_polynomialChart :
    EssentiallySmall.{u + 1} (PolynomialChart Λ B hS X hX) :=
  EssentiallySmall.mk' (smallChartEquiv Λ B hS X hX).symm

/-- The topology on the small model induced along `smallChartFunctor` by the topology of the site
of polynomial charts (Tag 08VK). -/
abbrev smallChartTopology : GrothendieckTopology (SmallChartSite Λ B hS X hX) :=
  (smallChartFunctor Λ B hS X hX).inducedTopology (topology Λ B hS X hX)

/-- Abelian presheaves on the small model admit sheafification with sections in the universe
`u + 1` of the model. -/
instance hasSheafify_smallChartTopology :
    HasSheafify (smallChartTopology Λ B hS X hX) AddCommGrpCat.{u + 1} :=
  CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat.{u + 1, u + 1, u + 1} _

/-- On the small model, the maps that sheafification of abelian presheaves inverts in the
universe `u + 1` of the model are the locally bijective ones. -/
instance wEqualsLocallyBijective_smallChartTopology :
    (smallChartTopology Λ B hS X hX).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat.{u + 1, u + 1, u + 1} _

/-- **The small model carries the same sheaves as the chart site**, with values in an arbitrary
category: the two sites are equivalent and the topology of the model is the one inherited from
the chart site, so restriction along `smallChartFunctor` is an equivalence. -/
def smallChartSheafEquiv (A : Type t₁) [Category.{t₂} A] :
    Sheaf (topology Λ B hS X hX) A ≌ Sheaf (smallChartTopology Λ B hS X hX) A :=
  letI e := (smallChartFunctor Λ B hS X hX).asEquivalence.symm
  letI : e.inverse.IsDenseSubsite (smallChartTopology Λ B hS X hX) (topology Λ B hS X hX) :=
    show (smallChartFunctor Λ B hS X hX).IsDenseSubsite (smallChartTopology Λ B hS X hX)
      (topology Λ B hS X hX) from inferInstance
  e.sheafCongr (topology Λ B hS X hX) (smallChartTopology Λ B hS X hX) A

end AlgebraicGeometry.Space.PolynomialChart

end
