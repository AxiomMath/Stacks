module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompCondition

/-!
# The affine quadruple of the site cut out by a chart

Let `ch` be a Cartesian affine-open chart (`AlgebraicGeometry.BaseChangeChart`) of the square of
schemes underlying a cartesian square `U' → V'`, `U' → U`, `U → V`, `V' → V` of the big fppf site.
Its affine opens `Spec A ⟶ U`, `Spec R ⟶ V`, `Spec R' ⟶ V'` are objects of the site, and with the
fibre product of the site they form an affine cartesian square étale over the given one.

## Main definitions

* `AlgebraicGeometry.Space.chartSiteObject`: an affine open of an object of the site, as an
  object of the site, with its inclusion `chartSiteObjectι`.
* `AlgebraicGeometry.Space.chartSiteObjectMap`: a morphism of affine opens over a morphism of the
  site.
* `AlgebraicGeometry.Space.chartQuadrupleF`, `AlgebraicGeometry.Space.chartQuadrupleG`: the two
  morphisms of the affine quadruple of a chart; `AlgebraicGeometry.Space.chartQuadrupleι'` the
  inclusion of their fibre product into `U'`.

## Main results

* `AlgebraicGeometry.Space.isEtale_representedSpaceMap_chartSiteObjectι_comp`: an affine open of
  an étale chart is an étale chart.
* `AlgebraicGeometry.Space.chartQuadruple_ha'`, `chartQuadruple_hfa`, `chartQuadruple_hgb`,
  `chartQuadruple_hfc`: the squares of the affine quadruple over the given ones.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Construction

variable {U : BigFppfOver B S hS} {A : CommRingCat.{u}}
  (i : Spec A ⟶ (BigFppfOver.toScheme B S hS).obj U) [AlgebraicGeometry.IsOpenImmersion i]

/-- The scheme `Spec A` of an affine open `Spec A ⟶ U` of an object of the site, as an object of
the underlying category of the site. -/
abbrev chartSiteScheme : B.Schemes :=
  B.obj (Scheme.size_lt_of_isOpenImmersion i U.left.property)

/-- An affine open `Spec A ⟶ U` of the underlying scheme of an object of the site, as an object
of the site. -/
def chartSiteObject : BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage (X := chartSiteScheme i) (Y := U.left) i ≫ U.hom)

/-- The inclusion of `chartSiteObject i` into `U`. -/
def chartSiteObjectι : chartSiteObject i ⟶ U :=
  Over.homMk (B.inclusion.preimage (X := chartSiteScheme i) (Y := U.left) i)

/-- The morphism of schemes underlying `chartSiteObjectι i` is `i`. -/
theorem toScheme_map_chartSiteObjectι :
    (BigFppfOver.toScheme B S hS).map (chartSiteObjectι i) = i :=
  B.inclusion.map_preimage (X := chartSiteScheme i) (Y := U.left) i

/-- The scheme underlying `chartSiteObject i` is affine. -/
instance : IsAffine ((BigFppfOver.toScheme B S hS).obj (chartSiteObject i)) :=
  inferInstanceAs (IsAffine (Spec A))

variable {V : BigFppfOver B S hS} {A₂ : CommRingCat.{u}}
  (j : Spec A₂ ⟶ (BigFppfOver.toScheme B S hS).obj V) [AlgebraicGeometry.IsOpenImmersion j]
  (f : U ⟶ V) (m : Spec A ⟶ Spec A₂)

/-- A morphism of affine opens over a morphism of the site, as a morphism of the site. -/
def chartSiteObjectMap (h : i ≫ (BigFppfOver.toScheme B S hS).map f = m ≫ j) :
    chartSiteObject i ⟶ chartSiteObject j :=
  Over.homMk (B.inclusion.preimage (X := chartSiteScheme i) (Y := chartSiteScheme j) m) (by
    have h' : B.inclusion.preimage (X := chartSiteScheme i) (Y := chartSiteScheme j) m ≫
        B.inclusion.preimage (X := chartSiteScheme j) (Y := V.left) j =
        B.inclusion.preimage (X := chartSiteScheme i) (Y := U.left) i ≫ f.left :=
      B.inclusion.map_injective (by
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
          Functor.map_preimage, Functor.map_preimage, Functor.map_preimage]
        exact h.symm)
    simp only [chartSiteObject, Over.mk_hom]
    rw [reassoc_of% h', Over.w])

/-- The morphism of schemes underlying `chartSiteObjectMap i j f m h` is `m`. -/
theorem toScheme_map_chartSiteObjectMap (h : i ≫ (BigFppfOver.toScheme B S hS).map f = m ≫ j) :
    (BigFppfOver.toScheme B S hS).map (chartSiteObjectMap i j f m h) = m :=
  B.inclusion.map_preimage (X := chartSiteScheme i) (Y := chartSiteScheme j) m

/-- The inclusions `chartSiteObjectι i` and `chartSiteObjectι j` intertwine
`chartSiteObjectMap i j f m h` with `f`. -/
theorem chartSiteObjectι_comp (h : i ≫ (BigFppfOver.toScheme B S hS).map f = m ≫ j) :
    chartSiteObjectι i ≫ f = chartSiteObjectMap i j f m h ≫ chartSiteObjectι j :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      toScheme_map_chartSiteObjectι, toScheme_map_chartSiteObjectι,
      toScheme_map_chartSiteObjectMap]
    exact h)

end Construction

/-- A commuting square of the site, pasted with a commuting square of algebraic spaces. -/
private theorem representedSpaceMap_comp_square_of_comp_eq {P Q T T' : BigFppfOver B S hS}
    {X Y : AlgebraicSpaces B S hS} {s : P ⟶ Q} {t : Q ⟶ T} {u : P ⟶ T'} {w : T' ⟶ T}
    (hs : s ≫ t = u ≫ w)
    {a : (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS) ⟶ X}
    {b : (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y}
    {f : X ⟶ Y} (h : representedSpaceMap B S hS w ≫ b = a ≫ f) :
    representedSpaceMap B S hS s ≫ (representedSpaceMap B S hS t ≫ b) =
      (representedSpaceMap B S hS u ≫ a) ≫ f := by
  rw [← Category.assoc, representedSpaceMap_comp, hs, ← representedSpaceMap_comp,
    Category.assoc, h, Category.assoc]


section Quadruple

attribute [local instance] BaseChangeChart.isOpenImmersion_incU BaseChangeChart.isOpenImmersion_incV
  BaseChangeChart.isOpenImmersion_incV'

variable {U V U' V' : BigFppfOver B S hS} {f₀ : U ⟶ V} {g₀ : V' ⟶ V} {f₀' : U' ⟶ V'}
  {g₀' : U' ⟶ U}
  (ch : BaseChangeChart ((BigFppfOver.toScheme B S hS).map f₀)
    ((BigFppfOver.toScheme B S hS).map g₀) ((BigFppfOver.toScheme B S hS).map f₀')
    ((BigFppfOver.toScheme B S hS).map g₀'))

/-- The morphism `Spec A ⟶ Spec R` of the chart, as a morphism of the site. -/
abbrev chartQuadrupleF : chartSiteObject ch.incU ⟶ chartSiteObject ch.incV :=
  chartSiteObjectMap ch.incU ch.incV f₀ (Spec.map ch.a) ch.wU

/-- The morphism `Spec R' ⟶ Spec R` of the chart, as a morphism of the site. -/
abbrev chartQuadrupleG : chartSiteObject ch.incV' ⟶ chartSiteObject ch.incV :=
  chartSiteObjectMap ch.incV' ch.incV g₀ (Spec.map ch.b) ch.wV'

/-- The inclusion of the fibre product of the chart into `U'`. -/
def chartQuadrupleι' (hpb : IsPullback g₀' f₀' f₀ g₀) :
    pullback (chartQuadrupleF ch) (chartQuadrupleG ch) ⟶ U' :=
  hpb.lift (pullback.fst _ _ ≫ chartSiteObjectι ch.incU)
    (pullback.snd _ _ ≫ chartSiteObjectι ch.incV')
    (by rw [Category.assoc, chartSiteObjectι_comp ch.incU ch.incV f₀ (Spec.map ch.a) ch.wU,
      Category.assoc, chartSiteObjectι_comp ch.incV' ch.incV g₀ (Spec.map ch.b) ch.wV',
      pullback.condition_assoc])

variable {X X' : AlgebraicSpaces B S hS} (g' : X' ⟶ X)

variable (hpb : IsPullback g₀' f₀' f₀ g₀)

/-- The fibre product of the affine quadruple of a chart is affine. -/
instance : IsAffine ((BigFppfOver.toScheme B S hS).obj
    (pullback (chartQuadrupleF ch) (chartQuadrupleG ch))) :=
  isAffine_toScheme_pullback B S hS _ _

/-- The square of the affine quadruple of a chart over `g' : X' ⟶ X`. -/
theorem chartQuadruple_ha'
    (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (ha' : representedSpaceMap B S hS g₀' ≫ a = a' ≫ g') :
    representedSpaceMap B S hS (pullback.fst (chartQuadrupleF ch) (chartQuadrupleG ch)) ≫
        (representedSpaceMap B S hS (chartSiteObjectι ch.incU) ≫ a) =
      (representedSpaceMap B S hS (chartQuadrupleι' ch hpb) ≫ a') ≫ g' := by
  exact representedSpaceMap_comp_square_of_comp_eq (hpb.lift_fst _ _ _).symm ha'

end Quadruple

section Etale

variable {U : BigFppfOver B S hS} {A : CommRingCat.{u}}
  (i : Spec A ⟶ (BigFppfOver.toScheme B S hS).obj U) [AlgebraicGeometry.IsOpenImmersion i]

/-- An affine open of an étale chart of an algebraic space is an étale chart. -/
theorem isEtale_representedSpaceMap_chartSiteObjectι_comp {X : AlgebraicSpaces B S hS}
    (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (ha : IsEtale B S hS a.hom) :
    IsEtale B S hS (representedSpaceMap B S hS (chartSiteObjectι i) ≫ a).hom :=
  isEtale_yoneda_map_comp B S hS a.hom (chartSiteObjectι i)
    (by rw [toScheme_map_chartSiteObjectι]; exact inferInstanceAs (Etale i)) ha

end Etale

section QuadrupleSquares

attribute [local instance] BaseChangeChart.isOpenImmersion_incU BaseChangeChart.isOpenImmersion_incV
  BaseChangeChart.isOpenImmersion_incV'

variable {U V U' V' : BigFppfOver B S hS} {f₀ : U ⟶ V} {g₀ : V' ⟶ V} {f₀' : U' ⟶ V'}
  {g₀' : U' ⟶ U}
  (ch : BaseChangeChart ((BigFppfOver.toScheme B S hS).map f₀)
    ((BigFppfOver.toScheme B S hS).map g₀) ((BigFppfOver.toScheme B S hS).map f₀')
    ((BigFppfOver.toScheme B S hS).map g₀'))
  {X Y X' Y' : AlgebraicSpaces B S hS}

/-- The square `U_Q → V_Q` of the affine quadruple of a chart, over `f : X ⟶ Y`. -/
theorem chartQuadruple_hfa (f : X ⟶ Y)
    (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (hfa : representedSpaceMap B S hS f₀ ≫ b = a ≫ f) :
    representedSpaceMap B S hS (chartQuadrupleF ch) ≫
        (representedSpaceMap B S hS (chartSiteObjectι ch.incV) ≫ b) =
      (representedSpaceMap B S hS (chartSiteObjectι ch.incU) ≫ a) ≫ f := by
  exact representedSpaceMap_comp_square_of_comp_eq
    (chartSiteObjectι_comp ch.incU ch.incV f₀ (Spec.map ch.a) ch.wU).symm hfa

/-- The square `V'_Q → V_Q` of the affine quadruple of a chart, over `g : Y' ⟶ Y`. -/
theorem chartQuadruple_hgb (g : Y' ⟶ Y)
    (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y')
    (hgb : representedSpaceMap B S hS g₀ ≫ b = c ≫ g) :
    representedSpaceMap B S hS (chartQuadrupleG ch) ≫
        (representedSpaceMap B S hS (chartSiteObjectι ch.incV) ≫ b) =
      (representedSpaceMap B S hS (chartSiteObjectι ch.incV') ≫ c) ≫ g := by
  exact representedSpaceMap_comp_square_of_comp_eq
    (chartSiteObjectι_comp ch.incV' ch.incV g₀ (Spec.map ch.b) ch.wV').symm hgb

/-- The square `U'_Q → V'_Q` of the affine quadruple of a chart, over `f' : X' ⟶ Y'`. -/
theorem chartQuadruple_hfc (hpb : IsPullback g₀' f₀' f₀ g₀) (f' : X' ⟶ Y')
    (c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y')
    (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (hfc : representedSpaceMap B S hS f₀' ≫ c = a' ≫ f') :
    representedSpaceMap B S hS (pullback.snd (chartQuadrupleF ch) (chartQuadrupleG ch)) ≫
        (representedSpaceMap B S hS (chartSiteObjectι ch.incV') ≫ c) =
      (representedSpaceMap B S hS (chartQuadrupleι' ch hpb) ≫ a') ≫ f' := by
  exact representedSpaceMap_comp_square_of_comp_eq (hpb.lift_snd _ _ _).symm hfc

end QuadrupleSquares

end AlgebraicGeometry.Space
