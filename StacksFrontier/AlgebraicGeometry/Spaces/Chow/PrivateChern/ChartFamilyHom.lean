module

public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianChartFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing

/-!
# Morphisms of glueing data over the étale charts of an algebraic space

Let `X` be an algebraic space over a scheme `S` and `F`, `G` two families of schemes over the
étale charts of `X` with cartesian transitions
(`AlgebraicGeometry.Space.CartesianChartFamily`). A family of morphisms
`φ_V : F(V) ⟶ G(V)` over the charts, natural in the chart, glues to a morphism
`φ_X : F_X ⟶ G_X` of the glued algebraic spaces over `X`, and on the surjective chart `V₂` the
square formed by the charts of `F_X` and `G_X`, `φ_{V₂}` and `φ_X` is cartesian:
`F(V₂) = F_X ×_{G_X} G(V₂)`. So every property of morphisms that is étale local on the target
and holds for `φ_{V₂}` holds for `φ_X`.

## Main definitions

* `AlgebraicGeometry.Space.CartesianChartFamily.Hom`: a natural family of morphisms
  over the charts.
* `AlgebraicGeometry.Space.CartesianChartFamily.Hom.glued`: the glued morphism.

## Main results

* `AlgebraicGeometry.Space.CartesianChartFamily.Hom.quotientChart_comp_glued`: it
  restricts on the chart to `φ_{V₂}`.
* `AlgebraicGeometry.Space.CartesianChartFamily.Hom.glued_comp_quotientHom`: it lies
  over `X`.
* `AlgebraicGeometry.Space.CartesianChartFamily.Hom.isPullback_glued`: the cartesian
  square at the chart.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

namespace CartesianChartFamily

/-- **A morphism of glueing data**: morphisms `F(V) ⟶ G(V)` over the charts, natural in the
chart. -/
structure Hom (F G : CartesianChartFamily X) where
  /-- The morphism over a chart. -/
  app : ∀ V, F.obj V ⟶ G.obj V
  /-- It lies over the chart. -/
  app_toChart : ∀ V, app V ≫ G.toChart V = F.toChart V
  /-- It is natural in the chart. -/
  naturality : ∀ {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V),
    F.map h ≫ app V = app V' ≫ G.map h

namespace Hom

variable {F G : CartesianChartFamily X} (φ : Hom F G)

/-- The morphism over a chart, as a morphism of the site. -/
def siteApp (V : SmallEtale B S hS X.1) : F.site V ⟶ G.site V :=
  Over.homMk (ObjectProperty.homMk (φ.app V)) (by
    apply ObjectProperty.hom_ext
    change φ.app V ≫ G.toChart V ≫ B.inclusion.map ((SmallEtale.toOver B S hS X.1).obj V).hom =
      F.toChart V ≫ B.inclusion.map ((SmallEtale.toOver B S hS X.1).obj V).hom
    rw [← Category.assoc, φ.app_toChart])

/-- The morphism of schemes underlying `siteApp` is the morphism over the chart. -/
@[simp]
theorem toScheme_map_siteApp (V : SmallEtale B S hS X.1) :
    (BigFppfOver.toScheme B S hS).map (φ.siteApp V) = φ.app V :=
  rfl

/-- The morphism over a chart, as a morphism of the site, lies over the chart. -/
theorem siteApp_siteToChart (V : SmallEtale B S hS X.1) :
    φ.siteApp V ≫ G.siteToChart V = F.siteToChart V :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (φ.app_toChart V))

/-- The morphisms over the charts, as morphisms of the site, are natural in the chart. -/
theorem siteMap_siteApp {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    F.siteMap h ≫ φ.siteApp V = φ.siteApp V' ≫ G.siteMap h :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (φ.naturality h))

/-- The morphism over a chart commutes with the morphisms `F(V) ⟶ X` and `G(V) ⟶ X`. -/
theorem siteApp_siteToSpace (V : SmallEtale B S hS X.1) :
    yoneda.map (φ.siteApp V) ≫ G.siteToSpace V = F.siteToSpace V := by
  rw [siteToSpace, siteToSpace, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    φ.siteApp_siteToChart]

section Relation

variable {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)

/-- The morphisms over `V'` and `V₂` commute with the source maps of the relations of `F` and
`G` on `V'` over `V₂`. -/
theorem relation_source :
    (Over.post (X := B.obj hS) B.inclusion).map (φ.siteApp V') ≫
        (relation B S hS (G.siteMap pr₂) (G.siteMap pr₁)).source =
      (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)).source ≫
        (Over.post (X := B.obj hS) B.inclusion).map (φ.siteApp V₂) := by
  simp only [relation, prod.lift_snd, ← Functor.map_comp, φ.siteMap_siteApp]

/-- The morphisms over `V'` and `V₂` commute with the target maps of the relations of `F` and
`G` on `V'` over `V₂`. -/
theorem relation_target :
    (Over.post (X := B.obj hS) B.inclusion).map (φ.siteApp V') ≫
        (relation B S hS (G.siteMap pr₂) (G.siteMap pr₁)).target =
      (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)).target ≫
        (Over.post (X := B.obj hS) B.inclusion).map (φ.siteApp V₂) := by
  simp only [relation, prod.lift_fst, ← Functor.map_comp, φ.siteMap_siteApp]

/-- **The glued morphism** `F_X ⟶ G_X`. -/
def glued : F.quotient pr₁ pr₂ hsq ⟶ G.quotient pr₁ pr₂ hsq :=
  ObjectProperty.homMk (Stacks.Groupoids.quotientSheafMap (BigFppfOver.topology B S hS)
    (Over.post B.inclusion) (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁))
    (relation B S hS (G.siteMap pr₂) (G.siteMap pr₁))
    ((Over.post (X := B.obj hS) B.inclusion).map (φ.siteApp V'))
    ((Over.post (X := B.obj hS) B.inclusion).map (φ.siteApp V₂))
    (φ.relation_source pr₁ pr₂) (φ.relation_target pr₁ pr₂)).hom

/-- The glued morphism restricts on the chart to the morphism over the chart. -/
theorem quotientChart_comp_glued :
    F.quotientChart pr₁ pr₂ hsq ≫ (φ.glued pr₁ pr₂ hsq).hom =
      yoneda.map (φ.siteApp V₂) ≫ G.quotientChart pr₁ pr₂ hsq :=
  Stacks.Groupoids.quotientChart_comp_quotientSheafMap (BigFppfOver.topology B S hS)
    (Over.post B.inclusion) _ _ _ (φ.siteApp V₂) _ _

/-- The glued morphism lies over `X`. -/
theorem glued_comp_quotientHom :
    φ.glued pr₁ pr₂ hsq ≫ G.quotientHom pr₁ pr₂ hsq = F.quotientHom pr₁ pr₂ hsq := by
  refine F.quotientHom_unique pr₁ pr₂ hsq _ ?_
  have h1 := Stacks.Groupoids.toQuotientSheaf_comp_quotientSheafMap (BigFppfOver.topology B S hS)
    (Over.post B.inclusion) (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁))
    (relation B S hS (G.siteMap pr₂) (G.siteMap pr₁))
    ((Over.post (X := B.obj hS) B.inclusion).map (φ.siteApp V'))
    ((Over.post (X := B.obj hS) B.inclusion).map (φ.siteApp V₂))
    (φ.relation_source pr₁ pr₂) (φ.relation_target pr₁ pr₂)
  calc _ = (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ≫ (φ.glued pr₁ pr₂ hsq).hom) ≫
          (G.quotientHom pr₁ pr₂ hsq).hom := (Category.assoc _ _ _).symm
    _ = ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft (yoneda.map
            ((Over.post (X := B.obj hS) B.inclusion).map (φ.siteApp V₂))) ≫
          Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
            (relation B S hS (G.siteMap pr₂) (G.siteMap pr₁))) ≫
          (G.quotientHom pr₁ pr₂ hsq).hom := congrArg (· ≫ (G.quotientHom pr₁ pr₂ hsq).hom) h1
    _ = (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft (yoneda.map
            ((Over.post (X := B.obj hS) B.inclusion).map (φ.siteApp V₂))) ≫
          ((pointsYonedaIso (Over.post B.inclusion) (G.site V₂)).hom ≫ G.siteToSpace V₂) :=
        (Category.assoc _ _ _).trans
          (congrArg (_ ≫ ·) (G.toQuotientSheaf_comp_quotientHom pr₁ pr₂ hsq))
    _ = ((pointsYonedaIso (Over.post B.inclusion) (F.site V₂)).hom ≫ yoneda.map (φ.siteApp V₂)) ≫
          G.siteToSpace V₂ := by
      rw [← Category.assoc, whiskerLeft_yoneda_map_comp_pointsYonedaIso_hom
        (Over.post (X := B.obj hS) B.inclusion) (φ.siteApp V₂)]
    _ = _ := by rw [Category.assoc, φ.siteApp_siteToSpace]

include hsq in
/-- **The cartesian square at a surjective chart**: `F(V₂) = F_X ×_{G_X} G(V₂)`. -/
theorem isPullback_glued
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom) :
    IsPullback (F.quotientChart pr₁ pr₂ hsq) (yoneda.map (φ.siteApp V₂))
      (φ.glued pr₁ pr₂ hsq).hom (G.quotientChart pr₁ pr₂ hsq) := by
  have hF := F.isPullback_quotientHom pr₁ pr₂ hsq hsurj
  have hG := G.isPullback_quotientHom pr₁ pr₂ hsq hsurj
  have houter : IsPullback (yoneda.map (φ.siteApp V₂) ≫ yoneda.map (G.siteToChart V₂))
      (F.quotientChart pr₁ pr₂ hsq) V₂.obj.hom
      ((φ.glued pr₁ pr₂ hsq).hom ≫ (G.quotientHom pr₁ pr₂ hsq).hom) := by
    have e1 : yoneda.map (φ.siteApp V₂) ≫ yoneda.map (G.siteToChart V₂) =
        yoneda.map (F.siteToChart V₂) := by
      rw [← CategoryTheory.Functor.map_comp, φ.siteApp_siteToChart]
    have e2 : (φ.glued pr₁ pr₂ hsq).hom ≫ (G.quotientHom pr₁ pr₂ hsq).hom =
        (F.quotientHom pr₁ pr₂ hsq).hom :=
      congrArg (fun m => m.hom) (φ.glued_comp_quotientHom pr₁ pr₂ hsq)
    rw [e1, e2]
    exact hF.flip
  exact (IsPullback.of_right houter (φ.quotientChart_comp_glued pr₁ pr₂ hsq).symm hG.flip).flip

end Relation

end Hom

end CartesianChartFamily

end AlgebraicGeometry.Space

end
