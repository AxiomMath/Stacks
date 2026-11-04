module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistLegSquares

/-!
# The map `θ_n` of Stacks 085F, glued

For a map `ψ : 𝒜₁ ⟶ 𝒜₂` of quasi-coherent graded `𝒪_X`-algebras on an algebraic space `X`
(Situation 0849), the chart maps `θ_n` of Tag 07ZG over the scheme points of `X` are compatible
with the transitions of the twists `𝒪_P(n)` and `𝒪_Q(n)`, and glue to one morphism
`θ_n : r_ψ^*𝒪_P(n) ⟶ ι^*𝒪_Q(n)` on `U(ψ)`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.twistMap`: the map
  `θ_n : r_ψ^*𝒪_P(n) ⟶ ι^*𝒪_Q(n)` of Stacks 085F, glued from the chart maps.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.twistPieceComparison_hom_hom_eq`: the
  comparison of the twists along a morphism lying over `k`, in the form of the comparisons of
  `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom_transport`.
* `RelativeProjSituation.liesOverTwistComparison_hom_app_pullbackSection_psiU`: that comparison
  carries `ψ` to `ψ`, in the form of the inputs `χ_A`, `χ_B` of
  `Stacks.AlgebraicGeometry.Tag07ZGTwist.transportTwistHom_relativeTwistAlgebraHom`.
* `RelativeProjSituation.baseLiesOverTwistComparison_hom_app_pullbackSection_psiU`: the same,
  for Situation 0849 over the base site (the spelling of the scheme points of `X`).
* `AlgebraicGeometry.Space.RelativeProjSituation.twistPieceComparison_hom_hom_eq_of_eq`: the
  comparison of the twists, in the form of the comparisons of
  `AlgebraicGeometry.Space.RelativeProjHomPoints.schemeTransitionLeg_hom_comp_chartTwistMap`.
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeTwistAlgebraHom_eq_transportTwistHom`:
  the map `θ` of Tag 07ZG at a restricted point is the transport of `θ`.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistChartMap_leg`: the chart maps `θ_n`
  commute with the legs of the transitions of the twists along any square of charts.
* `AlgebraicGeometry.Space.RelativeProjSituation.chartTransitionsCompatible_twistChartMap`: the
  chart map `θ_n` is compatible with the transitions of `𝒪_P(n)` and `𝒪_Q(n)`.
* `AlgebraicGeometry.Space.RelativeProjSituation.isDescendedChartHom_twistMap` and
  `AlgebraicGeometry.Space.RelativeProjSituation.eq_twistMap`: the glued `θ_n` is the chart map
  `θ_n` on the chart `U(ψ)_U`, and it is the only such morphism.

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

universe u m

namespace AlgebraicGeometry.Space

attribute [local irreducible] CategoryTheory.yoneda

namespace RelativeProjSituation

section Generic

/-- A morphism between the images of an identity and an identity. -/
private theorem map_id_comp_comp_id {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟) {x : 𝒞}
    {y : 𝒟} (g : F.obj x ⟶ y) : F.map (𝟙 x) ≫ g ≫ 𝟙 y = g := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- A square with invertible sides `c₁`, `c₂`, read with those sides inverted. -/
private theorem asIso_symm_hom_comp_eq {𝒞 : Type*} [Category 𝒞] {W x y z : 𝒞} {c₁ : W ⟶ x}
    {c₂ : y ⟶ z} {a : x ⟶ z} {b : W ⟶ y} (i₁ : IsIso c₁) (i₂ : IsIso c₂)
    (h : b ≫ c₂ = c₁ ≫ a) :
    (@asIso _ _ _ _ c₁ i₁).symm.hom ≫ b = a ≫ (@asIso _ _ _ _ c₂ i₂).symm.hom := by
  rw [Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv, IsIso.inv_comp_eq, ← Category.assoc, ← h,
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

variable (s : RelativeProjSituation.{u, m})

/-- The morphism of relative homogeneous spectra underlying a morphism of base changes. -/
def projMap {U V : BigFppfOver s.site s.base s.containsBase} {u : yoneda.obj U ⟶ s.space.1}
    {v : yoneda.obj V ⟶ s.space.1}
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u) :
    (relativeProj (s.shrink.pointAlgebra V v)).scheme ⟶
      (relativeProj (s.shrink.pointAlgebra U u)).scheme :=
  (BigFppfOver.toScheme s.site s.base s.containsBase).map y

/-- `AlgebraicGeometry.Space.RelativeProjSituation.pointTwistComparison` along a morphism `y` of
base changes lying over `k`, as an isomorphism of sheaves of graded algebras on the structure
sheaf of the ringed space. -/
def liesOverTwistComparison {U V : BigFppfOver s.site s.base s.containsBase} (k : V ⟶ U)
    (u : yoneda.obj U ⟶ s.space.1) (v : yoneda.obj V ⟶ s.space.1) (hv : yoneda.map k ≫ u = v)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : s.relativeProjPoints.LiesOver y k) :
    Stacks.RingedSpace.pullbackGradedAlgebra (s.projMap y).toLRSHom.toShHom
        (Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra U u)) ≅
      Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra V v) :=
  s.pointTwistComparison k u v hv (s.projMap y) (s.toScheme_map_eq_of_liesOver hv hy)

/-- **The comparison of the twists along a morphism lying over `k`**, in the form of the
comparisons of `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom_transport`: the comparison
along the square of `AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj` of the
degree-`n` piece of `AlgebraicGeometry.Space.RelativeProjSituation.pointTwistComparison`, between
the identifications of the twists. -/
theorem twistPieceComparison_hom_hom_eq {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : s.relativeProjPoints.LiesOver y k) (n : ℤ) :
    (s.twistPieceComparison k hv y hy n).hom.hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)).map
          (s.twistPieceQcohObjIso U u n).hom ≫
        (pullbackIsoOfSquare (s.toRelativeProj U u) (s.toRelativeProj V v)
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
          (s.projMap y)
          (s.map_comp_toRelativeProj y)
          (gradedPieceIso (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
            (Y := (relativeProj (s.shrink.pointAlgebra V v)).scheme)
            (s.projMap y)
            (s.pointTwistComparison k u v hv (s.projMap y)
              (s.toScheme_map_eq_of_liesOver hv hy)) n)).hom ≫
        (s.twistPieceQcohObjIso V v n).inv := by
  rw [twistPieceComparison_hom_hom]
  exact (map_id_comp_comp_id _ _).symm

/-- `AlgebraicGeometry.Space.RelativeProjSituation.toScheme_map_eq_of_liesOver`, for the morphism
of relative homogeneous spectra underlying a morphism of base changes. -/
theorem projMap_eq_of_liesOver {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} {k : V ⟶ U}
    (hv : yoneda.map k ≫ u = v)
    {y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u}
    (hy : s.relativeProjPoints.LiesOver y k) :
    s.projMap y =
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relativeProjCongr
        (A₁ := s.shrink.pointAlgebra V v)
        (A₂ := (s.shrink.pointAlgebra U u).pullback
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k))
        (s.quadrupleRestriction.restrict k u v hv)
        (s.quadrupleRestriction.isIso_restrict_app k u v hv)).hom ≫
      Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
        (s.shrink.pointAlgebra U u)
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k) :=
  s.toScheme_map_eq_of_liesOver hv hy

/-- `AlgebraicGeometry.Space.RelativeProjSituation.toScheme_map_comp_toBase_of_liesOver`, for the
morphism of relative homogeneous spectra underlying a morphism of base changes. -/
theorem projMap_comp_toBase_of_liesOver {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} {k : V ⟶ U}
    (hv : yoneda.map k ≫ u = v)
    {y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u}
    (hy : s.relativeProjPoints.LiesOver y k) :
    s.projMap y ≫ (relativeProj (s.shrink.pointAlgebra U u)).toBase =
      (relativeProj (s.shrink.pointAlgebra V v)).toBase ≫
        (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k :=
  s.toScheme_map_comp_toBase_of_liesOver hv hy

/-- `AlgebraicGeometry.Space.RelativeProjSituation.liesOverTwistComparison` is the comparison of
twists along a restriction followed by a base change. -/
theorem liesOverTwistComparison_eq {U V : BigFppfOver s.site s.base s.containsBase} (k : V ⟶ U)
    (u : yoneda.obj U ⟶ s.space.1) (v : yoneda.obj V ⟶ s.space.1) (hv : yoneda.map k ≫ u = v)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : s.relativeProjPoints.LiesOver y k) :
    s.liesOverTwistComparison k u v hv y hy =
      Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.congrBaseChangeTwistIso
        (s.shrink.pointAlgebra U u)
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
        (A₁ := s.shrink.pointAlgebra V v) (s.quadrupleRestriction.restrict k u v hv)
        (s.quadrupleRestriction.isIso_restrict_app k u v hv) (s.projMap y)
        (s.projMap_eq_of_liesOver hv hy) :=
  rfl

/-! ### The same, in the spelling of the scheme points of `X` -/

/-- `AlgebraicGeometry.Space.RelativeProjSituation.projMap`, between the relative homogeneous
spectra of the restrictions of
`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjPoints`. -/
abbrev pointProjMap {U V : BigFppfOver s.site s.base s.containsBase} {u : yoneda.obj U ⟶ s.space.1}
    {v : yoneda.obj V ⟶ s.space.1}
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u) :
    (relativeProj (s.relativeProjPoints.algebra V v)).scheme ⟶
      (relativeProj (s.relativeProjPoints.algebra U u)).scheme :=
  s.projMap y

/-- `AlgebraicGeometry.Space.RelativeProjSituation.projMap_eq_of_liesOver`, in the spelling of the
scheme points of `X`. -/
theorem pointProjMap_eq_of_liesOver {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} {k : V ⟶ U}
    (hv : yoneda.map k ≫ u = v)
    {y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u}
    (hy : s.relativeProjPoints.LiesOver y k) :
    s.pointProjMap y =
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relativeProjCongr
        (A₁ := (s.relativeProjPoints.algebra V v))
        (A₂ := (s.relativeProjPoints.algebra U u).pullback
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map k))
        (s.quadrupleRestriction.restrict k u v hv)
        (s.quadrupleRestriction.isIso_restrict_app k u v hv)).hom ≫
      Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
        (s.relativeProjPoints.algebra U u)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map k) :=
  s.toScheme_map_eq_of_liesOver hv hy

/-- `AlgebraicGeometry.Space.RelativeProjSituation.projMap_comp_toBase_of_liesOver`, in the
spelling of the scheme points of `X`. -/
theorem pointProjMap_comp_toBase_of_liesOver {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} {k : V ⟶ U}
    (hv : yoneda.map k ≫ u = v)
    {y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u}
    (hy : s.relativeProjPoints.LiesOver y k) :
    s.pointProjMap y ≫ (relativeProj (s.relativeProjPoints.algebra U u)).toBase =
      (relativeProj (s.relativeProjPoints.algebra V v)).toBase ≫
        (BigFppfOver.toScheme s.site s.base s.containsBase).map k :=
  s.toScheme_map_comp_toBase_of_liesOver hv hy

/-- The restriction map of the quadruples along `k : V ⟶ U`, between the restrictions of
`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjPoints`. -/
abbrev relativeProjPointsRestrict {U V : BigFppfOver s.site s.base s.containsBase} (k : V ⟶ U)
    (u : yoneda.obj U ⟶ s.space.1) (v : yoneda.obj V ⟶ s.space.1) (hv : yoneda.map k ≫ u = v) :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra
        (s.relativeProjPoints.algebra V v))
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra
        ((s.relativeProjPoints.algebra U u).pullback
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map k))) :=
  s.quadrupleRestriction.restrict k u v hv

/-- `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjPointsRestrict` is an isomorphism in
every degree. -/
theorem isIso_relativeProjPointsRestrict_app
    {U V : BigFppfOver s.site s.base s.containsBase} (k : V ⟶ U)
    (u : yoneda.obj U ⟶ s.space.1) (v : yoneda.obj V ⟶ s.space.1) (hv : yoneda.map k ≫ u = v)
    (n : ℤ) : IsIso ((s.relativeProjPointsRestrict k u v hv).app n) :=
  s.quadrupleRestriction.isIso_restrict_app k u v hv n

/-- `AlgebraicGeometry.Space.RelativeProjSituation.pointProjMap_eq_of_liesOver`, through
`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjPointsRestrict`. -/
theorem pointProjMap_eq_relativeProjCongr_relativeProjPointsRestrict
    {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} {k : V ⟶ U}
    (hv : yoneda.map k ≫ u = v)
    {y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u}
    (hy : s.relativeProjPoints.LiesOver y k) :
    s.pointProjMap y =
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relativeProjCongr
        (A₁ := s.relativeProjPoints.algebra V v)
        (A₂ := (s.relativeProjPoints.algebra U u).pullback
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map k))
        (s.relativeProjPointsRestrict k u v hv)
        (s.isIso_relativeProjPointsRestrict_app k u v hv)).hom ≫
      Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
        (s.relativeProjPoints.algebra U u)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map k) :=
  s.pointProjMap_eq_of_liesOver hv hy

/-- `AlgebraicGeometry.Space.RelativeProjSituation.map_comp_toRelativeProj`, through
`AlgebraicGeometry.Space.RelativeProjSituation.pointProjMap`. -/
theorem map_comp_toRelativeProj_pointProjMap {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1}
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map y ≫ s.toRelativeProj U u =
      s.toRelativeProj V v ≫ s.pointProjMap y :=
  s.map_comp_toRelativeProj y


open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (congrHom) in
/-- The identification `k^*(u^*𝒜)_d ≅ (v^*𝒜)_d` of the restrictions of the pieces along a
morphism `k : V ⟶ U` with `v = u ∘ k`, inverse to the restriction map of the quadruples. -/
def restrictPointPieceIso {U V : BigFppfOver s.site s.base s.containsBase} (k : V ⟶ U)
    (u : yoneda.obj U ⟶ s.space.1) (v : yoneda.obj V ⟶ s.space.1) (hv : yoneda.map k ≫ u = v)
    (d : ℕ) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map k)).obj
        ((s.relativeProjPoints.algebra U u).piece (d : ℤ)) ≅
      (s.relativeProjPoints.algebra V v).piece (d : ℤ) :=
  (@asIso _ _ _ _
    ((congrHom (A₁ := s.relativeProjPoints.algebra V v)
      (A₂ := (s.relativeProjPoints.algebra U u).pullback
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map k))
      (s.relativeProjPointsRestrict k u v hv)).app (d : ℤ))
    (s.isIso_relativeProjPointsRestrict_app k u v hv d)).symm

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (congrHom) in
/-- The inverse of `AlgebraicGeometry.Space.RelativeProjSituation.restrictPointPieceIso` is the
restriction map of the quadruples. -/
theorem restrictPointPieceIso_inv {U V : BigFppfOver s.site s.base s.containsBase} (k : V ⟶ U)
    (u : yoneda.obj U ⟶ s.space.1) (v : yoneda.obj V ⟶ s.space.1) (hv : yoneda.map k ≫ u = v)
    (d : ℕ) :
    (s.restrictPointPieceIso k u v hv d).inv =
      (congrHom (A₁ := s.relativeProjPoints.algebra V v)
        (A₂ := (s.relativeProjPoints.algebra U u).pullback
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map k))
        (s.relativeProjPointsRestrict k u v hv)).app (d : ℤ) :=
  rfl

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (psiU) in
/-- **The comparison of twists along a morphism lying over `k` on the homogeneous sections**: it
carries the inverse image of `ψ(a)` to `ψ` of the restriction of `a`. -/
theorem liesOverTwistComparison_hom_app_pullbackSection_psiU
    {U V : BigFppfOver s.site s.base s.containsBase} (k : V ⟶ U) (u : yoneda.obj U ⟶ s.space.1)
    (v : yoneda.obj V ⟶ s.space.1) (hv : yoneda.map k ≫ u = v)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : s.relativeProjPoints.LiesOver y k) (d : ℕ)
    (O : ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj U).Opens)
    (a : Γ((s.shrink.pointAlgebra U u).piece (d : ℤ), O))
    (hO : (relativeProj (s.shrink.pointAlgebra V v)).toBase ⁻¹ᵁ
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k ⁻¹ᵁ O) ≤
      s.projMap y ⁻¹ᵁ ((relativeProj (s.shrink.pointAlgebra U u)).toBase ⁻¹ᵁ O)) :
    ((s.liesOverTwistComparison k u v hv y hy).hom.app (d : ℤ)).val.app
        (Opposite.op ((relativeProj (s.shrink.pointAlgebra V v)).toBase ⁻¹ᵁ
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k ⁻¹ᵁ O)))
        (Scheme.Modules.pullbackSection (s.projMap y)
          (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist (s.shrink.pointAlgebra U u) d)
          _ _ hO (psiU (s.shrink.pointAlgebra U u) d O a)) =
      psiU (s.shrink.pointAlgebra V v) d
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k ⁻¹ᵁ O)
        ((s.restrictPointPieceIso k u v hv d).hom.val.app
          (Opposite.op
            ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k ⁻¹ᵁ O))
          (Scheme.Modules.pullbackSection
            ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
            ((s.shrink.pointAlgebra U u).piece (d : ℤ)) O _ le_rfl a)) :=
  Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.hom_app_pullbackSection_psiU_of_app_eq
    (s.shrink.pointAlgebra U u)
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
    (A₁ := s.shrink.pointAlgebra V v)
    (s.quadrupleRestriction.restrict k u v hv) (s.quadrupleRestriction.isIso_restrict_app k u v hv)
    (s.projMap y) (s.projMap_eq_of_liesOver hv hy) (s.liesOverTwistComparison_eq k u v hv y hy)
    (s.restrictPointPieceIso_inv k u v hv) d O a hO

/-- Composites through `AlgebraicGeometry.Space.pullbackIsoOfSquare` depend only on the
comparison `T`. -/
private theorem comp_pullbackIsoOfSquare_hom_comp_congr {X' X Y' Y : Scheme.{u}} {ιX : X' ⟶ X}
    {ιY : Y' ⟶ Y} {y : Y' ⟶ X'} {pc : Y ⟶ X} {e e' : y ≫ ιX = ιY ≫ pc} {M : X.Modules}
    {M' : Y.Modules} {T T' : (Scheme.Modules.pullback pc).obj M ≅ M'} (hT : T = T')
    {N₀ : Y'.Modules} {N₁ : Y'.Modules}
    (a : N₀ ⟶ (Scheme.Modules.pullback y).obj ((Scheme.Modules.pullback ιX).obj M))
    (b : (Scheme.Modules.pullback ιY).obj M' ⟶ N₁) :
    a ≫ (pullbackIsoOfSquare ιX ιY y pc e T).hom ≫ b =
      a ≫ (pullbackIsoOfSquare ιX ιY y pc e' T').hom ≫ b := by
  subst hT
  rfl

end Generic

/-! ### The same, in the spelling of the scheme points of the base -/

section MapPoint

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {𝒜 : SheafOfModules.GradedAlgebra.{u, m, u, u + 1} (structureRingSheaf B S hS X)}
  (hc : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜.piece i).val.obj U)
    (b : (𝒜.piece j).val.obj U), HEq ((𝒜.mul i j).app U a b) ((𝒜.mul j i).app U b a))
  (hn : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜.piece n))
  (hq : ∀ n : ℤ, (𝒜.piece n).IsQuasicoherentOnSite)
  (hk : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜.piece n).val.obj U) B.cutoff)

local notation "𝔰" => RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hk

/-- `AlgebraicGeometry.Space.RelativeProjSituation.pointProjMap`, for Situation 0849 over the base
site. -/
abbrev basePointProjMap {U V : BigFppfOver B S hS} {u : yoneda.obj U ⟶ X.1} {v : yoneda.obj V ⟶ X.1}
    (y : @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v ⟶
      @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u) :
    (relativeProj (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v)).scheme ⟶
      (relativeProj
      (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u)).scheme :=
  (𝔰).pointProjMap y

/-- The restriction map of the quadruples along `k : V ⟶ U`, for Situation 0849 over the base
site. -/
abbrev basePointRestrict {U V : BigFppfOver B S hS} (k : V ⟶ U) (u : yoneda.obj U ⟶ X.1)
    (v : yoneda.obj V ⟶ X.1) (hv : yoneda.map k ≫ u = v) :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra
      (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v))
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra
        ((@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u).pullback
          ((BigFppfOver.toScheme B S hS).map k))) :=
  (𝔰).relativeProjPointsRestrict k u v hv

/-- The restriction map of the quadruples is an isomorphism in every degree. -/
theorem isIso_basePointRestrict_app {U V : BigFppfOver B S hS} (k : V ⟶ U)
    (u : yoneda.obj U ⟶ X.1) (v : yoneda.obj V ⟶ X.1) (hv : yoneda.map k ≫ u = v) (n : ℤ) :
    IsIso ((basePointRestrict hc hn hq hk k u v hv).app n) :=
  (𝔰).isIso_relativeProjPointsRestrict_app k u v hv n

/-- `AlgebraicGeometry.Space.RelativeProjSituation.pointProjMap_eq_of_liesOver`, for Situation 0849
over the base site. -/
theorem basePointProjMap_eq_of_liesOver {U V : BigFppfOver B S hS} {u : yoneda.obj U ⟶ X.1}
    {v : yoneda.obj V ⟶ X.1} {k : V ⟶ U} (hv : yoneda.map k ≫ u = v)
    {y : @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v ⟶
      @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u}
      (hy : @RelativeProjPoints.LiesOver B S hS X.1 _ _ (𝔰).relativeProjPoints _ _ _ _ y k) :
    basePointProjMap hc hn hq hk y =
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relativeProjCongr
        (A₁ := @RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v)
        (A₂ := (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u).pullback
          ((BigFppfOver.toScheme B S hS).map k))
        (basePointRestrict hc hn hq hk k u v hv)
        (isIso_basePointRestrict_app hc hn hq hk k u v hv)).hom ≫
      Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
        (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u)
        ((BigFppfOver.toScheme B S hS).map k) :=
  (𝔰).pointProjMap_eq_relativeProjCongr_relativeProjPointsRestrict hv hy

/-- `AlgebraicGeometry.Space.RelativeProjSituation.pointProjMap_comp_toBase_of_liesOver`, for
Situation 0849 over the base site. -/
theorem basePointProjMap_comp_toBase_of_liesOver {U V : BigFppfOver B S hS}
    {u : yoneda.obj U ⟶ X.1} {v : yoneda.obj V ⟶ X.1} {k : V ⟶ U} (hv : yoneda.map k ≫ u = v)
    {y : @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v ⟶
      @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u}
      (hy : @RelativeProjPoints.LiesOver B S hS X.1 _ _ (𝔰).relativeProjPoints _ _ _ _ y k) :
    basePointProjMap hc hn hq hk y ≫
      (relativeProj
      (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u)).toBase =
      (relativeProj
        (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v)).toBase ≫
        (BigFppfOver.toScheme B S hS).map k :=
  (𝔰).pointProjMap_comp_toBase_of_liesOver hv hy

/-- `AlgebraicGeometry.Space.RelativeProjSituation.liesOverTwistComparison`, for Situation 0849
over the base site. -/
abbrev baseLiesOverTwistComparison {U V : BigFppfOver B S hS} (k : V ⟶ U) (u : yoneda.obj U ⟶ X.1)
    (v : yoneda.obj V ⟶ X.1) (hv : yoneda.map k ≫ u = v)
    (y : @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v ⟶
      @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u)
    (hy : @RelativeProjPoints.LiesOver B S hS X.1 _ _ (𝔰).relativeProjPoints _ _ _ _ y k) :
    Stacks.RingedSpace.pullbackGradedAlgebra (basePointProjMap hc hn hq hk y).toLRSHom.toShHom
        (Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra
          (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u)) ≅
      Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra
        (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v) :=
  (𝔰).liesOverTwistComparison k u v hv y hy

/-- `AlgebraicGeometry.Space.RelativeProjSituation.baseLiesOverTwistComparison` is the comparison
of twists along a restriction followed by a base change. -/
theorem baseLiesOverTwistComparison_eq {U V : BigFppfOver B S hS} (k : V ⟶ U)
    (u : yoneda.obj U ⟶ X.1) (v : yoneda.obj V ⟶ X.1) (hv : yoneda.map k ≫ u = v)
    (y : @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v ⟶
      @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u)
    (hy : @RelativeProjPoints.LiesOver B S hS X.1 _ _ (𝔰).relativeProjPoints _ _ _ _ y k) :
    baseLiesOverTwistComparison hc hn hq hk k u v hv y hy =
      Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.congrBaseChangeTwistIso
        (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u)
        ((BigFppfOver.toScheme B S hS).map k)
        (A₁ := @RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v)
        (basePointRestrict hc hn hq hk k u v hv)
        (isIso_basePointRestrict_app hc hn hq hk k u v hv) (basePointProjMap hc hn hq hk y)
        (basePointProjMap_eq_of_liesOver hc hn hq hk hv hy) :=
  rfl

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (psiU) in
/-- **The comparison of twists along a morphism lying over `k` on the homogeneous sections**, for
Situation 0849 over the base site: the input `χ_A` of
`Stacks.AlgebraicGeometry.Tag07ZGTwist.transportTwistHom_relativeTwistAlgebraHom`. -/
theorem baseLiesOverTwistComparison_hom_app_pullbackSection_psiU {U V : BigFppfOver B S hS}
    (k : V ⟶ U) (u : yoneda.obj U ⟶ X.1) (v : yoneda.obj V ⟶ X.1) (hv : yoneda.map k ≫ u = v)
    (y : @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v ⟶
      @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u)
    (hy : @RelativeProjPoints.LiesOver B S hS X.1 _ _ (𝔰).relativeProjPoints _ _ _ _ y k) (d : ℕ)
    (O : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (a : Γ((@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u).piece (d : ℤ),
        O))
    (hO : (relativeProj
        (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v)).toBase ⁻¹ᵁ
      ((BigFppfOver.toScheme B S hS).map k ⁻¹ᵁ O) ≤
      basePointProjMap hc hn hq hk y ⁻¹ᵁ
        ((relativeProj
          (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u)).toBase ⁻¹ᵁ O)) :
    ((baseLiesOverTwistComparison hc hn hq hk k u v hv y hy).hom.app (d : ℤ)).val.app
        (Opposite.op
          ((relativeProj
              (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v)).toBase ⁻¹ᵁ
            ((BigFppfOver.toScheme B S hS).map k ⁻¹ᵁ O)))
        (Scheme.Modules.pullbackSection (basePointProjMap hc hn hq hk y)
          (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist
            (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u) d)
          _ _ hO
            (psiU (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u) d O a)) =
      psiU (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v) d
        ((BigFppfOver.toScheme B S hS).map k ⁻¹ᵁ O)
        (((𝔰).restrictPointPieceIso k u v hv d).hom.val.app
          (Opposite.op ((BigFppfOver.toScheme B S hS).map k ⁻¹ᵁ O))
          (Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map k)
            ((@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u).piece (d : ℤ))
            O _ le_rfl a)) :=
  Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.hom_app_pullbackSection_psiU_of_app_eq
    (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u)
    ((BigFppfOver.toScheme B S hS).map k)
    (A₁ := @RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v)
    (basePointRestrict hc hn hq hk k u v hv) (isIso_basePointRestrict_app hc hn hq hk k u v hv)
    (basePointProjMap hc hn hq hk y) (basePointProjMap_eq_of_liesOver hc hn hq hk hv hy)
    (baseLiesOverTwistComparison_eq hc hn hq hk k u v hv y hy)
    ((𝔰).restrictPointPieceIso_inv k u v hv) d O a hO

/-- `AlgebraicGeometry.Space.RelativeProjSituation.map_comp_toRelativeProj`, for Situation 0849
over the base site. -/
theorem map_comp_toRelativeProj_basePointProjMap {U V : BigFppfOver B S hS}
    {u : yoneda.obj U ⟶ X.1} {v : yoneda.obj V ⟶ X.1}
      (y : @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v ⟶
      @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u) :
    (BigFppfOver.toScheme B S hS).map y ≫ (𝔰).toRelativeProj U u =
      (𝔰).toRelativeProj V v ≫ basePointProjMap hc hn hq hk y :=
  (𝔰).map_comp_toRelativeProj_pointProjMap y

/-- The degree-`n` piece of
`AlgebraicGeometry.Space.RelativeProjSituation.baseLiesOverTwistComparison` is that of
`AlgebraicGeometry.Space.RelativeProjSituation.pointTwistComparison`. -/
theorem gradedPieceIso_baseLiesOverTwistComparison {U V : BigFppfOver B S hS} (k : V ⟶ U)
    (u : yoneda.obj U ⟶ X.1) (v : yoneda.obj V ⟶ X.1) (hv : yoneda.map k ≫ u = v)
    (y : @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v ⟶
      @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u)
    (hy : @RelativeProjPoints.LiesOver B S hS X.1 _ _ (𝔰).relativeProjPoints _ _ _ _ y k) (n : ℤ) :
    gradedPieceIso (basePointProjMap hc hn hq hk y)
      (baseLiesOverTwistComparison hc hn hq hk k u v hv y hy) n =
      gradedPieceIso (X := (relativeProj ((𝔰).shrink.pointAlgebra U u)).scheme)
        (Y := (relativeProj ((𝔰).shrink.pointAlgebra V v)).scheme) ((𝔰).projMap y)
        ((𝔰).pointTwistComparison k u v hv ((𝔰).projMap y) ((𝔰).toScheme_map_eq_of_liesOver hv hy))
        n :=
  rfl

/-- **The comparison of the twists along a morphism lying over `k`**, for Situation 0849 over the
base site, in the form of the comparisons of
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistHom_transport`, through
`AlgebraicGeometry.Space.RelativeProjSituation.baseLiesOverTwistComparison`. -/
theorem twistPieceComparison_hom_hom_eq_baseLiesOverTwistComparison {U V : BigFppfOver B S hS}
    (k : V ⟶ U) (u : yoneda.obj U ⟶ X.1) (v : yoneda.obj V ⟶ X.1) (hv hv' : yoneda.map k ≫ u = v)
    (y : @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v ⟶
      @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u)
    (hy : @RelativeProjPoints.LiesOver B S hS X.1 _ _ (𝔰).relativeProjPoints _ _ _ _ y k) (n : ℤ) :
    ((𝔰).twistPieceComparison (u := u) (v := v) k hv y hy n).hom.hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map y)).map
        (X := ((𝔰).twistPieceQcoh U u n).obj)
        (Y :=
          ((@Scheme.Modules.pullback
              ((BigFppfOver.toScheme B S hS).obj
                (@RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u))
              (relativeProj
                (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u)).scheme
              ((𝔰).toRelativeProj U u)).obj
            ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra
                (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u)).piece n)))
          (Iso.hom (X := ((𝔰).twistPieceQcoh U u n).obj)
            (Y :=
                ((@Scheme.Modules.pullback
                    ((BigFppfOver.toScheme B S hS).obj
                      (@RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u))
                    (relativeProj
                      (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U
                        u)).scheme ((𝔰).toRelativeProj U u)).obj
                  ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra
                      (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u)).piece
                    n))) ((𝔰).twistPieceQcohObjIso U u n)) ≫
        (pullbackIsoOfSquare
          (X' := (BigFppfOver.toScheme B S hS).obj
            (@RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u))
          (X :=
              (relativeProj
                (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u)).scheme)
          (Y' := (BigFppfOver.toScheme B S hS).obj
            (@RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v))
          (Y :=
              (relativeProj
                (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v)).scheme)
          ((𝔰).toRelativeProj U u) ((𝔰).toRelativeProj V v) ((BigFppfOver.toScheme B S hS).map y)
          (basePointProjMap hc hn hq hk y)
          (map_comp_toRelativeProj_basePointProjMap hc hn hq hk y)
          (gradedPieceIso (basePointProjMap hc hn hq hk y)
            (baseLiesOverTwistComparison hc hn hq hk k u v hv' y hy) n)).hom ≫
        Iso.inv (X := ((𝔰).twistPieceQcoh V v n).obj)
          (Y :=
            ((@Scheme.Modules.pullback
                ((BigFppfOver.toScheme B S hS).obj
                  (@RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v))
                (relativeProj
                  (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v)).scheme
                ((𝔰).toRelativeProj V v)).obj
              ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra
                  (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v)).piece
                n))) ((𝔰).twistPieceQcohObjIso V v n) :=
  ((𝔰).twistPieceComparison_hom_hom_eq k hv y hy n).trans
    (comp_pullbackIsoOfSquare_hom_comp_congr
      (gradedPieceIso_baseLiesOverTwistComparison hc hn hq hk k u v hv' y hy n).symm _ _)

/-- `RelativeProjSituation.twistPieceComparison_hom_hom_eq_baseLiesOverTwistComparison`, for any
comparison `a` equal to the comparison of the twists and any identifications `c`, `c'` equal to
those of the twists. -/
theorem twistPieceComparison_hom_hom_eq_of_eq {U V : BigFppfOver B S hS}
    (k : V ⟶ U) (u : yoneda.obj U ⟶ X.1) (v : yoneda.obj V ⟶ X.1) (hv hv' : yoneda.map k ≫ u = v)
    (y : @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v ⟶
      @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u)
    (hy : @RelativeProjPoints.LiesOver B S hS X.1 _ _ (𝔰).relativeProjPoints _ _ _ _ y k) (n : ℤ)
    (c : @Iso
      (SheafOfModules.{u}
        ((BigFppfOver.toScheme B S hS).obj
          (@RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u)).ringCatSheaf) _
      ((𝔰).twistPieceQcoh U u n).obj
      ((@Scheme.Modules.pullback
          ((BigFppfOver.toScheme B S hS).obj
            (@RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u))
          (relativeProj
            (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u)).scheme
          ((𝔰).toRelativeProj U u)).obj
        ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra
            (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u)).piece n)))
    (e₁ : c = (𝔰).twistPieceQcohObjIso U u n)
    (c' : @Iso
      (SheafOfModules.{u}
        ((BigFppfOver.toScheme B S hS).obj
          (@RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v)).ringCatSheaf) _
      ((𝔰).twistPieceQcoh V v n).obj
      ((@Scheme.Modules.pullback
          ((BigFppfOver.toScheme B S hS).obj
            (@RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v))
          (relativeProj
            (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v)).scheme
          ((𝔰).toRelativeProj V v)).obj
        ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra
            (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v)).piece n)))
    (e₂ : c' = (𝔰).twistPieceQcohObjIso V v n)
    (a : quasicoherentPullbackObj B S hS y ((𝔰).twistPieceQcoh U u n) ≅ (𝔰).twistPieceQcoh V v n)
    (e₃ : a = (𝔰).twistPieceComparison (u := u) (v := v) k hv y hy n) :
    a.hom.hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map y)).map c.hom ≫
        (pullbackIsoOfSquare
          (X' := (BigFppfOver.toScheme B S hS).obj
            (@RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints U u))
          (X :=
              (relativeProj
                (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints U u)).scheme)
          (Y' := (BigFppfOver.toScheme B S hS).obj
            (@RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰).relativeProjPoints V v))
          (Y :=
              (relativeProj
                (@RelativeProjPoints.algebra B S hS X.1 _ _ (𝔰).relativeProjPoints V v)).scheme)
          ((𝔰).toRelativeProj U u) ((𝔰).toRelativeProj V v) ((BigFppfOver.toScheme B S hS).map y)
          (basePointProjMap hc hn hq hk y)
          (map_comp_toRelativeProj_basePointProjMap hc hn hq hk y)
          (gradedPieceIso (basePointProjMap hc hn hq hk y)
            (baseLiesOverTwistComparison hc hn hq hk k u v hv' y hy) n)).hom ≫ c'.inv := by
  subst e₁ e₂ e₃
  exact twistPieceComparison_hom_hom_eq_baseLiesOverTwistComparison hc hn hq hk k u v hv hv' y hy n

end MapPoint

section Map

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {𝒜₁ 𝒜₂ : SheafOfModules.GradedAlgebra.{u, m, u, u + 1} (structureRingSheaf B S hS X)}
  (h₁c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₁.piece i).val.obj U)
    (b : (𝒜₁.piece j).val.obj U), HEq ((𝒜₁.mul i j).app U a b) ((𝒜₁.mul j i).app U b a))
  (h₁n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₁.piece n))
  (h₁q : ∀ n : ℤ, (𝒜₁.piece n).IsQuasicoherentOnSite)
  (h₁k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₁.piece n).val.obj U) B.cutoff)
  (h₂c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₂.piece i).val.obj U)
    (b : (𝒜₂.piece j).val.obj U), HEq ((𝒜₂.mul i j).app U a b) ((𝒜₂.mul j i).app U b a))
  (h₂n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₂.piece n))
  (h₂q : ∀ n : ℤ, (𝒜₂.piece n).IsQuasicoherentOnSite)
  (h₂k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₂.piece n).val.obj U) B.cutoff)
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₁ 𝒜₂)

local notation "𝔰₁" => RelativeProjSituation.mk B S hS X 𝒜₁ h₁c h₁n h₁q h₁k
local notation "𝔰₂" => RelativeProjSituation.mk B S hS X 𝒜₂ h₂c h₂n h₂q h₂k
local notation "𝔥" => homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ

/-- **The map `θ` of Tag 07ZG at a restricted point is the transport of `θ`**: along a morphism
`k : V ⟶ U` of test objects with `v = u ∘ k` and morphisms `y_P`, `y_Q` of base changes lying over
`k`, the map `θ` for `ψ|_V` is the transport of `θ` for `ψ|_U` along any `k'` between the opens
`U(ψ|_V)` and `U(ψ|_U)` lying over the morphisms of relative Projs underlying `y_P`, `y_Q`,
through the comparisons of twists along `y_P` and `y_Q`. -/
theorem relativeTwistAlgebraHom_eq_transportTwistHom {U V : BigFppfOver B S hS} (k : V ⟶ U)
    (u : yoneda.obj U ⟶ X.1) (v : yoneda.obj V ⟶ X.1) (hv : yoneda.map k ≫ u = v)
    (yP : @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰₁).relativeProjPoints V v ⟶
      @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰₁).relativeProjPoints U u)
    (hyP : @RelativeProjPoints.LiesOver B S hS X.1 _ _ (𝔰₁).relativeProjPoints _ _ _ _ yP k)
    (yQ : @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰₂).relativeProjPoints V v ⟶
      @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰₂).relativeProjPoints U u)
    (hyQ : @RelativeProjPoints.LiesOver B S hS X.1 _ _ (𝔰₂).relativeProjPoints _ _ _ _ yQ k)
    (kk : ((𝔥).hom V v).relativeMapDomain.toScheme ⟶ ((𝔥).hom U u).relativeMapDomain.toScheme)
    (hr : relativeMapHom ((𝔥).hom V v) ≫ basePointProjMap h₁c h₁n h₁q h₁k yP =
      kk ≫ relativeMapHom ((𝔥).hom U u))
    (hι : kk ≫ ((𝔥).hom U u).relativeMapDomain.ι =
      ((𝔥).hom V v).relativeMapDomain.ι ≫ basePointProjMap h₂c h₂n h₂q h₂k yQ) :
    Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom ((𝔥).hom V v) =
      Stacks.AlgebraicGeometry.Tag07ZGTwist.transportTwistHom ((𝔥).hom U u) ((𝔥).hom V v)
        (baseLiesOverTwistComparison h₁c h₁n h₁q h₁k k u v hv yP hyP)
        (baseLiesOverTwistComparison h₂c h₂n h₂q h₂k k u v hv yQ hyQ) kk hr hι
        (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom ((𝔥).hom U u)) := by
  refine (Stacks.AlgebraicGeometry.Tag07ZGTwist.transportTwistHom_relativeTwistAlgebraHom
    ((𝔥).hom U u) ((BigFppfOver.toScheme B S hS).map k) ((𝔥).hom V v) _ _ kk hr hι
    (basePointProjMap_comp_toBase_of_liesOver h₁c h₁n h₁q h₁k hv hyP)
    (basePointProjMap_comp_toBase_of_liesOver h₂c h₂n h₂q h₂k hv hyQ)
    ((𝔰₁).restrictPointPieceIso k u v hv) ((𝔰₂).restrictPointPieceIso k u v hv)
    ?_ (baseLiesOverTwistComparison_hom_app_pullbackSection_psiU h₁c h₁n h₁q h₁k k u v hv yP hyP)
    (baseLiesOverTwistComparison_hom_app_pullbackSection_psiU h₂c h₂n h₂q h₂k k u v hv yQ hyQ)).symm
  subst hv
  exact fun d => asIso_symm_hom_comp_eq _ _
    (restrictHom_comp_restrict_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ k u d)

/-- **The chart maps `θ_n` commute with the legs of the transitions of the twists**: for a
square `t'` of charts of `U(ψ)` over morphisms `y_P`, `y_Q` of base changes lying over `k`, the leg
of the comparison of the twists along `y_P` followed by `θ_n` on the second chart is the pullback
of `θ_n` on the first chart followed by the leg of the comparison along `y_Q`. -/
theorem twistChartMap_leg {T T' : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X.1)
    (f' : yoneda.obj T' ⟶ X.1) (k : T' ⟶ T) (hv : yoneda.map k ≫ f = f')
    (t' : (𝔥).chartObj T' f' ⟶ (𝔥).chartObj T f)
    (yP : @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰₁).relativeProjPoints T' f' ⟶
      @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰₁).relativeProjPoints T f)
    (hyP' : @RelativeProjPoints.LiesOver B S hS X.1 _ _ (𝔰₁).relativeProjPoints _ _ _ _ yP k)
    (yQ : @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰₂).relativeProjPoints T' f' ⟶
      @RelativeProjPoints.fibre B S hS X.1 _ _ (𝔰₂).relativeProjPoints T f)
    (hyQ' : @RelativeProjPoints.LiesOver B S hS X.1 _ _ (𝔰₂).relativeProjPoints _ _ _ _ yQ k)
    (ht₁ : t' ≫ (𝔥).chartMapHom T f = (𝔥).chartMapHom T' f' ≫ yP)
    (ht₂ : t' ≫ (𝔥).chartIncl T f = (𝔥).chartIncl T' f' ≫ yQ) (n : ℤ) :
    (schemeTransitionLeg yP t' ((𝔥).chartMapHom T f) ((𝔥).chartMapHom T' f') ht₁
        ((𝔰₁).twistPieceComparison (u := f) (v := f') k hv yP hyP' n)).hom ≫ twistChartMap h₁c h₁n
          h₁q h₁k h₂c h₂n h₂q h₂k ψ T' f' n =
      quasicoherentPullbackMap B S hS t' (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ T f n) ≫
        (schemeTransitionLeg yQ t' ((𝔥).chartIncl T f) ((𝔥).chartIncl T' f') ht₂
          ((𝔰₂).twistPieceComparison (u := f) (v := f') k hv yQ hyQ' n)).hom := by
  have hr := (𝔥).relativeMapHom_comp_of_chartSquare (X := X) t' yP ht₁ ((𝔰₁).toRelativeProj T f)
    ((𝔰₁).toRelativeProj_eq_fibreIso_hom T f) ((𝔰₁).toRelativeProj T' f')
    ((𝔰₁).toRelativeProj_eq_fibreIso_hom T' f')
    (map_comp_toRelativeProj_basePointProjMap h₁c h₁n h₁q h₁k yP)
  have hι := (𝔥).comp_ι_of_chartSquare (X := X) t' yQ ht₂ ((𝔰₂).toRelativeProj T f)
    ((𝔰₂).toRelativeProj_eq_fibreIso_hom T f) ((𝔰₂).toRelativeProj T' f')
    ((𝔰₂).toRelativeProj_eq_fibreIso_hom T' f')
    (map_comp_toRelativeProj_basePointProjMap h₂c h₂n h₂q h₂k yQ)
  refine (𝔥).schemeTransitionLeg_hom_comp_chartTwistMap (X := X) (T := T) (f := f) (n := n)
      (p := ((𝔰₁).toRelativeProj T f)) (hp := ((𝔰₁).toRelativeProj_eq_fibreIso_hom T f))
      (c₁ := (𝔰₁).twistPieceQcohObjIso T f n)
      (q := ((𝔰₂).toRelativeProj T f)) (hq := ((𝔰₂).toRelativeProj_eq_fibreIso_hom T f))
      (c₂ := (𝔰₂).twistPieceQcohObjIso T f n)
      (T' := T') (f' := f') (t' := t') (yP := yP) (yQ := yQ) (ht₁ := ht₁) (ht₂ := ht₂)
      (p' := ((𝔰₁).toRelativeProj T' f')) (hp' := ((𝔰₁).toRelativeProj_eq_fibreIso_hom T' f'))
      (c₁' := (𝔰₁).twistPieceQcohObjIso T' f' n)
      (q' := ((𝔰₂).toRelativeProj T' f')) (hq' := ((𝔰₂).toRelativeProj_eq_fibreIso_hom T' f'))
      (c₂' := (𝔰₂).twistPieceQcohObjIso T' f' n)
      (a₁ := (𝔰₁).twistPieceComparison (u := f) (v := f') k hv yP hyP' n)
      (a₂ := (𝔰₂).twistPieceComparison (u := f) (v := f') k hv yQ hyQ' n)
      (χA := baseLiesOverTwistComparison h₁c h₁n h₁q h₁k k f f' hv yP hyP')
      (χB := baseLiesOverTwistComparison h₂c h₂n h₂q h₂k k f f' hv yQ hyQ')
      (hyP := (map_comp_toRelativeProj_basePointProjMap h₁c h₁n h₁q h₁k yP))
      (hyQ := (map_comp_toRelativeProj_basePointProjMap h₂c h₂n h₂q h₂k yQ))
      (k := (((𝔥).chartSchemeIso T' f').inv ≫ (BigFppfOver.toScheme B S hS).map t' ≫
            ((𝔥).chartSchemeIso T f).hom))
      (hr := hr) (hι := hι) ?_ ?_ ?_ ?_
  · exact Iso.hom_inv_id_assoc _ _
  · exact twistPieceComparison_hom_hom_eq_of_eq h₁c h₁n h₁q h₁k k f f' hv hv yP hyP' n
      _ rfl _ rfl _ rfl
  · exact twistPieceComparison_hom_hom_eq_of_eq h₂c h₂n h₂q h₂k k f f' hv hv yQ hyQ' n
      _ rfl _ rfl _ rfl
  · exact relativeTwistAlgebraHom_eq_transportTwistHom h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ k f f' hv
      yP hyP' yQ hyQ'
      (((𝔥).chartSchemeIso T' f').inv ≫ (BigFppfOver.toScheme B S hS).map t' ≫
        ((𝔥).chartSchemeIso T f).hom) hr hι

variable (Px : Presentation B S hS X.1 X.2)

local notation "𝒢" => relativeMapSpace h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ

/-- The source projection of the presentation of `P` lies over the source projection of the
relation, in the spelling of the scheme points of the base. -/
theorem liesOver_baseSpaceSource₁ :
    @RelativeProjPoints.LiesOver B S hS X.1 _ _ (𝔰₁).relativeProjPoints _ _ _ _
      (@RelativeProjPoints.spaceSource B S hS X _ _ (𝔰₁).relativeProjPoints Px
        (𝔰₁).isAlgebraicSpace_relativeProjFunctor) Px.source :=
  (𝔰₁).relativeProjPoints.liesOver_spaceSource Px (𝔰₁).isAlgebraicSpace_relativeProjFunctor

/-- The source projection of the presentation of `P` lies over the source projection of the
relation, in the spelling of the scheme points of the base. -/
theorem liesOver_baseSpaceSource₂ :
    @RelativeProjPoints.LiesOver B S hS X.1 _ _ (𝔰₂).relativeProjPoints _ _ _ _
      (@RelativeProjPoints.spaceSource B S hS X _ _ (𝔰₂).relativeProjPoints Px
        (𝔰₂).isAlgebraicSpace_relativeProjFunctor) Px.source :=
  (𝔰₂).relativeProjPoints.liesOver_spaceSource Px (𝔰₂).isAlgebraicSpace_relativeProjFunctor

/-- **The chart maps `θ_n` of Tag 07ZG are compatible with the transitions of the twists**
`𝒪_P(n)` and `𝒪_Q(n)` along the presentation of `X`. -/
theorem chartTransitionsCompatible_twistChartMap (n : ℤ) :
    (𝔥).ChartTransitionsCompatible Px (𝒢).2 (𝔰₁).isAlgebraicSpace_relativeProjFunctor
      (𝔰₂).isAlgebraicSpace_relativeProjFunctor ((𝔰₁).twistPieceQcoh Px.U Px.toSpace n)
      ((𝔰₁).twistTransition Px n) ((𝔰₂).twistPieceQcoh Px.U Px.toSpace n)
      ((𝔰₂).twistTransition Px n)
      (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.U Px.toSpace n) :=
  (𝔥).chartTransitionsCompatible_of_chartLegs (X := X) Px (𝒢).2
    (𝔰₁).isAlgebraicSpace_relativeProjFunctor
    (𝔰₂).isAlgebraicSpace_relativeProjFunctor
    ((𝔰₁).twistPieceComparison (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px)
      Px.target rfl
        ((𝔰₁).relativeProjPoints.spaceTarget Px (𝔰₁).isAlgebraicSpace_relativeProjFunctor)
      ((𝔰₁).relativeProjPoints.liesOver_spaceTarget Px (𝔰₁).isAlgebraicSpace_relativeProjFunctor) n)
    ((𝔰₁).twistPieceComparison (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px)
      Px.source ((𝔰₁).map_source_comp_toSpace Px)
      ((𝔰₁).relativeProjPoints.spaceSource Px (𝔰₁).isAlgebraicSpace_relativeProjFunctor)
      ((𝔰₁).relativeProjPoints.liesOver_spaceSource Px (𝔰₁).isAlgebraicSpace_relativeProjFunctor) n)
    ((𝔰₂).twistPieceComparison (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px)
      Px.target rfl
        ((𝔰₂).relativeProjPoints.spaceTarget Px (𝔰₂).isAlgebraicSpace_relativeProjFunctor)
      ((𝔰₂).relativeProjPoints.liesOver_spaceTarget Px (𝔰₂).isAlgebraicSpace_relativeProjFunctor) n)
    ((𝔰₂).twistPieceComparison (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px)
      Px.source ((𝔰₂).map_source_comp_toSpace Px)
      ((𝔰₂).relativeProjPoints.spaceSource Px (𝔰₂).isAlgebraicSpace_relativeProjFunctor)
      ((𝔰₂).relativeProjPoints.liesOver_spaceSource Px (𝔰₂).isAlgebraicSpace_relativeProjFunctor) n)
    (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.U Px.toSpace n)
    (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.R (RelativeProjPoints.relationPoint Px) n)
    (fun t' ht₁ ht₂ => twistChartMap_leg h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.toSpace
      (RelativeProjPoints.relationPoint Px) Px.target rfl t'
      ((𝔰₁).relativeProjPoints.spaceTarget Px (𝔰₁).isAlgebraicSpace_relativeProjFunctor)
      ((𝔰₁).relativeProjPoints.liesOver_spaceTarget Px (𝔰₁).isAlgebraicSpace_relativeProjFunctor)
      ((𝔰₂).relativeProjPoints.spaceTarget Px (𝔰₂).isAlgebraicSpace_relativeProjFunctor)
      ((𝔰₂).relativeProjPoints.liesOver_spaceTarget Px (𝔰₂).isAlgebraicSpace_relativeProjFunctor)
      ht₁ ht₂ n)
    (fun t' ht₁ ht₂ => twistChartMap_leg h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.toSpace
      (RelativeProjPoints.relationPoint Px) Px.source ((𝔰₁).map_source_comp_toSpace Px) t'
      (@RelativeProjPoints.spaceSource B S hS X _ _ (𝔰₁).relativeProjPoints Px
        (𝔰₁).isAlgebraicSpace_relativeProjFunctor) (liesOver_baseSpaceSource₁ h₁c h₁n h₁q h₁k Px)
      (@RelativeProjPoints.spaceSource B S hS X _ _ (𝔰₂).relativeProjPoints Px
        (𝔰₂).isAlgebraicSpace_relativeProjFunctor) (liesOver_baseSpaceSource₂ h₂c h₂n h₂q h₂k Px)
      ht₁ ht₂ n)

/-- **The map `θ_n : r_ψ^*𝒪_P(n) ⟶ ι^*𝒪_Q(n)` of Stacks 085F**: the morphism glued from the chart
maps `θ_n` of Tag 07ZG over the scheme points of `X`, along the presentation `Px` of `X`. -/
def twistMap (n : ℤ) :
    (modulePullback B S hS (ObjectProperty.homMk (𝔥).relativeMapSpaceHom :
        (⟨(𝔥).relativeMapSubfunctor.toFunctor, (𝒢).2⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨_, (𝔰₁).isAlgebraicSpace_relativeProjFunctor⟩)).obj
        ((𝔰₁).twistModule Px n).obj ⟶
      (modulePullback B S hS (ObjectProperty.homMk (𝔥).relativeMapSubfunctor.ι :
        (⟨(𝔥).relativeMapSubfunctor.toFunctor, (𝒢).2⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨_, (𝔰₂).isAlgebraicSpace_relativeProjFunctor⟩)).obj
        ((𝔰₂).twistModule Px n).obj :=
  (𝔥).descendedChartHom Px (𝒢).2 (𝔰₁).isAlgebraicSpace_relativeProjFunctor
    (𝔰₂).isAlgebraicSpace_relativeProjFunctor ((𝔰₁).twistPieceQcoh Px.U Px.toSpace n)
    ((𝔰₁).twistTransition Px n) ((𝔰₁).presentationSchemeCocycle_twistTransition Px n)
    ((𝔰₁).presentationSchemeUnit_twistTransition Px n)
    ((𝔰₂).twistPieceQcoh Px.U Px.toSpace n)
    ((𝔰₂).twistTransition Px n) ((𝔰₂).presentationSchemeCocycle_twistTransition Px n)
    ((𝔰₂).presentationSchemeUnit_twistTransition Px n)
    (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.U Px.toSpace n)
    (chartTransitionsCompatible_twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n)

/-- **The glued `θ_n` is the chart map `θ_n` of Tag 07ZG on the chart `U(ψ)_U`.** -/
theorem isDescendedChartHom_twistMap (n : ℤ) :
    (𝔥).IsDescendedChartHom Px (𝒢).2 (𝔰₁).isAlgebraicSpace_relativeProjFunctor
      (𝔰₂).isAlgebraicSpace_relativeProjFunctor ((𝔰₁).twistPieceQcoh Px.U Px.toSpace n)
      ((𝔰₁).twistTransition Px n) ((𝔰₁).presentationSchemeCocycle_twistTransition Px n)
      ((𝔰₁).presentationSchemeUnit_twistTransition Px n)
      ((𝔰₂).twistPieceQcoh Px.U Px.toSpace n)
      ((𝔰₂).twistTransition Px n) ((𝔰₂).presentationSchemeCocycle_twistTransition Px n)
      ((𝔰₂).presentationSchemeUnit_twistTransition Px n)
      (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.U Px.toSpace n)
      (twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n) :=
  (𝔥).isDescendedChartHom_descendedChartHom Px (𝒢).2 (𝔰₁).isAlgebraicSpace_relativeProjFunctor
    (𝔰₂).isAlgebraicSpace_relativeProjFunctor ((𝔰₁).twistPieceQcoh Px.U Px.toSpace n)
    ((𝔰₁).twistTransition Px n) ((𝔰₁).presentationSchemeCocycle_twistTransition Px n)
    ((𝔰₁).presentationSchemeUnit_twistTransition Px n)
    ((𝔰₂).twistPieceQcoh Px.U Px.toSpace n)
    ((𝔰₂).twistTransition Px n) ((𝔰₂).presentationSchemeCocycle_twistTransition Px n)
    ((𝔰₂).presentationSchemeUnit_twistTransition Px n)
    (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.U Px.toSpace n)
    (chartTransitionsCompatible_twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n)

/-- **The glued `θ_n` is the only morphism `r_ψ^*𝒪_P(n) ⟶ ι^*𝒪_Q(n)` which is the chart map `θ_n`
of Tag 07ZG on the chart `U(ψ)_U`.** -/
theorem eq_twistMap (n : ℤ) {χ}
    (hχ : (𝔥).IsDescendedChartHom Px (𝒢).2 (𝔰₁).isAlgebraicSpace_relativeProjFunctor
      (𝔰₂).isAlgebraicSpace_relativeProjFunctor ((𝔰₁).twistPieceQcoh Px.U Px.toSpace n)
      ((𝔰₁).twistTransition Px n) ((𝔰₁).presentationSchemeCocycle_twistTransition Px n)
      ((𝔰₁).presentationSchemeUnit_twistTransition Px n)
      ((𝔰₂).twistPieceQcoh Px.U Px.toSpace n)
      ((𝔰₂).twistTransition Px n) ((𝔰₂).presentationSchemeCocycle_twistTransition Px n)
      ((𝔰₂).presentationSchemeUnit_twistTransition Px n)
      (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.U Px.toSpace n) χ) :
    χ = twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n :=
  (𝔥).eq_descendedChartHom Px (𝒢).2 (𝔰₁).isAlgebraicSpace_relativeProjFunctor
    (𝔰₂).isAlgebraicSpace_relativeProjFunctor ((𝔰₁).twistPieceQcoh Px.U Px.toSpace n)
    ((𝔰₁).twistTransition Px n) ((𝔰₁).presentationSchemeCocycle_twistTransition Px n)
    ((𝔰₁).presentationSchemeUnit_twistTransition Px n)
    ((𝔰₂).twistPieceQcoh Px.U Px.toSpace n)
    ((𝔰₂).twistTransition Px n) ((𝔰₂).presentationSchemeCocycle_twistTransition Px n)
    ((𝔰₂).presentationSchemeUnit_twistTransition Px n)
    (twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px.U Px.toSpace n)
    (chartTransitionsCompatible_twistChartMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n) hχ

end Map

end RelativeProjSituation

end AlgebraicGeometry.Space

end
