module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianChartFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# Morphisms out of the space glued from a cartesian chart family

Let `X` be an algebraic space over `S` and `F` a cartesian chart family over `X`
(`AlgebraicGeometry.Space.CartesianChartFamily`), glued over a relation of charts
`pr₁, pr₂ : V' ⇉ V₂` into the algebraic space `F_X = F.quotient pr₁ pr₂ hsq`. This file records
the universal property of `F_X` among algebraic spaces and a criterion for a morphism out of it to
be an isomorphism:

* a morphism `φ : F(V₂) ⟶ Y` to an algebraic space which identifies the two morphisms
  `F(V') ⇉ F(V₂)` descends uniquely to `F_X ⟶ Y`
  (`AlgebraicGeometry.Space.CartesianChartFamily.quotientDesc`);
* if moreover `Y` lies over `X` through `q : Y ⟶ X`, `φ` lies over the chart, and the square
  `F(V₂) ⟶ Y` over `V₂ ⟶ X` is cartesian, then the descended morphism is an isomorphism over `X`
  (`AlgebraicGeometry.Space.CartesianChartFamily.isIso_quotientDesc_hom`). In words: an algebraic
  space over `X` whose restriction to the surjective chart `V₂` is `F(V₂)`, compatibly with the
  relation, is the glued space.

The second item rests on a general fact about sheaves of sets, recorded first: a morphism
`Ψ : A ⟶ Y` of sheaves over `X` is an isomorphism as soon as there are cartesian squares
`W' ⟶ A` and `W' ⟶ Y` over one locally surjective `W ⟶ X` whose tops are related by `Ψ`
(`AlgebraicGeometry.Space.isIso_of_isPullback_of_isLocallySurjective`).

## Main definitions

* `AlgebraicGeometry.Space.CartesianChartFamily.quotientDesc`: the descended morphism.

## Main results

* `AlgebraicGeometry.Space.CartesianChartFamily.quotientChart_comp_quotientDesc`: it restricts
  to `φ` on the chart.
* `AlgebraicGeometry.Space.CartesianChartFamily.hom_ext_quotient`: morphisms out of `F_X` are
  determined by their restriction to the chart.
* `AlgebraicGeometry.Space.CartesianChartFamily.quotientChart_comp_quotientHom`: the structure
  morphism `F_X ⟶ X` restricts on the chart to `F(V₂) ⟶ V₂ ⟶ X`.
* `AlgebraicGeometry.Space.CartesianChartFamily.quotientDesc_comp`: the descended morphism lies
  over `X`.
* `AlgebraicGeometry.Space.CartesianChartFamily.isIso_quotientDesc_hom`: the isomorphism
  criterion.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u

namespace AlgebraicGeometry.Space

/-! ### An isomorphism criterion for morphisms of sheaves of sets -/

section IsoCriterion

variable {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)

/-- **A morphism of sheaves of sets over `X` is an isomorphism if it is one after base change
along a locally surjective `c : W ⟶ X`**, in the form: there are cartesian squares
`φ : W' ⟶ A` over `c` and `φ ≫ Ψ : W' ⟶ Y` over `c`, with the same second projection
`w : W' ⟶ W`. Then `Ψ` is locally injective and locally surjective, hence invertible. -/
theorem isIso_of_isPullback_of_isLocallySurjective {A Y X W W' : Cᵒᵖ ⥤ Type v}
    (hA : Presheaf.IsSheaf J A) (hY : Presheaf.IsSheaf J Y) (a : A ⟶ X) (q : Y ⟶ X)
    (Ψ : A ⟶ Y) (hΨ : Ψ ≫ q = a) (c : W ⟶ X) (hc : Presheaf.IsLocallySurjective J c)
    (φ : W' ⟶ A) (w : W' ⟶ W) (hφ : IsPullback φ w a c) (hφΨ : IsPullback (φ ≫ Ψ) w q c) :
    IsIso Ψ := by
  let Ψs : (⟨A, hA⟩ : Sheaf J (Type v)) ⟶ ⟨Y, hY⟩ := ObjectProperty.homMk Ψ
  have hsurj : Sheaf.IsLocallySurjective Ψs := by
    refine ⟨fun {T} y => J.superset_covering ?_ (hc.imageSieve_mem (q.app (op T) y))⟩
    rintro T' f ⟨v, hv⟩
    -- lift `(Y.map f y, v)` through the cartesian square of `Y`
    let yh : yoneda.obj T' ⟶ Y := yonedaEquiv.symm (Y.map f.op y)
    let vh : yoneda.obj T' ⟶ W := yonedaEquiv.symm v
    have hw : yh ≫ q = vh ≫ c := yonedaEquiv.injective <| by simp [yh, vh, yonedaEquiv_comp, hv]
    refine ⟨φ.app _ (yonedaEquiv (hφΨ.lift yh vh hw)), ?_⟩
    have h := congrArg yonedaEquiv (hφΨ.lift_fst yh vh hw)
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply] at h
    exact h
  have hinj : Sheaf.IsLocallyInjective Ψs := by
    refine ⟨fun {T} x₁ x₂ hx => J.superset_covering ?_ (hc.imageSieve_mem (a.app T x₁))⟩
    rintro T' f ⟨v, hv⟩
    change A.map f.op x₁ = A.map f.op x₂
    let xh₁ : yoneda.obj T' ⟶ A := yonedaEquiv.symm (A.map f.op x₁)
    let xh₂ : yoneda.obj T' ⟶ A := yonedaEquiv.symm (A.map f.op x₂)
    let vh : yoneda.obj T' ⟶ W := yonedaEquiv.symm v
    have ha : a.app T x₂ = a.app T x₁ := by
      rw [← hΨ]
      exact congrArg (q.app T) hx.symm
    have hw₁ : xh₁ ≫ a = vh ≫ c := yonedaEquiv.injective <| by simp [xh₁, vh, yonedaEquiv_comp, hv]
    have hw₂ : xh₂ ≫ a = vh ≫ c := yonedaEquiv.injective <| by
      simp [xh₂, vh, yonedaEquiv_comp, hv, ha]
    have hl : hφ.lift xh₁ vh hw₁ = hφ.lift xh₂ vh hw₂ := by
      apply hφΨ.hom_ext
      · rw [← Category.assoc, hφ.lift_fst, ← Category.assoc, hφ.lift_fst]
        apply yonedaEquiv.injective
        rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        change (Ψ.app _ (A.map f.op x₁)) = Ψ.app _ (A.map f.op x₂)
        rw [Ψ.naturality_apply, Ψ.naturality_apply]
        exact congrArg (Y.map f.op) hx
      · rw [hφ.lift_snd, hφ.lift_snd]
    refine yonedaEquiv.symm.injective ?_
    change xh₁ = xh₂
    rw [← hφ.lift_fst xh₁ vh hw₁, hl, hφ.lift_fst]
  have : IsIso Ψs := (Sheaf.isLocallyBijective_iff_isIso Ψs).1 ⟨hinj, hsurj⟩
  exact (sheafToPresheaf J (Type v)).map_isIso Ψs

end IsoCriterion


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CartesianChartFamily

variable {X : AlgebraicSpaces B S hS} (F : CartesianChartFamily X)
  {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
  (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
    (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)

/-! ### The universal property of the glued space -/

/-- The condition of the quotient sheaf for a morphism out of the chart, read on the restricted
functor of points. -/
theorem sourceMap_comp_pointsYonedaIso_hom_comp {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (φ : yoneda.obj (F.site V₂) ⟶ Y)
    (hφ : yoneda.map (F.siteMap pr₁) ≫ φ = yoneda.map (F.siteMap pr₂) ≫ φ) :
    Stacks.Groupoids.sourceMap (Over.post B.inclusion)
          (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ≫
        ((pointsYonedaIso (Over.post B.inclusion) (F.site V₂)).hom ≫ φ) =
      Stacks.Groupoids.targetMap (Over.post B.inclusion)
          (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ≫
        ((pointsYonedaIso (Over.post B.inclusion) (F.site V₂)).hom ≫ φ) := by
  have hsrc : (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)).source =
      (Over.post (X := B.obj hS) B.inclusion).map (F.siteMap pr₂) := prod.lift_snd _ _
  have htgt : (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)).target =
      (Over.post (X := B.obj hS) B.inclusion).map (F.siteMap pr₁) := prod.lift_fst _ _
  rw [Stacks.Groupoids.sourceMap, Stacks.Groupoids.targetMap, hsrc, htgt, ← Category.assoc,
    ← Category.assoc,
    whiskerLeft_yoneda_map_comp_pointsYonedaIso_hom,
    whiskerLeft_yoneda_map_comp_pointsYonedaIso_hom, Category.assoc, Category.assoc, hφ]

/-- **The universal property of the glued space.** A morphism `φ : F(V₂) ⟶ Y` from the scheme
over the chart to an algebraic space, identifying the two morphisms `F(V') ⇉ F(V₂)` of the
relation, descends to a morphism `F_X ⟶ Y` of algebraic spaces. -/
def quotientDesc (Y : AlgebraicSpaces B S hS) (φ : yoneda.obj (F.site V₂) ⟶ Y.1)
    (hφ : yoneda.map (F.siteMap pr₁) ≫ φ = yoneda.map (F.siteMap pr₂) ≫ φ) :
    F.quotient pr₁ pr₂ hsq ⟶ Y :=
  ObjectProperty.homMk
    (Stacks.Groupoids.quotientSheafDesc (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ⟨Y.1, Y.property.isSheaf⟩
      ((pointsYonedaIso (Over.post B.inclusion) (F.site V₂)).hom ≫ φ)
      (F.sourceMap_comp_pointsYonedaIso_hom_comp pr₁ pr₂ φ hφ)).hom

/-- The comparison of the represented presheaf with the restricted functor of points, followed
by its inverse, is the identity. -/
theorem yonedaToPoints_comp_pointsYonedaIso_hom (U : BigFppfOver B S hS) :
    Stacks.Groupoids.yonedaToPoints (Over.post (X := B.obj hS) B.inclusion) U ≫
        (pointsYonedaIso (Over.post B.inclusion) U).hom = 𝟙 _ := by
  rw [← pointsYonedaIso_inv_eq_yonedaToPoints, Iso.inv_hom_id]

/-- **The descended morphism restricts on the chart to `φ`.** -/
@[reassoc (attr := simp)]
theorem quotientChart_comp_quotientDesc (Y : AlgebraicSpaces B S hS)
    (φ : yoneda.obj (F.site V₂) ⟶ Y.1)
    (hφ : yoneda.map (F.siteMap pr₁) ≫ φ = yoneda.map (F.siteMap pr₂) ≫ φ) :
    F.quotientChart pr₁ pr₂ hsq ≫ (F.quotientDesc pr₁ pr₂ hsq Y φ hφ).hom = φ := by
  change Stacks.Groupoids.yonedaToPoints (Over.post B.inclusion) (F.site V₂) ≫
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ≫
        (Stacks.Groupoids.quotientSheafDesc (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ⟨Y.1, Y.property.isSheaf⟩
          ((pointsYonedaIso (Over.post B.inclusion) (F.site V₂)).hom ≫ φ)
          (F.sourceMap_comp_pointsYonedaIso_hom_comp pr₁ pr₂ φ hφ)).hom) = φ
  rw [Stacks.Groupoids.toQuotientSheaf_quotientSheafDesc, ← Category.assoc,
    yonedaToPoints_comp_pointsYonedaIso_hom, Category.id_comp]

/-- **Morphisms out of the glued space are determined on the chart.** -/
theorem hom_ext_quotient {Y : AlgebraicSpaces B S hS} (m₁ m₂ : F.quotient pr₁ pr₂ hsq ⟶ Y)
    (h : F.quotientChart pr₁ pr₂ hsq ≫ m₁.hom = F.quotientChart pr₁ pr₂ hsq ≫ m₂.hom) :
    m₁ = m₂ := by
  let J := BigFppfOver.topology B S hS
  let k := (pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) (F.site V₂)).hom ≫
    (F.quotientChart pr₁ pr₂ hsq ≫ m₁.hom)
  have hk₁ := toQuotientSheaf_comp_of_quotientChart_comp J (Over.post B.inclusion) (F.site V₂)
    (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) m₁.hom _ rfl
  have hk₂ := toQuotientSheaf_comp_of_quotientChart_comp J (Over.post B.inclusion) (F.site V₂)
    (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) m₂.hom _ h.symm
  have hcond : Stacks.Groupoids.sourceMap (Over.post B.inclusion)
        (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ≫ k =
      Stacks.Groupoids.targetMap (Over.post B.inclusion)
        (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ≫ k := by
    have hk : k = Stacks.Groupoids.toQuotientSheaf J (Over.post B.inclusion)
        (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ≫ m₁.hom := hk₁.symm
    rw [hk]
    have hst := congrArg (fun t => t ≫ m₁.hom)
      (Stacks.Groupoids.sourceMap_toQuotientSheaf J (Over.post (X := B.obj hS) B.inclusion)
        (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)))
    exact (Category.assoc _ _ _).symm.trans (hst.trans (Category.assoc _ _ _))
  have e₁ := Stacks.Groupoids.quotientSheafDesc_unique J (Over.post B.inclusion)
    (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ⟨Y.1, Y.property.isSheaf⟩ k hcond
    ⟨m₁.hom⟩ hk₁
  have e₂ := Stacks.Groupoids.quotientSheafDesc_unique J (Over.post B.inclusion)
    (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ⟨Y.1, Y.property.isSheaf⟩ k hcond
    ⟨m₂.hom⟩ hk₂
  refine ObjectProperty.hom_ext _ ?_
  exact congrArg (fun m => m.hom) (e₁.trans e₂.symm)

/-- The structure morphism `F_X ⟶ X` restricts on the chart to `F(V₂) ⟶ V₂ ⟶ X`. -/
@[reassoc]
theorem quotientChart_comp_quotientHom :
    F.quotientChart pr₁ pr₂ hsq ≫ (F.quotientHom pr₁ pr₂ hsq).hom = F.siteToSpace V₂ := by
  change Stacks.Groupoids.yonedaToPoints (Over.post B.inclusion) (F.site V₂) ≫
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ≫
        (F.quotientHom pr₁ pr₂ hsq).hom) = F.siteToSpace V₂
  rw [toQuotientSheaf_comp_quotientHom, ← Category.assoc,
    yonedaToPoints_comp_pointsYonedaIso_hom, Category.id_comp]

/-- **The descended morphism lies over `X`** when `φ` does. -/
theorem quotientDesc_comp (Y : AlgebraicSpaces B S hS) (φ : yoneda.obj (F.site V₂) ⟶ Y.1)
    (hφ : yoneda.map (F.siteMap pr₁) ≫ φ = yoneda.map (F.siteMap pr₂) ≫ φ) (q : Y ⟶ X)
    (hq : φ ≫ q.hom = F.siteToSpace V₂) :
    F.quotientDesc pr₁ pr₂ hsq Y φ hφ ≫ q = F.quotientHom pr₁ pr₂ hsq := by
  apply F.hom_ext_quotient pr₁ pr₂ hsq
  change F.quotientChart pr₁ pr₂ hsq ≫ ((F.quotientDesc pr₁ pr₂ hsq Y φ hφ).hom ≫ q.hom) = _
  rw [quotientChart_comp_quotientDesc_assoc, hq, quotientChart_comp_quotientHom]

/-- **The isomorphism criterion.** An algebraic space `Y` over `X` whose restriction to the
surjective chart `V₂` is `F(V₂)` — a morphism `φ : F(V₂) ⟶ Y` over the chart making the square
over `V₂ ⟶ X` cartesian — and which identifies the two morphisms of the relation, is the glued
space: the descended morphism `F_X ⟶ Y` is an isomorphism. -/
theorem isIso_quotientDesc_hom (Y : AlgebraicSpaces B S hS) (φ : yoneda.obj (F.site V₂) ⟶ Y.1)
    (hφ : yoneda.map (F.siteMap pr₁) ≫ φ = yoneda.map (F.siteMap pr₂) ≫ φ) (q : Y ⟶ X)
    (hpb : IsPullback φ (yoneda.map (F.siteToChart V₂)) q.hom V₂.obj.hom)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom) :
    IsIso (F.quotientDesc pr₁ pr₂ hsq Y φ hφ).hom := by
  have hq : φ ≫ q.hom = F.siteToSpace V₂ := by
    rw [hpb.w]
    rfl
  have hcomp := congrArg (fun m => m.hom) (F.quotientDesc_comp pr₁ pr₂ hsq Y φ hφ q hq)
  refine isIso_of_isPullback_of_isLocallySurjective (BigFppfOver.topology B S hS)
    (F.quotient pr₁ pr₂ hsq).property.isSheaf Y.property.isSheaf
    (F.quotientHom pr₁ pr₂ hsq).hom q.hom _ hcomp V₂.obj.hom
    (isLocallySurjective_of_surjective_etale B S hS V₂.obj.hom hsurj V₂.property)
    (F.quotientChart pr₁ pr₂ hsq) (yoneda.map (F.siteToChart V₂))
    (F.isPullback_quotientHom pr₁ pr₂ hsq hsurj) ?_
  rw [quotientChart_comp_quotientDesc]
  exact hpb

/-! ### The relation is identified on the glued space, and charts over the presenting chart -/

/-- **The chart of the glued space identifies the two morphisms of the relation**
`F(V') ⇉ F(V₂)`: they are the source and target maps of the étale equivalence relation whose
quotient is `F_X`. -/
theorem siteMap_comp_quotientChart :
    yoneda.map (F.siteMap pr₁) ≫ F.quotientChart pr₁ pr₂ hsq =
      yoneda.map (F.siteMap pr₂) ≫ F.quotientChart pr₁ pr₂ hsq := by
  have hsrc : (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)).source =
      (Over.post (X := B.obj hS) B.inclusion).map (F.siteMap pr₂) := prod.lift_snd _ _
  have htgt : (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)).target =
      (Over.post (X := B.obj hS) B.inclusion).map (F.siteMap pr₁) := prod.lift_fst _ _
  have h := Stacks.Groupoids.sourceMap_toQuotientSheaf (BigFppfOver.topology B S hS)
    (Over.post (X := B.obj hS) B.inclusion) (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁))
  rw [Stacks.Groupoids.sourceMap, Stacks.Groupoids.targetMap, hsrc, htgt] at h
  change yoneda.map (F.siteMap pr₁) ≫ (Stacks.Groupoids.yonedaToPoints (Over.post B.inclusion)
        (F.site V₂) ≫ Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁))) =
    yoneda.map (F.siteMap pr₂) ≫ (Stacks.Groupoids.yonedaToPoints (Over.post B.inclusion)
        (F.site V₂) ≫ Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)))
  have n₁ := Stacks.Groupoids.yonedaToPoints_naturality (Over.post (X := B.obj hS) B.inclusion)
    (F.siteMap pr₁)
  have n₂ := Stacks.Groupoids.yonedaToPoints_naturality (Over.post (X := B.obj hS) B.inclusion)
    (F.siteMap pr₂)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) n₁.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) h.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) n₂).trans ?_
  exact Category.assoc _ _ _

/-- **`F(V) = F_X ×_X V` over a chart `V` with a morphism `m : V ⟶ V₂` to the surjective
presenting chart**: the cartesian square of the family over `m` pasted with the cartesian square
of the glued space over `V₂`. -/
theorem isPullback_siteMap_comp_quotientChart
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom) {V : SmallEtale B S hS X.1} (m : V ⟶ V₂) :
    IsPullback (yoneda.map (F.siteMap m) ≫ F.quotientChart pr₁ pr₂ hsq)
      (yoneda.map (F.siteToChart V)) (F.quotientHom pr₁ pr₂ hsq).hom V.obj.hom := by
  have h₁ := (F.isPullback_siteMap m).map yoneda
  have h₂ := F.isPullback_quotientHom pr₁ pr₂ hsq hsurj
  have h := h₁.paste_horiz h₂
  rwa [yoneda_map_toOver_map_comp_hom m] at h

/-! ### Changing the relation of charts the family is glued over -/

section ChangeOfCharts

variable {W' W : SmallEtale B S hS X.1} (q₁ q₂ : W' ⟶ W)
  (hsqW : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map q₁))
    (yoneda.map ((SmallEtale.toOver B S hS X.1).map q₂)) W.obj.hom W.obj.hom)
  (m : W ⟶ V₂)

/-- The morphism `F(W) ⟶ F_X` of a chart `W` over the presenting chart `V₂`. -/
abbrev quotientChartOfHom : yoneda.obj (F.site W) ⟶ (F.quotient pr₁ pr₂ hsq).1 :=
  yoneda.map (F.siteMap m) ≫ F.quotientChart pr₁ pr₂ hsq

/-- The morphism `F(W) ⟶ F_X` identifies the two morphisms of a relation `W' ⇉ W` of charts: the
two composites `W' ⇉ W ⟶ V₂` factor through the relation `V' ⇉ V₂`. -/
theorem siteMap_comp_quotientChartOfHom :
    yoneda.map (F.siteMap q₁) ≫ F.quotientChartOfHom pr₁ pr₂ hsq m =
      yoneda.map (F.siteMap q₂) ≫ F.quotientChartOfHom pr₁ pr₂ hsq m := by
  let l := chartRelationLift pr₁ pr₂ hsq (q₁ ≫ m) (q₂ ≫ m)
  have h₁ : l ≫ pr₁ = q₁ ≫ m := chartRelationLift_comp_fst pr₁ pr₂ hsq _ _
  have h₂ : l ≫ pr₂ = q₂ ≫ m := chartRelationLift_comp_snd pr₁ pr₂ hsq _ _
  simp only [quotientChartOfHom]
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    ← F.siteMap_comp, ← F.siteMap_comp, ← h₁, ← h₂, F.siteMap_comp, F.siteMap_comp,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    F.siteMap_comp_quotientChart pr₁ pr₂ hsq]

/-- **The glued space does not depend on the relation of charts**: for a second surjective chart
`W` with a relation `W' ⇉ W` and a morphism `m : W ⟶ V₂` to the presenting chart, the morphism
from the space glued over `W' ⇉ W` to the one glued over `V' ⇉ V₂` descended from
`F(W) ⟶ F(V₂) ⟶ F_X` is an isomorphism. -/
theorem isIso_quotientDesc_quotientChartOfHom
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom)
    (hsurjW : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      W.obj.hom) :
    IsIso (F.quotientDesc q₁ q₂ hsqW (F.quotient pr₁ pr₂ hsq)
      (F.quotientChartOfHom pr₁ pr₂ hsq m)
      (F.siteMap_comp_quotientChartOfHom pr₁ pr₂ hsq q₁ q₂ m)).hom :=
  F.isIso_quotientDesc_hom q₁ q₂ hsqW _ _ _ (F.quotientHom pr₁ pr₂ hsq)
    (F.isPullback_siteMap_comp_quotientChart pr₁ pr₂ hsq hsurj m) hsurjW

end ChangeOfCharts

end CartesianChartFamily

/-! ### The kernel pair of an étale chart -/

section KernelPair

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : SmallEtale B S hS F)

/-- The object of the site representing the kernel pair `W ×_F W` of an étale chart. -/
abbrev chartKernelPairObj : BigFppfOver B S hS :=
  W.property.1.pullback W.obj.hom

/-- The second projection `W ×_F W ⟶ W`, as a morphism of the site. -/
abbrev chartKernelPairSnd : chartKernelPairObj W ⟶ W.obj.left :=
  W.property.1.snd W.obj.hom

/-- The first projection `W ×_F W ⟶ W`, as a morphism of the site. -/
abbrev chartKernelPairFst : chartKernelPairObj W ⟶ W.obj.left :=
  yoneda.preimage (W.property.1.fst W.obj.hom)

/-- The kernel pair square of an étale chart. -/
theorem isPullback_chartKernelPair :
    IsPullback (yoneda.map (chartKernelPairFst W)) (yoneda.map (chartKernelPairSnd W)) W.obj.hom
      W.obj.hom := by
  simpa [chartKernelPairFst, chartKernelPairSnd] using W.property.1.isPullback W.obj.hom

/-- The second projection of the kernel pair of an étale chart is étale. -/
theorem etale_chartKernelPairSnd :
    Etale ((BigFppfOver.toScheme B S hS).map (chartKernelPairSnd W)) :=
  W.property.2 W.obj.hom (W.property.1.fst W.obj.hom) (W.property.1.snd W.obj.hom)
    (W.property.1.isPullback W.obj.hom)

/-- **The kernel pair `W ×_F W` of an étale chart**, as an étale chart: the second projection
is étale, and so is its composite with the chart. -/
def chartKernelPair : SmallEtale B S hS F :=
  ⟨CostructuredArrow.mk (yoneda.map (chartKernelPairSnd W) ≫ W.obj.hom),
    etale_comp_of_scheme B S hS _ _ (etale_chartKernelPairSnd W) W.property⟩

/-- The first projection of the kernel pair, as a morphism of étale charts. -/
def chartKernelPairFstHom : chartKernelPair W ⟶ W :=
  ObjectProperty.homMk (CostructuredArrow.homMk (chartKernelPairFst W)
    (isPullback_chartKernelPair W).w)

/-- The second projection of the kernel pair, as a morphism of étale charts. -/
def chartKernelPairSndHom : chartKernelPair W ⟶ W :=
  ObjectProperty.homMk (CostructuredArrow.homMk (chartKernelPairSnd W) rfl)

/-- **The kernel pair chart is the fibre product `W ×_F W`**, in the form the glueing of a
cartesian chart family over a relation of charts consumes. -/
theorem isPullback_chartKernelPairHom :
    IsPullback (yoneda.map ((SmallEtale.toOver B S hS F).map (chartKernelPairFstHom W)))
      (yoneda.map ((SmallEtale.toOver B S hS F).map (chartKernelPairSndHom W))) W.obj.hom
      W.obj.hom :=
  isPullback_chartKernelPair W

end KernelPair

end AlgebraicGeometry.Space

end
