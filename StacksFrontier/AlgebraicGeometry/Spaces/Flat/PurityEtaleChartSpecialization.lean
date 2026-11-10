module

public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityEtaleMorphism

/-!
# Purity specializes the relative assassin along an étale scheme chart of the base

In the situation of Stacks 0CV6 — `f : X ⟶ Y` of finite type and decent, `ℱ` a quasi-coherent
`𝒪_X`-module of finite type and `y ∈ |Y|` — let `b : V ⟶ Y` be an étale morphism from a scheme
of the site and `v ∈ V` a point over `y`.  If `ℱ` is pure above `y`, then every point `ξ` of the
relative assassin `Ass_{X_V/V}(ℱ_V)` of the base change `X_V = X ×_Y V` lying over a
generalization of `v` specializes to a point of `X_V` lying over `v`.

This is the definition of purity above `y` (Stacks 0CVD, condition (4) of Stacks 0CVB) read at
the impurity diagram `(V, b, v' ⤳ v, ξ)`: the structure morphism `b` is étale, hence quasi-finite
at `v`, so this diagram is not an impurity, and since `ξ` lies in the relative assassin that
means exactly that `v` lies in the image of the closure of `ξ`.  The only thing to supply is the
passage from an arbitrary presentation of `X_V` as a fibre product to the chosen one which
impurity diagrams are stated on, which is part (1) of Stacks 0CV2 at an isomorphism.

It is the step of the proof of Stacks 0CWC which spends purity: together with an étale chart of
`X_V` covering the fibre over `v` it puts every point of `Ass_{X_V/V}(ℱ_V)` over a
generalization of `v` into that chart, because the image of an étale morphism is open.

## Main results

* `AlgebraicGeometry.Space.exists_specializes_fibre_of_isPureAbove_of_isPullback`: the statement
  above.

## References

* [Stacks Project, Tag 0CVD](https://stacks.math.columbia.edu/tag/0CVD)
* [Stacks Project, Tag 0CVB](https://stacks.math.columbia.edu/tag/0CVB)
* [Stacks Project, Tag 0CV2](https://stacks.math.columbia.edu/tag/0CV2)
* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instances (file-unique names). -/
local instance (priority := high) hasPullbacks_presheaf_PurityEtaleChartSpecialization :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_PurityEtaleChartSpecialization
    {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W) (g : Z ⟶ W) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

/-- **Purity above `y` specializes the relative assassin of an étale base change into the
fibre.**  Let `P` be a situation of Stacks 0CV6 whose module is pure above `y`, let
`b : V ⟶ Y` be étale from a scheme of the site and `v ∈ |V|` a point over `y`, and let
`X_V`, with projections `p : X_V ⟶ X` and `q : X_V ⟶ V`, be a fibre product of `f` and `b`.
Every point `ξ` of `Ass_{X_V/V}(p^*ℱ)` whose image in `V` specializes to `v` specializes to a
point of `X_V` lying over `v`. -/
theorem exists_specializes_fibre_of_isPureAbove_of_isPullback
    (P : PrePureSituation.{u, u} B S hS) (hpure : IsPureAbove P)
    (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ P.Y) (hb : IsEtale B S hS b)
    (v : points B S hS (yoneda.obj V)) (hv : pointsMap B S hS (yoneda.obj V) b v = P.y)
    {XV : AlgebraicSpaces B S hS} {p : XV ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS)}
    {q : XV ⟶ schemeSpace V} (sq : IsPullback p.hom q.hom P.f b)
    {ξ : points B S hS XV.1}
    (hξ : ξ ∈ relativeWeaklyAssociatedPoints B S hS q ((modulePullback B S hS p).obj P.F))
    (hspec : pointsToScheme B S hS V (pointsMap B S hS XV.1 q.hom ξ) ⤳
      pointsToScheme B S hS V v) :
    ∃ θ : points B S hS XV.1, ξ ⤳ θ ∧ pointsMap B S hS XV.1 q.hom θ = v := by
  -- The comparison with the chosen fibre product `V ×_Y X`.
  let e : XV.1 ≅ pullback b P.f := sq.flip.isoPullback
  have hefst : e.hom ≫ pullback.fst b P.f = q.hom := sq.flip.isoPullback_hom_fst
  let E : XV ⟶ P.baseChangeSpace V b := ObjectProperty.homMk e.hom
  -- Part (1) of Stacks 0CV2 at the isomorphism `e` carries `ξ` into the relative assassin of
  -- the chosen fibre product.
  have hEiso : IsIso E.hom := by
    change IsIso e.hom
    infer_instance
  have hid : IsIso (𝟙 (schemeSpace V) : schemeSpace V ⟶ schemeSpace V).hom := by
    change IsIso (𝟙 (yoneda.obj V))
    infer_instance
  have sqE : IsPullback E.hom q.hom (P.baseChangeToBase V b).hom
      (𝟙 (schemeSpace V) : schemeSpace V ⟶ schemeSpace V).hom :=
    @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ hEiso hid ⟨by
      change e.hom ≫ pullback.fst b P.f = q.hom ≫ 𝟙 _
      rw [hefst, Category.comp_id]⟩
  have hcomp : E ≫ P.baseChangeToSource V b = p :=
    ObjectProperty.hom_ext (h := sq.flip.isoPullback_hom_snd)
  have hmod : (modulePullback B S hS E).obj (P.baseChangeModule V b) ≅
      (modulePullback B S hS p).obj P.F := by
    refine (modulePullbackCompIso B S hS E (P.baseChangeToSource V b)).app P.F ≪≫ ?_
    rw [hcomp]
  have hξE : IsRelativeWeaklyAssociatedPoint B S hS (P.baseChangeToBase V b)
      (P.baseChangeModule V b) (pointsMap B S hS XV.1 e.hom ξ) :=
    isRelativeWeaklyAssociatedPoint_of_baseChange B S hS
      (g := (𝟙 (schemeSpace V) : schemeSpace V ⟶ schemeSpace V)) sqE (P.baseChangeModule V b)
      ((isRelativeWeaklyAssociatedPoint_congr q hmod ξ).2 hξ)
  have hlies : pointsMap B S hS (pullback b P.f) (pullback.fst b P.f)
      (pointsMap B S hS XV.1 e.hom ξ) = pointsMap B S hS XV.1 q.hom ξ := by
    rw [← pointsMap_comp_apply, hefst]
    rfl
  -- The impurity diagram `(V, b, q(ξ) ⤳ v, ξ)` is not an impurity.
  let D : ImpurityDiagram P :=
    { T := V, g := b, t' := pointsMap B S hS XV.1 q.hom ξ, t := v, specializes := hspec,
      mapsToChosenPoint := hv, xi := pointsMap B S hS XV.1 e.hom ξ, xi_liesOver := hlies }
  have hnot := hpure D (isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS
    (isAlgebraicSpace_yoneda B S hS V) (isLocallyQuasiFinite_of_isEtale' B S hS hb) v)
  rw [ImpurityDiagram.isImpurity_iff] at hnot
  push Not at hnot
  obtain ⟨θ', hθ', hθ'v⟩ := hnot hξE
  refine ⟨pointsMap B S hS (pullback b P.f) e.inv θ', ?_, ?_⟩
  · have h := hθ'.map (continuous_pointsMap B S hS e.inv)
    rwa [← pointsMap_comp_apply, e.hom_inv_id, pointsMap_id, id_eq] at h
  · have hcomp' : e.inv ≫ q.hom = pullback.fst b P.f := by
      rw [← hefst]
      exact e.inv_hom_id_assoc _
    rw [← pointsMap_comp_apply, hcomp']
    exact hθ'v

end AlgebraicGeometry.Space

end
