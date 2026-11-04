module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartRealizedSchemeSize
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientImmersion

/-!
# The étale charts of the thickened quotient `X' = U'/R'` coming from charts of `X`

Let `E` be a square-zero extension of the small étale structure sheaf of an algebraic space `X`
over `S` by a quasi-coherent ideal (the data of Stacks 05ZT), `X = U/R` an étale presentation
whose chart thickenings lie in the site, and `X' = U'/R'` the thickened quotient. Every étale
chart `W` of `X` admitting a morphism `a : W ⟶ U` of charts gives an étale chart of `X'`: the
chart thickening `W'` with the étale map `W' ⟶ U' ⟶ X'`. The chart does not depend on `a`: two
maps `a, b : W ⟶ U` factor through `(a, b) : W ⟶ R = U ×_X U`, so `a'` and `b'` factor through
`R'`, whose two legs agree in `X'`. So `W ↦ W'` is a functor from the full subcategory of the
charts of `X` lying over `U` to the small étale site of `X'`, and `W = X ×_{X'} W'`.

This is the dense family of charts on which the proof of Stacks 05ZT compares `𝒪_{X'}` with
the extension: on such a chart `𝒪_{X'}(W') = Γ(W') = 𝒜(W)`.

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.thickenedChart`: the chart `W' ⟶ U' ⟶ X'`.
* `AlgebraicGeometry.Space.SquareZeroExtension.OverPresentation`: the full subcategory of
  charts of `X` admitting a map to the presenting chart.
* `AlgebraicGeometry.Space.SquareZeroExtension.thickenedChartFunctor`: `W ↦ W'` on it.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.thickenedChartHom_eq`: independence of `a`.
* `AlgebraicGeometry.Space.SquareZeroExtension.isPullback_thickenedChartHom`: `W = X ×_{X'} W'`.
* `AlgebraicGeometry.Space.SquareZeroExtension.isCoverDense_overPresentation`: the charts over
  `U` are cover-dense in the small étale site of `X`.
* `AlgebraicGeometry.Space.SquareZeroExtension.isThickeningHom_thickeningImmersion`: `X ⟶ X'`
  is a thickening of algebraic spaces.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
variable (P : Presentation B S hS X.obj X.property)
  (hU : B.Contains (E.chartRealizedScheme (presentationChart P)))
  (hR : B.Contains (E.chartRealizedScheme (presentationRelationChart P)))

/-- The map `W' ⟶ U'` of a chart `a : W ⟶ U` over the presenting chart, followed by the
quotient map `U' ⟶ X'`. -/
noncomputable abbrev thickenedChartHom {W : SmallEtale B S hS X.1} (a : W ⟶ presentationChart P) :
    yoneda.obj (E.chartRealizedSchemeOver hS W (E.contains_chartRealizedScheme_of_hom a hU)) ⟶
      (E.thickeningQuotient hS P hU hR).1 :=
  yoneda.map (E.chartRealizedSchemeOverMap hS a hU (E.contains_chartRealizedScheme_of_hom a hU)) ≫
    E.thickeningQuotientMap P hU hR

/-- **The étale chart `W' ⟶ U' ⟶ X'` of the thickened quotient** attached to a chart `W` of `X`
with a map `a : W ⟶ U` to the presenting chart. -/
noncomputable def thickenedChart {W : SmallEtale B S hS X.1} (a : W ⟶ presentationChart P) :
    SmallEtale B S hS (E.thickeningQuotient hS P hU hR).1 :=
  letI := hasSheafify_bigFppfOver B S hS
  ⟨CostructuredArrow.mk (E.thickenedChartHom P hU hR a),
    etale_comp_of_scheme B S hS _ _ (E.etale_chartRealizedSchemeMap a)
      (quotientMap_etale_unconditional B S hS _ _)⟩

/-- The morphism `W ⟶ R = U ×_X U` of the big fppf site given by two maps of charts
`a, b : W ⟶ U` (the target leg first, as in `Presentation.isPullback`). -/
noncomputable def presentationRelationLiftHom {W : SmallEtale B S hS X.1}
    (a b : W ⟶ presentationChart P) : W.obj.left ⟶ P.R :=
  Yoneda.fullyFaithful.preimage (P.isPullback.lift (yoneda.map (b.hom.left : W.obj.left ⟶ P.U))
    (yoneda.map (a.hom.left : W.obj.left ⟶ P.U))
    ((yoneda_map_toOver_map_comp_hom b).trans (yoneda_map_toOver_map_comp_hom a).symm))

/-- The Yoneda image of `presentationRelationLiftHom P a b` is the lift of the pair of Yoneda
images of `b` and `a` into the pullback `R = U ×_X U`. -/
theorem yoneda_map_presentationRelationLiftHom {W : SmallEtale B S hS X.1}
    (a b : W ⟶ presentationChart P) :
    yoneda.map (presentationRelationLiftHom P a b) =
      P.isPullback.lift (yoneda.map (b.hom.left : W.obj.left ⟶ P.U))
        (yoneda.map (a.hom.left : W.obj.left ⟶ P.U))
        ((yoneda_map_toOver_map_comp_hom b).trans (yoneda_map_toOver_map_comp_hom a).symm) :=
  Yoneda.fullyFaithful.map_preimage _

/-- The composite of `presentationRelationLiftHom P a b` with the source map `R ⟶ U` is `a`. -/
theorem presentationRelationLiftHom_source {W : SmallEtale B S hS X.1}
    (a b : W ⟶ presentationChart P) :
    presentationRelationLiftHom P a b ≫ P.source = (a.hom.left : W.obj.left ⟶ P.U) :=
  yoneda.map_injective (by
    rw [Functor.map_comp, yoneda_map_presentationRelationLiftHom]
    exact IsPullback.lift_snd _ _ _ _)

/-- The composite of `presentationRelationLiftHom P a b` with the target map `R ⟶ U` is `b`. -/
theorem presentationRelationLiftHom_target {W : SmallEtale B S hS X.1}
    (a b : W ⟶ presentationChart P) :
    presentationRelationLiftHom P a b ≫ P.target = (b.hom.left : W.obj.left ⟶ P.U) :=
  yoneda.map_injective (by
    rw [Functor.map_comp, yoneda_map_presentationRelationLiftHom]
    exact IsPullback.lift_fst _ _ _ _)

/-- The pair `(a, b) : W ⟶ R = U ×_X U` of two maps of charts to the presenting chart. -/
noncomputable def presentationRelationLift {W : SmallEtale B S hS X.1}
    (a b : W ⟶ presentationChart P) : W ⟶ presentationRelationChart P :=
  ObjectProperty.homMk (CostructuredArrow.homMk (presentationRelationLiftHom P a b) (by
    change yoneda.map _ ≫ yoneda.map P.source ≫ P.toSpace = W.obj.hom
    rw [← Category.assoc, ← Functor.map_comp, presentationRelationLiftHom_source]
    exact yoneda_map_toOver_map_comp_hom a))

/-- The composite of `presentationRelationLift P a b` with the source map of charts `R ⟶ U` is
`a`. -/
theorem presentationRelationLift_source {W : SmallEtale B S hS X.1}
    (a b : W ⟶ presentationChart P) :
    presentationRelationLift P a b ≫ presentationRelationSourceHom P = a :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    (presentationRelationLiftHom_source P a b))

/-- The composite of `presentationRelationLift P a b` with the target map of charts `R ⟶ U` is
`b`. -/
theorem presentationRelationLift_target {W : SmallEtale B S hS X.1}
    (a b : W ⟶ presentationChart P) :
    presentationRelationLift P a b ≫ presentationRelationTargetHom P = b :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    (presentationRelationLiftHom_target P a b))

/-- `(h ≫ g)' = h' ≫ g'` for the morphisms of the big fppf site between chart thickenings. -/
theorem chartRealizedSchemeOverMap_comp {U V W : SmallEtale B S hS X.1} (g : V ⟶ U) (h : W ⟶ V)
    (hU' : B.Contains (E.chartRealizedScheme U)) (hV : B.Contains (E.chartRealizedScheme V))
    (hW : B.Contains (E.chartRealizedScheme W)) :
    E.chartRealizedSchemeOverMap hS h hV hW ≫ E.chartRealizedSchemeOverMap hS g hU' hV =
      E.chartRealizedSchemeOverMap hS (h ≫ g) hU' hW :=
  BigFppfOver.map_toScheme_injective B S hS (by
    show (BigFppfOver.toScheme B S hS).map _ = (BigFppfOver.toScheme B S hS).map _
    rw [Functor.map_comp, toScheme_map_chartRealizedSchemeOverMap,
      toScheme_map_chartRealizedSchemeOverMap,
      toScheme_map_chartRealizedSchemeOverMap]
    exact (E.chartRealizedSchemeMap_comp g h).symm)

/-- **The chart `W' ⟶ X'` does not depend on the map to the presenting chart.** -/
theorem thickenedChartHom_eq {W : SmallEtale B S hS X.1} (a b : W ⟶ presentationChart P) :
    E.thickenedChartHom P hU hR a = E.thickenedChartHom P hU hR b := by
  let := hasSheafify_bigFppfOver B S hS
  have hW := E.contains_chartRealizedScheme_of_hom a hU
  have w := (quotientMap_isPullback B S hS
    (E.chartRealizedSchemeOverMap hS (presentationRelationSourceHom P) hU hR)
    (E.chartRealizedSchemeOverMap hS (presentationRelationTargetHom P) hU hR)).w
  have key {c : presentationRelationChart P ⟶ presentationChart P} {x : W ⟶ presentationChart P}
      (h : presentationRelationLift P a b ≫ c = x) :
      E.chartRealizedSchemeOverMap hS x hU hW =
        E.chartRealizedSchemeOverMap hS (presentationRelationLift P a b) hR hW ≫
          E.chartRealizedSchemeOverMap hS c hU hR := by
    rw [chartRealizedSchemeOverMap_comp, h]
  show yoneda.map _ ≫ _ = yoneda.map _ ≫ _
  rw [key (presentationRelationLift_source P a b), key (presentationRelationLift_target P a b),
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg (yoneda.map (E.chartRealizedSchemeOverMap hS (presentationRelationLift P a b)
    hR hW) ≫ ·) w.symm

/-- `𝟙' = 𝟙` for the morphisms of the big fppf site between chart thickenings. -/
theorem chartRealizedSchemeOverMap_id (U : SmallEtale B S hS X.1)
    (hU' : B.Contains (E.chartRealizedScheme U)) :
    E.chartRealizedSchemeOverMap hS (𝟙 U) hU' hU' = 𝟙 _ :=
  BigFppfOver.map_toScheme_injective B S hS (by
    show (BigFppfOver.toScheme B S hS).map _ = (BigFppfOver.toScheme B S hS).map _
    rw [CategoryTheory.Functor.map_id, toScheme_map_chartRealizedSchemeOverMap]
    exact E.chartRealizedSchemeMap_id U)

/-- **`W = X ×_{X'} W'`**: the base change of `X ⟶ X'` along the chart `W' ⟶ U' ⟶ X'` is the
inclusion `W ⟶ W'`. -/
theorem isPullback_thickenedChartHom {W : SmallEtale B S hS X.1}
    (a : W ⟶ presentationChart P) :
    IsPullback W.obj.hom
      (yoneda.map (E.chartInclusionOver W (E.contains_chartRealizedScheme_of_hom a hU)))
      (E.thickeningImmersion P hU hR).hom (E.thickenedChartHom P hU hR a) := by
  have hW := E.contains_chartRealizedScheme_of_hom a hU
  have hsch : IsPullback
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map a))
      ((BigFppfOver.toScheme B S hS).map (E.chartInclusionOver W hW))
      ((BigFppfOver.toScheme B S hS).map (E.chartInclusionOver (presentationChart P) hU))
      ((BigFppfOver.toScheme B S hS).map (E.chartRealizedSchemeOverMap hS a hU hW)) := by
    rw [toScheme_map_chartInclusionOver, toScheme_map_chartInclusionOver,
      toScheme_map_chartRealizedSchemeOverMap]
    exact (E.isPullback_chartRealizedSchemeMap a).flip
  have _ : ReflectsLimit (cospan (E.chartInclusionOver (presentationChart P) hU)
      (E.chartRealizedSchemeOverMap hS a hU hW)) (BigFppfOver.toScheme B S hS) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  have hsite := IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) hsch
  have hleft := hsite.map yoneda
  have h := hleft.paste_horiz (E.isPullback_thickeningImmersion P hU hR)
  have e : yoneda.map ((SmallEtale.toOver B S hS X.1).map a) ≫ P.toSpace = W.obj.hom :=
    yoneda_map_toOver_map_comp_hom a
  exact e ▸ h

/-- The charts of `X` admitting a morphism of charts to the presenting chart `U`. -/
def overPresentationChart : ObjectProperty (SmallEtale B S hS X.1) :=
  fun W ↦ Nonempty (W ⟶ presentationChart P)

/-- The full subcategory of the charts of `X` lying over the presenting chart `U`. -/
abbrev OverPresentation := (overPresentationChart P).FullSubcategory

/-- The chart `W'` of `X'` attached to a chart of `X` over `U`, through a chosen map to `U`. -/
noncomputable abbrev thickenedChartObj (W : OverPresentation P) :
    SmallEtale B S hS (E.thickeningQuotient hS P hU hR).1 :=
  E.thickenedChart P hU hR (Classical.choice W.property)

/-- **`W ↦ W'` from the charts of `X` over `U` to the small étale site of `X'`.** On morphisms
it is `g ↦ g'`. -/
noncomputable def thickenedChartFunctor :
    OverPresentation P ⥤ SmallEtale B S hS (E.thickeningQuotient hS P hU hR).1 where
  obj W := E.thickenedChartObj P hU hR W
  map {W₁ W₂} g := ObjectProperty.homMk (CostructuredArrow.homMk
    (E.chartRealizedSchemeOverMap hS g.hom
      (E.contains_chartRealizedScheme_of_hom (Classical.choice W₂.property) hU)
      (E.contains_chartRealizedScheme_of_hom (Classical.choice W₁.property) hU)) (by
    change yoneda.map _ ≫ yoneda.map _ ≫ _ = yoneda.map _ ≫ _
    refine (Category.assoc _ _ _).symm.trans ?_
    refine Eq.trans (congrArg (· ≫ E.thickeningQuotientMap P hU hR)
      ((yoneda.map_comp _ _).symm.trans
        (congrArg yoneda.map (E.chartRealizedSchemeOverMap_comp _ _ _ _ _)))) ?_
    exact E.thickenedChartHom_eq P hU hR (g.hom ≫ Classical.choice W₂.property)
      (Classical.choice W₁.property)))
  map_id W := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    (E.chartRealizedSchemeOverMap_id _ _))
  map_comp {W₁ W₂ W₃} g h := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    (E.chartRealizedSchemeOverMap_comp _ _ _ _ _).symm)

/-- The functor `thickenedChartFunctor` sends a chart `W` over `U` to `thickenedChartObj W`. -/
theorem thickenedChartFunctor_obj (W : OverPresentation P) :
    (E.thickenedChartFunctor P hU hR).obj W = E.thickenedChartObj P hU hR W :=
  rfl

/-- On underlying schemes, the image under `thickenedChartFunctor` of a morphism `g` of charts
over `U` is the morphism `chartRealizedSchemeMap g` of chart thickenings. -/
theorem toScheme_map_toOver_map_thickenedChartFunctor_map {W₁ W₂ : OverPresentation P}
    (g : W₁ ⟶ W₂) :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map
      ((E.thickenedChartFunctor P hU hR).map g)) = E.chartRealizedSchemeMap g.hom :=
  rfl

/-- **The charts of `X` over the presenting chart are cover-dense in the small étale site of
`X`**. -/
instance isCoverDense_overPresentation :
    (overPresentationChart P).ι.IsCoverDense (SmallEtale.topology B S hS X.1) where
  is_cover W := by
    refine (SmallEtale.topology B S hS X.1).superset_covering ?_
      (coversTop_singleton_of_isSurjective B S hS X (presentationChart P)
        (isSurjective_of_presheafSurjective B S hS _ P.surjective) W)
    rintro Z g ⟨_, ⟨h⟩⟩
    exact ⟨⟨⟨Z, ⟨h⟩⟩, 𝟙 Z, g, Category.id_comp g⟩⟩

/-- **`X ⟶ X'` is a thickening of algebraic spaces** (an isomorphism onto its range, which is a
thickening of `X'`). -/
theorem isThickeningHom_thickeningImmersion :
    IsThickeningHom B S hS (E.thickeningImmersion P hU hR) := by
  have : Mono (E.thickeningImmersion P hU hR).hom :=
    mono_of_isClosedImmersion B S hS _ (E.isClosedImmersion_thickeningImmersion P hU hR)
  exact (isThickeningHom_iff_of_mono _).2 (E.isThickening_range_thickeningImmersion P hU hR)

end AlgebraicGeometry.Space.SquareZeroExtension

end
