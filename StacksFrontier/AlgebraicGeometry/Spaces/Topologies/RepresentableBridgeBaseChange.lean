module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.RepresentableSmallEtaleBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition

/-!
# The chart functor of a representable algebraic space commutes with base change

For a morphism `f : W ⟶ V` of the big fppf site of `S`, base change of étale schemes along the
underlying morphism of schemes and base change of algebraic spaces étale over `h_V` along
`h_f : h_W ⟶ h_V` correspond under the chart functors of
`AlgebraicGeometry.Space.representedChartFunctor`: the square

```
V'_étale --- c_V ---> (h_V)_{spaces-étale}
   |                          |
 f'^*                       h_f^*
   v                          v
W'_étale --- c_W ---> (h_W)_{spaces-étale}
```

commutes up to the canonical isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.representedSchemeChartFunctor`: the chart functor, written out, and
  `AlgebraicGeometry.Space.representedSchemeChartFunctorIso` identifying it with
  `AlgebraicGeometry.Space.representedChartFunctor`.
* `AlgebraicGeometry.Space.representedChartBaseChangeIso`: the isomorphism filling the square.
* `AlgebraicGeometry.Space.representedRestriction`: restriction along the chart functor, an
  equivalence (`AlgebraicGeometry.Space.representedRestrictionIso`).
* `AlgebraicGeometry.Space.representedPushforwardIso`: restriction along the chart functors
  intertwines the spaces-étale and the small étale direct images.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An étale scheme over the scheme underlying `V`, regarded as an object of the big fppf site
over `S`. -/
abbrev representedChartObj {V : BigFppfOver B S hS} (U : representedSchemeSmallEtale B S hS V) :
    BigFppfOver B S hS :=
  Over.mk (U.obj.hom ≫ V.hom)

/-- The structure morphism of `representedChartObj U` to `V`. -/
abbrev representedChartStructureHom {V : BigFppfOver B S hS}
    (U : representedSchemeSmallEtale B S hS V) : representedChartObj U ⟶ V :=
  Over.homMk U.obj.hom

/-- The morphism of objects of the site underlying a morphism of étale schemes over the scheme
underlying `V`. -/
abbrev representedChartHomMap {V : BigFppfOver B S hS}
    {U₁ U₂ : representedSchemeSmallEtale B S hS V} (k : U₁ ⟶ U₂) :
    representedChartObj U₁ ⟶ representedChartObj U₂ :=
  Over.homMk k.hom.left (by
    change k.hom.left ≫ U₂.obj.hom ≫ V.hom = U₁.obj.hom ≫ V.hom
    rw [← Category.assoc, Over.w k.hom])

/-- The morphism of representable algebraic spaces induced by a morphism of the site: an
abbreviation of `AlgebraicGeometry.schemeSpaceMap`. -/
abbrev yonedaSpaceHom {V W : BigFppfOver B S hS} (f : W ⟶ V) :
    yonedaSpace B S hS W ⟶ yonedaSpace B S hS V :=
  schemeSpaceMap f

/-- `yonedaSpaceHom` preserves composition. -/
theorem yonedaSpaceHom_comp {U V W : BigFppfOver B S hS} (a : U ⟶ V) (b : V ⟶ W) :
    yonedaSpaceHom (a ≫ b) = yonedaSpaceHom a ≫ yonedaSpaceHom b :=
  ObjectProperty.hom_ext _ (yoneda.map_comp a b)

/-- `yonedaSpaceHom` preserves identities. -/
theorem yonedaSpaceHom_id (V : BigFppfOver B S hS) :
    yonedaSpaceHom (𝟙 V) = 𝟙 (yonedaSpace B S hS V) :=
  ObjectProperty.hom_ext _ (yoneda.map_id V)

/-- **The chart functor, written out.** An étale scheme over the scheme underlying `V` is sent
to the Yoneda algebraic space of its object of the site, over `h_V`. It is
`AlgebraicGeometry.Space.representedChartFunctor` by definition
(`AlgebraicGeometry.Space.representedSchemeChartFunctorIso`). -/
abbrev representedSchemeChartFunctor (V : BigFppfOver B S hS) :
    representedSchemeSmallEtale B S hS V ⥤ SpacesEtale B S hS (yonedaSpace B S hS V) where
  obj U := ⟨Over.mk (yonedaSpaceHom (representedChartStructureHom U)),
    by exact ((representedChartFunctor B S hS V).obj U).property⟩
  map {U₁ U₂} k := ObjectProperty.homMk (Over.homMk
    (yonedaSpaceHom (representedChartHomMap k)) (by
      change yonedaSpaceHom (representedChartHomMap k) ≫
          yonedaSpaceHom (representedChartStructureHom U₂) =
        yonedaSpaceHom (representedChartStructureHom U₁)
      rw [← yonedaSpaceHom_comp]
      exact congrArg yonedaSpaceHom (Over.OverMorphism.ext (Over.w k.hom))))
  map_id U := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (by
    change yonedaSpaceHom (representedChartHomMap (𝟙 U)) =
      𝟙 (yonedaSpace B S hS (representedChartObj U))
    rw [← yonedaSpaceHom_id]
    exact congrArg yonedaSpaceHom (Over.OverMorphism.ext rfl)))
  map_comp {U₁ U₂ U₃} k l := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (by
    change yonedaSpaceHom (representedChartHomMap (k ≫ l)) =
      yonedaSpaceHom (representedChartHomMap k) ≫ yonedaSpaceHom (representedChartHomMap l)
    rw [← yonedaSpaceHom_comp]
    exact congrArg yonedaSpaceHom (Over.OverMorphism.ext rfl)))

/-- The written-out chart functor is the chart functor. -/
def representedSchemeChartFunctorIso (V : BigFppfOver B S hS) :
    representedSchemeChartFunctor V ≅ representedChartFunctor B S hS V :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

variable {V W : BigFppfOver B S hS} (f : W ⟶ V)

/-- The base change along `f` of an étale scheme over the scheme underlying `V`, as an object of
the site. -/
abbrev representedChartPullbackObj (U : representedSchemeSmallEtale B S hS V) :
    BigFppfOver B S hS :=
  Over.mk (pullback.snd U.obj.hom f.left ≫ W.hom)

/-- The first projection of the base change, as a morphism of the site. -/
abbrev representedChartPullbackFst (U : representedSchemeSmallEtale B S hS V) :
    representedChartPullbackObj f U ⟶ representedChartObj U :=
  Over.homMk (pullback.fst U.obj.hom f.left) (by
    change pullback.fst U.obj.hom f.left ≫ U.obj.hom ≫ V.hom =
      pullback.snd U.obj.hom f.left ≫ W.hom
    rw [pullback.condition_assoc, Over.w f])

/-- The second projection of the base change, as a morphism of the site. -/
abbrev representedChartPullbackSnd (U : representedSchemeSmallEtale B S hS V) :
    representedChartPullbackObj f U ⟶ W :=
  Over.homMk (pullback.snd U.obj.hom f.left)

/-- The base change of an étale scheme over the scheme underlying `V` is a fibre product in the
big fppf site. -/
theorem isPullback_representedChartPullback (U : representedSchemeSmallEtale B S hS V) :
    IsPullback (representedChartPullbackFst f U) (representedChartPullbackSnd f U)
      (representedChartStructureHom U) f :=
  IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext pullback.condition)
    (IsPullback.of_hasPullback U.obj.hom f.left)

/-- The Yoneda image of the base-change square of `isPullback_representedChartPullback` is a fibre
product of algebraic spaces. -/
theorem isPullback_yonedaSpace_representedChartPullback
    (U : representedSchemeSmallEtale B S hS V) :
    IsPullback (yonedaSpaceHom (representedChartPullbackFst f U))
      (yonedaSpaceHom (representedChartPullbackSnd f U))
      (yonedaSpaceHom (representedChartStructureHom U)) (yonedaSpaceHom f) :=
  isPullback_of_isPullback_hom B S hS ((isPullback_representedChartPullback f U).map yoneda)

/-- The cartesian square of a spaces-étale base change of a chart. -/
theorem isPullback_spacesBaseChange_representedChart (U : representedSchemeSmallEtale B S hS V) :
    IsPullback ((spacesBaseChange B S hS (yonedaSpaceHom f)).projection.app
        ((representedSchemeChartFunctor V).obj U))
      ((spacesBaseChange B S hS (yonedaSpaceHom f)).functor.obj
        ((representedSchemeChartFunctor V).obj U)).obj.hom
      (yonedaSpaceHom (representedChartStructureHom U)) (yonedaSpaceHom f) :=
  (spacesBaseChange B S hS (yonedaSpaceHom f)).isPullback ((representedSchemeChartFunctor V).obj U)

/-- The component of the base-change comparison of chart functors. -/
def representedChartBaseChangeIsoApp (U : representedSchemeSmallEtale B S hS V) :
    (representedSchemeChartFunctor W).obj
        ((smallEtaleBaseChange (associatedBigEtaleSite B) f.left).obj U) ≅
      (spacesBaseChange B S hS (yonedaSpaceHom f)).functor.obj
        ((representedSchemeChartFunctor V).obj U) :=
  ObjectProperty.isoMk _
    (Over.isoMk ((isPullback_yonedaSpace_representedChartPullback f U).isoIsPullback _ _
        (isPullback_spacesBaseChange_representedChart f U))
      (IsPullback.isoIsPullback_hom_snd _ _ _ _))

/-- The component of the base-change comparison, followed by the cartesian projection, is the
Yoneda image of the first projection of the scheme base change. -/
@[reassoc (attr := simp)]
theorem representedChartBaseChangeIsoApp_hom_fst (U : representedSchemeSmallEtale B S hS V) :
    (representedChartBaseChangeIsoApp f U).hom.hom.left ≫
        (spacesBaseChange B S hS (yonedaSpaceHom f)).projection.app
          ((representedSchemeChartFunctor V).obj U) =
      yonedaSpaceHom (representedChartPullbackFst f U) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The component of the base-change comparison, followed by the structure morphism, is the
Yoneda image of the second projection of the scheme base change. -/
@[reassoc (attr := simp)]
theorem representedChartBaseChangeIsoApp_hom_snd (U : representedSchemeSmallEtale B S hS V) :
    (representedChartBaseChangeIsoApp f U).hom.hom.left ≫
        ((spacesBaseChange B S hS (yonedaSpaceHom f)).functor.obj
          ((representedSchemeChartFunctor V).obj U)).obj.hom =
      yonedaSpaceHom (representedChartPullbackSnd f U) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- **The chart functors commute with base change.** -/
def representedChartBaseChangeIso :
    smallEtaleBaseChange (associatedBigEtaleSite B) f.left ⋙ representedSchemeChartFunctor W ≅
      representedSchemeChartFunctor V ⋙ (spacesBaseChange B S hS (yonedaSpaceHom f)).functor :=
  NatIso.ofComponents (representedChartBaseChangeIsoApp f) (fun {U₁ U₂} k => by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (isPullback_spacesBaseChange_representedChart f U₂).hom_ext
    · have h1 : ((representedSchemeChartFunctor V ⋙
          (spacesBaseChange B S hS (yonedaSpaceHom f)).functor).map k).hom.left ≫
          (spacesBaseChange B S hS (yonedaSpaceHom f)).projection.app
            ((representedSchemeChartFunctor V).obj U₂) =
          (spacesBaseChange B S hS (yonedaSpaceHom f)).projection.app
            ((representedSchemeChartFunctor V).obj U₁) ≫
          ((representedSchemeChartFunctor V).map k).hom.left :=
        pullback.lift_fst _ _ _
      have h2 := representedChartBaseChangeIsoApp_hom_fst f U₁
      have h3 := representedChartBaseChangeIsoApp_hom_fst f U₂
      simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left,
        Category.assoc] at h1 h2 h3 ⊢
      rw [h1, h3, reassoc_of% h2]
      simp only [Functor.comp_map, ObjectProperty.homMk_hom, Over.homMk_left]
      have e : (representedChartHomMap
            ((smallEtaleBaseChange (associatedBigEtaleSite B) f.left).map k) ≫
          representedChartPullbackFst f U₂ :
            representedChartPullbackObj f U₁ ⟶ representedChartObj U₂) =
          representedChartPullbackFst f U₁ ≫ representedChartHomMap k :=
        Over.OverMorphism.ext (pullback.lift_fst _ _ _)
      exact (yonedaSpaceHom_comp _ _).symm.trans
        ((congrArg yonedaSpaceHom e).trans (yonedaSpaceHom_comp _ _))
    · have h1 : ((representedSchemeChartFunctor V ⋙
          (spacesBaseChange B S hS (yonedaSpaceHom f)).functor).map k).hom.left ≫
          ((spacesBaseChange B S hS (yonedaSpaceHom f)).functor.obj
            ((representedSchemeChartFunctor V).obj U₂)).obj.hom =
          ((spacesBaseChange B S hS (yonedaSpaceHom f)).functor.obj
            ((representedSchemeChartFunctor V).obj U₁)).obj.hom :=
        Over.w _
      have h2 := representedChartBaseChangeIsoApp_hom_snd f U₁
      have h3 := representedChartBaseChangeIsoApp_hom_snd f U₂
      simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left,
        Category.assoc] at h1 h2 h3 ⊢
      rw [h1, h2, h3]
      simp only [Functor.comp_map, ObjectProperty.homMk_hom, Over.homMk_left]
      have e : (representedChartHomMap
            ((smallEtaleBaseChange (associatedBigEtaleSite B) f.left).map k) ≫
          representedChartPullbackSnd f U₂ : representedChartPullbackObj f U₁ ⟶ W) =
          representedChartPullbackSnd f U₁ :=
        Over.OverMorphism.ext (pullback.lift_snd _ _ _)
      exact congrArg yonedaSpaceHom e)

/-- The written-out chart functor is continuous. -/
instance representedSchemeChartFunctor_isContinuous (V : BigFppfOver B S hS) :
    (representedSchemeChartFunctor V).IsContinuous (representedSchemeTopology B S hS V)
      (SpacesEtale.topology B S hS (yonedaSpace B S hS V)) :=
  Functor.isContinuous_of_iso (representedSchemeChartFunctorIso V).symm _ _

section Restriction

universe v' u'

/-- Restriction along the written-out chart functor: the comparison of the spaces-étale topos of
`h_V` with the small étale topos of the scheme underlying `V`, for sheaves with values in `A`. -/
abbrev representedRestriction (V : BigFppfOver B S hS) (A : Type u') [Category.{v'} A] :
    Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS V)) A ⥤
      Sheaf (representedSchemeTopology B S hS V) A :=
  (representedSchemeChartFunctor V).sheafPushforwardContinuous A
    (representedSchemeTopology B S hS V) (SpacesEtale.topology B S hS (yonedaSpace B S hS V))

/-- The restriction of sheaves of sets is the functor of the equivalence
`AlgebraicGeometry.Space.representedSpacesEtaleSheafEquiv`. -/
def representedRestrictionIso (V : BigFppfOver B S hS) :
    representedRestriction V (Type (u + 1)) ≅ (representedSpacesEtaleSheafEquiv B S hS V).functor :=
  Functor.sheafPushforwardContinuousIso (representedSchemeChartFunctorIso V) (Type (u + 1))
      (representedSchemeTopology B S hS V) (SpacesEtale.topology B S hS (yonedaSpace B S hS V)) ≪≫
    (representedSpacesEtaleSheafEquiv_functor_iso B S hS V).symm

/-- **The restriction is an equivalence of categories**, for every coefficient category in which
the right Kan extensions along the comparison functor of Stacks 03G1 exist. -/
instance representedRestriction_isEquivalence (V : BigFppfOver B S hS) (A : Type u')
    [Category.{v'} A] [∀ Y, HasLimitsOfShape
      (StructuredArrow Y (comparisonFunctor B S hS (yonedaSpace B S hS V)).op) A] :
    (representedRestriction V A).IsEquivalence :=
  letI : (comparisonFunctor B S hS (yonedaSpace B S hS V)).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj V))
      (SpacesEtale.topology B S hS (yonedaSpace B S hS V)) :=
    comparisonFunctor_isContinuous B S hS (yonedaSpace B S hS V)
  letI : ((comparisonFunctor B S hS (yonedaSpace B S hS V)).sheafPushforwardContinuous A
      (SmallEtale.topology B S hS (yoneda.obj V))
      (SpacesEtale.topology B S hS (yonedaSpace B S hS V))).IsEquivalence :=
    comparisonFunctor_sheafEquivalence B S hS (yonedaSpace B S hS V) A
  let E : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS V)) A ≌
      Sheaf (representedSchemeTopology B S hS V) A :=
    ((comparisonFunctor B S hS (yonedaSpace B S hS V)).sheafPushforwardContinuous A
      (SmallEtale.topology B S hS (yoneda.obj V))
      (SpacesEtale.topology B S hS (yonedaSpace B S hS V))).asEquivalence.trans
    ((representedSmallEtaleEquivalence B S hS V).sheafCongr
      (SmallEtale.topology B S hS (yoneda.obj V)) (representedSchemeTopology B S hS V) A)
  Functor.isEquivalence_of_iso
    ((Iso.refl _ : E.functor ≅ (representedChartFunctor B S hS V).sheafPushforwardContinuous A
        (representedSchemeTopology B S hS V)
        (SpacesEtale.topology B S hS (yonedaSpace B S hS V))) ≪≫
      Functor.sheafPushforwardContinuousIso (representedSchemeChartFunctorIso V).symm A
        (representedSchemeTopology B S hS V) (SpacesEtale.topology B S hS (yonedaSpace B S hS V)))

/-- **The comparison of the two topoi commutes with direct image.** Under the restrictions along
the chart functors, the spaces-étale direct image along `h_f` is the small étale direct image
along the morphism of schemes underlying `f`. -/
def representedPushforwardIso (A : Type u') [Category.{v'} A] :
    letI := (spacesBaseChange_isMorphismOfSites B S hS (yonedaSpaceHom f)).isContinuous
    letI : (smallEtaleBaseChange (associatedBigEtaleSite B) f.left).IsContinuous
        (representedSchemeTopology B S hS V) (representedSchemeTopology B S hS W) :=
      smallEtaleBaseChange_isContinuous (associatedBigEtaleSite B) f.left
    (spacesBaseChange B S hS (yonedaSpaceHom f)).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS (yonedaSpace B S hS V))
        (SpacesEtale.topology B S hS (yonedaSpace B S hS W)) ⋙ representedRestriction V A ≅
      representedRestriction W A ⋙
        (smallEtaleBaseChange (associatedBigEtaleSite B) f.left).sheafPushforwardContinuous
          A (representedSchemeTopology B S hS V) (representedSchemeTopology B S hS W) :=
  letI := (spacesBaseChange_isMorphismOfSites B S hS (yonedaSpaceHom f)).isContinuous
  letI : (smallEtaleBaseChange (associatedBigEtaleSite B) f.left).IsContinuous
      (representedSchemeTopology B S hS V) (representedSchemeTopology B S hS W) :=
    smallEtaleBaseChange_isContinuous (associatedBigEtaleSite B) f.left
  letI : (smallEtaleBaseChange (associatedBigEtaleSite B) f.left ⋙
      representedSchemeChartFunctor W).IsContinuous
      (representedSchemeTopology B S hS V) (SpacesEtale.topology B S hS (yonedaSpace B S hS W)) :=
    Functor.isContinuous_comp _ _ _ (representedSchemeTopology B S hS W) _
  letI : (representedSchemeChartFunctor V ⋙
      (spacesBaseChange B S hS (yonedaSpaceHom f)).functor).IsContinuous
      (representedSchemeTopology B S hS V) (SpacesEtale.topology B S hS (yonedaSpace B S hS W)) :=
    Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS (yonedaSpace B S hS V)) _
  Functor.sheafPushforwardContinuousComp _ _ A _
      (SpacesEtale.topology B S hS (yonedaSpace B S hS V)) _ ≪≫
    Functor.sheafPushforwardContinuousIso (representedChartBaseChangeIso f).symm A
      (representedSchemeTopology B S hS V) (SpacesEtale.topology B S hS (yonedaSpace B S hS W)) ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ A _
      (representedSchemeTopology B S hS W) _).symm

end Restriction

end AlgebraicGeometry.Space

end
