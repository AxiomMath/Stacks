module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.FppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleTargetChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSmallEtaleEssImageLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleHigherVanishing

/-!
# Fppf descent of small étale sheaves of algebraic spaces

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site of
algebraic spaces over the same big fppf site of schemes, and `f : X ⟶ Y` a morphism of algebraic
spaces which is flat, locally of finite presentation and surjective. Write `a_X` for the morphism
from the big fppf topos of `X` to its small étale topos (Stacks 0DGI). Stacks 0DGL says that the
functor `F ↦ (f_small⁻¹F, a_Y⁻¹F, can)` from small étale sheaves on `Y` to triples
`(G, H, α : a_X⁻¹G ≅ f_{big,fppf}⁻¹H)` is an equivalence.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtale_essImage_schemeSliceSheafRestriction` —
  restriction along `Ψ_s : (Sch/A) ⥤ (Spaces/X)`, for `s : h_A ⟶ X`, carries the essential image
  of `a_X⁻¹` into that of the scheme `a_A⁻¹`.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtale_essImage_of_schemeSliceSheafRestriction`
  — conversely, for a surjective étale `t : h_A ⟶ Y`, a big fppf sheaf on `Y` whose restriction
  along `Ψ_t` lies in the essential image of `a_A⁻¹` lies in that of `a_Y⁻¹`.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtale_essImage_of_bigFppfInverseImage` — for
  `f` flat, locally of finite presentation and surjective, `H` lies in the essential image of
  `a_Y⁻¹` as soon as `f_{big,fppf}⁻¹H` lies in that of `a_X⁻¹`.
* `AlgebraicGeometry.BigFppfSpaceSite.isEquivalence_fppfSmallEtaleTripleFunctor` — for `f` flat,
  locally of finite presentation and surjective, the functor `F ↦ (f_small⁻¹F, a_Y⁻¹F, can)`
  into triples is an equivalence.

## References

* [Stacks Project, Tag 0DGL](https://stacks.math.columbia.edu/tag/0DGL)
* [Stacks Project, Tag 0DEU](https://stacks.math.columbia.edu/tag/0DEU)
* [Stacks Project, Tag 0DFV](https://stacks.math.columbia.edu/tag/0DFV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-- Restriction of big fppf sheaves of sets on an algebraic space `X` along
`Ψ_s : (Sch/A) ⥤ (Spaces/X)` (`AlgebraicGeometry.Space.schemeSliceToSpaceSlice`), for a scheme
`A` over `S` and a morphism `s : h_A ⟶ X`: a sheaf on the big fppf site of the scheme `A`. -/
abbrev schemeSliceSheafRestriction {X : T.Spaces} (A : T.Schemes)
    (s : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A ⟶ X) :
    Sheaf (BigFppfSpaceOver.topology T X) (Type (u + 1)) ⥤
      Sheaf (T.schemeSite.topology.over A.left) (Type (u + 1)) :=
  (Space.schemeSliceToSpaceSlice T.schemeSite S T.scheme_mem A s).sheafPushforwardContinuous
    (Type (u + 1)) (T.schemeSite.topology.over A.left) (T.topology.over X)

/-- **Restriction along `Ψ_s` carries the essential image of `a_X⁻¹` into that of `a_A⁻¹`.** -/
theorem fppfToSmallEtale_essImage_schemeSliceSheafRestriction {X : T.Spaces} (A : T.Schemes)
    (s : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A ⟶ X)
    {K : Sheaf (BigFppfSpaceOver.topology T X) (Type (u + 1))}
    (hK : (fppfToSmallEtaleMorphism T E h X).inverseImage.essImage K) :
    (AlgebraicGeometry.fppfToSmallEtaleMorphism T.schemeSite A.left).inverseImage.essImage
      ((schemeSliceSheafRestriction T A s).obj K) := by
  obtain ⟨G, ⟨e⟩⟩ := hK
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let T' : BigFppfSpaceSite S :=
        ⟨tScheme, tSchemeMem, tInitial, tInitialSmall, tInitialFppf, tBound, tOrdinal,
          tOrdinalLim, tInitialBounded, tIsSite, tRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, tScheme, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      exact ⟨(schemeChartSheaf T' E' rfl X A s).obj G,
        ⟨((schemeSliceToBigFppfRestriction_inverseImageIsoType T' E' rfl X A s).app G).symm ≪≫
          (schemeSliceToBigFppfRestrictionType T' E' rfl X A s).mapIso e⟩⟩

/-- **`a_{A,*}` of a restriction along `Ψ_t`, on sections.** Let `t : h_A ⟶ Y` be étale. If
`a_{Y,*}φ` is an isomorphism, so is `a_{A,*}` of the restriction of `φ` along `Ψ_t` on sections
over every object `U` of the small étale site of the scheme `A`. -/
theorem isIso_fppfToSmallEtale_pushforward_map_schemeSliceSheafRestriction_app {Y : T.Spaces}
    (A : T.Schemes) (t : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A ⟶ Y)
    (het : Space.IsEtale T.schemeSite S T.scheme_mem t.hom)
    {K K' : Sheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1))} (φ : K ⟶ K')
    (hφ : IsIso ((fppfToSmallEtaleMorphism T E h Y).pushforward.map φ))
    (U : (SmallEtale (associatedBigEtaleSite T.schemeSite) A.left.obj A.left.property)ᵒᵖ) :
    IsIso (((AlgebraicGeometry.fppfToSmallEtaleMorphism T.schemeSite A.left).pushforward.map
      ((schemeSliceSheafRestriction T A t).map φ)).hom.app U) := by
  have hφp : IsIso ((fppfToSmallEtaleMorphism T E h Y).pushforward.map φ).hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ (Type (u + 1))).map
      ((fppfToSmallEtaleMorphism T E h Y).pushforward.map φ)))
  have hU : Space.IsEtale T.schemeSite S T.scheme_mem
      (((Space.schemeSliceToSpaceSlice T.schemeSite S T.scheme_mem A t).obj
        U.unop.obj).hom.hom) :=
    Space.isEtale_comp _ _ _
      (Space.isEtale_schemeSpaceMap _ _ _ _ (Over.homMk U.unop.obj.hom :
        Over.mk (U.unop.obj.hom ≫ A.hom) ⟶ A) U.unop.property) het
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    change T.schemeSite = eFppfSite at h
    cases h
    let W : Space.SpacesEtale T.schemeSite S T.scheme_mem Y :=
      ⟨(Space.schemeSliceToSpaceSlice T.schemeSite S T.scheme_mem A t).obj U.unop.obj, hU⟩
    exact (inferInstance : IsIso (((fppfToSmallEtaleMorphism T
      ⟨eSchemeSite, eSchemeMem, T.schemeSite, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
        eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
          rfl Y).pushforward.map φ).hom.app (op W)))

/-- **Restriction along `Ψ_t` detects isomorphisms of big fppf sheaves when `t : h_A ⟶ Y` is
surjective and étale.** -/
theorem isIso_of_isIso_schemeSliceSheafRestriction_map {Y : T.Spaces} (A : T.Schemes)
    (t : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A ⟶ Y)
    (het : Space.IsEtale T.schemeSite S T.scheme_mem t.hom)
    (hsurj : Space.IsSurjective T.schemeSite S T.scheme_mem t.hom)
    {K K' : Sheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1))} (φ : K ⟶ K')
    (hφ : IsIso ((schemeSliceSheafRestriction T A t).map φ)) : IsIso φ := by
  let R : Sheaf (T.topology.over ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A))
      (Type (u + 1)) ⥤ Sheaf (T.schemeSite.topology.over A.left) (Type (u + 1)) :=
    (Over.post (X := A) (schemeSpaceFunctor T.schemeSite S T.scheme_mem)).sheafPushforwardContinuous
        (Type (u + 1)) ((BigFppfOver.topology T.schemeSite S T.scheme_mem).over A)
        (T.topology.over ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A)) ⋙
      (Over.iteratedSliceEquiv A).inverse.sheafPushforwardContinuous (Type (u + 1))
        (T.schemeSite.topology.over A.left)
        ((BigFppfOver.topology T.schemeSite S T.scheme_mem).over A)
  have : R.IsEquivalence := inferInstance
  have h₁ : IsIso (R.map ((T.topology.overMapPullback (Type (u + 1)) t).map φ)) := hφ
  exact isIso_of_isIso_overMap_pushforward_map T t (liftingSieve_mem_of_isEtale T t het hsurj) φ
    (isIso_of_reflects_iso _ R)

/-- **Descent of the essential image of `a⁻¹` from a surjective étale scheme chart.** Let
`t : h_A ⟶ Y` be a surjective étale morphism from the algebraic space of a scheme `A`, and `H` a
big fppf sheaf on `Y` whose restriction along `Ψ_t` lies in the essential image of `a_A⁻¹`. Then
`H` lies in the essential image of `a_Y⁻¹`. -/
theorem fppfToSmallEtale_essImage_of_schemeSliceSheafRestriction {Y : T.Spaces} (A : T.Schemes)
    (t : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A ⟶ Y)
    (het : Space.IsEtale T.schemeSite S T.scheme_mem t.hom)
    (hsurj : Space.IsSurjective T.schemeSite S T.scheme_mem t.hom)
    {H : Sheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1))}
    (hH : (AlgebraicGeometry.fppfToSmallEtaleMorphism T.schemeSite A.left).inverseImage.essImage
      ((schemeSliceSheafRestriction T A t).obj H)) :
    (fppfToSmallEtaleMorphism T E h Y).inverseImage.essImage H := by
  let a := fppfToSmallEtaleMorphism T E h Y
  rw [← a.adj.isIso_counit_app_iff_mem_essImage]
  have hu := isIso_fppfToSmallEtaleMorphism_unit T E h Y
  have hε : IsIso (a.pushforward.map (a.adj.counit.app H)) := by
    have : IsIso (a.adj.unit.app (a.pushforward.obj H) ≫
        a.pushforward.map (a.adj.counit.app H)) := by
      rw [a.adj.right_triangle_components H]
      exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩
    exact IsIso.of_isIso_comp_left (a.adj.unit.app _) _
  refine isIso_of_isIso_schemeSliceSheafRestriction_map T A t het hsurj _ ?_
  refine AlgebraicGeometry.isIso_of_isIso_fppfToSmallEtale_pushforward_map T.schemeSite
    ((schemeSliceSheafRestriction T A t).map (a.adj.counit.app H))
    (fppfToSmallEtale_essImage_schemeSliceSheafRestriction T E h A t ⟨_, ⟨Iso.refl _⟩⟩) hH ?_
  have key := isIso_fppfToSmallEtale_pushforward_map_schemeSliceSheafRestriction_app T E h A t
    het (a.adj.counit.app H) hε
  have : IsIso ((sheafToPresheaf _ (Type (u + 1))).map
      ((AlgebraicGeometry.fppfToSmallEtaleMorphism T.schemeSite A.left).pushforward.map
        ((schemeSliceSheafRestriction T A t).map (a.adj.counit.app H)))) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ key
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ (Type (u + 1)))

/-- The identity of `W` as an isomorphism of schemes over `S` between the two structure
morphisms `W ⟶ A ⟶ S` and `W ⟶ A ⟶ A' ⟶ S`. -/
abbrev schemeSliceSquareSchemeIso {A A' : T.Schemes} (f₀ : A ⟶ A') (W : Over A.left) :
    (Over.mk (W.hom ≫ A.hom) : T.Schemes) ≅ Over.mk ((W.hom ≫ f₀.left) ≫ A'.hom) :=
  Over.isoMk (Iso.refl W.left) (by simp [Over.w f₀])

/-- `schemeSliceSquareSchemeIso` followed by `W ⟶ A ⟶ A'` over `A'` is `W ⟶ A` followed by
`f₀`. -/
theorem schemeSliceSquareSchemeIso_hom_comp {A A' : T.Schemes} (f₀ : A ⟶ A') (W : Over A.left) :
    (schemeSliceSquareSchemeIso T f₀ W).hom ≫
        (Over.homMk (W.hom ≫ f₀.left) : Over.mk ((W.hom ≫ f₀.left) ≫ A'.hom) ⟶ A') =
      (Over.homMk W.hom : Over.mk (W.hom ≫ A.hom) ⟶ A) ≫ f₀ := by
  ext
  simp

/-- **`Ψ` along a commutative square.** For a commutative square `h_{f₀} ≫ t = a ≫ f` with
`f₀ : A ⟶ A'` a morphism of schemes over `S`, `a : h_A ⟶ X`, `t : h_{A'} ⟶ Y` and `f : X ⟶ Y`,
composing `Ψ_a` with `f` is base change along `f₀` followed by `Ψ_t`: both send a scheme `W`
over `A` to `h_W` over `Y`. -/
def schemeSliceToSpaceSliceSquareIso {X Y : T.Spaces} {A A' : T.Schemes}
    (a : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A ⟶ X)
    (t : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A' ⟶ Y) (f : X ⟶ Y)
    (f₀ : A ⟶ A') (w : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map f₀ ≫ t = a ≫ f) :
    Space.schemeSliceToSpaceSlice T.schemeSite S T.scheme_mem A a ⋙ Over.map f ≅
      Over.map f₀.left ⋙ Space.schemeSliceToSpaceSlice T.schemeSite S T.scheme_mem A' t :=
  NatIso.ofComponents (fun W => Over.isoMk ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).mapIso
      (schemeSliceSquareSchemeIso T f₀ W)) (by
        refine ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map_comp_assoc _ _ t).symm.trans ?_
        refine (congrArg (fun m => (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map m ≫ t)
          (schemeSliceSquareSchemeIso_hom_comp T f₀ W)).trans ?_
        refine ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map_comp_assoc _ _ t).trans ?_
        refine (congrArg (fun m => (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map
          (Over.homMk W.hom : Over.mk (W.hom ≫ A.hom) ⟶ A) ≫ m) w).trans ?_
        exact (Category.assoc _ _ _).symm)) (by
    intro W W' g
    apply Over.OverMorphism.ext
    have h₀ : (Over.homMk g.left (Over.w_assoc g A.hom) :
          (Over.mk (W.hom ≫ A.hom) : T.Schemes) ⟶ Over.mk (W'.hom ≫ A.hom)) ≫
          (schemeSliceSquareSchemeIso T f₀ W').hom =
        (schemeSliceSquareSchemeIso T f₀ W).hom ≫
          (Over.homMk g.left (by
            dsimp only [Over.mk_hom]
            simp only [Category.assoc]
            exact Over.w_assoc g _) :
            (Over.mk ((W.hom ≫ f₀.left) ≫ A'.hom) : T.Schemes) ⟶
              Over.mk ((W'.hom ≫ f₀.left) ≫ A'.hom)) := by
      ext
      simp
    exact ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map_comp _ _).symm.trans
      ((congrArg (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map h₀).trans
        ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map_comp _ _)))

/-- **Descent of the essential image of `a⁻¹` along a flat, locally finitely presented,
surjective morphism of algebraic spaces.** Let `f : X ⟶ Y` be flat, locally of finite
presentation and surjective, and `H` a big fppf sheaf on `Y` such that `f_{big,fppf}⁻¹H` lies in
the essential image of `a_X⁻¹`. Then `H` lies in the essential image of `a_Y⁻¹`. -/
theorem fppfToSmallEtale_essImage_of_bigFppfInverseImage {X Y : T.Spaces} (f : X ⟶ Y)
    (hf : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation T.schemeSite S T.scheme_mem f.hom)
    (hsurj : Space.IsSurjective T.schemeSite S T.scheme_mem f.hom)
    {H : Sheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1))}
    (hH : (fppfToSmallEtaleMorphism T E h X).inverseImage.essImage
      ((bigFppfMorphism T f).inverseImage.obj H)) :
    (fppfToSmallEtaleMorphism T E h Y).inverseImage.essImage H := by
  obtain ⟨U₀, t₀, ht_surj, ht_et⟩ := Y.property.exists_atlas
  let t : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj U₀ ⟶ Y := ObjectProperty.homMk t₀
  have het : Space.IsEtale T.schemeSite S T.scheme_mem t.hom :=
    (Space.isEtale_iff_presheaf_of_yoneda _ _ _ t₀).2 ht_et
  have htsurj : Space.IsSurjective T.schemeSite S T.scheme_mem t.hom :=
    (Space.surjective_iff_surjective_pointsMap _ _ _ Y.1 Y.property U₀ t₀).1 ht_surj
  let P := AlgebraicSpaces.fiberProduct T.schemeSite S T.scheme_mem f t
  obtain ⟨X₀, c₀, hc_surj, hc_et⟩ := P.property.exists_atlas
  let a₀ : yoneda.obj X₀ ⟶ X.1 := c₀ ≫ pullback.fst f.hom t.hom
  let q₀ : yoneda.obj X₀ ⟶ yoneda.obj U₀ := c₀ ≫ pullback.snd f.hom t.hom
  let f₀ : X₀ ⟶ U₀ := yoneda.preimage q₀
  let a : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj X₀ ⟶ X := ObjectProperty.homMk a₀
  have hq : yoneda.map f₀ = q₀ := Functor.map_preimage _ _
  have hsq₀ : yoneda.map f₀ ≫ t₀ = a₀ ≫ f.hom := by
    rw [hq]
    simp only [q₀, a₀]
    exact congrArg (c₀ ≫ ·) pullback.condition.symm
  have hsq : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map f₀ ≫ t = a ≫ f :=
    ObjectProperty.hom_ext _ hsq₀
  have ha_et : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme T.schemeSite S T.scheme_mem)).presheaf
        a₀ := by
    have : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
        MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme T.schemeSite S T.scheme_mem)).IsStableUnderComposition :=
      MorphismProperty.IsStableUnderComposition.inverseImage _
    have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme T.schemeSite S T.scheme_mem))).IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition (F := yoneda) _
    exact MorphismProperty.comp_mem _ _ _ hc_et
      (Space.presheaf_pullback_fst _ _ _ t₀ f.hom ht_et)
  have hflat : Flat ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map f₀) :=
    hf X₀ U₀ a₀ t₀ f₀ ha_et ht_et hsq₀
  have hlfp₀ : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map f₀) :=
    hlfp X₀ U₀ a₀ t₀ f₀ ha_et ht_et hsq₀
  have hsurj₀ : Surjective ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map f₀) := by
    have hc : Space.IsSurjective T.schemeSite S T.scheme_mem c₀ :=
      (Space.surjective_iff_surjective_pointsMap _ _ _ P.1 P.property X₀ c₀).1 hc_surj
    have hsnd := Space.isSurjective_of_isPullback _ _ _
      (AlgebraicSpaces.isPullback_fiberProduct T.schemeSite S T.scheme_mem f t) hsurj
    have hq₀ : Space.IsSurjective T.schemeSite S T.scheme_mem q₀ :=
      Space.isSurjective_comp _ _ _ hc hsnd
    rw [← hq] at hq₀
    exact (Space.presheaf_yoneda_map_iff _ _ _ inferInstance f₀).1
      ((Space.surjective_yonedaMap_iff_surjective_pointsMap _ _ _ f₀).2 hq₀)
  have : Flat (T.schemeSite.inclusion.map f₀.left) := hflat
  have : LocallyOfFinitePresentation (T.schemeSite.inclusion.map f₀.left) := hlfp₀
  have : Surjective (T.schemeSite.inclusion.map f₀.left) := hsurj₀
  have h₁ := fppfToSmallEtale_essImage_schemeSliceSheafRestriction T E h X₀ a hH
  let : (Space.schemeSliceToSpaceSlice T.schemeSite S T.scheme_mem X₀ a ⋙ Over.map f).IsContinuous
      (T.schemeSite.topology.over X₀.left) (T.topology.over Y) :=
    Functor.isContinuous_comp _ _ _ (T.topology.over X) _
  let : (Over.map f₀.left ⋙
      Space.schemeSliceToSpaceSlice T.schemeSite S T.scheme_mem U₀ t).IsContinuous
      (T.schemeSite.topology.over X₀.left) (T.topology.over Y) :=
    Functor.isContinuous_comp _ _ _ (T.schemeSite.topology.over U₀.left) _
  have e : (schemeSliceSheafRestriction T X₀ a).obj ((bigFppfMorphism T f).inverseImage.obj H) ≅
      ((Over.map f₀.left).sheafPushforwardContinuous (Type (u + 1))
        (T.schemeSite.topology.over X₀.left) (T.schemeSite.topology.over U₀.left)).obj
          ((schemeSliceSheafRestriction T U₀ t).obj H) :=
    (schemeSliceSheafRestriction T X₀ a).mapIso ((bigFppfMorphism_inverseImageIso T f).app H) ≪≫
      (Functor.sheafPushforwardContinuousIso (schemeSliceToSpaceSliceSquareIso T a t f f₀ hsq)
        (Type (u + 1)) (T.schemeSite.topology.over X₀.left) (T.topology.over Y)).app H
  have h₂ := ObjectProperty.prop_of_iso _ e h₁
  have h₃ := AlgebraicGeometry.fppfToSmallEtale_essImage_of_restriction T.schemeSite f₀.left h₂
  exact fppfToSmallEtale_essImage_of_schemeSliceSheafRestriction T E h U₀ t het htsurj h₃

/-- **Fppf descent of small étale sheaves.** Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S` which is flat, locally of finite presentation and surjective. Then the functor
`Sh(Y_étale) ⥤ {(G, H, α)}`, `F ↦ (f_small⁻¹F, a_Y⁻¹F, can)`, into the category of triples with
`G ∈ Sh(X_étale)`, `H ∈ Sh((Spaces/Y)_fppf)` and `α : a_X⁻¹G ⟶ f_{big,fppf}⁻¹H` an isomorphism,
is an equivalence of categories.

The category of triples is the two-fibre product `a_X⁻¹ ⊡ f_{big,fppf}⁻¹`
(`CategoryTheory.Limits.CategoricalPullback`), whose objects are exactly the triples, and the
functor is `AlgebraicGeometry.BigFppfSpaceSite.fppfSmallEtaleTripleFunctor`, built from the
canonical isomorphism `can = AlgebraicGeometry.BigFppfSpaceSite.fppfSmallEtaleInverseImageCommIso`.
-/
@[stacks 0DGL]
theorem isEquivalence_fppfSmallEtaleTripleFunctor {X Y : T.Spaces} (f : X ⟶ Y)
    (hf : Space.IsFlat T.schemeSite S T.scheme_mem f.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation T.schemeSite S T.scheme_mem f.hom)
    (hsurj : Space.IsSurjective T.schemeSite S T.scheme_mem f.hom) :
    (fppfSmallEtaleTripleFunctor T E h f).IsEquivalence :=
  isEquivalence_fppfSmallEtaleTripleFunctor_of_essImage T E h f fun _ hH =>
    fppfToSmallEtale_essImage_of_bigFppfInverseImage T E h f hf hlfp hsurj hH

end AlgebraicGeometry.BigFppfSpaceSite

end
