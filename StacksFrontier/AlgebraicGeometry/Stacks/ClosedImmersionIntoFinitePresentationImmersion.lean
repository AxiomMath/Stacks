module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedImmersionIntoFinitePresentationStage
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaQuotientStackSquareFibred
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFppfCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackOfIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance

/-!
# The closed immersion in the proof of Stacks 0CQ1

Let `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over `Y` whose source square is cartesian. Stacks 04ZN says that the square formed by the charts
`U ⟶ [U/R]`, `U' ⟶ [U'/R']`, the map `U ⟶ U'` and `[φ] : [U/R] ⟶ [U'/R']` is a 2-fibre product.
The proof of Stacks 0CQ1 uses it, together with Stacks 0503, to see that `[φ]` is a closed
immersion as soon as `U ⟶ U'` is one. Quotient stacks are not objects of the 2-category of
algebraic stacks (their hom sets sit one universe higher), so the argument is carried out on
algebraic stacks `𝒳 ≃ [U/R]` and `𝒳' ≃ [U'/R']` over `S`: this file transports the 2-fibre product
of Stacks 04ZN to the corresponding square of `𝒳` and `𝒳'`, and applies Stacks 0503 to it.

## Main definitions

* `AlgebraicGeometry.Stack.modelChart`, `AlgebraicGeometry.Stack.modelMap` and
  `AlgebraicGeometry.Stack.modelSquare`: the square of Stacks 04ZN read on `𝒳` and `𝒳'`.

## Main results

* `AlgebraicGeometry.Stack.isSurjectiveFlatLocallyOfFinitePresentation_quotientChart`: the chart
  of a smooth groupoid is a flat surjection locally of finite presentation.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_modelSquare`: Stacks 04ZN on `𝒳` and `𝒳'`.
* `AlgebraicGeometry.Stack.exists_isClosedImmersion_of_models`: the closed immersion `𝒳 ⟶ 𝒳'`
  over `Y`, by Stacks 0503.
* `AlgebraicGeometry.Stack.exists_closedImmersion_stageModel_of_isFiniteType`: the stage stack of
  the proof of Stacks 0CQ1 together with the closed immersion into its base change, at every late
  stage.

## References

* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
* [Stacks Project, Tag 0503](https://stacks.math.columbia.edu/tag/0503)
* [Stacks Project, Tag 0CQ1](https://stacks.math.columbia.edu/tag/0CQ1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

open Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS}

/-- **The chart of a quotient stack is a flat surjection locally of finite presentation.** -/
theorem isSurjectiveFlatLocallyOfFinitePresentation_quotientChart
    {Y : AlgebraicSpaces B S hS} {G : GroupoidInAlgebraicSpaces B S hS Y}
    (hG : GroupoidInAlgebraicSpaces.IsSmooth B S hS G)
    (hdiag : HasRepresentableDiagonal B S hS (quotientStackCFG B S hS G))
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (e : BasedCategory.Equivalence (quotientStack G) 𝒳.val) :
    IsSurjectiveFlatLocallyOfFinitePresentation B S hS
      (Bicategory.InducedBicategory.mkHom (BasedFunctor.comp (quotientStackProjection G)
        e.functor) : fibredCategory B S hS G.objects.obj ⟶ 𝒳) := by
  have hπ := isRepresentableByAlgebraicSpaces_quotientStackProjectionHom_of_hasRepresentableDiagonal
    B S hS G hdiag
  let A := QuotientAtlas.presentation G hπ
  have hsm := QuotientAtlas.hasRelativeProperty.{u, u} A (smoothMorphismProperty B S hS) hG.1
  have hsu := QuotientAtlas.isSurjective.{u, u} A
  let a : (fibredCategory B S hS G.objects.obj).val ⥤ᵇ (liftedObjectSpace G).val :=
    ⟨ULiftHom.up, rfl⟩
  let g : fibredCategory B S hS G.objects.obj ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom (BasedFunctor.comp (quotientStackProjection G) e.functor)
  let α : BasedFunctor.comp a (quotientStackProjectionHom G).hom ≅
      BasedFunctor.comp g.hom e.inverse :=
    (BasedCategory.isoWhiskerLeft (quotientStackProjection G) e.unitIso).symm
  have : Functor.IsEquivalence a.toFunctor :=
    (ULiftHom.equiv (C := (fibredCategory B S hS G.objects.obj).val.obj)).isEquivalence_functor
  have : Functor.IsEquivalence e.inverse.toFunctor := e.symm.equiv.isEquivalence_functor
  have hg := (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS g.hom
    (quotientStackProjectionHom G).hom a e.inverse α).1 hπ
  have hsm' := hasRelativeProperty_of_equivalences B S hS _ g (quotientStackProjectionHom G) a
    e.inverse α hπ hg hsm
  have hsu' := hasRelativeProperty_of_equivalences B S hS _ g (quotientStackProjectionHom G) a
    e.inverse α hπ hg hsu
  intro V yv hyv F hF hE
  have h1 := hsm' V yv hyv F hF hE
  exact ⟨hsu' V yv hyv F hF hE, isFlat_of_isSmooth B S hS _ h1,
    isLocallyOfFinitePresentation_of_isSmooth B S hS h1⟩

section Square

variable {Y : AlgebraicSpaces B S hS} {G G' : GroupoidInAlgebraicSpaces B S hS Y}
  (φ : GroupoidInAlgebraicSpaces.Hom G G')
  {𝒳 𝒳' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (e : BasedCategory.Equivalence 𝒳.val (quotientStack G))
  (e' : BasedCategory.Equivalence (quotientStack G') 𝒳'.val)

/-- The chart `U' ⟶ [U'/R'] ≃ 𝒳'` of a model of a quotient stack. -/
noncomputable abbrev modelChart : fibredCategory B S hS G'.objects.obj ⟶ 𝒳' :=
  Bicategory.InducedBicategory.mkHom (BasedFunctor.comp (quotientStackProjection G') e'.functor)

/-- The 1-morphism `𝒳 ≃ [U/R] ⟶ [U'/R'] ≃ 𝒳'` of models induced by a morphism of groupoids. -/
noncomputable abbrev modelMap : 𝒳 ⟶ 𝒳' :=
  Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp (BasedFunctor.comp e.functor (quotientStackMap φ)) e'.functor)

/-- The filler `π ≫ [φ] ≅ 𝒮_f ≫ π'` of the square of Stacks 04ZN, as a 2-isomorphism of
1-morphisms over the site. -/
noncomputable abbrev functorialityCellBased :
    BasedFunctor.comp (quotientStackProjection G) (quotientStackMap φ) ≅
      BasedFunctor.comp (objectSpaceMap φ) (quotientStackProjection G') :=
  BasedNatIso.mkNatIso (functorialityProjectionCellUnlifted φ)
    (functorialityProjectionCellUnlifted_isHomLift φ)

/-- The 2-commutative square `U ⟶ U'`, `U ⟶ [U/R] ≃ 𝒳` over `U' ⟶ 𝒳'`, `𝒳 ⟶ 𝒳'` whose 2-fibre
product property is Stacks 04ZN read on the models. -/
noncomputable def modelSquare :
    Bicategory.TwoCommSq (modelChart (G' := G') e') (modelMap φ e e') where
  pt := fibredCategory B S hS G.objects.obj
  fst := Bicategory.InducedBicategory.mkHom (objectSpaceMap φ)
  snd := Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp (quotientStackProjection G) e.inverse)
  iso := Bicategory.InducedBicategory.isoMk
    ((BasedCategory.isoWhiskerRight (functorialityCellBased φ) e'.functor).symm ≪≫
      BasedCategory.isoWhiskerRight (BasedCategory.isoWhiskerRight
        (BasedCategory.isoWhiskerLeft (quotientStackProjection G) e.counitIso).symm
          (quotientStackMap φ)) e'.functor)

/-- The comparison of the square of Stacks 04ZN read on the models with the square of Stacks 04ZN
itself: the 2-fibre product of the models, carried by the two equivalences onto the 2-fibre
product of the quotient stacks. -/
noncomputable abbrev modelComparison :
    TwoFibreProductOver (fibredCategory B S hS G'.objects.obj).val.p 𝒳.val.p 𝒳'.val.p
        (modelChart (G' := G') e').hom.toFunctor (modelMap φ e e').hom.toFunctor ⥤
      functorialityTwoFibreProductObj φ :=
  TwoFibreProductOver.swap _ _ _ _ _ ⋙
  TwoFibreProductOver.mapBase (pT := 𝒳.val.p) (p𝒜 := (fibredCategory B S hS G'.objects.obj).val.p)
    _ _ e'.inverse.toFunctor e'.inverse.w ⋙
  TwoFibreProductOver.reindex (p𝒴 := (fibredCategory B S hS G'.objects.obj).val.p)
    (F' := e.functor.toFunctor ⋙ (quotientStackMap φ).toFunctor)
    (Functor.isoWhiskerLeft (e.functor.toFunctor ⋙ (quotientStackMap φ).toFunctor)
      (BasedFunctor.toFunctorIso e'.functor e'.inverse e'.unitIso)) (fun x => by
        have h := e'.unitIso.hom.isHomLift' ((quotientStackMap φ).obj (e.functor.obj x))
        rwa [BasedFunctor.w_obj, BasedFunctor.w_obj] at h) ⋙
  TwoFibreProductOver.precomposeFst _ _ _ _ _ _ e.functor.toFunctor e.functor.w ⋙
  TwoFibreProductOver.swap _ _ _ _ _ ⋙
  TwoFibreProductOver.reindex (p𝒴 := (quotientStack G).p)
    (F := (quotientStackProjection G').toFunctor ⋙ e'.functor.toFunctor ⋙ e'.inverse.toFunctor)
    (F' := (ULiftHom.up : (fibredCategory B S hS G'.objects.obj).val.obj ⥤ _) ⋙
          (liftedQuotientStackProjection G').toFunctor)
    (Functor.isoWhiskerLeft (quotientStackProjection G').toFunctor
      (BasedFunctor.toFunctorIso e'.functor e'.inverse e'.unitIso)) (fun x => by
        have h := e'.unitIso.hom.isHomLift' ((quotientStackProjection G').obj x)
        rwa [BasedFunctor.w_obj] at h) ⋙
  TwoFibreProductOver.precomposeFst (fibredCategory B S hS G'.objects.obj).val.p
    (liftedFibredCategory G'.objects).p _ _ _ _
    (ULiftHom.up : (fibredCategory B S hS G'.objects.obj).val.obj ⥤ _) rfl ⋙
  TwoFibreProductOver.swap _ _ _ _ _

/-- **The comparison of the two 2-fibre products is an equivalence**: it is a composite of two
exchanges of factors, a change of target along an equivalence, two reindexings along
2-isomorphisms and two changes of the first factor along equivalences. -/
theorem isEquivalence_modelComparison : (modelComparison φ e e').IsEquivalence := by
  have hW := (fibredCategory B S hS G'.objects.obj).isFiberedInGroupoids
  have hX := 𝒳.isFiberedInGroupoids
  have hQ := isFiberedInGroupoids_quotientStack G
  have hL := isFiberedInGroupoids_liftedFibredCategory G'.objects
  have : e'.inverse.toFunctor.IsEquivalence := e'.symm.equiv.isEquivalence_functor
  unfold modelComparison
  refine @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ inferInstance <|
    @Functor.isEquivalence_trans _ _ _ _ _ _ _ _
      (TwoFibreProductOver.isEquivalence_mapBase e'.inverse.w) <|
    @Functor.isEquivalence_trans _ _ _ _ _ _ _ _
      (TwoFibreProductOver.isEquivalence_reindex _ _) <|
    @Functor.isEquivalence_trans _ _ _ _ _ _ _ _
      (TwoFibreProductOver.isEquivalence_precomposeFst _ _ _ _ _ _ _ _ hW hX hQ
        e.equiv.isEquivalence_functor (quotientStackMap φ).w) <|
    @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ inferInstance <|
    @Functor.isEquivalence_trans _ _ _ _ _ _ _ _
      (TwoFibreProductOver.isEquivalence_reindex _ _) <|
    @Functor.isEquivalence_trans _ _ _ _ _ _ _ _
      (TwoFibreProductOver.isEquivalence_precomposeFst _ _ _ _ _ _ _ _ hQ hW hL
        (ULiftHom.equiv (C := (fibredCategory B S hS G'.objects.obj).val.obj)).isEquivalence_functor
        (liftedQuotientStackProjection G').w) inferInstance

/-- The comparison 1-morphism of the square of models, followed by the comparison of the two
2-fibre products, is the comparison 1-morphism of the square of Stacks 04ZN. -/
noncomputable def modelComparisonIso :
    (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1}
      (modelChart (G' := G') e') (modelMap φ e e') (modelSquare φ e e')).hom.toFunctor ⋙
        modelComparison φ e e' ≅
      (ULiftHom.up : (fibredCategory B S hS G.objects.obj).val.obj ⥤ _) ⋙
        functorialityComparison φ :=
  NatIso.ofComponents (fun u => TwoFibreProductOver.isoMkVertical
    ((BasedFunctor.toFunctorIso e.inverse e.functor e.counitIso).app
      ((quotientStackProjection G).obj u)) (Iso.refl _)
    (e.counitIso.hom.isHomLift' ((quotientStackProjection G).obj u))
    (IsHomLift.id rfl) (by
        have hn := e'.unitIso.hom.toNatTrans.naturality
          ((quotientStackMap φ).toFunctor.map
            (e.counitIso.hom.toNatTrans.app ((quotientStackProjection G).obj u)) ≫
            (functorialityProjectionCellUnlifted φ).hom.app u)
        have hi := congrArg (fun t => t.toNatTrans.app ((quotientStackMap φ).obj
          (e.functor.obj (e.inverse.obj ((quotientStackProjection G).obj u)))))
          e'.unitIso.inv_hom_id
        have hR : (e'.unitIso.inv.toNatTrans.app ((quotientStackMap φ).obj
            (e.functor.obj (e.inverse.obj ((quotientStackProjection G).obj u)))) ≫
          e'.inverse.toFunctor.map (e'.functor.toFunctor.map
            ((quotientStackMap φ).toFunctor.map
              (e.counitIso.hom.toNatTrans.app ((quotientStackProjection G).obj u))) ≫
              e'.functor.toFunctor.map ((functorialityProjectionCellUnlifted φ).hom.app u))) ≫
          e'.unitIso.hom.toNatTrans.app
            ((quotientStackProjection G').obj ((objectSpaceMap φ).obj u)) =
          (quotientStackMap φ).toFunctor.map
            (e.counitIso.hom.toNatTrans.app ((quotientStackProjection G).obj u)) ≫
            (functorialityProjectionCellUnlifted φ).hom.app u := by
          refine (congrArg (fun t => (_ ≫ e'.inverse.toFunctor.map t) ≫ _)
            (CategoryTheory.Functor.map_comp e'.functor.toFunctor _ _).symm).trans ?_
          refine (Category.assoc _ _ _).trans ?_
          refine (congrArg (_ ≫ ·) hn).trans ?_
          refine (Category.assoc _ _ _).symm.trans ?_
          refine (congrArg (· ≫ _) hi).trans ?_
          exact Category.id_comp _
        refine Eq.trans hR.symm (Eq.trans (Category.comp_id _).symm ?_)
        exact congrArg (_ ≫ ·)
          (CategoryTheory.Functor.map_id (liftedQuotientStackProjection G').toFunctor _).symm))
    (by
    intro u v f
    apply TwoFibreProductOver.Hom.ext'
    · simp only [TwoFibreProductOver.comp_a]
      exact e.counitIso.hom.toNatTrans.naturality ((quotientStackProjection G).toFunctor.map f)
    · rw [TwoFibreProductOver.comp_b, TwoFibreProductOver.comp_b]
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      rw [Category.comp_id]
      exact (Category.id_comp _).symm)

/-- **Stacks 04ZN read on the models.** If the source square of `φ` is cartesian, the square
`modelSquare φ e e'` is a 2-fibre product in the 2-category of categories fibred in groupoids. -/
noncomputable def isTwoFibreProduct_modelSquare
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects) :
    Bicategory.IsTwoFibreProduct (modelSquare φ e e') := by
  have h₁ := isEquivalence_functorialityComparison φ hφ
  have h₂ : ((ULiftHom.up : (fibredCategory B S hS G.objects.obj).val.obj ⥤ _) ⋙
      functorialityComparison φ).IsEquivalence :=
    @Functor.isEquivalence_trans _ _ _ _ _ _ _ _
      (ULiftHom.equiv (C := (fibredCategory B S hS G.objects.obj).val.obj)).isEquivalence_functor
      h₁
  have h₃ := @Functor.isEquivalence_of_iso _ _ _ _ _ _ (modelComparisonIso φ e e').symm h₂
  exact Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1} _ _
      (modelSquare φ e e'))
    (@Functor.isEquivalence_of_comp_right _ _ _ _ _ _ _ (modelComparison φ e e')
      (isEquivalence_modelComparison φ e e') h₃)

end Square

section ClosedImmersion

variable {Y : AlgebraicSpaces B S hS} {G G' : GroupoidInAlgebraicSpaces B S hS Y}
  (φ : GroupoidInAlgebraicSpaces.Hom G G')

/-- **The closed immersion of Stacks 0CQ1, on models.** Let `φ : (U, R, s, t, c) ⟶ (U', R', s',
t', c')` be a morphism of groupoids over `Y` whose source square is cartesian and whose map
`U ⟶ U'` is a closed immersion, with `(U', R', s', t', c')` smooth and `[U'/R']` an algebraic
stack. For algebraic stacks `𝒳 ≃ [U/R]` and `𝒳' ≃ [U'/R']`, the induced 1-morphism `𝒳 ⟶ 𝒳'` is a
closed immersion, by Stacks 0503 for closed immersions
(`AlgebraicStacks.isClosedImmersion_iff_exists_isClosedImmersion_representingMap`). -/
theorem isClosedImmersion_modelMap {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    (e : BasedCategory.Equivalence 𝒳.val.val (quotientStack G))
    (e' : BasedCategory.Equivalence (quotientStack G') 𝒳'.val.val)
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects)
    (hU : Space.IsClosedImmersion B S hS φ.toGroupoidHom.mapObjects)
    (hG' : GroupoidInAlgebraicSpaces.IsSmooth B S hS G')
    (halg' : IsAlgebraicStack.{u, w} B S hS (quotientStack G')) :
    AlgebraicStacks.IsClosedImmersion B S hS
      (Bicategory.InducedBicategory.mkHom (modelMap φ e e') : 𝒳 ⟶ 𝒳') := by
  have hdiag : HasRepresentableDiagonal B S hS (quotientStackCFG B S hS G') := halg'.2.2.1
  refine (AlgebraicStacks.isClosedImmersion_iff_exists_isClosedImmersion_representingMap B S hS
    (fibredCategory B S hS G'.objects.obj) _ (modelChart (G' := G') e')
    (isSurjectiveFlatLocallyOfFinitePresentation_quotientChart hG' hdiag e')
    (modelSquare φ e e') (isTwoFibreProduct_modelSquare φ e e' hφ) G'.objects.obj
    G'.objects.property (StacksRepresentableCFG.EquivalenceOver.refl _)).2
    ⟨G.objects.obj, G.objects.property, StacksRepresentableCFG.EquivalenceOver.refl _, ?_⟩
  change Space.IsClosedImmersion B S hS (representingMap B S hS
    (fibredCategory B S hS G.objects.obj) (fibredCategory B S hS G'.objects.obj) _ _
    (StacksRepresentableCFG.EquivalenceOver.refl _) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (associatedMap B S hS φ.toGroupoidHom.mapObjects).1)
  exact (congrArg (Space.IsClosedImmersion B S hS) (representingMap_associatedMap B S hS
    G.objects.obj G'.objects.obj φ.toGroupoidHom.mapObjects)).mpr hU

/-- **The closed immersion of Stacks 0CQ1 over `Y`, on models.** In the situation of
`isClosedImmersion_modelMap`, let `f : 𝒳 ⟶ Y` and `f' : 𝒳' ⟶ Y` identify `𝒳` and `𝒳'` with
`[U/R]` and `[U'/R']` over `Y`. Then there is a closed immersion `i : 𝒳 ⟶ 𝒳'` with
`i ≫ f' ≅ f`. -/
theorem exists_isClosedImmersion_of_models {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (e : BasedCategory.EquivalenceOver f.hom.hom (quotientStackToBase G))
    (e' : BasedCategory.EquivalenceOver (quotientStackToBase G') f'.hom.hom)
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects)
    (hU : Space.IsClosedImmersion B S hS φ.toGroupoidHom.mapObjects)
    (hG' : GroupoidInAlgebraicSpaces.IsSmooth B S hS G')
    (halg' : IsAlgebraicStack.{u, w} B S hS (quotientStack G')) :
    ∃ i : 𝒳 ⟶ 𝒳', AlgebraicStacks.IsClosedImmersion B S hS i ∧ Nonempty (i ≫ f' ≅ f) := by
  refine ⟨Bicategory.InducedBicategory.mkHom (modelMap φ e.equiv e'.equiv),
    isClosedImmersion_modelMap φ e.equiv e'.equiv hφ hU hG' halg', ⟨?_⟩⟩
  exact isoMkAlgebraicStacks B S hS
    (BasedCategory.isoWhiskerLeft (BasedFunctor.comp e.equiv.functor (quotientStackMap φ))
      e'.compIso ≪≫
    eqToIso (congrArg (BasedFunctor.comp e.equiv.functor)
      (quotientStackMap_comp_quotientStackToBase φ)) ≪≫ e.compIso)

end ClosedImmersion

section Stage

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- **The stage stack and the closed immersion of the proof of Stacks 0CQ1**, granted the inputs
of `AlgebraicGeometry.Stack.exists_stageModel_of_isFiniteType`. At every stage `i` past the
index of the limit descriptions, the model `𝒳_i` of `[U_i/R_i]` is of finite presentation over
`Y_i`, its base change `Y ×_{Y_i} 𝒳_i` is of finite presentation over `Y`, and `𝒳` embeds over
`Y` into it by a closed immersion: the square of Stacks 04ZN for
`(U, R, s, t, c) ⟶ Y ×_{Y_i} (U_i, R_i, s_i, t_i, c_i)` is cartesian because the source square
is, and `U ⟶ Y ×_{Y_i} U_i` is a closed immersion by the construction of the image system of `U`
(Stacks 0CP9). -/
theorem exists_closedImmersion_stageModel_of_isFiniteType
    (D : Space.NoetherianLimitSystem B S hS B.contains_terminal I)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS D.limitSpace.obj D.limitSpace.property)
    (hlft : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒳qc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        Space.IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        Space.IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal
          B.contains_terminal Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z) :
    ∃ (G : GroupoidInAlgebraicSpaces B S hS D.limitSpace) (Δ : G.LimitDescent),
      Space.IsQuasiSeparated B S hS G.objectsToBase.hom ∧
      Space.IsQuasiSeparated B S hS G.arrowsToBase.hom ∧
      Nonempty (BasedCategory.EquivalenceOver f.hom.hom (quotientStackToBase G)) ∧
      ∀ (i : I) (h : Δ.index ≤ i),
        ∃ M : QuotientStackModel.{u, w} (D.stageSpace i) (Δ.stageGroupoid i h),
        AlgebraicStacks.IsFinitePresentation B S hS M.structureMorphism ∧
        AlgebraicStacks.IsFinitePresentation B S hS
          (twoFibreProductSquareAlgebraicStacks.{u, w} B S hS M.structureMorphism
            (Bicategory.InducedBicategory.mkHom
              (associatedMap B S hS (D.limitProjection i).hom).1 :
              algebraicSpaceStack.{u, w} B S hS D.limitSpace.obj D.limitSpace.property ⟶
                algebraicSpaceStack.{u, w} B S hS (D.stageSpace i).obj
                  (D.stageSpace i).property)).snd ∧
        ∃ ι : 𝒳 ⟶ (twoFibreProductSquareAlgebraicStacks.{u, w} B S hS M.structureMorphism
            (Bicategory.InducedBicategory.mkHom
              (associatedMap B S hS (D.limitProjection i).hom).1 :
              algebraicSpaceStack.{u, w} B S hS D.limitSpace.obj D.limitSpace.property ⟶
                algebraicSpaceStack.{u, w} B S hS (D.stageSpace i).obj
                  (D.stageSpace i).property)).pt,
          AlgebraicStacks.IsClosedImmersion B S hS ι ∧
          Nonempty (ι ≫ (twoFibreProductSquareAlgebraicStacks.{u, w} B S hS M.structureMorphism
            (Bicategory.InducedBicategory.mkHom
              (associatedMap B S hS (D.limitProjection i).hom).1 :
              algebraicSpaceStack.{u, w} B S hS D.limitSpace.obj D.limitSpace.property ⟶
                algebraicSpaceStack.{u, w} B S hS (D.stageSpace i).obj
                  (D.stageSpace i).property)).snd ≅ f) := by
  obtain ⟨G, Δ, hUqs, hRqs, ⟨e⟩, hst⟩ := exists_stageModel_of_isFiniteType D 𝒳 f hlft h𝒳qc hqs
    h07SU
  refine ⟨G, Δ, hUqs, hRqs, ⟨e⟩, fun i h => ?_⟩
  obtain ⟨M, hM, hfp, ⟨e'⟩⟩ := hst i h
  refine ⟨M, hM, hfp, ?_⟩
  have hsm := Space.isSmooth_baseChange (Δ.stageGroupoid i h) (D.limitProjection i)
    (Δ.stageGroupoid_isSmooth i h)
  exact exists_isClosedImmersion_of_models (Δ.toBaseChangeHom i h) f _ e e'
    (Δ.isPullback_mapArrows_source i h) (Δ.isClosedImmersion_objects i h) hsm
    (isAlgebraicStack_quotientStack_of_isSmooth_unconditional.{u, w} hsm)

end Stage

end AlgebraicGeometry.Stack

end
