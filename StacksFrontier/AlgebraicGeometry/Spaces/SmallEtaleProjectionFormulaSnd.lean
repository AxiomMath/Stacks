module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaIso
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMapSndBaseChange

/-!
# The projection formula for algebraic spaces, with the factors exchanged

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces,
`K ∈ D_QCoh(𝒪_Y)` and `E ∈ D_QCoh(𝒪_X)`.  The map `K ⊗^L Rf_*E ⟶ Rf_*(Lf^*K ⊗^L E)`, the
transpose of the isomorphism of Stacks 07A4 followed by the counit in the second factor
(`Stacks.ProjectionFormula.adjunctionTensorMapSnd`), is an isomorphism.  This is Stacks 08IN with
the two tensor factors exchanged, proved by the same argument: étale locally on `Y` through the
mirror image of the hexagon of Stacks 0E48, and over an affine target by dévissage from `𝒪_Y`.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleProjectionFormulaMapSnd_of_isAffineSpace`
* `AlgebraicGeometry.Space.isIso_map_smallEtaleProjectionFormulaMapSnd_iff`
* `AlgebraicGeometry.Space.isIso_smallEtaleProjectionFormulaMapSnd`

## References

* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] isGrothendieckAbelian_modules_ringUniverse
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

section Affine

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- The projection formula map `K ⊗^L Rf_*E ⟶ Rf_*(Lf^*K ⊗^L E)`. -/
abbrev smallEtaleProjectionFormulaMapSnd (f : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :=
  Stacks.ProjectionFormula.adjunctionTensorMapSnd (smallEtaleDerivedModuleAdjunction B S hS f)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleDerivedPullbackTensorIso f).hom K E

/-- **The projection formula map with the factors exchanged is invertible at a shift of the
structure sheaf**, for every morphism `f`. -/
theorem isIso_smallEtaleProjectionFormulaMapSnd_of_iso (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))} (q : ℤ)
    (e : K ≅ DerivedCategory.Q.obj
      (Stacks.SheafOfModules.singleUnitComplex (smallEtaleRingedTopos B S hS Y).O q)) :
    IsIso (smallEtaleProjectionFormulaMapSnd f K E) := by
  let L := smallEtaleDerivedModulePullback B S hS f
  haveI : ((smallEtaleDerivedTensor B S hS Y).obj K).IsEquivalence :=
    (smallEtaleDerivedTensorProduct B S hS Y).isEquivalence_tensor_obj_of_iso q e
  haveI : ((smallEtaleDerivedTensor B S hS X).obj (L.obj K)).IsEquivalence :=
    (smallEtaleDerivedTensorProduct B S hS X).isEquivalence_tensor_obj_of_iso q
      (L.mapIso e ≪≫ Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackSingleUnitIso
        (smallEtaleRingedToposHom B S hS f) q)
  haveI := isEquivalence_curry_uncurry_obj (smallEtaleDerivedTensor B S hS Y) K
  haveI := isEquivalence_curry_uncurry_obj (smallEtaleDerivedTensor B S hS X) (L.obj K)
  exact Stacks.ProjectionFormula.isIso_adjunctionTensorMapSnd_of_isEquivalence
    (smallEtaleDerivedModuleAdjunction B S hS f)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleDerivedPullbackTensorIso f).hom K E

/-- The projection formula map `K ⊗^L Rf_*E ⟶ Rf_*(Lf^*K ⊗^L E)` as a natural transformation
in `K`. -/
def smallEtaleProjectionFormulaSndNatTrans (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedTensor B S hS Y).flip.obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj E) ⟶
      smallEtaleDerivedModulePullback B S hS f ⋙ (smallEtaleDerivedTensor B S hS X).flip.obj E ⋙
        derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f) where
  app K := smallEtaleProjectionFormulaMapSnd f K E
  naturality _ _ k := by
    have h := Stacks.ProjectionFormula.adjunctionTensorMapSnd_natural
      (smallEtaleDerivedModuleAdjunction B S hS f)
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
      (smallEtaleDerivedPullbackTensorIso f).hom k (𝟙 E)
    simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.comp_id] at h
    exact h

/-- **The projection formula with the factors exchanged over an affine target.** Let
`f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces with `Y` affine,
`K ∈ D_QCoh(𝒪_Y)` and `E ∈ D_QCoh(𝒪_X)`. Then `K ⊗^L Rf_*E ⟶ Rf_*(Lf^*K ⊗^L E)` is an
isomorphism. -/
theorem isIso_smallEtaleProjectionFormulaMapSnd_of_isAffineSpace (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : QcohDerived B S hS Y K)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E) :
    IsIso (smallEtaleProjectionFormulaMapSnd f K E) := by
  let P := QcohDerived B S hS Y
  let DY := DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
  let DX := DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  let ι : P.FullSubcategory ⥤ DY := P.ι
  letI : ι.CommShift ℤ := (inferInstance : P.ι.CommShift ℤ)
  letI : ι.IsTriangulated := (inferInstance : P.ι.IsTriangulated)
  let L : DY ⥤ DX := smallEtaleDerivedModulePullback B S hS f
  let R : DX ⥤ DY := derivedModulePushforward B S hS f
  letI : R.CommShift ℤ := derivedModulePushforward_commShift B S hS f
  letI : R.IsTriangulated := derivedModulePushforward_isTriangulated B S hS f
  have hcl : ∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I) :=
    isClosedUnderColimitsOfShape_qcohDerived B S hS Y
  haveI : HasCoproducts.{u} P.FullSubcategory := fun I => by
    have := hcl I
    infer_instance
  haveI : LocallySmall.{u} P.FullSubcategory := inferInstance
  let TY := smallEtaleDerivedTensorProduct B S hS Y
  let TX := smallEtaleDerivedTensorProduct B S hS X
  let T₁ : DY ⥤ DY := (smallEtaleDerivedTensor B S hS Y).flip.obj (R.obj E)
  let T₂ : DX ⥤ DX := (smallEtaleDerivedTensor B S hS X).flip.obj E
  letI : T₁.CommShift ℤ := TY.commShift_left _
  letI : T₁.IsTriangulated := TY.exact_left _
  letI : T₂.CommShift ℤ := TX.commShift_left _
  letI : T₂.IsTriangulated := TX.exact_left _
  let τ : ι ⋙ T₁ ⟶ ι ⋙ L ⋙ T₂ ⋙ R :=
    Functor.whiskerLeft P.ι (smallEtaleProjectionFormulaSndNatTrans f E)
  have hι : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) ι := fun I => by
    have := hcl I
    exact (inferInstance : PreservesColimitsOfShape (Discrete I) P.ι)
  haveI : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) (ι ⋙ T₁) :=
    fun I => by
      have : PreservesColimitsOfShape (Discrete I) T₁ :=
        Stacks.SheafOfModules.DerivedTensorProduct.preservesColimitsOfShape_tensor_flip_obj TY _ I
      infer_instance
  haveI : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) (ι ⋙ L ⋙ T₂ ⋙ R) := fun I => by
    have : PreservesColimitsOfShape (Discrete I) L :=
      (smallEtaleDerivedModuleAdjunction B S hS f).leftAdjoint_preservesColimits.preservesColimitsOfShape
    have : PreservesColimitsOfShape (Discrete I) T₂ :=
      Stacks.SheafOfModules.DerivedTensorProduct.preservesColimitsOfShape_tensor_flip_obj TX _ I
    let G : P.FullSubcategory ⥤ DX := ι ⋙ L ⋙ T₂
    have hG : PreservesColimitsOfShape (Discrete I) G := inferInstance
    have hGq : ∀ K' : P.FullSubcategory, QcohDerived B S hS X (G.obj K') := fun K' =>
      qcohDerived_smallEtaleDerivedTensor X _ E
        (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ f K'.obj K'.property) hE
    suffices key : PreservesColimitsOfShape (Discrete I) (G ⋙ R) from key
    refine ⟨fun {J} => ?_⟩
    suffices ∀ F : I → P.FullSubcategory,
        PreservesColimit (Discrete.functor F) (G ⋙ R) from
      preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm
    intro F
    have : PreservesColimit (Discrete.functor (G.obj ∘ F)) R :=
      preservesColimit_derivedModulePushforward B S hS f hfqc hfqs _ fun i => hGq (F i)
    have : PreservesColimit (Discrete.functor F ⋙ G) R :=
      preservesColimit_of_iso_diagram _ (Discrete.compNatIsoDiscrete F G).symm
    exact comp_preservesColimit G R
  obtain ⟨hc, hg⟩ :=
    isCompactObject_and_isWeakTriangulatedGenerator_unitQuasicoherent (X := Y.1) (hX := Y.2) hY
  have hb : ∀ n : ℤ, IsIso (τ.app ((unitQuasicoherent Y.2)⟦n⟧)) := fun n => by
    have e : P.ι.obj ((unitQuasicoherent Y.2)⟦n⟧) ≅ DerivedCategory.Q.obj
        (Stacks.SheafOfModules.singleUnitComplex (smallEtaleRingedTopos B S hS Y).O (-n)) :=
      ((QcohDerived B S hS Y).ι.commShiftIso n).app _ ≪≫ structureDerivedShiftIso Y n
    exact isIso_smallEtaleProjectionFormulaMapSnd_of_iso f E (-n) e
  exact StacksDraft.CompactDevissage.isIso_app_of_isCompactlyGenerated_of_forall_shift_of_locallySmall
    τ (fun _ : PUnit.{u + 1} => unitQuasicoherent Y.2) (fun _ => hc)
    (fun Z hZ => hg Z (by
      have : ObjectProperty.ofObj (fun _ : PUnit.{u + 1} => unitQuasicoherent Y.2) =
          ObjectProperty.singleton (unitQuasicoherent Y.2) := by
        ext Z
        rw [ObjectProperty.ofObj_iff, ObjectProperty.singleton_iff]
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨PUnit.unit, h⟩⟩
      rwa [← this]))
    (fun _ n => hb n)
    ⟨K, hK⟩

end Affine

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- **The projection formula map with the factors exchanged is compatible with étale base
change.**  For a cartesian square whose bottom arrow `g` is étale and representable, the pullback
along `g` of the map of `f` at `(K, E)` is invertible if and only if the map of `f'` at
`(Lg^*K, L(g')^*E)` is. -/
theorem isIso_map_smallEtaleProjectionFormulaMapSnd_iff (sq : IsPullback g' f' f g)
    (hg : IsEtale B S hS g.hom) (hrep : yoneda.relativelyRepresentable g.hom)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    IsIso ((smallEtaleDerivedModulePullback B S hS g).map
        (smallEtaleProjectionFormulaMapSnd f K E)) ↔
      IsIso (smallEtaleProjectionFormulaMapSnd f'
        ((smallEtaleDerivedModulePullback B S hS g).obj K)
        ((smallEtaleDerivedModulePullback B S hS g').obj E)) := by
  have hex := Stacks.AffineProjectionFormula.adjunctionTensorMapSnd_baseChange_square
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y'))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X'))
    (smallEtaleDerivedPullbackTensorIso f).hom (smallEtaleDerivedPullbackTensorIso f').hom
    (smallEtaleDerivedPullbackTensorIso g).hom (smallEtaleDerivedPullbackTensorIso g').hom K E
    (tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso f g f' g' sq.w K _)
  have h₁ := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS f g f' g' sq hg hrep E
  have h₂ := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS f g f' g' sq hg hrep
    (((smallEtaleDerivedTensor B S hS X).obj
      ((smallEtaleDerivedModulePullback B S hS f).obj K)).obj E)
  unfold smallEtaleDerivedModuleBaseChangeMap at h₁ h₂
  have h₃ : IsIso (𝟙 ((smallEtaleDerivedModulePullback B S hS g).obj K) ×ₘ
      Stacks.CategoryTheory.BaseChange.map
      (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS f')
      (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
      (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w) E) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, h₁⟩
  have h₄ : IsIso ((Stacks.AffineProjectionFormula.squareCompositeIso
        (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
        (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w)).inv.app K ×ₘ
      𝟙 ((smallEtaleDerivedModulePullback B S hS g').obj E)) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have h₅ : IsIso (Stacks.CategoryTheory.BaseChange.map
      (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS f')
      (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
      (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w)
      ((Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X)).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj K, E))) := h₂
  exact Stacks.CategoryTheory.isIso_iff_isIso_of_comp₃_eq hex inferInstance
    (Functor.map_isIso _ _) h₅ (Functor.map_isIso _ _)

/-- **Stacks 08IN with the tensor factors exchanged.**  Let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces, `K ∈ D_QCoh(𝒪_Y)` and `E ∈ D_QCoh(𝒪_X)`.  Then
`K ⊗^L Rf_*E ⟶ Rf_*(Lf^*K ⊗^L E)` is an isomorphism. -/
theorem isIso_smallEtaleProjectionFormulaMapSnd (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : QcohDerived B S hS Y K)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E) :
    IsIso (smallEtaleProjectionFormulaMapSnd f K E) := by
  refine isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (SmallEtale.coversTop_affineCharts B S hS Y.1) _ fun V => ?_
  have sq := isPullback_chartBaseChangeInclusion B S hS f V.1
  refine (isIso_map_smallEtaleProjectionFormulaMapSnd_iff B S hS f (chartToSpace B S hS Y V.1)
    (chartBaseChangeProjection B S hS f V.1) (chartBaseChangeInclusion B S hS f V.1) sq
    (isEtale_chartToSpace B S hS Y V.1) (relativelyRepresentable_chartToSpace B S hS Y V.1)
    K E).2 ?_
  exact isIso_smallEtaleProjectionFormulaMapSnd_of_isAffineSpace
    (chartBaseChangeProjection B S hS f V.1)
    (isQuasiCompact_chartBaseChangeProjection B S hS f V.1 hfqc)
    (isQuasiSeparated_chartBaseChangeProjection B S hS f V.1 hfqs)
    (isAffineSpace_chartSpace B S hS Y V.1 V.2) _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (chartToSpace B S hS Y V.1) K hK) _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
      (chartBaseChangeInclusion B S hS f V.1) E hE)

end AlgebraicGeometry.Space

end
