module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Equivalence
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.QuasiCoherentPushforward
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPullback
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.SupportedSerreQuotient
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Changing the source and the target of an integral transform

Let `R` be a commutative ring, let `X` and `Y` be schemes over `R` with `X` affine and let `K`
be a quasi-coherent module on `X ×_R Y`, with integral transform
`F ↦ pr_{2,*}(pr_1^*F ⊗ K)` from quasi-coherent modules on `X` to quasi-coherent modules on
`Y`.  This file computes the kernel of the integral transform after an affine change of the
source `X` and after a change of the target `Y`.

## Main definitions

* `AlgebraicGeometry.sourceChangeMap` is the morphism `X' ×_R Y ⟶ X ×_R Y` induced by a
  morphism `X' ⟶ X` over `R`, and `AlgebraicGeometry.sourceChangeKernel` is the inverse image
  of a quasi-coherent kernel along it.
* `AlgebraicGeometry.targetChangeMap` is the morphism `X ×_R Y' ⟶ X ×_R Y` induced by a
  morphism `Y' ⟶ Y` over `R`, with inverse image `AlgebraicGeometry.targetChangeKernel` and,
  for an open immersion, restriction `AlgebraicGeometry.openTargetKernel`.
* `AlgebraicGeometry.baseChangeIsoOfFunctor`,
  `AlgebraicGeometry.projectionFormulaSourceIsoOfFunctor` and
  `AlgebraicGeometry.pullbackTensorLeftIso`: affine base change for direct images (Tag 02KG),
  the projection formula for an affine morphism (Tag 0FZE) and the compatibility of the inverse
  image with the tensor product (Tag 01CD), each as an isomorphism of functors.

## Main results

* `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso`: for an affine morphism
  `f : X' ⟶ X`, the integral transform of `K` precomposed with the direct image along `f` is
  the integral transform of `(f × id_Y)^*K`.
* `AlgebraicGeometry.quasicoherentIntegralTransformTargetChangeIso`: for a flat morphism
  `g : Y' ⟶ Y`, the integral transform of `K` followed by the inverse image along `g` is the
  integral transform of `(id_X × g)^*K`.
* `AlgebraicGeometry.quasicoherentIntegralTransformOpenTargetIso`: for an open immersion
  `j : V ⟶ Y`, the integral transform of `K` followed by restriction to `V` is the integral
  transform of `K|_{X ×_R V}`.

## References

* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
* [Stacks Project, Tag 0FZD](https://stacks.math.columbia.edu/tag/0FZD)
* [Stacks Project, Tag 0FZB](https://stacks.math.columbia.edu/tag/0FZB)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

/-! ### Isomorphisms of functors attached to an affine morphism -/

/-- **Affine base change, Tag 02KG, as an isomorphism of functors.**  The base-change morphism
`g^*f_* ⟶ f'_*(g')^*` of a cartesian square with `f` affine is an isomorphism after restriction
along a functor whose values are quasi-coherent. -/
def baseChangeIsoOfFunctor {C : Type v} [Category.{w} C] {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (sq : IsPullback g' f' f g)
    [IsAffineHom f] (F : C ⥤ X.Modules) (hF : ∀ A, (F.obj A).IsQuasicoherent) :
    F ⋙ Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback g ≅
      F ⋙ Scheme.Modules.pullback g' ⋙ Scheme.Modules.pushforward f' :=
  have _happ : ∀ A, IsIso ((Functor.whiskerLeft F
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans sq.w)).app A) := fun A ↦
    have := hF A
    Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom sq
      (F.obj A)
  have : IsIso (Functor.whiskerLeft F
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans sq.w)) :=
    NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerLeft F
    (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans sq.w))

/-- The projection-formula morphism `h_*(-) ⊗ H ⟶ h_*(- ⊗ h^*H)` is natural in the module on
the source of `h`. -/
theorem projectionFormulaMap_naturality_source {T S : Scheme.{u}} (h : T ⟶ S)
    (H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    {G G' : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)}
    (ψ : G ⟶ G') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(S.toRingedSpace).presheaf,
        (S.toRingedSpace).IsSheaf⟩).flip.obj (H))).map
          ((RingedSpaceModuleAdjunction.modulePushforward h.toLRSHom.toShHom).map ψ) ≫
        Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap h G' H =
      Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap h G H ≫
        (RingedSpaceModuleAdjunction.modulePushforward h.toLRSHom.toShHom).map
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(T.toRingedSpace).presheaf,
              (T.toRingedSpace).IsSheaf⟩).flip.obj
              (((RingedSpaceModuleAdjunction.modulePullback
                h.toLRSHom.toShHom).obj H)))).map ψ) := by
  have hid := (RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom).map_id H
  have hnat := Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_natural h ψ (𝟙 H)
  simp only [hid, Functor.uncurry_obj_map] at hnat
  let sourceTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    S.toRingedSpace.sheaf
  let targetTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    T.toRingedSpace.sheaf
  let inverseImage := RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom
  let directImage := RingedSpaceModuleAdjunction.modulePushforward h.toLRSHom.toShHom
  have sourceIdentity :=
    (congrArg (fun arrow ↦ (sourceTensor.map (directImage.map ψ)).app H ≫ arrow)
      ((sourceTensor.obj (directImage.obj G')).map_id H)).trans
        (Category.comp_id ((sourceTensor.map (directImage.map ψ)).app H))
  have targetIdentity :=
    (congrArg (fun arrow ↦ (targetTensor.map ψ).app (inverseImage.obj H) ≫ arrow)
      ((targetTensor.obj G').map_id (inverseImage.obj H))).trans
        (Category.comp_id ((targetTensor.map ψ).app (inverseImage.obj H)))
  exact (congrArg (fun arrow ↦ arrow ≫
      Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap h G' H)
    sourceIdentity).symm.trans
      (hnat.trans (congrArg (fun arrow ↦
        Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap h G H ≫
          directImage.map arrow) targetIdentity))

/-- The projection-formula morphism of Tag 0FZE, as a natural transformation in the module on
the source of `h`. -/
def projectionFormulaSourceNatTrans {T S : Scheme.{u}} (h : T ⟶ S) (H : S.Modules) :
    Scheme.Modules.pushforward h ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(S.toRingedSpace).presheaf,
            (S.toRingedSpace).IsSheaf⟩).flip.obj (H)) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(T.toRingedSpace).presheaf,
          (T.toRingedSpace).IsSheaf⟩).flip.obj
          (((Scheme.Modules.pullback h).obj H))) ⋙ Scheme.Modules.pushforward h where
  app G := Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap h G H
  naturality _ _ ψ := projectionFormulaMap_naturality_source h H ψ

/-- **The projection formula, Tag 0FZE, as an isomorphism of functors.**  For an affine
morphism `h` and a quasi-coherent `H`, the morphism `h_*(-) ⊗ H ⟶ h_*(- ⊗ h^*H)` is an
isomorphism after restriction along a functor whose values are quasi-coherent. -/
def projectionFormulaSourceIsoOfFunctor {C : Type v} [Category.{w} C] {T S : Scheme.{u}}
    (h : T ⟶ S) [IsAffineHom h] (H : S.Modules) (hH : H.IsQuasicoherent) (F : C ⥤ T.Modules)
    (hF : ∀ A, (F.obj A).IsQuasicoherent) :
    F ⋙ Scheme.Modules.pushforward h ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(S.toRingedSpace).presheaf,
            (S.toRingedSpace).IsSheaf⟩).flip.obj (H)) ≅
      F ⋙ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(T.toRingedSpace).presheaf,
          (T.toRingedSpace).IsSheaf⟩).flip.obj
          (((Scheme.Modules.pullback h).obj H))) ⋙ Scheme.Modules.pushforward h :=
  have _happ : ∀ A, IsIso ((Functor.whiskerLeft F (projectionFormulaSourceNatTrans h H)).app A) :=
    fun A ↦ Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap h
      (F.obj A) H (hF A) hH
  have : IsIso (Functor.whiskerLeft F (projectionFormulaSourceNatTrans h H)) :=
    NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerLeft F (projectionFormulaSourceNatTrans h H))

/-- **Tag 01CD with the first tensor factor held fixed, as an isomorphism of functors.**
Tensoring on the left by `K` and then taking inverse images along `q` is taking inverse images
and then tensoring on the left by `q^*K`. -/
def pullbackTensorLeftIso {P P' : Scheme.{u}} (q : P' ⟶ P) (K : P.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} P.toRingedSpace.sheaf).obj (K)) ⋙
        Scheme.Modules.pullback q ≅
      Scheme.Modules.pullback q ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} P'.toRingedSpace.sheaf).obj
            (((Scheme.Modules.pullback q).obj K))) :=
  NatIso.ofComponents
    (fun moduleSheaf ↦
      (Stacks.RingedSpace.comparisonBifunctorIso q.toLRSHom.toShHom).app (K, moduleSheaf))
    (by
      intro sourceModule targetModule morphism
      let sourceTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        P.toRingedSpace.sheaf
      let targetTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        P'.toRingedSpace.sheaf
      let inverseImage := Scheme.Modules.pullback q
      let comparison := Stacks.RingedSpace.comparisonBifunctorIso q.toLRSHom.toShHom
      let sourceArrow := (sourceTensor.obj K).map morphism
      let targetArrow := (targetTensor.obj (inverseImage.obj K)).map
        (inverseImage.map morphism)
      have sourceIdentity : (sourceTensor.map (𝟙 K)).app sourceModule = 𝟙 _ :=
        congrArg (fun transformation ↦ transformation.app sourceModule) (sourceTensor.map_id K)
      have targetIdentity : (targetTensor.map (inverseImage.map (𝟙 K))).app
          (inverseImage.obj sourceModule) = 𝟙 _ :=
        (congrArg (fun arrow ↦ (targetTensor.map arrow).app (inverseImage.obj sourceModule))
          (inverseImage.map_id K)).trans
            (congrArg (fun transformation ↦ transformation.app (inverseImage.obj sourceModule))
              (targetTensor.map_id (inverseImage.obj K)))
      have naturality : inverseImage.map
          ((sourceTensor.map (𝟙 K)).app sourceModule ≫ sourceArrow) ≫
            comparison.hom.app (K, targetModule) =
          comparison.hom.app (K, sourceModule) ≫
            ((targetTensor.map (inverseImage.map (𝟙 K))).app
              (inverseImage.obj sourceModule) ≫ targetArrow) :=
        comparison.hom.naturality (Prod.mkHom (𝟙 K) morphism)
      exact (congrArg (fun arrow ↦ inverseImage.map arrow ≫
          comparison.hom.app (K, targetModule))
        ((congrArg (fun arrow ↦ arrow ≫ sourceArrow) sourceIdentity).trans
          (Category.id_comp sourceArrow))).symm.trans
        (naturality.trans
          (congrArg (fun arrow ↦ comparison.hom.app (K, sourceModule) ≫ arrow)
            ((congrArg (fun arrow ↦ arrow ≫ targetArrow) targetIdentity).trans
              (Category.id_comp targetArrow)))))

/-- The inverse image of a quasi-coherent module along the first projection of `X ×_R Y` is
quasi-coherent. -/
theorem isQuasicoherent_pullbackFst (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
    (M : Scheme.QuasicoherentModules X.left) :
    (((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
      Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).obj M).IsQuasicoherent :=
  have : M.obj.IsQuasicoherent := M.property
  @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
    (pullback.fst X.hom Y.hom).toLRSHom.toShHom M.obj (by assumption)

/-! ### Affine change of source -/

/-- The morphism `X' ×_R Y ⟶ X ×_R Y` induced by a morphism `f : X' ⟶ X` of schemes over
`R`. -/
def sourceChangeMap (R : Type u) [CommRing R] (X X' Y : Over (Spec (.of R))) (f : X' ⟶ X) :
    pullback X'.hom Y.hom ⟶ pullback X.hom Y.hom :=
  pullback.map X'.hom Y.hom X.hom Y.hom f.left (𝟙 Y.left) (𝟙 (Spec (.of R)))
    (by simp [Over.w f]) (by simp)

/-- The source-change morphism followed by the first projection is the first projection followed
by `f`. -/
@[simp]
theorem sourceChangeMap_comp_fst (R : Type u) [CommRing R] (X X' Y : Over (Spec (.of R)))
    (f : X' ⟶ X) :
    sourceChangeMap R X X' Y f ≫ pullback.fst X.hom Y.hom =
      pullback.fst X'.hom Y.hom ≫ f.left :=
  pullback.lift_fst _ _ _

/-- The source-change morphism commutes with the second projections. -/
@[simp]
theorem sourceChangeMap_comp_snd (R : Type u) [CommRing R] (X X' Y : Over (Spec (.of R)))
    (f : X' ⟶ X) :
    sourceChangeMap R X X' Y f ≫ pullback.snd X.hom Y.hom = pullback.snd X'.hom Y.hom :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The square relating the first projections of `X' ×_R Y` and of `X ×_R Y` is cartesian. -/
theorem isPullback_sourceChangeMap (R : Type u) [CommRing R] (X X' Y : Over (Spec (.of R)))
    (f : X' ⟶ X) :
    IsPullback (pullback.fst X'.hom Y.hom) (sourceChangeMap R X X' Y f) f.left
      (pullback.fst X.hom Y.hom) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd X.hom Y.hom) (v₂₂ := X.hom) ?_ ?_
    (IsPullback.of_hasPullback X.hom Y.hom)
  · rw [sourceChangeMap_comp_snd, Over.w f]
    exact IsPullback.of_hasPullback X'.hom Y.hom
  · simp

/-- The source-change morphism along an affine morphism is affine. -/
instance isAffineHom_sourceChangeMap (R : Type u) [CommRing R] (X X' Y : Over (Spec (.of R)))
    (f : X' ⟶ X) [IsAffineHom f.left] : IsAffineHom (sourceChangeMap R X X' Y f) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_sourceChangeMap R X X' Y f) inferInstance

/-- The inverse image of a quasi-coherent kernel on `X ×_R Y` along the source-change
morphism. -/
def sourceChangeKernel (R : Type u) [CommRing R] (X X' Y : Over (Spec (.of R))) (f : X' ⟶ X)
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    Scheme.QuasicoherentModules (pullback X'.hom Y.hom) :=
  ⟨(Scheme.Modules.pullback (sourceChangeMap R X X' Y f)).obj K.obj,
    have : K.obj.IsQuasicoherent := K.property
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (sourceChangeMap R X X' Y f).toLRSHom.toShHom K.obj (by assumption)⟩

/-- Affine change of source for the pullback--tensor--pushforward formula of Tag 0FZB. -/
def integralTransformFormulaSourceChangeIso (R : Type u) [CommRing R]
    (X X' Y : Over (Spec (.of R))) (f : X' ⟶ X) [IsAffineHom f.left]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    quasicoherentPushforward f.left ⋙ integralTransformFormula R X Y K.obj ≅
      integralTransformFormula R X' Y (sourceChangeKernel R X X' Y f K).obj :=
  Functor.isoWhiskerRight
      (baseChangeIsoOfFunctor (isPullback_sourceChangeMap R X X' Y f)
        (SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι (fun M ↦ M.property))
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(pullback X.hom Y.hom).presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
          (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj (K.obj)) ⋙
        Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι ⋙
          Scheme.Modules.pullback (pullback.fst X'.hom Y.hom) ⋙
            Scheme.Modules.pushforward (sourceChangeMap R X X' Y f))
        ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
            ((pullback X.hom Y.hom)).presheaf ((pullback X.hom Y.hom)).ringCatSheaf.2 (K.obj))))
      (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) ≪≫
    Functor.isoWhiskerRight
      (projectionFormulaSourceIsoOfFunctor (sourceChangeMap R X X' Y f) K.obj K.property
        ((SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι ⋙
          Scheme.Modules.pullback (pullback.fst X'.hom Y.hom))
        (isQuasicoherent_pullbackFst R X' Y))
      (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι ⋙
          Scheme.Modules.pullback (pullback.fst X'.hom Y.hom))
        ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
            ((pullback X'.hom Y.hom)).presheaf ((pullback X'.hom Y.hom)).ringCatSheaf.2
            (((Scheme.Modules.pullback (sourceChangeMap R X X' Y f)).obj K.obj)))).symm)
      (Scheme.Modules.pushforward (sourceChangeMap R X X' Y f) ⋙
        Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) ≪≫
    Functor.isoWhiskerLeft
      ((SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι ⋙
        Scheme.Modules.pullback (pullback.fst X'.hom Y.hom) ⋙
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
              ⟨(pullback X'.hom Y.hom).presheaf, Presheaf.isSheaf_of_isSheaf_comp _
              ((pullback X'.hom Y.hom).presheaf) (forget₂ CommRingCat RingCat)
              ((pullback X'.hom Y.hom).ringCatSheaf.2)⟩).obj (((Scheme.Modules.pullback
              (sourceChangeMap R X X' Y f)).obj K.obj))))
      (Scheme.Modules.pushforwardComp (sourceChangeMap R X X' Y f)
          (pullback.snd X.hom Y.hom) ≪≫
        Scheme.Modules.pushforwardCongr (sourceChangeMap_comp_snd R X X' Y f))

/-- Let `X` be an affine scheme over `R`, let `f : X' ⟶ X` be an affine morphism of schemes over
`R` and let `K` be a quasi-coherent module on `X ×_R Y`.  Then the integral transform of `K`
precomposed with the direct image along `f` is the integral transform of `(f × id_Y)^*K`. -/
@[stacks 0FZF "affine source change"]
def quasicoherentIntegralTransformSourceChangeIso (R : Type u) [CommRing R]
    (X X' Y : Over (Spec (.of R))) [IsAffine X.left] (f : X' ⟶ X) [IsAffineHom f.left]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    letI : IsAffine X'.left := isAffine_of_isAffineHom f.left
    quasicoherentPushforward f.left ⋙ quasicoherentIntegralTransform R X Y K ≅
      quasicoherentIntegralTransform R X' Y (sourceChangeKernel R X X' Y f K) := by
  letI : IsAffine X'.left := isAffine_of_isAffineHom f.left
  exact ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
      _).preimageIso
    (Functor.isoWhiskerLeft (quasicoherentPushforward f.left)
        (quasicoherentIntegralTransformData R X Y K).comparison ≪≫
      integralTransformFormulaSourceChangeIso R X X' Y f K ≪≫
      (quasicoherentIntegralTransformData R X' Y
        (sourceChangeKernel R X X' Y f K)).comparison.symm)

/-! ### Change of target -/

/-- The morphism `X ×_R Y' ⟶ X ×_R Y` induced by a morphism `g : Y' ⟶ Y` of schemes over
`R`. -/
def targetChangeMap (R : Type u) [CommRing R] (X Y Y' : Over (Spec (.of R))) (g : Y' ⟶ Y) :
    pullback X.hom Y'.hom ⟶ pullback X.hom Y.hom :=
  pullback.map X.hom Y'.hom X.hom Y.hom (𝟙 X.left) g.left (𝟙 (Spec (.of R)))
    (by simp) (by simp [Over.w g])

/-- The target-change morphism commutes with the first projections. -/
@[simp]
theorem targetChangeMap_comp_fst (R : Type u) [CommRing R] (X Y Y' : Over (Spec (.of R)))
    (g : Y' ⟶ Y) :
    targetChangeMap R X Y Y' g ≫ pullback.fst X.hom Y.hom = pullback.fst X.hom Y'.hom :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The target-change morphism followed by the second projection is the second projection
followed by `g`. -/
@[simp]
theorem targetChangeMap_comp_snd (R : Type u) [CommRing R] (X Y Y' : Over (Spec (.of R)))
    (g : Y' ⟶ Y) :
    targetChangeMap R X Y Y' g ≫ pullback.snd X.hom Y.hom =
      pullback.snd X.hom Y'.hom ≫ g.left :=
  pullback.lift_snd _ _ _

/-- The square relating the second projections of `X ×_R Y'` and of `X ×_R Y` is cartesian. -/
theorem isPullback_targetChangeMap (R : Type u) [CommRing R] (X Y Y' : Over (Spec (.of R)))
    (g : Y' ⟶ Y) :
    IsPullback (targetChangeMap R X Y Y' g) (pullback.snd X.hom Y'.hom)
      (pullback.snd X.hom Y.hom) g.left := by
  refine IsPullback.of_right (h₁₂ := pullback.fst X.hom Y.hom) (v₁₃ := X.hom) ?_ ?_
    (IsPullback.of_hasPullback X.hom Y.hom)
  · rw [targetChangeMap_comp_fst, Over.w g]
    exact IsPullback.of_hasPullback X.hom Y'.hom
  · simp

/-- The inverse image of a quasi-coherent kernel on `X ×_R Y` along the target-change
morphism. -/
def targetChangeKernel (R : Type u) [CommRing R] (X Y Y' : Over (Spec (.of R))) (g : Y' ⟶ Y)
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    Scheme.QuasicoherentModules (pullback X.hom Y'.hom) :=
  ⟨(Scheme.Modules.pullback (targetChangeMap R X Y Y' g)).obj K.obj,
    have : K.obj.IsQuasicoherent := K.property
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (targetChangeMap R X Y Y' g).toLRSHom.toShHom K.obj (by assumption)⟩

/-- Change of target for the pullback--tensor--pushforward formula of Tag 0FZB. -/
def integralTransformFormulaTargetChangeIso (R : Type u) [CommRing R]
    (X Y Y' : Over (Spec (.of R))) [IsAffine X.left] (g : Y' ⟶ Y)
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    integralTransformFormula R X Y K.obj ⋙ Scheme.Modules.pullback g.left ≅
      integralTransformFormula R X Y' (targetChangeKernel R X Y Y' g K).obj :=
  have : IsAffineHom (pullback.snd X.hom Y.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback X.hom Y.hom) inferInstance
  baseChangeIsoOfFunctor (isPullback_targetChangeMap R X Y Y' g)
      ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
        Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
              ⟨(pullback X.hom Y.hom).presheaf, Presheaf.isSheaf_of_isSheaf_comp _
              ((pullback X.hom Y.hom).presheaf) (forget₂ CommRingCat RingCat)
              ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj (K.obj)))
      (isQuasicoherent_tensorLeftFunctor_pullback R X Y K) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
          Scheme.Modules.pullback (pullback.fst X.hom Y.hom))
        (pullbackTensorLeftIso (targetChangeMap R X Y Y' g) K.obj))
      (Scheme.Modules.pushforward (pullback.snd X.hom Y'.hom)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι
        (Scheme.Modules.pullbackComp (targetChangeMap R X Y Y' g)
            (pullback.fst X.hom Y.hom) ≪≫
          Scheme.Modules.pullbackCongr (targetChangeMap_comp_fst R X Y Y' g)))
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(pullback X.hom Y'.hom).presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y'.hom).presheaf)
          (forget₂ CommRingCat RingCat) ((pullback X.hom Y'.hom).ringCatSheaf.2)⟩).obj
          (((Scheme.Modules.pullback (targetChangeMap R X Y Y' g)).obj K.obj))) ⋙
        Scheme.Modules.pushforward (pullback.snd X.hom Y'.hom))

/-- Let `X` be an affine scheme over `R`, let `g : Y' ⟶ Y` be a flat morphism of schemes over `R`
and let `K` be a quasi-coherent module on `X ×_R Y`.  Then the integral transform of `K` followed
by the inverse image along `g` is the integral transform of `(id_X × g)^*K`. -/
@[stacks 0FZF "flat target change"]
def quasicoherentIntegralTransformTargetChangeIso (R : Type u) [CommRing R]
    (X Y Y' : Over (Spec (.of R))) [IsAffine X.left] (g : Y' ⟶ Y) [Flat g.left]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    quasicoherentIntegralTransform R X Y K ⋙ quasicoherentPullback g.left ≅
      quasicoherentIntegralTransform R X Y' (targetChangeKernel R X Y Y' g K) :=
  ((SheafOfModules.isQuasicoherent Y'.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
      _).preimageIso
    (Functor.isoWhiskerRight (quasicoherentIntegralTransformData R X Y K).comparison
        (Scheme.Modules.pullback g.left) ≪≫
      integralTransformFormulaTargetChangeIso R X Y Y' g K ≪≫
      (quasicoherentIntegralTransformData R X Y'
        (targetChangeKernel R X Y Y' g K)).comparison.symm)

/-! ### Restriction of the target to an open subscheme -/

/-- The open immersion `X ×_R V ⟶ X ×_R Y` induced by an open immersion `j : V ⟶ Y`, where
`V` is a scheme over `R` through `j`. -/
def openTargetChangeMap (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) {V : Scheme.{u}}
    (j : V ⟶ Y.left) :
    pullback X.hom (Over.mk (j ≫ Y.hom) : Over (Spec (.of R))).hom ⟶ pullback X.hom Y.hom :=
  targetChangeMap R X Y (Over.mk (j ≫ Y.hom)) (Over.homMk j rfl)

/-- The target-change morphism along an open immersion is an open immersion. -/
instance isOpenImmersion_openTargetChangeMap (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) {V : Scheme.{u}} (j : V ⟶ Y.left) [IsOpenImmersion j] :
    IsOpenImmersion (openTargetChangeMap R X Y j) :=
  Scheme.pullback_map_isOpenImmersion _ _ _ _ (𝟙 X.left) j (𝟙 (Spec (.of R)))
    (by simp) (by simp)

/-- The restriction of a quasi-coherent kernel on `X ×_R Y` to the open subscheme
`X ×_R V`. -/
def openTargetKernel (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) {V : Scheme.{u}}
    (j : V ⟶ Y.left) [IsOpenImmersion j]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    Scheme.QuasicoherentModules
      (pullback X.hom (Over.mk (j ≫ Y.hom) : Over (Spec (.of R))).hom) :=
  ⟨(Scheme.Modules.restrictFunctor (openTargetChangeMap R X Y j)).obj K.obj,
    have : K.obj.IsQuasicoherent := K.property
    Scheme.Modules.isQuasicoherent_restrictFunctor (openTargetChangeMap R X Y j) K.obj⟩

/-- Restriction along an open immersion is the inverse image, on quasi-coherent modules. -/
def quasicoherentRestrictionIsoPullback {V Y : Scheme.{u}} (j : V ⟶ Y) [IsOpenImmersion j] :
    quasicoherentRestriction j ≅ quasicoherentPullback j :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ ((Scheme.Modules.restrictFunctorIsoPullback j).app M.obj))
    (fun φ ↦ ObjectProperty.hom_ext _
      ((Scheme.Modules.restrictFunctorIsoPullback j).hom.naturality φ.hom))

/-- Let `X` be an affine scheme over `R`, let `j : V ⟶ Y` be an open immersion of schemes and let
`K` be a quasi-coherent module on `X ×_R Y`.  Then the integral transform of `K` followed by
restriction to `V` is the integral transform of the restriction of `K` to `X ×_R V`. -/
@[stacks 0FZF "open target restriction"]
def quasicoherentIntegralTransformOpenTargetIso (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) [IsAffine X.left] {V : Scheme.{u}} (j : V ⟶ Y.left)
    [IsOpenImmersion j] (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    quasicoherentIntegralTransform R X Y K ⋙ quasicoherentRestriction j ≅
      quasicoherentIntegralTransform R X (Over.mk (j ≫ Y.hom))
        (openTargetKernel R X Y j K) := by
  letI : Flat (Over.homMk j rfl :
      (Over.mk (j ≫ Y.hom) : Over (Spec (.of R))) ⟶ Y).left := inferInstanceAs (Flat j)
  exact Functor.isoWhiskerLeft (quasicoherentIntegralTransform R X Y K)
      (quasicoherentRestrictionIsoPullback j) ≪≫
    quasicoherentIntegralTransformTargetChangeIso R X Y (Over.mk (j ≫ Y.hom))
      (Over.homMk j rfl) K ≪≫
    (integralTransformQcohFunctor R X (Over.mk (j ≫ Y.hom))).mapIso
      (ObjectProperty.isoMk _
        ((Scheme.Modules.restrictFunctorIsoPullback (openTargetChangeMap R X Y j)).app
          K.obj)).symm

end AlgebraicGeometry

end
