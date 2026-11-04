module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedProjectionFormula

/-!
# The projection formula over an affine algebraic space

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces with `Y`
affine. For `E ∈ D_QCoh(𝒪_X)` and `K ∈ D_QCoh(𝒪_Y)` the projection formula map
`Rf_*(E) ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)` is an isomorphism. For fixed `E` both sides are exact functors
of `K` commuting with direct sums, `𝒪_Y[0]` is a compact generator of `D_QCoh(𝒪_Y)`, and the map
is invertible at every shift of `𝒪_Y[0]`, tensoring with `𝒪_Y[q]` and with `Lf^*𝒪_Y[q] ≅ 𝒪_X[q]`
being autoequivalences.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleProjectionFormulaMap_of_iso`: invertibility at an
  object isomorphic to `𝒪_Y[q]`, for every morphism `f`.
* `AlgebraicGeometry.Space.isIso_smallEtaleProjectionFormulaMap_of_isAffineSpace`: Stacks 08IN
  over an affine target.

## References

* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] isGrothendieckAbelian_modules_ringUniverse
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **The projection formula map is invertible at a shift of the structure sheaf**, for every
morphism `f`: tensoring with `𝒪_Y[q]` and with `Lf^*𝒪_Y[q] ≅ 𝒪_X[q]` on the right are
autoequivalences, so the map is the mate of an isomorphism along autoequivalences. -/
theorem isIso_smallEtaleProjectionFormulaMap_of_iso (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))} (q : ℤ)
    (e : K ≅ DerivedCategory.Q.obj
      (Stacks.SheafOfModules.singleUnitComplex (smallEtaleRingedTopos B S hS Y).O q)) :
    IsIso (smallEtaleProjectionFormulaMap B S hS f E K) := by
  let L := smallEtaleDerivedModulePullback B S hS f
  have : ((smallEtaleDerivedTensor B S hS Y).flip.obj K).IsEquivalence :=
    (smallEtaleDerivedTensorProduct B S hS Y).isEquivalence_tensor_flip_obj_of_iso q e
  have : ((smallEtaleDerivedTensor B S hS X).flip.obj (L.obj K)).IsEquivalence :=
    (smallEtaleDerivedTensorProduct B S hS X).isEquivalence_tensor_flip_obj_of_iso q
      (L.mapIso e ≪≫ Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackSingleUnitIso
        (smallEtaleRingedToposHom B S hS f) q)
  have := isEquivalence_curry_uncurry_flip_obj (smallEtaleDerivedTensor B S hS Y) K
  have := isEquivalence_curry_uncurry_flip_obj (smallEtaleDerivedTensor B S hS X) (L.obj K)
  exact isIso_adjunctionTensorMap_of_isEquivalence (smallEtaleDerivedModuleAdjunction B S hS f)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleDerivedPullbackTensorIso f).hom E K

/-- The projection formula map `Rf_*(E) ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)` as a natural transformation
in `K`. -/
def smallEtaleProjectionFormulaNatTrans (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedTensor B S hS Y).obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj E) ⟶
      smallEtaleDerivedModulePullback B S hS f ⋙ (smallEtaleDerivedTensor B S hS X).obj E ⋙
        derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f) where
  app K := smallEtaleProjectionFormulaMap B S hS f E K
  naturality _ _ k := by
    have h := adjunctionTensorMap_natural (smallEtaleDerivedModuleAdjunction B S hS f)
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
      (smallEtaleDerivedPullbackTensorIso f).hom (𝟙 E) k
    simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at h
    exact h

/-- **Stacks 08IN over an affine target.** Let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces with `Y` affine, `E ∈ D_QCoh(𝒪_X)` and
`K ∈ D_QCoh(𝒪_Y)`. Then the projection formula map `Rf_*(E) ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)` is an
isomorphism. -/
theorem isIso_smallEtaleProjectionFormulaMap_of_isAffineSpace (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : QcohDerived B S hS Y K) :
    IsIso (smallEtaleProjectionFormulaMap B S hS f E K) := by
  let P := QcohDerived B S hS Y
  let DY := DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
  let DX := DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  let ι : P.FullSubcategory ⥤ DY := P.ι
  let : ι.CommShift ℤ := (inferInstance : P.ι.CommShift ℤ)
  let : ι.IsTriangulated := (inferInstance : P.ι.IsTriangulated)
  let L : DY ⥤ DX := smallEtaleDerivedModulePullback B S hS f
  let R : DX ⥤ DY := derivedModulePushforward B S hS f
  let : R.CommShift ℤ := derivedModulePushforward_commShift B S hS f
  let : R.IsTriangulated := derivedModulePushforward_isTriangulated B S hS f
  have hcl : ∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I) :=
    isClosedUnderColimitsOfShape_qcohDerived B S hS Y
  have : HasCoproducts.{u} P.FullSubcategory := fun I => by
    have := hcl I
    infer_instance
  have : LocallySmall.{u} P.FullSubcategory := inferInstance
  let TY := smallEtaleDerivedTensorProduct B S hS Y
  let TX := smallEtaleDerivedTensorProduct B S hS X
  let T₁ : DY ⥤ DY := (smallEtaleDerivedTensor B S hS Y).obj (R.obj E)
  let T₂ : DX ⥤ DX := (smallEtaleDerivedTensor B S hS X).obj E
  let : T₁.CommShift ℤ := TY.commShift_right _
  let : T₁.IsTriangulated := TY.exact_right _
  let : T₂.CommShift ℤ := TX.commShift_right _
  let : T₂.IsTriangulated := TX.exact_right _
  let τ : ι ⋙ T₁ ⟶ ι ⋙ L ⋙ T₂ ⋙ R :=
    Functor.whiskerLeft P.ι (smallEtaleProjectionFormulaNatTrans f E)
  have hι : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) ι := fun I => by
    have := hcl I
    exact (inferInstance : PreservesColimitsOfShape (Discrete I) P.ι)
  have : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) (ι ⋙ T₁) :=
    fun I => by
      have : PreservesColimitsOfShape (Discrete I) T₁ :=
        Stacks.SheafOfModules.DerivedTensorProduct.preservesColimitsOfShape_tensor_obj TY _ I
      infer_instance
  have : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) (ι ⋙ L ⋙ T₂ ⋙ R) := fun I => by
    have : PreservesColimitsOfShape (Discrete I) L :=
      (smallEtaleDerivedModuleAdjunction B S hS f).leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape
    have : PreservesColimitsOfShape (Discrete I) T₂ :=
      Stacks.SheafOfModules.DerivedTensorProduct.preservesColimitsOfShape_tensor_obj TX _ I
    let G : P.FullSubcategory ⥤ DX := ι ⋙ L ⋙ T₂
    have hG : PreservesColimitsOfShape (Discrete I) G := inferInstance
    have hGq : ∀ K' : P.FullSubcategory, QcohDerived B S hS X (G.obj K') := fun K' =>
      qcohDerived_smallEtaleDerivedTensor X E _ hE
        (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ f K'.obj K'.property)
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
    exact isIso_smallEtaleProjectionFormulaMap_of_iso f E (-n) e
  exact
    StacksDraft.CompactDevissage.isIso_app_of_isCompactlyGenerated_of_forall_shift_of_locallySmall
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

end AlgebraicGeometry.Space

end
