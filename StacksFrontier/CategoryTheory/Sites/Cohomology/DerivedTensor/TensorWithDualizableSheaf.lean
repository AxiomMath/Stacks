module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSingleTensorIso
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite

/-!
# Tensoring with a dualizable sheaf of modules on the derived category

Let `(𝒞, 𝒪)` be a ringed site and let `ℰ` be a sheaf of `𝒪`-modules with a left dual `ℰ'` for the
tensor product of [Stacks, Tag 01CA]: an exact pairing `η : 𝒪 ⟶ ℰ ⊗ ℰ'`, `ε : ℰ' ⊗ ℰ ⟶ 𝒪` (for
instance a finite locally free `ℰ` with `ℰ' = ℰ^∨`, [Stacks, Tag 0FNY]). Then `- ⊗ ℰ` is left
adjoint to `- ⊗ ℰ'` on `Mod(𝒪)`, both functors are exact, and so the adjunction descends to the
derived category. On the derived category `- ⊗ ℰ` is the derived tensor product with `ℰ[0]`.

The consequence recorded here is the derived form of `Hom(Y ⊗ ℰ, ℳ) = Hom(Y, ℳ ⊗ ℰ')`: for an
object `Y` of `D(𝒪)` and a sheaf `ℳ`, a morphism `Y ⊗^𝐋 ℰ[0] ⟶ ℳ[0]` is the same thing as a
morphism `Y ⟶ (ℳ ⊗ ℰ')[0]`, the passage being "tensor with `ℰ[0]`, compare `(ℳ ⊗ ℰ')[0] ⊗^𝐋 ℰ[0]`
with `((ℳ ⊗ ℰ') ⊗ ℰ)[0]` and apply `1 ⊗ ε`".

## Main definitions

* `Stacks.DerivedTensor.RingedSite.derivedTensorSingleToTensor`: the canonical map
  `ℱ[0] ⊗^𝐋 𝒢[0] ⟶ (ℱ ⊗ 𝒢)[0]`.
* `Stacks.DerivedTensor.RingedSite.tensorRightSingleIso`: `- ⊗^𝐋 ℰ[0] ≅ D(- ⊗ ℰ)`.

## Main results

* `Stacks.DerivedTensor.RingedSite.bijective_tensorRightSingle_comp_counit`: the bijection
  `Hom(Y, (ℳ ⊗ ℰ')[0]) ≃ Hom(Y ⊗^𝐋 ℰ[0], ℳ[0])`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Stacks.DerivedTensor.RingedSite

open Stacks.SheafOfModules.DerivedMonoidal (Mod)

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {R} (E : Mod R) [HasRightDual E]

open BraidedCategory (tensorLeftIsoTensorRight)

/-- `- ⊗ ℰ` preserves finite colimits: it is a left adjoint. -/
instance preservesFiniteColimits_tensorRight_of_hasRightDual :
    PreservesFiniteColimits (tensorRight E) :=
  letI := (tensorRightAdjunction E Eᘁ).leftAdjoint_preservesColimits
  inferInstance

/-- `- ⊗ ℰ` preserves finite limits: it is isomorphic to `ℰ ⊗ -`, a right adjoint. -/
instance preservesFiniteLimits_tensorRight_of_hasRightDual :
    PreservesFiniteLimits (tensorRight E) :=
  letI := (tensorLeftAdjunction E Eᘁ).rightAdjoint_preservesLimits
  preservesFiniteLimits_of_natIso (tensorLeftIsoTensorRight E)

/-- `- ⊗ ℰ'` preserves finite limits: it is a right adjoint. -/
instance preservesFiniteLimits_tensorRight_rightDual :
    PreservesFiniteLimits (tensorRight Eᘁ) :=
  letI := (tensorRightAdjunction E Eᘁ).rightAdjoint_preservesLimits
  inferInstance

/-- `- ⊗ ℰ'` preserves finite colimits: it is isomorphic to `ℰ' ⊗ -`, a left adjoint. -/
instance preservesFiniteColimits_tensorRight_rightDual :
    PreservesFiniteColimits (tensorRight Eᘁ) :=
  letI := (tensorLeftAdjunction E Eᘁ).leftAdjoint_preservesColimits
  preservesFiniteColimits_of_natIso (tensorLeftIsoTensorRight Eᘁ)

/-- **A sheaf of modules with a left dual is flat.** -/
theorem isFlat_of_hasRightDual :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) E :=
  (Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor R E).2
    ((exactFunctor_iff _).2 ⟨preservesFiniteLimits_tensorRight_of_hasRightDual E,
      preservesFiniteColimits_tensorRight_of_hasRightDual E⟩)

/-! ### Tensoring with `ℰ[0]` on the derived category -/

universe d

variable [HasDerivedCategory.{d} (Mod R)]

/-- `ℰ` placed in degree zero, as a cochain complex. -/
abbrev singleComplex (M : Mod R) : CochainComplex (Mod R) ℤ :=
  (CochainComplex.singleFunctor (Mod R) 0).obj M

omit [HasDerivedCategory.{d} (Mod R)] in
/-- `ℰ[0]` is K-flat, `ℰ` being flat. -/
theorem kFlat_singleComplex_of_hasRightDual :
    Stacks.SheafOfModules.KFlat R (singleComplex E) :=
  Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat R E
    (isFlat_of_hasRightDual E) 0

/-- On complexes, the derived tensor product with `ℰ[0]` is `- ⊗ ℰ` applied degreewise: the K-flat
comparison of the right factor, `Tot(K ⊗ ℰ[0]) ≅ K ⊗ ℰ`, and the comparison of
`(- ⊗ ℰ).mapDerivedCategory` with its definition. -/
def tensorRightSingleIsoQ :
    DerivedCategory.Q ⋙ (derivedTensorProductFunctor R).flip.obj
        (DerivedCategory.Q.obj (singleComplex E)) ≅
      DerivedCategory.Q ⋙ (tensorRight E).mapDerivedCategory :=
  NatIso.ofComponents
    (fun K => (canonicalDerivedTensorProduct R).comparisonRight K (singleComplex E)
        (kFlat_singleComplex_of_hasRightDual E) ≪≫
      DerivedCategory.Q.mapIso (HomologicalComplex.mapBifunctorSingleRightIso
        (Stacks.SheafOfModules.Tensor.sheafTensor R) K E) ≪≫
      ((tensorRight E).mapDerivedCategoryFactors.app K).symm)
    (fun {K K'} φ => by
      have h₁ := (canonicalDerivedTensorProduct R).comparisonRight_naturality φ
        (𝟙 (singleComplex E)) (kFlat_singleComplex_of_hasRightDual E)
        (kFlat_singleComplex_of_hasRightDual E)
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h₁
      have h₂ := HomologicalComplex.mapBifunctorSingleRightIso_hom_naturality
        (Stacks.SheafOfModules.Tensor.sheafTensor R) K E φ
      have h₃ := (tensorRight E).mapDerivedCategoryFactors.inv.naturality φ
      dsimp only [Iso.trans_hom, Functor.comp_map, Functor.flip_obj_map, Functor.mapIso_hom,
        Iso.symm_hom, Iso.app_inv, Functor.comp_obj, Functor.flip_obj_obj] at h₃ ⊢
      rw [reassoc_of% h₁]
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine congrArg (((canonicalDerivedTensorProduct R).comparisonRight K (singleComplex E)
        (kFlat_singleComplex_of_hasRightDual E)).hom ≫ ·) ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      calc _ = DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ (𝟙 (singleComplex E))
              (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ) ≫
            (HomologicalComplex.mapBifunctorSingleRightIso
              (Stacks.SheafOfModules.Tensor.sheafTensor R) K' E).hom) ≫
            (tensorRight E).mapDerivedCategoryFactors.inv.app K' :=
            (DerivedCategory.Q.map_comp_assoc _ _ _).symm
        _ = DerivedCategory.Q.map ((HomologicalComplex.mapBifunctorSingleRightIso
              (Stacks.SheafOfModules.Tensor.sheafTensor R) K E).hom ≫
            ((tensorRight E).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) ≫
            (tensorRight E).mapDerivedCategoryFactors.inv.app K' := by rw [h₂]; rfl
        _ = _ := (DerivedCategory.Q.map_comp_assoc _ _ _).trans
            (congrArg (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorSingleRightIso
              (Stacks.SheafOfModules.Tensor.sheafTensor R) K E).hom ≫ ·) h₃))

/-- **The derived tensor product with `ℰ[0]` is `- ⊗ ℰ` on the derived category**, as functors
`D(𝒪) ⥤ D(𝒪)`. -/
def tensorRightSingleIso :
    (derivedTensorProductFunctor R).flip.obj (DerivedCategory.Q.obj (singleComplex E)) ≅
      (tensorRight E).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (Mod R) (ComplexShape.up ℤ)) _ _ _ _
    (tensorRightSingleIsoQ E)

/-- On the image `Q(K)` of a cochain complex `K`, the component of `tensorRightSingleIso E` is the
component at `K` of `tensorRightSingleIsoQ E`. -/
theorem tensorRightSingleIso_hom_app_Q (K : CochainComplex (Mod R) ℤ) :
    (tensorRightSingleIso E).hom.app (DerivedCategory.Q.obj K) =
      (tensorRightSingleIsoQ E).hom.app K := by
  simp [tensorRightSingleIso, Localization.liftNatIso, Localization.liftNatTrans_app]

/-! ### The canonical map `ℱ[0] ⊗^𝐋 𝒢[0] ⟶ (ℱ ⊗ 𝒢)[0]` -/

/-- **The canonical map `ℱ[0] ⊗^𝐋 𝒢[0] ⟶ (ℱ ⊗ 𝒢)[0]`** from the derived tensor product of two
modules placed in degree zero to their tensor product placed in degree zero: the canonical map of
[Stacks, Tag 06YU] to the total tensor complex, followed by the identification
`Tot(ℱ[0] ⊗ 𝒢[0]) = (ℱ ⊗ 𝒢)[0]`. It is an isomorphism when `𝒢` is flat. -/
def derivedTensorSingleToTensor (F G : Mod R) :
    ((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (singleComplex F))).obj
        (DerivedCategory.Q.obj (singleComplex G)) ⟶
      DerivedCategory.Q.obj (singleComplex (F ⊗ G)) :=
  (canonicalDerivedTensorProduct R).toTensor (singleComplex F) (singleComplex G) ≫
    DerivedCategory.Q.map ((HomologicalComplex.mapBifunctorSingleRightIso
      (Stacks.SheafOfModules.Tensor.sheafTensor R) (singleComplex F) G).hom ≫
      ((tensorRight G).mapCochainComplexSingleFunctor 0).hom.app F)

omit [HasDerivedCategory.{d} (Mod R)] in
/-- The counit of the adjunction induced on complexes, at a single complex. -/
theorem mapHomologicalComplex_counit_app_single (M : Mod R) :
    ((tensorRight E).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((tensorRight Eᘁ).mapCochainComplexSingleFunctor 0).inv.app M) ≫
      (((tensorRightAdjunction E Eᘁ).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app
        (singleComplex M)) =
      ((tensorRight E).mapCochainComplexSingleFunctor 0).hom.app (M ⊗ Eᘁ) ≫
        (CochainComplex.singleFunctor (Mod R) 0).map
          ((tensorRightAdjunction E Eᘁ).counit.app M) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases h : i = 0
  · subst h
    simp only [CochainComplex.singleFunctor, Functor.comp_obj,
      Functor.flip_obj_obj, curriedTensor_obj_obj,
      Functor.mapHomologicalComplex_obj_X, singleComplex, Functor.id_obj,
      Functor.mapCochainComplexSingleFunctor, Adjunction.mapHomologicalComplex,
      NatTrans.mapHomologicalComplex, Adjunction.mkOfUnitCounit_counit, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Functor.flip_obj_map,
      curriedTensor_map_app, Functor.map_comp, NatTrans.comp_app, Category.assoc,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc]
    have hn := (tensorRightAdjunction E Eᘁ).counit_naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv
    dsimp at hn
    rw [hn]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i h).eq_of_tgt _ _

/-- The counit of the adjunction induced on derived categories, on the image of a complex: the
degreewise counit, read through the comparisons of the two functors with their definitions. -/
theorem mapDerivedCategory_counit_app_Q (K : CochainComplex (Mod R) ℤ) :
    (tensorRightAdjunction E Eᘁ).mapDerivedCategory.counit.app (DerivedCategory.Q.obj K) =
      (tensorRight E).mapDerivedCategory.map
          ((tensorRight Eᘁ).mapDerivedCategoryFactors.hom.app K) ≫
        (tensorRight E).mapDerivedCategoryFactors.hom.app
          (((tensorRight Eᘁ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          (((tensorRightAdjunction E Eᘁ).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app
            K) := by
  simp only [CategoryTheory.Adjunction.mapDerivedCategory, Adjunction.localization_counit_app]
  rfl

/-- **`Hom(Y, (ℳ ⊗ ℰ')[0]) ≃ Hom(Y ⊗^𝐋 ℰ[0], ℳ[0])`.** For `Y` in `D(𝒪)` and a sheaf `ℳ`, a
morphism `ψ : Y ⟶ (ℳ ⊗ ℰ')[0]` is determined by, and every morphism `Y ⊗^𝐋 ℰ[0] ⟶ ℳ[0]` is, the
composite of `ψ ⊗ ℰ[0]`, the canonical map `(ℳ ⊗ ℰ')[0] ⊗^𝐋 ℰ[0] ⟶ ((ℳ ⊗ ℰ') ⊗ ℰ)[0]` and
`1 ⊗ ε : (ℳ ⊗ ℰ') ⊗ ℰ ⟶ ℳ`, the counit of `- ⊗ ℰ ⊣ - ⊗ ℰ'`. -/
theorem bijective_tensorRightSingle_comp_counit (Y : DerivedCategory (Mod R)) (M : Mod R) :
    Function.Bijective (fun ψ : Y ⟶ DerivedCategory.Q.obj (singleComplex (M ⊗ Eᘁ)) =>
      ((derivedTensorProductFunctor R).map ψ).app (DerivedCategory.Q.obj (singleComplex E)) ≫
        derivedTensorSingleToTensor (M ⊗ Eᘁ) E ≫
          DerivedCategory.Q.map ((CochainComplex.singleFunctor (Mod R) 0).map
            ((tensorRightAdjunction E Eᘁ).counit.app M))) := by
  let adjD := (tensorRightAdjunction E Eᘁ).mapDerivedCategory
  let θ := tensorRightSingleIso E
  let ι : DerivedCategory.Q.obj (singleComplex (M ⊗ Eᘁ)) ⟶
      (tensorRight Eᘁ).mapDerivedCategory.obj (DerivedCategory.Q.obj (singleComplex M)) :=
    DerivedCategory.Q.map (((tensorRight Eᘁ).mapCochainComplexSingleFunctor 0).inv.app M) ≫
      (tensorRight Eᘁ).mapDerivedCategoryFactors.inv.app (singleComplex M)
  have hι : IsIso ι := by dsimp [ι]; infer_instance
  have key : derivedTensorSingleToTensor (M ⊗ Eᘁ) E ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor (Mod R) 0).map
          ((tensorRightAdjunction E Eᘁ).counit.app M)) =
      θ.hom.app (DerivedCategory.Q.obj (singleComplex (M ⊗ Eᘁ))) ≫
        (tensorRight E).mapDerivedCategory.map ι ≫
          adjD.counit.app (DerivedCategory.Q.obj (singleComplex M)) := by
    rw [tensorRightSingleIso_hom_app_Q, mapDerivedCategory_counit_app_Q]
    have hc := mapHomologicalComplex_counit_app_single E M
    have hn := (tensorRight E).mapDerivedCategoryFactors_hom_naturality
      (((tensorRight Eᘁ).mapCochainComplexSingleFunctor 0).inv.app M)
    simp only [derivedTensorSingleToTensor, tensorRightSingleIsoQ, ι, NatIso.ofComponents_hom_app,
      Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp, Category.assoc,
      (canonicalDerivedTensorProduct R).toTensor_eq_comparisonRight _ _
        (kFlat_singleComplex_of_hasRightDual E)]
    congr 1
    refine (congrArg (· ≫ _) (DerivedCategory.Q.map_comp _ _)).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_))
    refine Eq.symm ?_
    rw [← Functor.map_comp_assoc (tensorRight E).mapDerivedCategory
        ((tensorRight Eᘁ).mapDerivedCategoryFactors.inv.app (singleComplex M)),
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hn]
    refine (Iso.inv_hom_id_app_assoc ((tensorRight E).mapDerivedCategoryFactors) _ _).trans ?_
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, hc]
  have h₁ := ((θ.app Y).symm.homFromEquiv (Z := DerivedCategory.Q.obj (singleComplex M))).bijective
  have h₂ := (adjD.homEquiv Y (DerivedCategory.Q.obj (singleComplex M))).symm.bijective
  have h₃ := (asIso ι).homToEquiv (Z := Y).bijective
  refine Eq.mp (congrArg Function.Bijective ?_) (h₁.comp (h₂.comp h₃))
  funext ψ
  simp only [Function.comp_apply, Iso.homFromEquiv_apply, Iso.homToEquiv_apply, asIso_hom,
    Iso.symm_inv, Iso.app_hom]
  rw [key, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hθ := θ.hom.naturality ψ
  dsimp only [Functor.flip_obj_map] at hθ
  rw [reassoc_of% hθ]

end Stacks.DerivedTensor.RingedSite

end
