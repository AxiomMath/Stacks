module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.DerivedLeftUnitorSingle

/-!
# The multiplication of Tag 0G75 with the structure sheaf on the left

When the left factor is `𝒪_X[0]` and the multiplication is the left unitor `𝒪_X ⊗ L ≅ L`, the
map `edgeMatchingLeft` built from the multiplication of [Stacks, Tag 0G75] is the left unit
constraint of `⊗^L` followed by the edge morphism.

## Main results

* `edgeMatchingLeft_unit`: `edgeMatchingLeft` along the left unitor `𝒪_X ⊗ L ≅ L` is the left
  unit constraint of `⊗^L` followed by the given morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.SupportedComplexes RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.Tensor (sheafTensor)
open AlgebraicGeometry.SheafOfModules (moduleDerived multiplicationInt)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)
open DerivedCategory

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.GysinCupHodge

private lemma unit_law_chase {C : Type*} [Category* C] (T : C ⥤ C) (lam : T ⟶ 𝟭 C)
    {P A₁ B Lo Lm Lt PK PT : C} (a : P ⟶ A₁) (sL : A₁ ⟶ B) (εL : B ⟶ Lo) (m : Lm ≅ Lo)
    (tt₁ : T.obj Lm ⟶ Lt) (tt₂ : Lt ⟶ Lm) (STPM : T.obj B ⟶ PK) (εT : PK ⟶ T.obj Lo)
    (DΦ : PK ⟶ PT) (εM : PT ⟶ Lo) (hlam : lam.app Lm = tt₁ ≫ tt₂)
    (hc : T.map εL = STPM ≫ εT) (hn : DΦ ≫ εM = εT ≫ T.map m.inv ≫ tt₁ ≫ tt₂ ≫ m.hom) :
    (T.map (a ≫ sL) ≫ STPM ≫ DΦ) ≫ εM = (lam.app P ≫ a ≫ sL) ≫ εL := by
  have hnat := lam.naturality (a ≫ sL ≫ εL ≫ m.inv)
  simp only [Functor.id_map] at hnat
  rw [Category.assoc, Category.assoc, hn, ← Category.assoc STPM, ← hc,
    ← Category.assoc tt₁, ← hlam, ← T.map_comp_assoc, ← T.map_comp_assoc]
  simp only [Category.assoc] at hnat ⊢
  rw [reassoc_of% hnat]
  simp

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} (Z : Set X.carrier) (hZ : IsClosed Z)

/-- **The edge map of Tag 0G75 with `𝒪_X` on the left is the left unit constraint followed by
the edge morphism.** For a sheaf `G` placed in degree `c` whose image in the derived category is
the direct image of an object `W` from the closed subset, and any morphism
`sL : G[-c] ⟶ i_*R𝓗_Z(L[0])`, `edgeMatchingLeft` along the left unitor `𝒪_X ⊗ L ≅ L` is the left
unit constraint of `⊗^L` followed by `sL`. -/
theorem edgeMatchingLeft_unit (c : ℕ)
    {L G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (sL : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj G ⟶
      (derivedSupportedPushforward X Z hZ).obj
        ((singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj L))
    (W : DerivedCategory (_root_.SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z))))
    (e : letI := pushforward_preservesFiniteLimits X Z
      letI := pushforward_preservesFiniteColimits X Z hZ
      (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj W ≅
        (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj G) :
    edgeMatchingLeft Z hZ c (sheafLeftUnitor L).hom sL =
      (derivedLeftUnitor X).app (moduleDerived (A := X.sheaf) (singleNat G c)) ≫
        (moduleDerivedSingleIso G c).hom ≫ sL := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  have := ((derivedPushforwardAdjunction X Z hZ).fullyFaithfulLOfIsIsoUnit).full
  have := ((derivedPushforwardAdjunction X Z hZ).fullyFaithfulLOfIsIsoUnit).faithful
  have : IsIso ((derivedLeftUnitor X).app (moduleDerived (A := X.sheaf) (singleNat G c))) := by
    rw [derivedLeftUnitor_app_Q, (canonicalDerivedTensorProduct X.sheaf).toTensor_eq_comparisonLeft
      _ _ (isKFlat_unitExtend X)]
    exact IsIso.comp_isIso' inferInstance
      (Functor.map_isIso (F := DerivedCategory.Q) (f := complexLeftUnitor (X := X)
        ((singleNat G c).extend ComplexShape.embeddingUpNat)))
  refine eq_of_comp_counit (derivedPushforwardAdjunction X Z hZ)
    (e ≪≫ (moduleDerivedSingleIso G c).symm ≪≫
      (asIso ((derivedLeftUnitor X).app (moduleDerived (A := X.sheaf) (singleNat G c)))).symm)
    _ _ ?_
  have hlam := (derivedLeftUnitor_app_Q (X := X)
    ((singleNat L 0).extend ComplexShape.embeddingUpNat)).trans
      (congrArg (fun t => _ ≫ DerivedCategory.Q.map t)
        (multiplicationInt_singleTensorMult_leftUnitor L 0).symm)
  have hn := (derivedPushforwardAdjunction X Z hZ).counit.naturality
    (((derivedTensorProductFunctor X.sheaf).obj
          (moduleDerived (A := X.sheaf) (singleNat (unitModule X) 0))).map
        (moduleDerivedSingleIso L 0).inv ≫
      (canonicalDerivedTensorProduct X.sheaf).toTensor
        ((singleNat (unitModule X) 0).extend ComplexShape.embeddingUpNat)
        ((singleNat L 0).extend ComplexShape.embeddingUpNat) ≫
      DerivedCategory.Q.map
        (multiplicationInt (singleTensorMult (sheafLeftUnitor L).hom 0 0 0 rfl)) ≫
      (moduleDerivedSingleIso L 0).hom)
  simp only [Functor.id_map] at hn
  dsimp only [edgeMatchingLeft]
  exact unit_law_chase _ (derivedLeftUnitor X) _ _ _ (moduleDerivedSingleIso L 0) _ _ _ _ _ _ hlam
    (tensor_map_counit_eq X Z hZ _ _) hn

end StandardModel

end Stacks.DeRham.GysinCupHodge
