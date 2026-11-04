module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeCohomologyModuleBridge
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.SupportedTensorPushforward

/-!
# A criterion for the matching of a multiplication with two Gysin edge morphisms

(statement of the criterion: the matching holds as soon as the two maps into `i_*Rℋ_Z(M)`
before the counit agree on degree-`c` cohomology)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.DeRham.CohomologicalGysin
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule tensorBifunctorNat
  baseRingedSpace multiplicationInt)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.GysinCupHodge

open DerivedCategory

/-- The algebra of `tensor_map_counit_eq`, at variables. -/
private lemma counit_braiding_chase {C : Type*} [Category* C] {P Q R S : C} (b : P ≅ Q)
    (b' : R ≅ S) (f : P ⟶ R) (g : Q ⟶ S) (h : f ≫ b'.hom = b.hom ≫ g) :
    b.inv ≫ f ≫ b'.hom = g := by
  rw [h, Iso.inv_hom_id_assoc]

/-- The algebra of `edgeTensorMatching_of_eq`, at variables. -/
private lemma edge_chase {C : Type*} [Category* C]
    {A₀ A₁ B Lo Lm Mt PK PT Q₀ Q₁ Q₂ Mm Mo : C}
    (T : C ⥤ C) (a : A₀ ⟶ A₁) (sL : A₁ ⟶ B) (εL : B ⟶ Lo) (mL : Lo ⟶ Lm)
    (tt₁ : T.obj Lm ⟶ Mt) (tt₂ : Mt ⟶ Mo) (STPM : T.obj B ⟶ PK) (εT : PK ⟶ T.obj Lo)
    (e : Mo ≅ Mm) (DΦ : PK ⟶ PT) (εM : PT ⟶ Mm) (t₀ : T.obj A₀ ⟶ Q₀) (t₁ : Q₀ ⟶ Q₁)
    (t₂ : Q₁ ⟶ Q₂) (sM : Q₂ ⟶ PT)
    (hc : T.map εL = STPM ≫ εT)
    (hn : DΦ ≫ εM = εT ≫ T.map mL ≫ tt₁ ≫ tt₂ ≫ e.hom)
    (hR : (T.map (a ≫ sL) ≫ STPM ≫ DΦ) ≫ εM ≫ e.inv =
      (t₀ ≫ t₁ ≫ t₂ ≫ sM) ≫ εM ≫ e.inv) :
    T.map (a ≫ (sL ≫ εL) ≫ mL) ≫ tt₁ ≫ tt₂ = t₀ ≫ t₁ ≫ t₂ ≫ (sM ≫ εM) ≫ e.inv := by
  simp only [Category.assoc, T.map_comp] at hR ⊢
  rw [← hR, reassoc_of% hn, reassoc_of% hc]
  simp

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)

section Formal

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-- **Tensoring the canonical map `i_*Rℋ_Z(M) ⟶ M` on the left factors through the
multiplication of Tag 0G75**: `K ⊗^L ε_M` is the map `supportedTensorPushMap` followed by the
canonical map at `K ⊗^L M`. -/
theorem tensor_map_counit_eq
    (K M : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    ((derivedTensorProductFunctor X.sheaf).obj K).map
        ((derivedPushforwardAdjunction X Z hZ).counit.app M) =
      supportedTensorPushMap X Z hZ K M ≫
        (derivedPushforwardAdjunction X Z hZ).counit.app
          (((derivedTensorProductFunctor X.sheaf).obj K).obj M) := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  rw [supportedTensorPushMap_comp_counit]
  have h := (canonicalDerivedTensorProduct X.sheaf).braidingIso_hom_naturality
    (AlgebraicGeometry.RingedSpace.ringedSite X)
    ((derivedPushforwardAdjunction X Z hZ).counit.app M) (𝟙 K)
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  exact (counit_braiding_chase _ _ _ _ h).symm

variable {X} in
/-- The map before the canonical map on the left-hand side of the edge matching. -/
def edgeMatchingLeft {F L M G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (c : ℕ) (w : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj L ⟶ M)
    (sL : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj G ⟶
      (derivedSupportedPushforward X Z hZ).obj
        ((singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj L)) :
    ((derivedTensorProductFunctor X.sheaf).obj (moduleDerived (A := X.sheaf) (singleNat F 0))).obj
        (moduleDerived (A := X.sheaf) (singleNat G c)) ⟶
      (derivedSupportedPushforward X Z hZ).obj
        ((singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj M) :=
  ((derivedTensorProductFunctor X.sheaf).obj (moduleDerived (A := X.sheaf) (singleNat F 0))).map
      ((moduleDerivedSingleIso G c).hom ≫ sL) ≫
    supportedTensorPushMap X Z hZ _ _ ≫
    (derivedSupportedPushforward X Z hZ).map
      (((derivedTensorProductFunctor X.sheaf).obj
          (moduleDerived (A := X.sheaf) (singleNat F 0))).map (moduleDerivedSingleIso L 0).inv ≫
        (canonicalDerivedTensorProduct X.sheaf).toTensor
          ((singleNat F 0).extend ComplexShape.embeddingUpNat)
          ((singleNat L 0).extend ComplexShape.embeddingUpNat) ≫
        DerivedCategory.Q.map (multiplicationInt (singleTensorMult w 0 0 0 rfl)) ≫
        (moduleDerivedSingleIso M 0).hom)

variable {X} in
/-- The map before the canonical map on the right-hand side of the edge matching. -/
def edgeMatchingRight {F G M GM : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (c : ℕ) (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ GM)
    (sM : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj GM ⟶
      (derivedSupportedPushforward X Z hZ).obj
        ((singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj M)) :
    ((derivedTensorProductFunctor X.sheaf).obj (moduleDerived (A := X.sheaf) (singleNat F 0))).obj
        (moduleDerived (A := X.sheaf) (singleNat G c)) ⟶
      (derivedSupportedPushforward X Z hZ).obj
        ((singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj M) :=
  (canonicalDerivedTensorProduct X.sheaf).toTensor
      ((singleNat F 0).extend ComplexShape.embeddingUpNat)
      ((singleNat G c).extend ComplexShape.embeddingUpNat) ≫
    DerivedCategory.Q.map (multiplicationInt (singleTensorMult μ 0 c c (zero_add c))) ≫
    (moduleDerivedSingleIso GM c).hom ≫ sM

variable {X} in
/-- **A criterion for the edge matching.**  If the two maps into `i_*Rℋ_Z(M[0])` before the
canonical map agree, the matching `EdgeTensorMatching` holds for the edge morphisms
`sL ≫ ε` and `sM ≫ ε`. -/
theorem edgeTensorMatching_of_eq {F L M G GM : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (c : ℕ) (w : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj L ⟶ M)
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ GM)
    (sL : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj G ⟶
      (derivedSupportedPushforward X Z hZ).obj
        ((singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj L))
    (sM : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj GM ⟶
      (derivedSupportedPushforward X Z hZ).obj
        ((singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj M))
    (h : edgeMatchingLeft Z hZ c w sL = edgeMatchingRight Z hZ c μ sM) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    EdgeTensorMatching c w μ (sL ≫ (derivedPushforwardAdjunction X Z hZ).counit.app _)
      (sM ≫ (derivedPushforwardAdjunction X Z hZ).counit.app _) := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  have hc := tensor_map_counit_eq X Z hZ (moduleDerived (A := X.sheaf) (singleNat F 0))
    ((singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj L)
  have hR := congrArg (· ≫ (derivedPushforwardAdjunction X Z hZ).counit.app _ ≫
    (moduleDerivedSingleIso M 0).inv) h
  dsimp only [edgeMatchingLeft, edgeMatchingRight] at hR
  exact edge_chase (hc := hc) (hn := (derivedPushforwardAdjunction X Z hZ).counit.naturality _)
    (hR := hR)

end Formal

end StandardModel

end Stacks.DeRham.GysinCupHodge
