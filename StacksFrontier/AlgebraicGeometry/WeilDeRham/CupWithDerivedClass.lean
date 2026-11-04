module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeCupGysinEdge
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEdgeHomology
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ShiftedStructureSheafTensor
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.CanonicalSheafCertificate

/-!
# The cup product with the class of a morphism of the derived category

Let `(X, 𝒪_X)` be a ringed space, `G` and `L` sheaves of modules and `e : 𝒪_X[-n] ⟶ L[0]` a
morphism of `D(𝒪_X)`, so that `b = Hⁿ(e)(1) ∈ Hⁿ(X, L)` is the class it represents. The cup
product of Cohomology, Section 0FKU, `ε ↦ ε ∪ b`, `Hⁿ(X, G) ⟶ H^{2n}(X, G ⊗ L)`, is (up to a
sign) the map on cohomology of a morphism `G[-n] ⟶ (G ⊗ L)[0]` of the derived category of the
form `α ≫ (G[0] ⊗^𝐋 e) ≫ β`, where `α` and `β` do not depend on `e`: the cup product with the
class of `1` placed in degree `n` is an isomorphism `Hⁿ(X, G) ≅ H^{2n}(RΓ(G[0] ⊗^𝐋 𝒪[-n]))`
(`canonicalPairingModule_sectionClass`, the derived tensor product of `G[0]` with the K-flat
complex `𝒪[-n]` being computed by the total tensor complex), and the cup product is natural in
its second factor.

## Main results

* `Stacks.WeilDeRham.exists_cup_eq_cohomologyMapOfSingleHom`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.DeRham.CohomologicalGysin Stacks.DeRham.GysinCupHodge
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule tensorBifunctorNat
  baseRingedSpace multiplicationInt)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open DerivedCategory
open scoped Stacks.StandardDerivedModel

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.WeilDeRham

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

section KFlatRight

universe d

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules R)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ)]

/-- **The canonical map to the total tensor complex is invertible at a K-flat right factor.** -/
theorem isIso_toTensor_of_kFlat_right
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.{d, u} R)
    (K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ)
    (hL : Stacks.SheafOfModules.KFlat.KFlat R L) : IsIso (T.toTensor K L) := by
  rw [T.toTensor_eq_comparisonRight K L hL]
  infer_instance

end KFlatRight

variable {X : RingedSpace.{u, u}}

/-- The global section `1` of the structure sheaf. -/
abbrev unitSection : (unitModule X).val.sections :=
  (unitModule X).unitHomEquiv (𝟙 _)

/-- The structure sheaf placed in degree `n` and extended by zero is K-flat. -/
theorem kFlat_unitExtend (n : ℕ) :
    Stacks.SheafOfModules.KFlat.KFlat X.sheaf
      ((singleNat (X := X) (unitModule X) n).extend ComplexShape.embeddingUpNat) :=
  CochainComplex.KFlatBifunctor.KFlat.of_iso (sheafTensor.{u, u, u, u, u} X.sheaf)
    (Stacks.RingedSpace.kFlat_shiftedUnitComplex X (n : ℤ))
    (extendSingleIsoNat (unitModule X) n).symm

/-- **The derived tensor product with the structure sheaf placed in degree `n`**, computed by the
total tensor complex: `G[0] ⊗^𝐋 𝒪[-n] ⟶ Tot(G[0] ⊗ 𝒪[-n]) ≅ (G ⊗ 𝒪)[-n]`. -/
def unitTensorComparison (G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) (n : ℕ) :
    ((derivedTensorProductFunctor (baseRingedSpace X.sheaf).sheaf).obj
        (moduleDerived (A := X.sheaf) (singleNat G 0))).obj
        (moduleDerived (A := X.sheaf) (singleNat (unitModule X) n)) ⟶
      moduleDerived (A := X.sheaf)
        (singleNat (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj (unitModule X)) n) :=
  (canonicalDerivedTensorProduct (baseRingedSpace X.sheaf).sheaf).toTensor
      ((singleNat G 0).extend ComplexShape.embeddingUpNat)
      ((singleNat (unitModule X) n).extend ComplexShape.embeddingUpNat) ≫
    DerivedCategory.Q.map (multiplicationInt (singleTensorMult
      (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj (unitModule X))) 0 n n (zero_add n)))

/-- The comparison `unitTensorComparison G n` is an isomorphism. -/
instance isIso_unitTensorComparison (G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) (n : ℕ) :
    IsIso (unitTensorComparison G n) := by
  have : IsIso ((canonicalDerivedTensorProduct (baseRingedSpace X.sheaf).sheaf).toTensor
      ((singleNat G 0).extend ComplexShape.embeddingUpNat)
      ((singleNat (unitModule X) n).extend ComplexShape.embeddingUpNat)) :=
    isIso_toTensor_of_kFlat_right _ _ _ (kFlat_unitExtend (X := X) n)
  have h₂ : IsIso (DerivedCategory.Q.map (multiplicationInt (singleTensorMult
      (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj (unitModule X))) 0 n n
        (zero_add n)))) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _
      (isIso_multiplicationInt_singleTensorMult_id G (unitModule X) n)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ this h₂

/-- `unitTensorComparison` as an isomorphism. -/
def unitTensorComparisonIso (G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) (n : ℕ) :=
  asIso (unitTensorComparison G n)

/-- The map on the cohomology of derived global sections induced by a morphism. -/
abbrev derivedSectionsHomologyMap (m : ℤ)
    {K K' : DerivedCategory (_root_.SheafOfModules.{u}
      (structureSheafRing (baseRingedSpace X.sheaf)))} (f : K ⟶ K') :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace X.sheaf))) m).map
    ((baseSections (baseRingedSpace X.sheaf)).map f)

/-- `derivedSectionsHomologyMap` of a composite `f ≫ g` is the composite of the maps of `f` and
`g`, evaluated at an element. -/
theorem derivedSectionsHomologyMap_comp_apply (m : ℤ)
    {K K' K'' : DerivedCategory (_root_.SheafOfModules.{u}
      (structureSheafRing (baseRingedSpace X.sheaf)))} (f : K ⟶ K') (g : K' ⟶ K'')
    (z : (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (baseRingedSpace X.sheaf))) m).obj
        ((baseSections (baseRingedSpace X.sheaf)).obj K)) :
    (derivedSectionsHomologyMap m (f ≫ g)).hom z =
      (derivedSectionsHomologyMap m g).hom ((derivedSectionsHomologyMap m f).hom z) := by
  simp only [derivedSectionsHomologyMap, Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply]

/-- For an isomorphism `f`, the map induced by `inv f` undoes the map induced by `f`. -/
theorem derivedSectionsHomologyMap_inv_apply (m : ℤ)
    {K K' : DerivedCategory (_root_.SheafOfModules.{u}
      (structureSheafRing (baseRingedSpace X.sheaf)))} (f : K ⟶ K') [IsIso f]
    (z : (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (baseRingedSpace X.sheaf))) m).obj
        ((baseSections (baseRingedSpace X.sheaf)).obj K)) :
    (derivedSectionsHomologyMap m (inv f)).hom ((derivedSectionsHomologyMap m f).hom z) = z := by
  rw [← derivedSectionsHomologyMap_comp_apply, IsIso.hom_inv_id]
  simp [derivedSectionsHomologyMap]

/-- A map of modules commutes with the action of a unit of `ℤ`. -/
theorem moduleCat_hom_units_smul {R : Type u} [Ring R] {P Q : ModuleCat.{u} R} (f : P ⟶ Q)
    (s : ℤˣ) (p : P) : f.hom (s • p) = s • f.hom p := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/-- The multiplication of `G` and `L` along the identity, after the derived-to-ordinary
comparison. -/
abbrev identityTensorComparison (G L : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) :=
  (canonicalDerivedTensorProduct (baseRingedSpace X.sheaf).sheaf).toTensor
      ((singleNat G 0).extend ComplexShape.embeddingUpNat)
      ((singleNat L 0).extend ComplexShape.embeddingUpNat) ≫
    DerivedCategory.Q.map (multiplicationInt (singleTensorMult
      (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj L)) 0 0 0 rfl))

/-- The right multiplication `G ⟶ G ⊗ 𝒪` by the global section `1`. -/
abbrev rightMulUnit (G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) :
    G ⟶ ((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj (unitModule X) :=
  rightMulTensor (X := X)
    (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj (unitModule X))) unitSection

/-- The first factor `G[-n] ⟶ G[0] ⊗^𝐋 𝒪[-n]` of the morphism representing the cup product with
a class of degree `n`. -/
def cupEdgeLeft (G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) (n : ℕ) :
    (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X))
        (n : ℤ)).obj G ⟶
      ((derivedTensorProductFunctor (baseRingedSpace X.sheaf).sheaf).obj
        (moduleDerived (A := X.sheaf) (singleNat G 0))).obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X))
          (n : ℤ)).obj (unitModule X)) :=
  (moduleDerivedSingleIso (X := X) G n).inv ≫
    moduleDerivedMap ((DerivedCategory.singleFunctor _ (n : ℤ)).map (rightMulUnit G)) ≫
    (unitTensorComparisonIso G n).inv ≫
    ((derivedTensorProductFunctor (baseRingedSpace X.sheaf).sheaf).obj
      (moduleDerived (A := X.sheaf) (singleNat G 0))).map
        (moduleDerivedSingleIso (X := X) (unitModule X) n).hom

/-- The last factor `G[0] ⊗^𝐋 L[0] ⟶ (G ⊗ L)[0]` of the morphism representing the cup product
with a class. -/
def cupEdgeRight (G L : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) :
    ((derivedTensorProductFunctor (baseRingedSpace X.sheaf).sheaf).obj
        (moduleDerived (A := X.sheaf) (singleNat G 0))).obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X))
          ((0 : ℕ) : ℤ)).obj L) ⟶
      (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X))
        ((0 : ℕ) : ℤ)).obj (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj L) :=
    ((derivedTensorProductFunctor (baseRingedSpace X.sheaf).sheaf).obj
      (moduleDerived (A := X.sheaf) (singleNat G 0))).map
        (moduleDerivedSingleIso (X := X) L 0).inv ≫
    identityTensorComparison G L ≫
    (moduleDerivedSingleIso (X := X) (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj L) 0).hom

/-- Cancelling the two outer isomorphisms of a conjugated composite and collecting the middle
factors under a functor, at variables. -/
lemma edge_chase {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {P Q R T T' : D} {a b c d : C} (i : P ≅ Q) (x : P ⟶ R) (y : R ⟶ F.obj a) (u : a ⟶ b)
    (e : b ⟶ c) (v : c ⟶ d) (w : F.obj d ⟶ T) (j : T ≅ T') :
    i.hom ≫ ((i.inv ≫ x ≫ y ≫ F.map u) ≫ F.map e ≫ F.map v ≫ w ≫ j.hom) ≫ j.inv =
      x ≫ y ≫ F.map (u ≫ e ≫ v) ≫ w := by
  simp

/-- A functor into modules applied to a fourfold composite, on an element, at variables. -/
lemma functor_map_comp_four_apply {D : Type*} [Category* D] {R : Type u} [Ring R]
    (Φ : D ⥤ ModuleCat.{u} R) {a b c d e : D} (f₁ : a ⟶ b) (f₂ : b ⟶ c) (f₃ : c ⟶ d)
    (f₄ : d ⟶ e) (y : Φ.obj a) :
    (Φ.map (f₁ ≫ f₂ ≫ f₃ ≫ f₄)).hom y =
      (Φ.map f₄).hom ((Φ.map f₃).hom ((Φ.map f₂).hom ((Φ.map f₁).hom y))) := by
  simp

/-- **The morphism representing the cup product, read on the extended single complexes.** -/
theorem moduleDerivedMap_cupEdge (G L : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) (n : ℕ)
    (eL : (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X))
        (n : ℤ)).obj (unitModule X) ⟶
      (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X))
        ((0 : ℕ) : ℤ)).obj L) :
    moduleDerivedMap (cupEdgeLeft G n ≫
        ((derivedTensorProductFunctor (baseRingedSpace X.sheaf).sheaf).obj
          (moduleDerived (A := X.sheaf) (singleNat G 0))).map eL ≫ cupEdgeRight G L) =
      moduleDerivedMap ((DerivedCategory.singleFunctor _ (n : ℤ)).map (rightMulUnit G)) ≫
        (unitTensorComparisonIso G n).inv ≫
        ((derivedTensorProductFunctor (baseRingedSpace X.sheaf).sheaf).obj
          (moduleDerived (A := X.sheaf) (singleNat G 0))).map (moduleDerivedMap eL) ≫
        identityTensorComparison G L :=
  edge_chase _ _ _ _ _ _ _ _ _

/-- **The cup product with the class of a morphism `𝒪[-n] ⟶ L[0]` is the action of a morphism
`G[-n] ⟶ (G ⊗ L)[0]` factoring through `G[0] ⊗^𝐋 e`**, up to a sign: there are `α` and `β`, not
depending on `e`, such that for every `e : 𝒪_X[-n] ⟶ L[0]` and `ε ∈ Hⁿ(X, G)`,
`ε ∪ Hⁿ(e)(1) = s · H^{2n}(α ≫ (G[0] ⊗^𝐋 e) ≫ β)(ε)`. -/
theorem exists_cup_eq_cohomologyMapOfSingleHom (G L : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) (n : ℕ) :
    ∃ (s : ℤˣ)
      (α : (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X))
          (n : ℤ)).obj G ⟶
        ((derivedTensorProductFunctor (baseRingedSpace X.sheaf).sheaf).obj
          (moduleDerived (A := X.sheaf) (singleNat G 0))).obj
          ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X))
            (n : ℤ)).obj (unitModule X)))
      (β : ((derivedTensorProductFunctor (baseRingedSpace X.sheaf).sheaf).obj
          (moduleDerived (A := X.sheaf) (singleNat G 0))).obj
          ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X))
            ((0 : ℕ) : ℤ)).obj L) ⟶
        (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X))
          ((0 : ℕ) : ℤ)).obj (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj L)),
      ∀ (eL : (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X))
            (n : ℤ)).obj (unitModule X) ⟶
          (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X))
            ((0 : ℕ) : ℤ)).obj L)
        (ε : Hgroup (structureSheafRing X) ⊤ n G),
        (canonicalPairingModule (A := X.sheaf)
          (singleTensorMult (X := X) (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj L))
            0 0 0 rfl) (n : ℤ) (n : ℤ)).hom
          ((hgroupModuleShiftIso (X := X) G 0 n n (by simp)).hom ε ⊗ₜ
            (hgroupModuleShiftIso (X := X) L 0 (0 + n) n (by simp)).hom
              (cohomologyMapOfSingleHom X (unitModule X) L n 0 eL (sectionClass unitSection))) =
        s • (hgroupModuleShiftIso (X := X) (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj L) 0
            (n + n) ((n : ℤ) + (n : ℤ)) (by push_cast; ring)).hom
          (cohomologyMapOfSingleHom X G _ n n
            (α ≫ ((derivedTensorProductFunctor (baseRingedSpace X.sheaf).sheaf).obj
              (moduleDerived (A := X.sheaf) (singleNat G 0))).map eL ≫ β) ε) := by
  refine ⟨((n : ℤ) * (n : ℤ)).negOnePow, cupEdgeLeft G n, cupEdgeRight G L,
    fun eL ε => ?_⟩
  rw [hgroupModuleShiftIso_cohomologyMapOfSingleHom (X := X) (unitModule X) L n 0 (n : ℤ)
    (by simp) (by simp) eL (sectionClass unitSection)]
  refine Eq.trans ?_ (congrArg _ (hgroupModuleShiftIso_cohomologyMapOfSingleHom (X := X) G
    (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj L) n n ((n : ℤ) + (n : ℤ)) rfl
    (by push_cast; ring) _ ε).symm)
  -- the cup product with the class of `1` placed in degree `n`
  have hS := canonicalPairingModule_sectionClass (X := X)
    (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj (unitModule X))) unitSection n n ε
  rw [hgroupModuleShiftIso_naturality (X := X) (rightMulUnit G) n n ((n : ℤ) + (n : ℤ)) rfl ε] at hS
  have hS' := congrArg (derivedSectionsHomologyMap ((n : ℤ) + (n : ℤ))
    (unitTensorComparisonIso G n).inv).hom hS
  replace hS' := hS'.trans (moduleCat_hom_units_smul _ _ _)
  have hT := @derivedSectionsHomologyMap_inv_apply X ((n : ℤ) + (n : ℤ)) _ _
    (unitTensorComparison G n) (isIso_unitTensorComparison G n)
  rw [show (canonicalPairingModule (A := X.sheaf) (singleTensorMult (X := X)
      (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj G).obj (unitModule X))) 0 n n (zero_add n))
      (n : ℤ) (n : ℤ)) = _ from rfl] at hS'
  have hP := (hT ((Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing
    (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (baseRingedSpace X.sheaf))
    (moduleDerived (A := X.sheaf) (singleNat G 0))
    (moduleDerived (A := X.sheaf) (singleNat (unitModule X) n)) (n : ℤ) (n : ℤ)).hom
      ((hgroupModuleShiftIso (X := X) G 0 n n (by simp)).hom ε ⊗ₜ
        (hgroupModuleShiftIso (X := X) (unitModule X) n 0 (n : ℤ) (by simp)).hom
          (sectionClass unitSection)))).symm.trans hS'
  refine (congrArg (derivedSectionsHomologyMap ((n : ℤ) + (n : ℤ))
    (identityTensorComparison G L)).hom (cupPairing_naturality_right_apply
      (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (baseRingedSpace X.sheaf))
      (moduleDerivedMap eL) (n : ℤ) (n : ℤ) _ _)).trans ?_
  refine Eq.trans (congrArg (ModuleCat.Hom.hom _) (congrArg (ModuleCat.Hom.hom _) hP)) ?_
  refine (congrArg (ModuleCat.Hom.hom _) (moduleCat_hom_units_smul _ _ _)).trans ?_
  refine (moduleCat_hom_units_smul _ _ _).trans ?_
  refine congrArg (((n : ℤ) * (n : ℤ)).negOnePow • ·) ?_
  have h := congrArg (baseSections (baseRingedSpace X.sheaf) ⋙ DerivedCategory.homologyFunctor
    (ModuleCat.{u} (baseRing (baseRingedSpace X.sheaf))) ((n : ℤ) + (n : ℤ))).map
      ((moduleDerivedMap_cupEdge G L n eL).trans (congrArg (fun t =>
        moduleDerivedMap ((DerivedCategory.singleFunctor _ (n : ℤ)).map (rightMulUnit G)) ≫
          (unitTensorComparisonIso G n).inv ≫ t ≫ identityTensorComparison G L)
        (Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left
          (derivedTensorProductFunctor (baseRingedSpace X.sheaf).sheaf)
          (moduleDerived (A := X.sheaf) (singleNat G 0)) (moduleDerivedMap eL)).symm))
  exact (functor_map_comp_four_apply (baseSections (baseRingedSpace X.sheaf) ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace X.sheaf)))
      ((n : ℤ) + (n : ℤ))) _ _ _ _ _).symm.trans
    (ConcreteCategory.congr_hom h ((hgroupModuleShiftIso (X := X) G n n
      ((n : ℤ) + (n : ℤ)) rfl).hom ε)).symm

end Stacks.WeilDeRham

end
