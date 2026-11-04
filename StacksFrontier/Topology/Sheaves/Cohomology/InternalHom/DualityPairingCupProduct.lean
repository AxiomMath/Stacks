module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DualityPairingSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductOfCohomologyClasses
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LeftAdjointOfDerivedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints
import StacksCore.Tactic.StacksAttribute

/-!
# The cup product on degree-zero cohomology and the duality pairing square

Let `(X, O_X)` be a ringed space and `A = Γ(X, O_X)`. The cup product of Section 0FKU is the
relative cup product of Stacks 0B68 for the structure morphism `π : (X, O_X) ⟶ (pt, A)`. On
degree-zero cohomology, a class of `H⁰(X, Z)` is a morphism `O_pt ⟶ Rπ_*Z` in `D(pt)` (the
identification `H⁰(X, Z) = Hom_{D(O_X)}(O_X, Z)` of Stacks 08JA, the unit comparison
`Lπ^*O_pt ≅ O_X` and the adjunction `Lπ^* ⊣ Rπ_*`), and the cup product of two classes `a`, `b`
is

`O_pt = O_pt ⊗^L O_pt ⟶ Rπ_*K ⊗^L Rπ_*M ⟶ Rπ_*(K ⊗^L M)`.

This file proves that, read back as morphisms out of `O_X`, the cup product of the classes of
`ξ̃ : O_X ⟶ K` and `η̃ : O_X ⟶ M` is `ξ̃ ⊗ η̃` preceded by `O_X = O_X ⊗^L O_X` (Stacks 0FP2 in
degree zero), and deduces the square of Stacks 0FVB with the cup product as its top arrow.

The proof is Stacks 0FP2 (`homEquiv_symm_comp_relativeCupProduct`), the compatibility of the
comparison of Stacks 079U with the right unit constraints (`rightUnitorCoherence_unitObject`),
and the comparison of the derived tensor product of Stacks 06YU, over which the relative cup
product is stated, with the derived tensor product of the monoidal structure of Stacks 0FPT on
`D(O_X)`: both are re-seatings of one monoidal structure, so their unit constraints correspond.

## Main results

* `Stacks.SheafOfModules.globalCupProductZero`: the cup product on degree-zero cohomology.
* `Stacks.SheafOfModules.derivedStructureSheafGlobalSectionsEquiv_globalCupProductZero`: the cup
  product of two classes names the tensor product of the morphisms they name.
* `Stacks.SheafOfModules.derivedDualPairingSquare_cup`: Stacks 0FVB.

## References

* [Stacks Project, Tag 0FVB](https://stacks.math.columbia.edu/tag/0FVB)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FP2](https://stacks.math.columbia.edu/tag/0FP2)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.ModuleSections
open scoped CategoryTheory.Prod

universe u

namespace CategoryTheory.MonoidalCategory

/-- **Two re-seatings of one monoidal structure with the same unit**: the left unitor of the
first is the comparison of the two tensor products followed by the left unitor of the
second. -/
lemma reseat_leftUnitor_hom_eq_comp {C : Type*} [Category C] [MonoidalCategory C]
    {T₁ T₂ : C ⥤ C ⥤ C} {U : C} (e₁ : curriedTensor C ≅ T₁) (e₂ : curriedTensor C ≅ T₂)
    (ε : 𝟙_ C ≅ U) (X : C) :
    (@MonoidalCategoryStruct.leftUnitor C _ (reseat e₁ ε).toMonoidalCategoryStruct X).hom =
      ((e₁.symm ≪≫ e₂).hom.app U).app X ≫
        (@MonoidalCategoryStruct.leftUnitor C _ (reseat e₂ ε).toMonoidalCategoryStruct X).hom := by
  rw [reseat_leftUnitor, reseat_leftUnitor]
  simp [reseatIso]

end CategoryTheory.MonoidalCategory

namespace Stacks.Cohomology.DerivedProjectionFormula

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  StacksDraft.KFlat.modulePullback CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Cancelling the right unit constraint at the unit, over an arbitrary category: if
`c ≫ p ≫ r = Lρ` and `q ≫ r' = r ≫ ν`, then `Lρ⁻¹ ≫ c ≫ p ≫ q = ν ≫ r'⁻¹`. -/
private lemma unit_cancel {D : Type*} [Category D] {A B P Q W O : D}
    (lρ : A ≅ B) (c : A ⟶ P) (p : P ⟶ Q) (q : Q ⟶ W) (r : Q ⟶ B) (r' : W ≅ O) (ν : B ⟶ O)
    (h : c ≫ p ≫ r = lρ.hom) (hn : q ≫ r'.hom = r ≫ ν) :
    lρ.inv ≫ c ≫ p ≫ q = ν ≫ r'.inv := by
  rw [Iso.eq_comp_inv, Category.assoc, Category.assoc, Category.assoc, hn, ← Category.assoc p,
    ← Category.assoc c, h, Iso.inv_hom_id_assoc]

/-- **The comparison of Stacks 079U at the unit, against the right unit constraints.** -/
theorem map_rightUnitor_inv_comp_pullbackTensorComparison_unit :
    (derivedPullback f).map
        ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app (singleUnit Y)).inv ≫
      (pullbackTensorComparison f).app (singleUnit Y, singleUnit Y) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          ((derivedPullbackUnitIso f).hom ×ₘ (derivedPullbackUnitIso f).hom) =
      (derivedPullbackUnitIso f).hom ≫
        ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app (singleUnit X)).inv := by
  have h := rightUnitorCoherence_unitObject f (singleUnit Y)
  have hsplit : (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
        ((derivedPullbackUnitIso f).hom ×ₘ (derivedPullbackUnitIso f).hom) =
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          (𝟙 ((derivedPullback f).obj (singleUnit Y)) ×ₘ (derivedPullbackUnitIso f).hom) ≫
        ((derivedTensorProductFunctor X.sheaf).map (derivedPullbackUnitIso f).hom).app
          (singleUnit X) := by
    rw [uncurry_map_id_left]
    exact (((derivedTensorProductFunctor X.sheaf).map
      (derivedPullbackUnitIso f).hom).naturality (derivedPullbackUnitIso f).hom).symm
  have hn := (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).hom.naturality
    (derivedPullbackUnitIso f).hom
  rw [hsplit]
  exact unit_cancel ((derivedPullback f).mapIso
      ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app (singleUnit Y))) _ _ _ _
    ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app (singleUnit X)) _ h hn

/-- A pasting over an arbitrary category: the cup product of two classes out of the unit,
transported back along `ν`, is the right unit constraint followed by the tensor product of the
two morphisms. -/
private lemma unit_paste {D : Type*} [Category D] (F : D ⥤ D ⥤ D) {LO LO' LOO O K M : D}
    (ν : LO ≅ O) (lχ : LO ⟶ LOO) (c : LOO ⟶ (F.obj LO).obj LO')
    (s : LO ⟶ (F.obj K).obj M) (x : O ⟶ K) (y : O ⟶ M) (a : LO ⟶ K) (b : LO' ⟶ M)
    (ν' : LO' ⟶ O) (ri : O ⟶ (F.obj O).obj O)
    (h₁ : s = lχ ≫ c ≫ (F.map a).app LO' ≫ (F.obj K).map b) (ha : a = ν.hom ≫ x)
    (hb : b = ν' ≫ y)
    (h₃ : lχ ≫ c ≫ (F.map ν.hom).app LO' ≫ (F.obj O).map ν' = ν.hom ≫ ri) :
    ν.inv ≫ s = ri ≫ (F.map x).app O ≫ (F.obj K).map y := by
  subst h₁ ha hb
  have e : (F.map (ν.hom ≫ x)).app LO' ≫ (F.obj K).map (ν' ≫ y) =
      ((F.map ν.hom).app LO' ≫ (F.obj O).map ν') ≫ (F.map x).app O ≫ (F.obj K).map y := by
    simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc,
      NatTrans.naturality_assoc]
  rw [e, ← Category.assoc c, ← Category.assoc lχ, h₃, Category.assoc, Iso.inv_hom_id_assoc]

end Stacks.Cohomology.DerivedProjectionFormula

namespace Stacks.Cohomology.DerivedRelativeCupProduct

open Stacks.Cohomology.DerivedProjectionFormula

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  StacksDraft.KFlat.modulePullback CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The class on `Y` of a morphism out of the structure sheaf of `X`: a morphism
`x : 𝒪_X[0] ⟶ K` read as `𝒪_Y[0] ⟶ Rf_*K` through `ν : Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` and the
adjunction `Lf^* ⊣ Rf_*`. -/
def unitClass {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (x : singleUnit X ⟶ K) : singleUnit Y ⟶ (derivedPushforward f).obj K :=
  (derivedAdjunction f).homEquiv _ _ ((derivedPullbackUnitIso f).hom ≫ x)

/-- **The relative cup product of two classes out of the unit.** For `x : 𝒪_X[0] ⟶ K` and
`y : 𝒪_X[0] ⟶ M`, the cup product of their classes on `Y` by the relative cup product of
Stacks 0B68, with `𝒪_Y[0] = 𝒪_Y[0] ⊗^𝐋 𝒪_Y[0]` the right unit constraint, transposes back to
the right unit constraint of `𝒪_X[0]` followed by `x ⊗ y`. -/
theorem homEquiv_symm_unitClass_relativeCupProduct
    {K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (x : singleUnit X ⟶ K) (y : singleUnit X ⟶ M) :
    (derivedPullbackUnitIso f).inv ≫ ((derivedAdjunction f).homEquiv _ _).symm
        (((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app (singleUnit Y)).inv ≫
          ((derivedTensorProductFunctor Y.sheaf).map (unitClass f x)).app (singleUnit Y) ≫
            ((derivedTensorProductFunctor Y.sheaf).obj
              ((derivedPushforward f).obj K)).map (unitClass f y) ≫
              relativeCupProduct f K M) =
      ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app (singleUnit X)).inv ≫
        ((derivedTensorProductFunctor X.sheaf).map x).app (singleUnit X) ≫
          ((derivedTensorProductFunctor X.sheaf).obj K).map y := by
  have h₁ := homEquiv_symm_comp_relativeCupProduct f
    ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app (singleUnit Y)).inv
    (unitClass f x) (unitClass f y)
  exact unit_paste (derivedTensorProductFunctor X.sheaf) (derivedPullbackUnitIso f) _ _ _ x y
    _ _ (derivedPullbackUnitIso f).hom _ h₁ (Equiv.symm_apply_apply _ _)
    (Equiv.symm_apply_apply _ _) (map_rightUnitor_inv_comp_pullbackTensorComparison_unit f)

end Stacks.Cohomology.DerivedRelativeCupProduct

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

section RingedSpace

variable (X : RingedSpace.{u, u})

open Stacks.Cohomology.DerivedSectionsLeftAdjoint (basePoint toBasePoint)

/-- **The two derived tensor products of a ringed space agree**: the derived tensor product
`Stacks.SheafOfModules.derivedTensor` of the monoidal structure of Stacks 0FPT and the derived
tensor product of Stacks 06YU over which the relative cup product of Stacks 0B68 is stated, both
being the tensor product of `D(O_X)` re-seated along a comparison with the localized tensor
product of complexes. -/
def derivedTensorCanonicalIso :
    derivedTensor X.sheaf ≅ Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf :=
  (derivedTensorMonoidalIso X.sheaf).symm ≪≫ DerivedMonoidal.monoidalTensorCanonicalIso X.sheaf

/-- The left unitor of the monoidal structure of Stacks 0FPT is the comparison of the two
derived tensor products followed by the left unitor of the re-seating at Stacks 06YU. -/
theorem derivedLeftUnitor_hom_eq (Z : DerivedCategory (StructureSheafModules X.sheaf)) :
    letI := derivedMonoidalStructure X.sheaf
    (λ_ Z).hom = (((derivedTensorCanonicalIso X).hom.app (𝟙_ _)).app Z) ≫
      (@MonoidalCategoryStruct.leftUnitor _ _
        (DerivedMonoidal.canonicalDerivedMonoidal X.sheaf).toMonoidalCategoryStruct Z).hom :=
  @reseat_leftUnitor_hom_eq_comp _ _ (DerivedMonoidal.derivedMonoidal X.sheaf) _ _ _
    (derivedTensorMonoidalIso X.sheaf) (DerivedMonoidal.monoidalTensorCanonicalIso X.sheaf)
    (DerivedMonoidal.canonicalUnitIso X.sheaf) Z

/-- **At the unit, the left unitor of the re-seating at Stacks 06YU is the right unit
constraint of Stacks 06YU.** -/
theorem canonicalLeftUnitor_unit_eq :
    (@MonoidalCategoryStruct.leftUnitor _ _
        (DerivedMonoidal.canonicalDerivedMonoidal X.sheaf).toMonoidalCategoryStruct
        (Stacks.Cohomology.DerivedProjectionFormula.singleUnit X)).hom =
      (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).hom.app
        (Stacks.Cohomology.DerivedProjectionFormula.singleUnit X) := by
  have h₁ := @unitors_equal _ _ (DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
  have h₂ := DerivedMonoidal.canonicalComparison_rightUnitor X.sheaf
    _ (DerivedMonoidal.kFlat_tensorUnit_complexes X.sheaf)
  have h₃ := Stacks.Cohomology.DerivedProjectionFormula.derivedTensorRightUnitorNatIso_hom_app_q
    X (Stacks.DerivedTensor.RingedSite.unitComplex (Stacks.RingedSpace.toRingedSite X))
  have h₄ := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).comparisonRight_eq_comparison
    (Stacks.DerivedTensor.RingedSite.unitComplex (Stacks.RingedSpace.toRingedSite X))
    (Stacks.DerivedTensor.RingedSite.unitComplex (Stacks.RingedSpace.toRingedSite X))
    (Stacks.SheafOfModules.isKFlat_single_unit (Stacks.RingedSpace.toRingedSite X).O)
    (Stacks.SheafOfModules.isKFlat_single_unit (Stacks.RingedSpace.toRingedSite X).O)
  rw [h₄] at h₃
  refine h₁.trans (h₂.trans (Eq.trans ?_ h₃.symm))
  rfl

/-- The left unitor of the unit of the monoidal structure of Stacks 0FPT is the comparison of
the two derived tensor products followed by the right unit constraint of Stacks 06YU. -/
theorem derivedLeftUnitor_unit_hom_eq :
    letI := derivedMonoidalStructure X.sheaf
    (λ_ (𝟙_ (DerivedCategory (StructureSheafModules X.sheaf)))).hom =
      (((derivedTensorCanonicalIso X).hom.app (𝟙_ _)).app (𝟙_ _)) ≫
        (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).hom.app
          (Stacks.Cohomology.DerivedProjectionFormula.singleUnit X) :=
  (derivedLeftUnitor_hom_eq X _).trans
    (congrArg (fun g ↦ (((derivedTensorCanonicalIso X).hom.app _).app _) ≫ g)
      (canonicalLeftUnitor_unit_eq X))

/-- Moving a tensor product of two morphisms out of the unit across an isomorphism of
bifunctors and a pair of unit constraints related by it, over an arbitrary category. -/
private lemma tensor_unit_transport {D : Type*} [Category D] {T₁ T₂ : D ⥤ D ⥤ D}
    (τ : T₁ ≅ T₂) {O K M : D} (x : O ⟶ K) (y : O ⟶ M) (l : (T₁.obj O).obj O ≅ O)
    (r : (T₂.obj O).obj O ≅ O) (h : l.hom = (τ.hom.app O).app O ≫ r.hom) :
    r.inv ≫ (T₂.map x).app O ≫ (T₂.obj K).map y ≫ (τ.inv.app K).app M =
      l.inv ≫ (T₁.map x).app O ≫ (T₁.obj K).map y := by
  have hl : l.inv = r.inv ≫ (τ.inv.app O).app O := by
    rw [← cancel_mono l.hom, Iso.inv_hom_id, h, Category.assoc, ← Category.assoc _ _ r.hom,
      ← NatTrans.comp_app, Iso.inv_hom_id_app, NatTrans.id_app, Category.id_comp,
      Iso.inv_hom_id]
  have h₁ := congrArg (fun φ ↦ φ.app O) (τ.inv.naturality x)
  have h₂ := (τ.inv.app K).naturality y
  simp only [NatTrans.comp_app] at h₁
  rw [hl, Category.assoc, ← reassoc_of% h₁, h₂]

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  StacksDraft.KFlat.modulePullback CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

/-- **A degree-zero class as a class on the point.** For `Z ∈ D(O_X)` the identification of
`H⁰(X, Z)` with `Hom_{D(O_X)}(O_X, Z)` (Stacks 08JA), the unit comparison
`Lπ^*(O_pt) ≅ O_X` and the adjunction `Lπ^* ⊣ Rπ_*` for the structure morphism
`π : (X, O_X) ⟶ (pt, Γ(X, O_X))` identify `H⁰(X, Z)` with `Hom_{D(pt)}(O_pt, Rπ_* Z)`. -/
def globalClassToPoint (Z : DerivedCategory (StructureSheafModules X.sheaf)) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj Z) : Type u) ≃
      (Stacks.Cohomology.DerivedProjectionFormula.singleUnit (basePoint X) ⟶
        (derivedPushforward (toBasePoint X)).obj Z) where
  toFun ξ := Stacks.Cohomology.DerivedRelativeCupProduct.unitClass (toBasePoint X)
    (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) Z ξ)
  invFun c := (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) Z).symm
    ((Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso (toBasePoint X)).inv ≫
      ((derivedAdjunction (toBasePoint X)).homEquiv _ _).symm c)
  left_inv ξ := by
    simp only [Stacks.Cohomology.DerivedRelativeCupProduct.unitClass, Equiv.symm_apply_apply]
    exact (congrArg _ (Iso.inv_hom_id_assoc _ _)).trans (AddEquiv.symm_apply_apply _ _)
  right_inv c := by
    simp only [Stacks.Cohomology.DerivedRelativeCupProduct.unitClass, AddEquiv.apply_symm_apply]
    exact (congrArg _ (Iso.hom_inv_id_assoc _ _)).trans (Equiv.apply_symm_apply _ _)

/-- The class on the point of a degree-zero class is
`Stacks.Cohomology.DerivedRelativeCupProduct.unitClass` of the morphism it names. -/
theorem globalClassToPoint_apply (Z : DerivedCategory (StructureSheafModules X.sheaf))
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj Z) : Type u)) :
    globalClassToPoint X Z ξ =
      Stacks.Cohomology.DerivedRelativeCupProduct.unitClass (toBasePoint X)
        (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) Z ξ) :=
  rfl

/-- The morphism out of the structure sheaf named by the degree-zero class of a class on the
point is the inverse of the unit comparison followed by the adjoint transpose. -/
theorem derivedStructureSheafGlobalSectionsEquiv_globalClassToPoint_symm
    (Z : DerivedCategory (StructureSheafModules X.sheaf))
    (c : Stacks.Cohomology.DerivedProjectionFormula.singleUnit (basePoint X) ⟶
      (derivedPushforward (toBasePoint X)).obj Z) :
    RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) Z
        ((globalClassToPoint X Z).symm c) =
      (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso (toBasePoint X)).inv ≫
        ((derivedAdjunction (toBasePoint X)).homEquiv _ _).symm c := by
  have h : (globalClassToPoint X Z).symm c =
      (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) Z).symm
        ((Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso (toBasePoint X)).inv ≫
          ((derivedAdjunction (toBasePoint X)).homEquiv _ _).symm c) := rfl
  exact (congrArg _ h).trans (AddEquiv.apply_symm_apply _ _)

/-- The relative cup product of Stacks 0B68 for the structure morphism
`π : (X, O_X) ⟶ (pt, Γ(X, O_X))` on two classes `O_pt ⟶ Rπ_*K` and `O_pt ⟶ Rπ_*M`, after the
identification `O_pt = O_pt ⊗^L O_pt`, read in the derived tensor product of Stacks 0FPT. -/
def pointCupProduct (K M : DerivedCategory (StructureSheafModules X.sheaf))
    (a : Stacks.Cohomology.DerivedProjectionFormula.singleUnit (basePoint X) ⟶
      (derivedPushforward (toBasePoint X)).obj K)
    (b : Stacks.Cohomology.DerivedProjectionFormula.singleUnit (basePoint X) ⟶
      (derivedPushforward (toBasePoint X)).obj M) :
    Stacks.Cohomology.DerivedProjectionFormula.singleUnit (basePoint X) ⟶
      (derivedPushforward (toBasePoint X)).obj (((derivedTensor X.sheaf).obj K).obj M) :=
  (((Stacks.RingedSpace.derivedTensorRightUnitorNatIso (basePoint X)).app
      (Stacks.Cohomology.DerivedProjectionFormula.singleUnit (basePoint X))).inv ≫
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (basePoint X).sheaf).map a).app
      (Stacks.Cohomology.DerivedProjectionFormula.singleUnit (basePoint X)) ≫
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (basePoint X).sheaf).obj
        ((derivedPushforward (toBasePoint X)).obj K)).map b ≫
    Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct (toBasePoint X) K M) ≫
    (derivedPushforward (toBasePoint X)).map (((derivedTensorCanonicalIso X).inv.app K).app M)

/-- **The cup product on degree-zero cohomology** (Section 0FKU)

`∪ : H⁰(X, K) × H⁰(X, M) ⟶ H⁰(X, K ⊗^L_{O_X} M)`.

It is the relative cup product of Stacks 0B68 for the structure morphism
`π : (X, O_X) ⟶ (pt, Γ(X, O_X))`, applied to the classes of `ξ` and `η` in
`Hom_{D(pt)}(O_pt, Rπ_*(-))` after the identification `O_pt = O_pt ⊗^L O_pt`, and read in the
derived tensor product of Stacks 0FPT. -/
def globalCupProductZero (K M : DerivedCategory (StructureSheafModules X.sheaf))
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj K) : Type u))
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj M) : Type u)) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
        (((derivedTensor X.sheaf).obj K).obj M)) : Type u) :=
  (globalClassToPoint X (((derivedTensor X.sheaf).obj K).obj M)).symm
    (pointCupProduct X K M
      (Stacks.Cohomology.DerivedRelativeCupProduct.unitClass (toBasePoint X)
        (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) K ξ))
      (Stacks.Cohomology.DerivedRelativeCupProduct.unitClass (toBasePoint X)
        (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) M η)))

/-- The cup product on degree-zero cohomology, unfolded. -/
theorem derivedStructureSheafGlobalSectionsEquiv_globalCupProductZero_eq
    (K M : DerivedCategory (StructureSheafModules X.sheaf))
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj K) : Type u))
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj M) : Type u)) :
    RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf)
        (((derivedTensor X.sheaf).obj K).obj M) (globalCupProductZero X K M ξ η) =
      (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso (toBasePoint X)).inv ≫
        ((derivedAdjunction (toBasePoint X)).homEquiv _ _).symm
          (pointCupProduct X K M
            (Stacks.Cohomology.DerivedRelativeCupProduct.unitClass (toBasePoint X)
              (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) K ξ))
            (Stacks.Cohomology.DerivedRelativeCupProduct.unitClass (toBasePoint X)
              (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) M η))) := by
  unfold globalCupProductZero
  rw [derivedStructureSheafGlobalSectionsEquiv_globalClassToPoint_symm]

/-- **The cup product of two morphisms out of the structure sheaf, in the two derived tensor
products.** `derivedSectionTensor` — the left unitor of Stacks 0FPT followed by `x ⊗ y` — is the
right unit constraint of Stacks 06YU followed by `x ⊗ y` in the derived tensor product of
Stacks 06YU and the comparison of the two derived tensor products. -/
theorem derivedSectionTensor_eq_canonical {A B : DerivedCategory (StructureSheafModules X.sheaf)}
    (x : Stacks.Cohomology.DerivedProjectionFormula.singleUnit X ⟶ A)
    (y : Stacks.Cohomology.DerivedProjectionFormula.singleUnit X ⟶ B) :
    derivedSectionTensor X.sheaf x y =
      ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).inv.app
          (Stacks.Cohomology.DerivedProjectionFormula.singleUnit X) ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map x).app
          (Stacks.Cohomology.DerivedProjectionFormula.singleUnit X) ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj A).map y) ≫
        ((derivedTensorCanonicalIso X).inv.app A).app B := by
  letI := derivedMonoidalStructure X.sheaf
  have h := tensor_unit_transport (derivedTensorCanonicalIso X) x y
    (λ_ (𝟙_ (DerivedCategory (StructureSheafModules X.sheaf))))
    ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app
      (Stacks.Cohomology.DerivedProjectionFormula.singleUnit X))
    (derivedLeftUnitor_unit_hom_eq X)
  rw [Category.assoc, Category.assoc]
  refine Eq.trans ?_ h.symm
  change (λ_ (𝟙_ (DerivedCategory (StructureSheafModules X.sheaf)))).inv ≫ (x ⊗ₘ y) = _
  rw [MonoidalCategory.tensorHom_def]
  rfl

/-- Appending a morphism to both sides of an equation, over an arbitrary category. -/
private lemma comp_comp_eq_of_eq {D : Type*} [Category D] {A B C P Q E : D} (n : A ⟶ B)
    (s : B ⟶ C) (g : C ⟶ E) (a : A ⟶ P) (b : P ⟶ Q) (c : Q ⟶ C) (z : A ⟶ E)
    (h : n ≫ s = a ≫ b ≫ c) (hz : z = a ≫ b ≫ c ≫ g) : n ≫ s ≫ g = z := by
  rw [hz, ← Category.assoc n, h, Category.assoc, Category.assoc]

/-- The adjoint transpose of a morphism followed by the image of `g` under the right adjoint,
over an arbitrary adjunction. -/
private lemma adj_symm_comp_map {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A : C} {B Z Z' : D} (ν : L.obj A ≅ B) (p : A ⟶ R.obj Z) (g : Z ⟶ Z')
    (q : B ⟶ Z) (hp : ν.inv ≫ (adj.homEquiv _ _).symm p = q) :
    ν.inv ≫ (adj.homEquiv _ _).symm (p ≫ R.map g) = q ≫ g := by
  rw [Adjunction.homEquiv_naturality_right_symm, ← Category.assoc, hp]

/-- The point cup product of the classes of two morphisms out of the structure sheaf,
transposed back to `X`, is the right unit constraint followed by their tensor product and the
comparison of the two derived tensor products. -/
theorem unitPointCup (K M : DerivedCategory (StructureSheafModules X.sheaf))
    (x : Stacks.Cohomology.DerivedProjectionFormula.singleUnit X ⟶ K)
    (y : Stacks.Cohomology.DerivedProjectionFormula.singleUnit X ⟶ M) :
    (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso (toBasePoint X)).inv ≫
        ((derivedAdjunction (toBasePoint X)).homEquiv _ _).symm
          (pointCupProduct X K M
            (Stacks.Cohomology.DerivedRelativeCupProduct.unitClass (toBasePoint X) x)
            (Stacks.Cohomology.DerivedRelativeCupProduct.unitClass (toBasePoint X) y)) =
      ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).inv.app
          (Stacks.Cohomology.DerivedProjectionFormula.singleUnit X) ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map x).app
          (Stacks.Cohomology.DerivedProjectionFormula.singleUnit X) ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj K).map y) ≫
        ((derivedTensorCanonicalIso X).inv.app K).app M :=
  adj_symm_comp_map (derivedAdjunction (toBasePoint X))
    (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso (toBasePoint X)) _ _ _
    (Stacks.Cohomology.DerivedRelativeCupProduct.homEquiv_symm_unitClass_relativeCupProduct
      (toBasePoint X) x y)

/-- **The cup product on degree-zero cohomology is the tensor product of the morphisms out of
the structure sheaf** (Stacks 0FP2 in degree zero): for `ξ ∈ H⁰(X, K)` and `η ∈ H⁰(X, M)`, the
morphism `O_X ⟶ K ⊗^L M` that `ξ ∪ η` names under Stacks 08JA is the cup product
`(λ_{O_X})⁻¹ ≫ (ξ̃ ⊗ η̃)` of the morphisms `ξ̃`, `η̃` that `ξ` and `η` name. -/
theorem derivedStructureSheafGlobalSectionsEquiv_globalCupProductZero
    (K M : DerivedCategory (StructureSheafModules X.sheaf))
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj K) : Type u))
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj M) : Type u)) :
    RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf)
        (((derivedTensor X.sheaf).obj K).obj M) (globalCupProductZero X K M ξ η) =
      derivedSectionTensor X.sheaf
        (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) K ξ)
        (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) M η) := by
  have h₂ := unitPointCup X K M
    (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) K ξ)
    (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) M η)
  have h₃ := derivedSectionTensor_eq_canonical X
    (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) K ξ)
    (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) M η)
  rw [derivedStructureSheafGlobalSectionsEquiv_globalCupProductZero_eq]
  exact h₂.trans h₃.symm

/-- The cup product on degree-zero cohomology, as the class of the tensor product of the
morphisms out of the structure sheaf. -/
theorem globalCupProductZero_eq_symm (K M : DerivedCategory (StructureSheafModules X.sheaf))
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj K) : Type u))
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj M) : Type u)) :
    globalCupProductZero X K M ξ η =
      (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf)
          (((derivedTensor X.sheaf).obj K).obj M)).symm
        (derivedSectionTensor X.sheaf
          (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) K ξ)
          (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) M η)) :=
  (AddEquiv.eq_symm_apply _).mpr (derivedStructureSheafGlobalSectionsEquiv_globalCupProductZero X K M ξ η)

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.hasSheafifyOverOpen
  Stacks.Topology.RingedSpaceSheafifyOpens.wEqualsLocallyBijectiveOverOpen

/-- **Stacks 0FVB.** Let `(X, O_X)` be a ringed space
and let `K` and `E` be objects of `D(O_X)` with `E` perfect (Tag 08CM). The diagram

`H⁰(X, K ⊗^L E^∨) × H⁰(X, E) ⟶ H⁰(X, (K ⊗^L E^∨) ⊗^L E)`
`        ↓                               ↓`
`Hom_X(E, K) × H⁰(X, E)        ⟶       H⁰(X, K)`

commutes: the cup product `ξ ∪ η` (Section 0FKU, the relative cup product of Stacks 0B68 for
`(X, O_X) ⟶ (pt, Γ(X, O_X))`, `Stacks.SheafOfModules.globalCupProductZero`) followed by the map
induced on `H⁰` by `1_K ⊗ ε` and the unit constraint (`ε : E^∨ ⊗^L E ⟶ O_X` of Example 0FPC)
is the morphism `E ⟶ K` attached to `ξ` by the identification
`H⁰(X, K ⊗^L E^∨) = Hom_{D(O_X)}(E, K)` of Lemma 08DQ
(`Stacks.SheafOfModules.derivedTensorDualGlobalSectionsMap`), evaluated on `η`. -/
@[stacks 0FVB]
theorem derivedDualPairingSquare_cup (K E : DerivedCategory (StructureSheafModules X.sheaf))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) E)
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
        (((derivedTensor X.sheaf).obj K).obj (derivedDual X.sheaf E))) : Type u))
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj E) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).map
          (derivedDualContraction X.sheaf K E))
        (globalCupProductZero X (((derivedTensor X.sheaf).obj K).obj (derivedDual X.sheaf E)) E
          ξ η) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).map
          (derivedTensorDualGlobalSectionsMap X.sheaf E K ξ)) η := by
  rw [globalCupProductZero_eq_symm]
  convert derivedDualPairingSquare X K E hE ξ η using 1

end RingedSpace

end Stacks.SheafOfModules
