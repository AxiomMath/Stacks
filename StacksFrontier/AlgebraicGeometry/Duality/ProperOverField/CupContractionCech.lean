module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.PerfectSheafPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductSquareHypercohomologyClasses
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyPairingPrecomp
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBrutalDuality
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleLeftComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The cup product along a pairing of sheaves, computed by Čech cocycles

Let `X` be a scheme and `μ : ℱ ⊗ 𝒢 ⟶ 𝒲` a pairing of `𝒪_X`-modules. The cup product of
Cohomology, Section 0FKU followed by `μ`,

`Hⁱ(X, ℱ) ⊗ Hʲ(X, 𝒢) ⟶ Hⁱ⁺ʲ(X, 𝒲)`, `ξ ⊗ η ↦ μ(ξ ∪ η)`

(`Stacks.Duality.cupContraction`, the cup product used in Serre duality, [Stacks, Tag 0FW0], and
in the duality of Hodge cohomology, [Stacks, Tag 0FW4]), is computed by the Čech cup product of
Section 01FP along the bilinear map `β` of sheaves underlying `μ`, when Čech cohomology computes
the cohomology of the three sheaves. This is [Stacks, Tag 0FKV] for sheaves placed in degree
zero: the cup product of Section 0FKU followed by the canonical map to the total tensor complex is
the Čech cup product at the sheaf-tensor coefficients
(`Stacks.Cech.CupProductSquare.cupPairing_hypercohomologyToCohomologyModule`), and the
identification `Tot(ℱ[0] ⊗ 𝒢[0]) ≅ (ℱ ⊗ 𝒢)[0]` followed by `μ` carries the sheaf-tensor pairing to
the pairing attached to `β`.

## Main results

* `Stacks.Duality.cupContraction_hypercohomologyToCohomologyModule`: **the cup product along `μ`
  is the Čech cup product along `β`.**

## References

* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
attribute [local implicit_reducible] Stacks.Cech.CupProductSquare.tensorPlus
  Stacks.Cech.Hypercohomology.singlePlus

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace ComplexShape
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections)
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.DerivedTensor.RingedSite
open Stacks.Cech.Hypercohomology
open Stacks.Cech.CupProductSquare (hypercohomologyToCohomologyModule)
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.SheafOfModules.DerivedMonoidal (Mod)
open scoped CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace Stacks.Duality

open scoped Stacks.StandardDerivedModel
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

section Generic

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The identification `Tot(ℱ[0] ⊗ 𝒢[0]) ⟶ (ℱ ⊗ 𝒢)[0]`**, the morphism of complexes underlying
`Stacks.DerivedTensor.RingedSite.derivedTensorSingleToTensor`. -/
def singleTensorToSingle (F G : Mod R) :
    HomologicalComplex.mapBifunctor (singleComplex F) (singleComplex G)
        (Stacks.SheafOfModules.Tensor.sheafTensor R) (up ℤ) ⟶
      singleComplex (F ⊗ G) :=
  (HomologicalComplex.mapBifunctorSingleRightIso
      (Stacks.SheafOfModules.Tensor.sheafTensor R) (singleComplex F) G).hom ≫
    ((MonoidalCategory.tensorRight (C := Mod R) G).mapCochainComplexSingleFunctor 0).hom.app F

/-- `ℱ[0] ⊗^𝐋 𝒢[0] ⟶ (ℱ ⊗ 𝒢)[0]` is the canonical map to the total tensor complex followed by
`Tot(ℱ[0] ⊗ 𝒢[0]) ⟶ (ℱ ⊗ 𝒢)[0]`. -/
theorem derivedTensorSingleToTensor_eq [HasDerivedCategory.{u} (Mod R)] (F G : Mod R) :
    derivedTensorSingleToTensor F G =
      (canonicalDerivedTensorProduct R).toTensor (singleComplex F) (singleComplex G) ≫
        DerivedCategory.Q.map (singleTensorToSingle F G) :=
  rfl

/-- **`Tot(ℱ[0] ⊗ 𝒢[0]) ⟶ (ℱ ⊗ 𝒢)[0]` on the summand of bidegree `(0, 0)`** is the tensor product
of the identifications of the terms in degree zero. -/
theorem ιMapBifunctor_singleTensorToSingle_f (F G : Mod R) :
    HomologicalComplex.ιMapBifunctor (singleComplex F) (singleComplex G)
        (Stacks.SheafOfModules.Tensor.sheafTensor R) (up ℤ) 0 0 0 (by simp) ≫
      (singleTensorToSingle F G).f 0 =
    ((Stacks.SheafOfModules.Tensor.sheafTensor R).map
        (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom).app ((singleComplex G).X 0) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj F).map
        (HomologicalComplex.singleObjXSelf (up ℤ) 0 G).hom ≫
      (HomologicalComplex.singleObjXSelf (up ℤ) 0
        (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj F).obj G)).inv := by
  have h1 : HomologicalComplex.singleRightι (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (singleComplex F) G 0 ≫
      (HomologicalComplex.mapBifunctorSingleRightXIso (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (singleComplex F) G 0).hom =
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj ((singleComplex F).X 0)).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom := by
    have h := HomologicalComplex.mapBifunctorSingleRightXIso_inv
      (Stacks.SheafOfModules.Tensor.sheafTensor R) (singleComplex F) G 0
    have hι : HomologicalComplex.singleRightι (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (singleComplex F) G 0 =
        ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj ((singleComplex F).X 0)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom ≫
        (HomologicalComplex.mapBifunctorSingleRightXIso
          (Stacks.SheafOfModules.Tensor.sheafTensor R) (singleComplex F) G 0).inv := by
      rw [h, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    rw [hι, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hM := HomologicalComplex.singleMapHomologicalComplex_hom_app_self
    (MonoidalCategory.tensorRight (C := Mod R) G) (ComplexShape.up ℤ) 0 F
  have hnat := ((Stacks.SheafOfModules.Tensor.sheafTensor R).map
    (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom).naturality
      (HomologicalComplex.singleObjXSelf (up ℤ) 0 G).hom
  change HomologicalComplex.singleRightι (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (singleComplex F) G 0 ≫
      (HomologicalComplex.mapBifunctorSingleRightXIso (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (singleComplex F) G 0).hom ≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (MonoidalCategory.tensorRight (C := Mod R) G) (ComplexShape.up ℤ) 0).hom.app F).f 0 = _
  rw [reassoc_of% h1, hM, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ (HomologicalComplex.singleObjXSelf (up ℤ) 0
    (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj F).obj G)).inv) hnat

end Generic

variable {X : Scheme.{u}} {F G W : Mod X.sheaf}

/-- `ℱ[0] ⊗^𝐋 𝒢[0] ⟶ 𝒲[0]` is the canonical map to the total tensor complex followed by
`Tot(ℱ[0] ⊗ 𝒢[0]) ⟶ (ℱ ⊗ 𝒢)[0] ⟶ 𝒲[0]`. -/
theorem contractionMapOf_eq (μ : tensorModule F G ⟶ W) :
    contractionMapOf μ =
      ((canonicalDerivedTensorProduct X.sheaf).toTensor (singleComplex F) (singleComplex G) ≫
        DerivedCategory.Q.map (singleTensorToSingle (R := X.sheaf) F G)) ≫
          DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map μ) :=
  rfl

variable (X) in
/-- The cup product of Section 0FKU followed by `RΓ` of `Tot(ℱ[0] ⊗ 𝒢[0]) ⟶ (ℱ ⊗ 𝒢)[0] ⟶ 𝒲[0]`,
`Hⁱ(X, ℱ) ⊗ Hʲ(X, 𝒢) ⟶ Hⁱ⁺ʲ(X, 𝒲)`. -/
def contractionPairing (μ : tensorModule F G ⟶ W) (i j : ℤ) :
    cohomologyModule (DerivedCategory.Q.obj (singleComplex F)) i ⊗
        cohomologyModule (DerivedCategory.Q.obj (singleComplex G)) j ⟶
      cohomologyModule (DerivedCategory.Q.obj (singleComplex W)) (i + j) :=
  cupPairing (cupProductOnSpace X.toRingedSpace) (DerivedCategory.Q.obj (singleComplex F))
      (DerivedCategory.Q.obj (singleComplex G)) i j ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) (i + j)).map
      ((baseSections X.toRingedSpace).map
        (((Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans X.toRingedSpace).app
            (singleComplex F, singleComplex G) ≫
          DerivedCategory.Q.map (singleTensorToSingle (R := X.sheaf) F G)) ≫
          DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map μ)))

/-- `cupContraction` is `contractionPairing`. -/
theorem cupContraction_eq_contractionPairing (μ : tensorModule F G ⟶ W) (i j : ℤ) :
    cupContraction (cupProductOnSpace X.toRingedSpace) μ i j (i + j) rfl =
      contractionPairing X μ i j :=
  rfl

/-- **`contractionPairing` is `totalCupPairing` followed by `RΓ` of
`Tot(ℱ[0] ⊗ 𝒢[0]) ⟶ (ℱ ⊗ 𝒢)[0] ⟶ 𝒲[0]`.** -/
theorem contractionPairing_eq (μ : tensorModule F G ⟶ W) (i j : ℤ) :
    contractionPairing X μ i j =
      totalCupPairing (S := X.toRingedSpace) (singleComplex F) (singleComplex G) i j ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) (i + j)).map
          ((baseSections X.toRingedSpace).map (DerivedCategory.Q.map
            (singleTensorToSingle (R := X.sheaf) F G ≫
              (CochainComplex.singleFunctor _ 0).map μ))) := by
  unfold contractionPairing totalCupPairing
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
  refine congrArg (fun g => cupPairing (cupProductOnSpace X.toRingedSpace)
    (DerivedCategory.Q.obj (singleComplex F)) (DerivedCategory.Q.obj (singleComplex G)) i j ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) (i + j)).map g) ?_
  exact (congrArg (baseSections X.toRingedSpace).map ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (DerivedCategory.Q.map_comp _ _).symm))).trans
      ((baseSections X.toRingedSpace).map_comp _ _)

/-- **The morphism `Tot(ℱ[0] ⊗ 𝒢[0]) ⟶ (ℱ ⊗ 𝒢)[0] ⟶ 𝒲[0]` of bounded below complexes.** -/
def singleTensorToSinglePlus (μ : ((sheafTensor X.sheaf).obj F).obj G ⟶ W) :
    tensorPlusOf X.sheaf (singlePlus X.sheaf F 0) (singlePlus X.sheaf G 0)
        (Stacks.Cech.CupProductSquare.tensorPlus X.toRingedSpace (singlePlus X.sheaf F 0)
          (singlePlus X.sheaf G 0)).2 ⟶ singlePlus X.sheaf W 0 :=
  ObjectProperty.homMk (singleTensorToSingle (R := X.sheaf) F G ≫
    (CochainComplex.singleFunctor _ 0).map μ)

/-- The summand of bidegree `(0, 0)` of `Tot(ℱ[0] ⊗ 𝒢[0]) ⟶ 𝒲[0]` is the identification of the
terms in degree zero followed by `μ`. -/
theorem ιMapBifunctor_singleTensorToSinglePlus (μ : ((sheafTensor X.sheaf).obj F).obj G ⟶ W) :
    HomologicalComplex.ιMapBifunctor (singlePlus X.sheaf F 0).1 (singlePlus X.sheaf G 0).1
        (sheafTensor X.sheaf) (up ℤ) 0 0 0 (by simp) ≫ (singleTensorToSinglePlus μ).hom.f 0 =
      ((sheafTensor X.sheaf).map (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom).app
          ((singlePlus X.sheaf G 0).1.X 0) ≫
        ((sheafTensor X.sheaf).obj F).map (HomologicalComplex.singleObjXSelf (up ℤ) 0 G).hom ≫
          μ ≫ (HomologicalComplex.singleObjXSelf (up ℤ) 0 W).inv := by
  have h := ιMapBifunctor_singleTensorToSingle_f (R := X.sheaf) F G
  change HomologicalComplex.ιMapBifunctor (singleComplex F) (singleComplex G)
      (sheafTensor X.sheaf) (up ℤ) 0 0 0 (by simp) ≫
      ((singleTensorToSingle (R := X.sheaf) F G).f 0 ≫
        ((CochainComplex.singleFunctor _ 0).map μ).f 0) = _
  rw [← Category.assoc, h]
  change (_ ≫ _ ≫ _) ≫ ((HomologicalComplex.single _ (up ℤ) 0).map μ).f 0 = _
  rw [HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- **The sheaf-tensor pairing of `ℱ[0]` and `𝒢[0]` followed by `Tot(ℱ[0] ⊗ 𝒢[0]) ⟶ 𝒲[0]` is the
pairing of sheaves in degree zero attached to the bilinear map `β` underlying `μ`.** -/
theorem sheafTensorPairingOf_comp_singleTensorToSinglePlus
    (μ : ((sheafTensor X.sheaf).obj F).obj G ⟶ W) (β : Stacks.BilinearMap F.val G.val W.val)
    (hβ : bilinearPairing β = Stacks.Cech.SheafTensorPairing.sheafTensorPairing X.sheaf ⊤ F G ≫
      (Stacks.Cech.ModuleCupProduct.sectionsFunctor X.sheaf ⊤).map μ) :
    Stacks.Cech.LinearCupProduct.ComplexPairing.comp
        (sheafTensorPairingOf X.sheaf (singlePlus X.sheaf F 0) (singlePlus X.sheaf G 0)
          (Stacks.Cech.CupProductSquare.tensorPlus X.toRingedSpace (singlePlus X.sheaf F 0)
            (singlePlus X.sheaf G 0)).2)
        ((Stacks.Cech.Refinement.sectionsComplex X.sheaf).map (singleTensorToSinglePlus μ).hom) =
      singlePairing (bilinearPairing β) := by
  refine Stacks.Cech.LinearCupProduct.ComplexPairing.ext' fun a b n hn => ?_
  rw [Stacks.Cech.LinearCupProduct.ComplexPairing.comp_μ]
  change (Stacks.Cech.SheafTensorPairing.sheafTensorPairing X.sheaf ⊤
      ((singlePlus X.sheaf F 0).1.X a) ((singlePlus X.sheaf G 0).1.X b) ≫
      (Stacks.Cech.ModuleCupProduct.sectionsFunctor X.sheaf ⊤).map
        (HomologicalComplex.ιMapBifunctor (singlePlus X.sheaf F 0).1 (singlePlus X.sheaf G 0).1
          (sheafTensor X.sheaf) (up ℤ) a b n hn)) ≫
    (Stacks.Cech.ModuleCupProduct.sectionsFunctor X.sheaf ⊤).map
      ((singleTensorToSinglePlus μ).hom.f n) = _
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    obtain rfl : n = 0 := by omega
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ιMapBifunctor_singleTensorToSinglePlus,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      ← Category.assoc, ← Stacks.Cech.SheafTensorPairing.sheafTensorPairing_naturality_left,
      Category.assoc, ← Category.assoc (Stacks.Cech.SheafTensorPairing.sheafTensorPairing _ _ _ _),
      ← Stacks.Cech.SheafTensorPairing.sheafTensorPairing_naturality_right,
      singlePairing_μ_zero, hβ]
    simp only [Category.assoc, CategoryTheory.Functor.map_comp]
    rfl
  · rw [singlePairing_μ_of_ne _ _ _ _ _ hab]
    have := Stacks.Cohomology.CechDerived.preservesZeroMorphisms_sectionsPresheafFunctor.{u}
      (ringSheaf X.sheaf) ⊤
    have hz : IsZero (((sheafTensor X.sheaf).obj ((singlePlus X.sheaf F 0).1.X a)).obj
        ((singlePlus X.sheaf G 0).1.X b)) := by
      by_cases ha : a = 0
      · exact HomologicalComplex.isZero_obj_obj_single_obj_X_right (sheafTensor X.sheaf)
          (singlePlus X.sheaf F 0).1 G a b (fun hb => hab ⟨ha, hb⟩)
      · exact HomologicalComplex.isZero_obj_obj_single_obj_X_left (sheafTensor X.sheaf) F
          (singlePlus X.sheaf G 0).1 a b ha
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
      hz.eq_of_src (HomologicalComplex.ιMapBifunctor (singlePlus X.sheaf F 0).1
        (singlePlus X.sheaf G 0).1 (sheafTensor X.sheaf) (up ℤ) a b n hn ≫
          (singleTensorToSinglePlus μ).hom.f n) 0,
      CategoryTheory.Functor.map_zero, Limits.comp_zero]

/-- **The cup product along `μ`, `ξ ⊗ η ↦ μ(ξ ∪ η)`, is the Čech cup product of Section 01FP
along the bilinear map `β` underlying `μ`** ([Stacks, Tag 0FKV] for sheaves placed in degree
zero), under the identification `θ` of the two models of hypercohomology, when Čech cohomology
computes the cohomology of `ℱ` and `𝒢`. -/
theorem cupContraction_hypercohomologyToCohomologyModule (μ : tensorModule F G ⟶ W)
    (β : Stacks.BilinearMap F.val G.val W.val)
    (hβ : bilinearPairing β = Stacks.Cech.SheafTensorPairing.sheafTensorPairing X.sheaf ⊤ F G ≫
      (Stacks.Cech.ModuleCupProduct.sectionsFunctor X.sheaf ⊤).map μ)
    (hF : CechComputes X.sheaf (singlePlus X.sheaf F 0))
    (hG : CechComputes X.sheaf (singlePlus X.sheaf G 0)) (i j : ℤ)
    (x : hypercohomology X.sheaf (singlePlus X.sheaf F 0) i)
    (y : hypercohomology X.sheaf (singlePlus X.sheaf G 0) j) :
    (cupContraction (cupProductOnSpace X.toRingedSpace) μ i j (i + j) rfl).hom
        (hypercohomologyToCohomologyModule X.toRingedSpace (singlePlus X.sheaf F 0) i x ⊗ₜ
          hypercohomologyToCohomologyModule X.toRingedSpace (singlePlus X.sheaf G 0) j y) =
      hypercohomologyToCohomologyModule X.toRingedSpace (singlePlus X.sheaf W 0) (i + j)
        (cup X.sheaf hF hG (singlePairing (bilinearPairing β)) i j (i + j) rfl x y) := by
  have e₀ := congrArg (fun φ => φ.hom (hypercohomologyToCohomologyModule X.toRingedSpace
      (singlePlus X.sheaf F 0) i x ⊗ₜ hypercohomologyToCohomologyModule X.toRingedSpace
        (singlePlus X.sheaf G 0) j y))
    ((cupContraction_eq_contractionPairing μ i j).trans (contractionPairing_eq μ i j))
  have e₁ := Stacks.Cech.CupProductSquare.cupPairing_hypercohomologyToCohomologyModule
    X.toRingedSpace (singlePlus X.sheaf F 0) (singlePlus X.sheaf G 0) hF hG i j x y
  have e₂ := Stacks.Cech.CupProductSquare.hypercohomologyToCohomologyModule_hypercohomologyMap
    X.toRingedSpace (singleTensorToSinglePlus μ) (i + j)
    (cup X.sheaf hF hG (sheafTensorPairingOf X.sheaf (singlePlus X.sheaf F 0)
      (singlePlus X.sheaf G 0) (Stacks.Cech.CupProductSquare.tensorPlus X.toRingedSpace
        (singlePlus X.sheaf F 0) (singlePlus X.sheaf G 0)).2) i j (i + j) rfl x y)
  have e₃ := cup_comp X.sheaf hF hG (sheafTensorPairingOf X.sheaf (singlePlus X.sheaf F 0)
      (singlePlus X.sheaf G 0) (Stacks.Cech.CupProductSquare.tensorPlus X.toRingedSpace
        (singlePlus X.sheaf F 0) (singlePlus X.sheaf G 0)).2) (singleTensorToSinglePlus μ) i j
    (i + j) rfl x y
  rw [sheafTensorPairingOf_comp_singleTensorToSinglePlus μ β hβ] at e₃
  refine e₀.trans (Eq.trans ?_ ((e₂.symm.trans (congrArg _ e₃.symm))))
  exact congrArg _ e₁

/-- `cupContraction_hypercohomologyToCohomologyModule` with the target degree given by an
equation. -/
theorem cupContraction_hypercohomologyToCohomologyModule' (μ : tensorModule F G ⟶ W)
    (β : Stacks.BilinearMap F.val G.val W.val)
    (hβ : bilinearPairing β = Stacks.Cech.SheafTensorPairing.sheafTensorPairing X.sheaf ⊤ F G ≫
      (Stacks.Cech.ModuleCupProduct.sectionsFunctor X.sheaf ⊤).map μ)
    (hF : CechComputes X.sheaf (singlePlus X.sheaf F 0))
    (hG : CechComputes X.sheaf (singlePlus X.sheaf G 0)) (i j m : ℤ) (hm : i + j = m)
    (x : hypercohomology X.sheaf (singlePlus X.sheaf F 0) i)
    (y : hypercohomology X.sheaf (singlePlus X.sheaf G 0) j) :
    (cupContraction (cupProductOnSpace X.toRingedSpace) μ i j m hm).hom
        (hypercohomologyToCohomologyModule X.toRingedSpace (singlePlus X.sheaf F 0) i x ⊗ₜ
          hypercohomologyToCohomologyModule X.toRingedSpace (singlePlus X.sheaf G 0) j y) =
      hypercohomologyToCohomologyModule X.toRingedSpace (singlePlus X.sheaf W 0) m
        (cup X.sheaf hF hG (singlePairing (bilinearPairing β)) i j m hm x y) := by
  subst hm
  exact cupContraction_hypercohomologyToCohomologyModule μ β hβ hF hG i j x y

end Stacks.Duality

end
