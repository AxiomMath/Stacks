module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoAlongAComposite

/-!
# The derived tensor products of a ringed space and Tag 079U, on representatives

Let `(Z, 𝒪_Z)` be a ringed space.  Each of the two derived tensor products of Tag 06YU carried
by this development comes with a canonical map `QA ⊗^L QB ⟶ Q Tot(A ⊗ B)` to the ordinary total
tensor complex, defined for arbitrary complexes `A`, `B`.  This file proves that the comparison
`tensorBridge` of the two derived tensor products carries one canonical map to the other, and
that for a morphism of ringed spaces `h : X ⟶ Y` the isomorphism of Tag 079U at the derived
tensor product of the internal hom,

`Lh^*(QA ⊗^L QB) ≅ Lh^*QA ⊗^L Lh^*QB`,

is read on the canonical maps as the comparison `h^* Tot(A ⊗ B) ≅ Tot(h^*A ⊗ h^*B)` of Tag 01CD,
for arbitrary complexes `A`, `B` of `𝒪_Y`-modules.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.tensorBridge_hom_app_of_kFlat`
* `Stacks.Cohomology.DerivedInternalHomPullback.tensorBridge_hom_app_comp_toTensor`
* `Stacks.Cohomology.DerivedInternalHomPullback.pullbackTensorIso_inv_app_comp_toTensor`
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedPullbackTensor

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

noncomputable section

variable (Z : RingedSpace.{u, u})

attribute [local instance] kFlatQPair_isLocalization

/-- **The comparison of the two derived tensor products at a pair of K-flat objects of the
homotopy category is the models comparison it was descended from.** -/
theorem tensorBridge_hom_app_kFlatQPair
    (M : (CochainComplex.KFlatBifunctor.kFlatObjects
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).FullSubcategory ×
        (CochainComplex.KFlatBifunctor.kFlatObjects
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).FullSubcategory) :
    (tensorBridge Z).hom.app ((kFlatQPair (Y := Z)).obj M) = (tensorBridgeModels Z).hom.app M := by
  dsimp only [tensorBridge]
  rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp

/-- Cancelling an isomorphism on the left and one on the right. -/
private lemma eq_of_comp_hom_eq {C : Type*} [Category C] {a b c d : C} (iL : a ≅ b)
    (iR : c ≅ d) (x m : b ⟶ d) (h : iL.hom ≫ x = (iL.hom ≫ m ≫ iR.inv) ≫ iR.hom) : x = m := by
  simpa using h

/-- **On a pair of K-flat complexes the comparison of the two derived tensor products is the
composite of their two K-flat comparisons.** -/
theorem tensorBridge_hom_app_of_kFlat
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hA : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z A)
    (hB : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z B) :
    (tensorBridge Z).hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) =
      (tensorBridgeModel Z A B hA hB).hom := by
  let M : (CochainComplex.KFlatBifunctor.kFlatObjects
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).FullSubcategory ×
        (CochainComplex.KFlatBifunctor.kFlatObjects
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).FullSubcategory :=
    (⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj A, hA⟩,
      ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj B, hB⟩)
  have h := (tensorBridge Z).hom.naturality (kFlatQPairIso M).hom
  rw [tensorBridge_hom_app_kFlatQPair Z M] at h
  have key : (tensorBridgeModels Z).hom.app M =
      ((pullbackTensorUncurried Z).mapIso (kFlatQPairIso M)).hom ≫
        (tensorBridgeModel Z A B hA hB).hom ≫
          ((internalHomTensorUncurried Z).mapIso (kFlatQPairIso M)).inv := rfl
  have h' : ((pullbackTensorUncurried Z).mapIso (kFlatQPairIso M)).hom ≫
        (tensorBridge Z).hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) =
      (tensorBridgeModels Z).hom.app M ≫
        ((internalHomTensorUncurried Z).mapIso (kFlatQPairIso M)).hom := h
  exact eq_of_comp_hom_eq _ _ _ _
    (h'.trans (congrArg (· ≫ ((internalHomTensorUncurried Z).mapIso (kFlatQPairIso M)).hom) key))

/-- A naturality square of a bifunctor, read on the functor on pairs. -/
private lemma uncurry_square {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D ⥤ E) {A A' : C} {B B' : D} (f : A ⟶ A') (g : B ⟶ B') {T : E}
    (t : (F.obj A').obj B' ⟶ T) {S : E} (x : (F.obj A).obj B ⟶ S) (s : S ⟶ T)
    (h : (F.map f).app B ≫ (F.obj A').map g ≫ t = x ≫ s) :
    (Functor.uncurry.obj F).map (f ×ₘ g) ≫ t = x ≫ s := by
  simpa only [Functor.uncurry_obj_map, Category.assoc] using h

/-- The canonical map `QA ⊗^L QB ⟶ Q Tot(A ⊗ B)` of the derived tensor product of the internal
hom, at the spelling of the category of modules of the derived pullback. -/
def internalHomToTensor
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (internalHomTensorUncurried Z).obj (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ⟶
      DerivedCategory.Q.obj
        ((totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (A, B)) :=
  (internalHomTensorProduct Z).toTensor A B

/-- `internalHomToTensor Z A B` is the map `toTensor A B` of the derived tensor product of the
internal hom. -/
theorem internalHomToTensor_eq
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    internalHomToTensor Z A B = (internalHomTensorProduct Z).toTensor A B := rfl

/-- The canonical map of the derived tensor product of the internal hom is natural. -/
theorem internalHomToTensor_naturality
    {A A' B B' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ}
    (a : A ⟶ A') (b : B ⟶ B') :
    (internalHomTensorUncurried Z).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        internalHomToTensor Z A' B' =
      internalHomToTensor Z A B ≫ DerivedCategory.Q.map
        ((totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).map (a ×ₘ b)) :=
  (uncurry_square _ _ _ _ _ _ ((internalHomTensorProduct Z).toTensor_naturality a b)).trans
    (congrArg (internalHomToTensor Z A B ≫ DerivedCategory.Q.map ·)
      (totalComplexPair_map
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) a b).symm)

/-- At a pair of K-flat complexes the comparison of the two derived tensor products carries the
canonical map to the total tensor complex of the first to that of the second. -/
theorem tensorBridge_hom_app_comp_toTensor_of_kFlat
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hA : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z A)
    (hB : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z B) :
    (tensorBridge Z).hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
        internalHomToTensor Z A B =
      (derivedToTensorNatTrans Z).app (A, B) := by
  have e₁ : internalHomToTensor Z A B =
      ((internalHomTensorProduct Z).comparison A B hA hB).hom :=
    ((internalHomTensorProduct Z).toTensor_eq_comparisonRight A B hB).trans
      (congrArg Iso.hom ((internalHomTensorProduct Z).comparisonRight_eq_comparison A B hA hB))
  have e₂ : (derivedToTensorNatTrans Z).app (A, B) =
      ((pullbackTensorProduct Z).comparison A B hA hB).hom :=
    ((pullbackTensorProduct Z).toTensor_eq_comparisonRight A B hB).trans
      (congrArg Iso.hom ((pullbackTensorProduct Z).comparisonRight_eq_comparison A B hA hB))
  rw [tensorBridge_hom_app_of_kFlat Z A B hA hB, e₁, e₂]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans
    (Category.comp_id _))

/-- Transporting an identity along a naturality square whose leftmost leg is invertible. -/
private lemma eq_of_square {C : Type*} [Category C] {P P' R R' S T : C}
    (q : P' ⟶ P) [IsIso q] (b : P ⟶ R) (b' : P' ⟶ R') (r : R' ⟶ R) (t : R ⟶ T) (t' : R' ⟶ S)
    (s : S ⟶ T) (tt : P ⟶ T) (t'' : P' ⟶ S)
    (hb : q ≫ b = b' ≫ r) (ht : r ≫ t = t' ≫ s) (hkey : b' ≫ t' = t'') (htt : q ≫ tt = t'' ≫ s) :
    b ≫ t = tt := by
  rw [← cancel_epi q, reassoc_of% hb, ht, reassoc_of% hkey, htt]

/-- **The comparison of the two derived tensor products carries the canonical map to the total
tensor complex of the first to that of the second**, at an arbitrary pair of complexes. -/
theorem tensorBridge_hom_app_comp_toTensor
    (A B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (tensorBridge Z).hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
        internalHomToTensor Z A B =
      (derivedToTensorNatTrans Z).app (A, B) := by
  obtain ⟨A', pA, hA', -, hqA, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution Z A
  obtain ⟨B', pB, hB', -, hqB, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution Z B
  have hq : IsIso ((pullbackTensorUncurried Z).map
      (DerivedCategory.Q.map pA ×ₘ DerivedCategory.Q.map pB)) :=
    Iso.isIso_hom ((pullbackTensorUncurried Z).mapIso
      ((asIso (DerivedCategory.Q.map pA)).prod (asIso (DerivedCategory.Q.map pB))))
  exact eq_of_square _ _ _ _ _ _ _ _ _
    ((tensorBridge Z).hom.naturality (DerivedCategory.Q.map pA ×ₘ DerivedCategory.Q.map pB))
    (internalHomToTensor_naturality Z pA pB)
    (tensorBridge_hom_app_comp_toTensor_of_kFlat Z A' B' hA' hB')
    ((derivedToTensorNatTrans Z).naturality (pA ×ₘ pB))

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

/-- The shape of the comparison of Tag 079U against the canonical maps to total tensor complexes,
with every object a variable. -/
private lemma model_square {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ G G' K L : C}
    (binv : A₀ ⟶ A₁) (Dhom : A₂ ⟶ A₁) (Dinv : A₁ ⟶ A₂) (bY : A₂ ⟶ A₃) (tY : A₃ ⟶ A₄)
    (n : A₄ ⟶ L) (t'Y : A₂ ⟶ A₄) (T'ν : A₁ ⟶ G') (tt'X : G' ⟶ K) (Mhom : L ⟶ K) (Minv : K ⟶ L)
    (Tν : A₀ ⟶ G) (Bhom : G' ⟶ G) (Binv : G ⟶ G') (ttX : G ⟶ K)
    (pinv : A₀ ⟶ A₃) (hinv : pinv = binv ≫ Dinv ≫ bY)
    (hD : Dinv ≫ Dhom = 𝟙 _) (hM : Mhom ≫ Minv = 𝟙 _) (hB : Binv ≫ Bhom = 𝟙 _)
    (hY : bY ≫ tY = t'Y) (hE1 : Dhom ≫ T'ν ≫ tt'X = t'Y ≫ n ≫ Mhom)
    (hnat : Tν ≫ Binv = binv ≫ T'ν) (hX : Bhom ≫ ttX = tt'X) :
    pinv ≫ tY ≫ n = Tν ≫ ttX ≫ Minv := by
  subst hinv
  have h₁ : t'Y ≫ n = (Dhom ≫ T'ν ≫ tt'X) ≫ Minv := by
    rw [hE1]; simp only [Category.assoc, hM, Category.comp_id]
  simp only [Category.assoc]
  rw [reassoc_of% hY, h₁]
  simp only [Category.assoc, reassoc_of% hD]
  rw [← reassoc_of% hnat, ← hX]
  simp only [Category.assoc]
  rw [reassoc_of% hB]

/-- The inverse of Tag 079U at the derived tensor product of the internal hom, componentwise. -/
theorem pullbackTensorIso_inv_app
    (K L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (pullbackTensorIso h).inv.app (K, L) =
      (tensorBridge X).inv.app ((derivedPullbackFunctor h).obj K,
          (derivedPullbackFunctor h).obj L) ≫
        (derivedPullbackTensorIso h).inv.app (K, L) ≫
          (derivedPullbackFunctor h).map ((tensorBridge Y).hom.app (K, L)) := by
  simp only [pullbackTensorIso, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Iso.symm_inv, Functor.whiskerRight_app, Category.assoc]
  rfl

/-- **Tag 079U at the derived tensor product of the internal hom, on K-flat representatives.**
For K-flat complexes `H`, `E` of `𝒪_Y`-modules the inverse of the comparison
`Lh^*(QH ⊗^L QE) ≅ Lh^*QH ⊗^L Lh^*QE`, followed by `Lh^*` of the canonical map to
`Q Tot(H ⊗ E)` and by `Lh^*Q ⟶ Q h^*`, is the canonical map
`Lh^*QH ⊗^L Lh^*QE ⟶ Q h^*H ⊗^L Q h^*E ⟶ Q Tot(h^*H ⊗ h^*E)` followed by the comparison of
Tag 01CD. -/
theorem pullbackTensorIso_inv_app_comp_toTensor_of_kFlat
    (H E : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hH : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y H)
    (hE : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y E) :
    (pullbackTensorIso h).inv.app (DerivedCategory.Q.obj H, DerivedCategory.Q.obj E) ≫
        (derivedPullbackFunctor h).map (internalHomToTensor Y H E) ≫
          (derivedPullbackNatTrans h).app
            ((totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (H, E)) =
      (internalHomTensorUncurried X).map
          ((derivedPullbackNatTrans h).app H ×ₘ (derivedPullbackNatTrans h).app E) ≫
        internalHomToTensor X ((pullbackComplex h).obj H) ((pullbackComplex h).obj E) ≫
          DerivedCategory.Q.map ((pullbackTensorComplexNatIso h).inv.app (H, E)) := by
  have hY := congrArg (derivedPullbackFunctor h).map
    (tensorBridge_hom_app_comp_toTensor Y H E)
  rw [Functor.map_comp] at hY
  have hX := tensorBridge_hom_app_comp_toTensor X ((pullbackComplex h).obj H)
    ((pullbackComplex h).obj E)
  have hE1 := derivedPullbackTensorIso_hom_app_comp_derivedToTensor h H E hH hE
  have hnat := (tensorBridge X).inv.naturality
    ((derivedPullbackNatTrans h).app H ×ₘ (derivedPullbackNatTrans h).app E)
  have hE1' : (derivedPullbackTensorIso h).hom.app
        (DerivedCategory.Q.obj H, DerivedCategory.Q.obj E) ≫
      (pullbackTensorUncurried X).map
          ((derivedPullbackNatTrans h).app H ×ₘ (derivedPullbackNatTrans h).app E) ≫
        (derivedToTensorNatTrans X).app ((pullbackComplex h).obj H, (pullbackComplex h).obj E) =
      (derivedPullbackFunctor h).map ((derivedToTensorNatTrans Y).app (H, E)) ≫
        (derivedPullbackNatTrans h).app
          ((totalComplexPair
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (H, E)) ≫
        DerivedCategory.Q.map ((pullbackTensorComplexNatIso h).hom.app (H, E)) := hE1
  have hnat' : (internalHomTensorUncurried X).map
        ((derivedPullbackNatTrans h).app H ×ₘ (derivedPullbackNatTrans h).app E) ≫
      (tensorBridge X).inv.app (DerivedCategory.Q.obj ((pullbackComplex h).obj H),
        DerivedCategory.Q.obj ((pullbackComplex h).obj E)) =
      (tensorBridge X).inv.app ((derivedPullbackFunctor h).obj (DerivedCategory.Q.obj H),
          (derivedPullbackFunctor h).obj (DerivedCategory.Q.obj E)) ≫
        (pullbackTensorUncurried X).map
          ((derivedPullbackNatTrans h).app H ×ₘ (derivedPullbackNatTrans h).app E) := hnat
  exact model_square _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pullbackTensorIso_inv_app h _ _)
    ((derivedPullbackTensorIso h).app _).inv_hom_id
    (DerivedCategory.Q.mapIso ((pullbackTensorComplexNatIso h).app (H, E))).hom_inv_id
    ((tensorBridge X).app _).inv_hom_id hY hE1' hnat' hX


end

end Stacks.Cohomology.DerivedInternalHomPullback
